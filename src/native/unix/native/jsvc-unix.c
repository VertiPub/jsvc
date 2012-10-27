/* Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/* @version $Id: jsvc-unix.c 1293002 2012-02-23 22:48:24Z mturk $ */
#include "jsvc.h"

#include <signal.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <pwd.h>
#include <grp.h>
#include <errno.h>
#ifdef OS_LINUX
#include <sys/prctl.h>
#include <sys/syscall.h>
#define _LINUX_FS_H
#include <linux/capability.h>
#ifdef HAVE_LIBCAP
#include <sys/capability.h>
#endif
#endif
#include <time.h>
#include <semaphore.h>
#include <limits.h>
#include <assert.h>

/* This code does the following... 
 *
 * 1. main() initializes and validates.  Specifically:
 *    a. parses command-line args
 *    b. if user is specified, tests switching to that user in a separate proc.
 *    c. reads jvm info based on value of JAVA_HOME env var
 * 
 * 2. Call controller_main()
 *    a. if detach is specified (defaults to true), runs the controller in a
 *       background process.   Otherwise controller_main() is called in the
 *       original process.
 *    b. writes it's own pid to an external pid file
 *    c. installs signal handlers that will forward signals it catches to the
 *       jvm process
 *    d. the controller forks a new process for the jvm.  that process calls
 *       jvm_main().
 *    e. monitors the jvm process, restarting it if it is killed by a signal
 *       other than one it forwarded.
 * 
 * 3. The jvm process calls jvm_main()
 *    a. creates a new jvm using jni
 *    b. calls the org.apache.commons.daemon.Daemon.init() method via JNI as the
 *       main user (probably root).   Daemon implementations can bind to 
 *       privileged ports, etc.
 *    c. if user is specified in the command-line args, calls drop_privileges() 
 *       to switch to the user.
 *    d. calls the org.apache.commons.daemon.Daemon.start() method via JNI.
 *       Daemon implementations can start processing requests now that they
 *       are no longer running as root.
 *    e. runs until either a signal instructs it to exit or the jvm exits.
 */

/* Try restarting a jvm no more than once every x seconds. */
static time_t COOLDOWN_SEC = 30;

/* absolute path to cronolog file without extension myst be passed on the 
 * command line.   Examples:
 * 
 * /var/log/mydaemon_stderr
 * /var/log/mydaemon_stdout
 * /var/log/mydaemon (for combined stderr/stdout)
 * 
 * With this format cronolog will rotate daily and always maintain a date-less
 * symbolic link to the current file. 
 */
static const char * const CRONO_FMT =
        "cronolog -S %s.log %s-%%Y-%%m-%%d.log";

/* If the JVM exits with exit code 123, the controller will recreate it. */
static const int RELOAD_CODE = 123;

/* Max wait for stop */
static const int STOP_TIMEOUT_SEC = 60;

/* The following variables are volatile and global to the compilation unit
 * because they are shared with signal handlers
 */
static volatile pid_t jvm_pid = -1;
static volatile int reload_jvm = 0;

static sem_t controller_signal;
static sem_t jvm_signal;

static int controller_main(
        const arg_data *args,
        const struct home_data *jvm_info,
        const struct passwd *user,
        sem_t *sem);

static int jvm_main(
        const arg_data *args,
        const struct home_data *jvm_info,
        const struct passwd *user);

static void controller_signal_handler(int signo, siginfo_t *info, void *ctx);

static int install_controller_signal_handler(void);

static int install_jvm_signal_handler(void);

static void jvm_signal_handler(int signo);

typedef enum {
    SUCCESS = 0,
    NO_FILE = 1,
    ERROR = 2
} read_pid_status;

static read_pid_status read_controller_pid_file(
        const arg_data *args,
        pid_t *controller_pid);

static int write_controller_pid_file(
        const arg_data *args,
        pid_t controller_pid);

static int delete_controller_pid_file(const arg_data *args);

static int read_and_validate_user(const char *username, struct passwd *user);

static int redirect_stdout_stderr(
        const arg_data *args,
        FILE **crono_err,
        FILE **crono_out);

static void close_stdout_stderr(FILE *crono_err, FILE *crono_out);

static int drop_privileges(const struct passwd *user);

static int stop_controller(const arg_data *args);

static int print_java_version(
        const arg_data *args,
        const struct home_data *jvm_info);

typedef enum {
    SUCCESS_EXIT = 0,
    ERROR_EXIT = 1,
    SIGNAL_EXIT = 2,
    INTERNAL_ERROR = 3,
    INTERRUPTED = 4,
    CHILD_GONE = 5
} child_status;

static child_status wait_for_child(
        const char *parent_name,
        const char *child_name,
        pid_t child_pid,
        int *exit_code,
        int *signo,
        int wait_options);

static int sem_wait_tolerate_eintr(sem_t *sem);

int main(int argc, const char **argv) {
    arg_data *args = NULL;
    struct passwd user;
    struct home_data *jvm_info = NULL;
    pid_t controller_pid = 0;
    char sem_name[NAME_MAX - 4]; /* NAME_MAX - 4 from manpage */
    sem_t *sem = NULL;
    int result = 0;

    memset(&user, 0, sizeof (user));

    args = arguments(argc, argv);

    if (!args) {
        log_error("Cannot parse command-line arguments");

        help(NULL);

        return 1;
    }

    if (true == args->stop) {
        return 0 == stop_controller(args) ? 0 : 1;
    }

    /* read jvm details */

    jvm_info = home(args->home);

    if (!jvm_info) {
        log_error("Cannot determine jvm details");

        return 1;
    }

    if (args->help) {
        help(jvm_info);

        return 0;
    }

    if (args->vers) {
        return 0 == print_java_version(args, jvm_info) ? 0 : 1;
    }

    /* Start the daemon */

    /* map username to uid and gid, then try to fork and su to that user */

    if (args->user && 0 != read_and_validate_user(args->user, &user)) {
        return 1;
    }

    snprintf(sem_name, sizeof (sem_name) - 1, "jsvc_sem1_%d", getpid());
    sem_name[sizeof (sem_name) - 1] = 0;

    sem = sem_open(sem_name, O_CREAT, 0644, 0);

    if (NULL == sem) {
        fprintf(stderr, "Cannot init controller semaphore: %s",
                strerror(errno));

        return 1;
    }

    if (args->dtch) {
        log_debug("Detaching controller process");

        controller_pid = fork();

        if (0 > controller_pid) {
            log_error("Cannot detach controller process: %s", strerror(errno));

            return -1;
        }

        if (0 == controller_pid) {
            /* In child/controller process */

            /* Create a new session with the controller process as its leader */

            if (0 > setsid()) {
                log_error("Cannot create new session: %s", strerror(errno));

                return -1;
            }

            /* then run the controller_main() below */

        } else {
            /* In parent/original process */

            /* Wait for the controller proc to signal it has detached */

            if (0 != sem_wait_tolerate_eintr(sem)) {
                log_error("Cannot wait for controller process");

                return -1;
            }

            if (0 != sem_close(sem)) {
                log_error("Cannot close controller semaphore: %s",
                        strerror(errno));
            }

            /* controller has detached */

            log_debug("Controller detached, exiting to shell");

            return 0;
        }
    }

    /* Start the monitoring process (controller). */

    result = controller_main(args, jvm_info, &user, sem);

    if (!args->dtch) {
        if (0 != sem_close(sem)) {
            log_error("Cannot close controller semaphore: %s",
                    strerror(errno));
        }
    }

    return 0 == result ? result : 1;
}

int controller_main(
        const arg_data *args,
        const struct home_data *jvm_info,
        const struct passwd *user,
        sem_t *sem) {
    FILE *crono_err = NULL;
    FILE *crono_out = NULL;
    int first_time = 1;
    time_t last_jvm_start_sec = 0;
    time_t now = 0;

    if (0 != sem_init(&controller_signal, 0, 0)) {
        log_error("Cannot initialize semaphore: %s", strerror(errno));

        return 1;
    }

    /* Install controller signal handlers.  */

    if (0 != install_controller_signal_handler()) {
        return -1;
    }

    /* Redirect stderr and stdout to cronolog.   Cronlog will do log rotation.
     * Child processes (JVMs) will inherit the redirected stderr and stdout 
     */

    if (0 != redirect_stdout_stderr(args, &crono_err, &crono_out)) {
        return -1;
    }

    /* Until the controller is instructed to exit or a jvm process exits 
     * gracefully (is not terminated by a signal), try to keep one jvm
     * process running at all times
     */

    while (1) {

        /* Start a new jvm process if no jvm process is currently running */

        if (0 > jvm_pid) {
            /* Do not try to start a new JVM more than once every COOLDOWN_SEC */

            now = time(NULL);

            if (now - last_jvm_start_sec < COOLDOWN_SEC) {
                int wait = COOLDOWN_SEC - (now - last_jvm_start_sec);
                
                log_debug("Waiting for %d seconds before starting JVM", wait);
                
                sleep(wait);

                last_jvm_start_sec = time(NULL);
            } else {
                last_jvm_start_sec = now;
            }

            jvm_pid = fork();

            if (0 > jvm_pid) {
                log_error("Cannot fork jvm process: %s", strerror(errno));

                delete_controller_pid_file(args);

                return -1;
            }

            if (0 == jvm_pid) {
                /* In jvm process */

                return jvm_main(args, jvm_info, user);
            }
        }

        /* In controller process */

        if (first_time) {
            /* First time through, write controller pid to an external pid file 
             * and tell the original process that the controller has forked
             * its first jvm.  This could be improved a bit - ideally we'd 
             * propogate any jvm start failure all the way back to the original
             * process/shell.
             */

            if (0 != write_controller_pid_file(args, getpid())) {
                log_error("Cannot save controller pid to a file");

                return -1;
            }

            if (0 != sem_post(sem)) {
                log_error("Cannot signal main process: %s", strerror(errno));

                delete_controller_pid_file(args);

                return -1;
            }

            first_time = 0;
        }

        /* Wait until we catch a signal. */

        if (0 != sem_wait_tolerate_eintr(&controller_signal)) {
            log_error("Controller cannot wait for signal");

            delete_controller_pid_file(args);

            return -1;
        }

        if (reload_jvm) {
            jvm_pid = -1;

            continue;
        }

        break;
    }

    log_debug("Controller shutdown initiated");

    delete_controller_pid_file(args);

    /* Send cronolog an EOF on its stdin so it will exit. */

    close_stdout_stderr(crono_err, crono_out);

    return 0;
}

int jvm_main(
        const arg_data *args,
        const struct home_data *jvm_info,
        const struct passwd *user) {

    if (0 != sem_init(&jvm_signal, 0, 0)) {
        log_error("Cannot initialize semaphore: %s", strerror(errno));

        return 1;
    }

    /* Start a new JVM via JNI */

    if (true != java_init(args, jvm_info)) {
        log_error("Cannot initialize JVM");

        return 2;
    }

    log_debug("Initialized JVM");

    /* Install signal handlers */

    if (0 != install_jvm_signal_handler()) {
        log_error("Cannot install jvm signal handler");

        return 3;
    }

    /* Call org.apache.commons.daemon.support.DaemonLoader.load() via JNI.
     * This will ultimately call org.apache.commons.daemon.Daemon.init()
     */

    if (true != java_load(args)) {
        log_error("Cannot call Daemon.init()");

        return 4;
    }

    log_debug("Daemon.init() succeeded");

    /* Drop priviledges */

    if (0 != drop_privileges(user)) {
        log_error("Cannot perform privilege deescalation");

        return 5;
    }

    /* Call  org.apache.commons.daemon.Daemon.start() via JNI */

    if (true != java_start()) {
        log_error("Cannot call Daemon.start()");

        return 6;
    }

    log_debug("Daemon.start() succeeded");

    if (0 != sem_wait_tolerate_eintr(&jvm_signal)) {
        log_error("JVM cannot wait for signal");
    }

    log_debug("Daemon shutting down");

    /* Call org.apache.commons.daemon.Daemon.stop() via JNI */

    if (true != java_stop()) {
        log_error("Daemon.stop() failed");

        return reload_jvm ? 123 : 7;
    }

    log_debug("Daemon.stop() succeeded");

    /* Call org.apache.commons.daemon.Daemon.destroy() via JNI */

    if (true != java_destroy()) {
        log_error("Daemon.destroy() failed");

        return reload_jvm ? 123 : 8;
    }

    log_debug("Daemon.destroy() succeeded");

    /* Destroy the JVM itself */

    if (true != JVM_destroy(reload_jvm ? 123 : 0)) {
        log_error("JVM destroy failed");

        return reload_jvm ? 123 : 9;
    }

    log_debug("Daemon successfully shut down");

    return reload_jvm ? 123 : 0;
}

child_status wait_for_child(
        const char *parent_name,
        const char *child_name,
        pid_t child_pid,
        int *exit_code,
        int *signo,
        int wait_options) {
    int status = 0;
    pid_t result = -1;

    *signo = -1;
    *exit_code = -1;

    while (1) {
        result = waitpid(child_pid, &status, wait_options);

        if (-1 == result) {
            switch (errno) {
                case EINTR:

                    log_debug("%s --wait--> %s:%d, interrupted by signal",
                            parent_name, child_name, child_pid);

                    return INTERRUPTED;

                case ECHILD:

                    log_debug("%s --wait--> %s:%d, child no longer exists",
                            parent_name, child_name, child_pid);

                    return CHILD_GONE;

                default:

                    log_error("%s --wait--> %s:%d, error=%s",
                            parent_name, child_name, child_pid, strerror(errno));

                    return INTERNAL_ERROR;
            }
        }

        if (WIFEXITED(status)) {
            *exit_code = WEXITSTATUS(status);

            log_error("%s --wait--> %s:%d, %s exited=%d",
                    parent_name, child_name, child_pid, child_name, *exit_code);

            return 0 == *exit_code ? SUCCESS_EXIT : ERROR_EXIT;
        }

        if (WIFSIGNALED(status)) {
            *signo = WTERMSIG(status);

            log_error("%s --wait--> %s:%d, %s killed by signal=%d",
                    parent_name, child_name, child_pid, child_name, *signo);

            return SIGNAL_EXIT;
        }

        if (WIFSTOPPED(status)) {
            log_debug("%s --wait--> %s:%d, %s stopped by signal=%d",
                    parent_name, child_name, child_pid, child_name,
                    WSTOPSIG(status));

            continue;
        }

        if (WIFCONTINUED(status)) {
            log_debug("%s --wait--> %s:%d, %s continuing",
                    parent_name, child_name, child_pid, child_name);

            continue;
        }

        log_error("%s --wait--> %s:%d, unknown waitpid() status.");

        return INTERNAL_ERROR;
    }
}

int read_and_validate_user(const char *username, struct passwd *user) {
    struct passwd *result = NULL;
    char *buffer = NULL;
    int buffer_size = 0;
    int retval = 0;
    pid_t pid = 0;
    child_status status;
    int exit_code = 0;
    int signo = 0;

    /* translate username to uid_t and gid_t */

    if (!username || !user) {
        return -1;
    }

    buffer_size = sysconf(_SC_GETPW_R_SIZE_MAX);

    if (0 > buffer_size) {
        buffer_size = 16 * 1024;
    }

    buffer = (char *) malloc(buffer_size);

    if (NULL == buffer) {
        log_error("Cannot allocate buffer for getpwnam_r, error=%s",
                strerror(errno));

        return -1;
    }

    retval = getpwnam_r(username, user, buffer, buffer_size, &result);

    free(buffer);
    buffer = NULL;

    if (NULL == result) {
        if (0 == retval) {
            log_error("User %s does not exist", username);
            return -1;
        }

        log_error("User %s cannot be read, error=%s", strerror(errno));

        return -1;
    }

    log_debug("User %s has uid %d and gid %d", username, user->pw_uid,
            user->pw_gid);

    /* Validate the user name in another process */

    pid = fork();

    if (-1 == pid) {
        /* fork failed */

        log_error("Cannot fork new process to validate user, error=%s",
                strerror(errno));

        return -1;
    }

    if (0 == pid) {
        /* in child process */

        if (0 == drop_privileges(user)) {
            exit(EXIT_SUCCESS);
        }

        exit(EXIT_FAILURE);
    }

    /* in parent process */

    status = wait_for_child("main", "usertest", pid, &exit_code, &signo, 0);

    if (SUCCESS_EXIT != status) {
        log_error("Cannot validate user %s", username);

        return -1;
    }

    log_debug("Validated user %s", username);

    return 0;
}

/**
 * Redirect stderr and stdout to cronolog.   The caller must later call 
 * close_stdout_stderr on the two file handles or else cronolog will continue
 * running after the calling process exits.
 * 
 * @param args
 * @param crono_err
 * @param crono_out
 * @return 
 */
int redirect_stdout_stderr(
        const arg_data *args,
        FILE **crono_err,
        FILE **crono_out) {
    const char *outfile = args->outfile;
    const char *errfile = args->errfile;

    /* unconditionally close stdin, we don't need it. */

    fclose(stdin);

    if (0 == strcmp(errfile, "/dev/null")) {
        if (NULL == freopen(errfile, "w", stderr)) {
            log_error("Cannot redirect stderr to /dev/null: %s",
                    strerror(errno));

            return -1;
        }
    } else {
        char cmd[1024];
        cmd[sizeof (cmd) - 1] = 0;

        snprintf(cmd, sizeof (cmd) - 1, CRONO_FMT, errfile, errfile);

        *crono_err = popen(cmd, "w");

        if (!*crono_err) {
            log_error("Cannot open cronolog for stderr: file=%s, err=%s",
                    errfile, strerror(errno));

            return -1;
        }

        /* turn off buffering.  stderr and stdout will do their own buffering
         * as appropriate
         */

        setbuf(*crono_err, NULL);

        /* redirect the stderr file descriptor to cronolog's stdin */

        if (-1 == dup2(fileno(*crono_err), 2)) {
            log_error("Cannot redirect stderr to cronlog: %s", strerror(errno));

            return -1;
        }

        log_debug("Stderr redirected to %s", errfile);
    }

    if (0 == strcmp(outfile, "/dev/null")) {
        if (NULL == freopen(outfile, "w", stdout)) {
            log_error("Cannot redirect stdout to /dev/null: %s",
                    strerror(errno));

            return -1;
        }
    } else {
        if (0 == strcmp(outfile, errfile)) {
            /* If stderr and stdout go to the same file, use the stderr cronolog
             * file handle.
             * 
             * Implication: caller has to be smart enough to not pclose
             * both crono_out and crono_err if they are the same.  This is
             * handled by close_stdout_stderr().
             */

            *crono_out = *crono_err;
        } else {
            /* Otherwise create a separate cronolog process for stdout */

            char cmd[1024];
            cmd[sizeof (cmd) - 1] = 0;

            snprintf(cmd, sizeof (cmd) - 1, CRONO_FMT, outfile, outfile);

            *crono_out = popen(cmd, "w");

            if (!*crono_out) {
                log_error("Cannot open cronolog for stdout: file=%s, err=%s",
                        outfile, strerror(errno));

                return -1;
            }

            /* turn off buffering.  stderr and stdout will do their own buffering
             * as appropriate
             */

            setbuf(*crono_out, NULL);
        }

        /* redirect the stdout file descriptor to cronolog's stdin */

        if (-1 == dup2(fileno(*crono_out), 1)) {
            log_error("Cannot redirect stdout to cronlog: %s", strerror(errno));

            return -1;
        }

        log_debug("stdout redirected to %s", outfile);
    }

    return 0;
}

void close_stdout_stderr(FILE *crono_err, FILE *crono_out) {
    /* TODO - controller can block indefinitely on this.
     * 
     * if (crono_err) {
        pclose(crono_err);
    }

    if (crono_out && crono_out != crono_err) {
        pclose(crono_out);
    }*/
}

int install_controller_signal_handler() {
    struct sigaction action;

    memset(&action, 0, sizeof (action));

    action.sa_sigaction = controller_signal_handler;
    action.sa_flags = SA_SIGINFO | SA_NOCLDSTOP | SA_NOCLDWAIT;


    if (0 != sigaction(SIGHUP, &action, NULL)) {
        log_error("Cannot install controller SIGHUP handler: %s",
                strerror(errno));

        return -1;
    }

    if (0 != sigaction(SIGUSR1, &action, NULL)) {
        log_error("Cannot install controller SIGUSR1 handler: %s",
                strerror(errno));

        return -1;
    }

    if (0 != sigaction(SIGUSR2, &action, NULL)) {
        log_error("Cannot install controller SIGUSR2 handler: %s",
                strerror(errno));

        return -1;
    }

    if (0 != sigaction(SIGTERM, &action, NULL)) {
        log_error("Cannot install controller SIGTERM handler: %s",
                strerror(errno));

        return -1;
    }

    if (0 != sigaction(SIGINT, &action, NULL)) {
        log_error("Cannot install controller SIGINT handler: %s",
                strerror(errno));

        return -1;
    }

    if (0 != sigaction(SIGCHLD, &action, NULL)) {
        log_error("Cannot install controller SIGCHLD handler: %s",
                strerror(errno));

        return -1;
    }

    return 0;
}

int install_jvm_signal_handler() {
    if (SIG_ERR == signal(SIGHUP, jvm_signal_handler)) {
        log_error("Cannot install jvm SIGHUP handler: %s", strerror(errno));

        return -1;
    }

    if (SIG_ERR == signal(SIGUSR1, jvm_signal_handler)) {
        log_error("Cannot install jvm SIGUSR1 handler: %s", strerror(errno));

        return -1;
    }

    if (SIG_ERR == signal(SIGUSR2, jvm_signal_handler)) {
        log_error("Cannot install jvm SIGUSR2 handler: %s", strerror(errno));

        return -1;
    }

    if (SIG_ERR == signal(SIGTERM, jvm_signal_handler)) {
        log_error("Cannot install jvm SIGTERM handler: %s", strerror(errno));

        return -1;
    }

    if (SIG_ERR == signal(SIGINT, jvm_signal_handler)) {
        log_error("Cannot install jvm SIGINT handler: %s", strerror(errno));

        return -1;
    }

    if (SIG_ERR == signal(SIGPIPE, SIG_IGN)) {
        log_error("Cannot set SIGPIPE to ignore: %s", strerror(errno));

        return -1;
    }

    return 0;
}

int drop_privileges(const struct passwd *user) {
    if (NULL == user) {
        log_debug("Not dropping privs");

        return 0;
    }

    if (0 != setgid(user->pw_gid)) {
        log_error("Cannot change group to %d: %s",
                user->pw_gid,
                strerror(errno));

        return -1;
    }

    if (0 != initgroups(user->pw_name, user->pw_gid)) {
        log_error("Cannot set supplemental group list: %s", strerror(errno));

        return -1;
    }

    if (0 != setuid(user->pw_uid)) {
        log_error("Cannot change user to %d: %s",
                user->pw_uid,
                strerror(errno));
    }

    log_debug("Changed to user:group %d:%d", user->pw_uid, user->pw_gid);

    return 0;
}

void controller_signal_handler(int signo, siginfo_t *info, void *ctx) {

    log_debug("Controller caught signal %d", signo);

    fflush(stdout);

    switch (signo) {
        case SIGHUP:

            /* Forward the SIGHUP to the JVM process.  It should exit 123 
             * which will inform this controller process to restart it.
             */

            if (0 < jvm_pid) {
                log_debug("Forwarding SIGHUP to JVM");

                kill(jvm_pid, SIGHUP);
            }

            break;

        case SIGCHLD:

            /* Restart jvm killed by a signal or that exited with 123.
             * Otherwise exit ourself.
             */

            if (jvm_pid == info->si_pid) {
                switch (info->si_code) {
                    case CLD_EXITED:

                        if (RELOAD_CODE == info->si_status) {
                            log_debug("Restarting JVM at JVM request");

                            reload_jvm = 1;
                        } else if (0 == info->si_status) {
                            log_debug("JVM exited with %d, exiting controller",
                                    info->si_status);

                            reload_jvm = 0;
                        } else {
                            log_error("JVM exited with %d, exiting controller",
                                    info->si_status);

                            reload_jvm = 0;
                        }

                        jvm_pid = -1;

                        sem_post(&controller_signal);

                        break;

                    case CLD_KILLED:
                    case CLD_DUMPED:

                        log_error("JVM killed by signal %d, restarting JVM",
                                info->si_status);

                        reload_jvm = 1;

                        jvm_pid = -1;

                        sem_post(&controller_signal);

                        break;

                    default:

                        /* ignore*/

                        break;
                }
            }

            break;

        default:

            /* For everthing else, forward the signal to the JVM process, then
             * start the shutdown sequence.
             */

            if (0 < jvm_pid) {
                log_debug("Forwarding signal %d to JVM, exiting controller",
                        signo);

                kill(jvm_pid, signo);
            }

            reload_jvm = 0;

            jvm_pid = -1;

            sem_post(&controller_signal);
    }
}

void jvm_signal_handler(int signo) {

    log_debug("JVM caught signal %d", signo);

    switch (signo) {
        case SIGHUP:

            reload_jvm = 1;

            /* fall through */

        default:

            sem_post(&jvm_signal);
    }
}

read_pid_status read_controller_pid_file(
        const arg_data *args,
        pid_t *controller_pid) {
    int fd = -1;
    int bytes_read = 0;
    ssize_t result = 0;
    char buffer[80];

    memset(buffer, 0, sizeof (buffer));

    fd = open(args->pidf, O_RDONLY, 0);

    if (0 > fd) {
        log_error("Cannot open pid file %s: %s", args->pidf, strerror(errno));

        return ENOENT == errno ? NO_FILE : ERROR;
    }

    while (bytes_read < sizeof (buffer) - 1) {
        result = read(fd, buffer + bytes_read, sizeof (buffer) - 1 - bytes_read);

        if (0 > result) {
            log_error("Cannot read pid from file %s: %s", args->pidf,
                    strerror(errno));

            return ERROR;
        }

        if (0 == result) {
            break;
        }

        bytes_read += result;
    }

    close(fd);
    fd = -1;

    if (0 >= bytes_read) {
        log_error("Pid file %s is empty", args->pidf);

        return ERROR;
    }

    log_debug("Read pid %s from file %s", buffer, args->pidf);

    *controller_pid = atoi(buffer);

    return SUCCESS;
}

int write_controller_pid_file(const arg_data *args, pid_t controller_pid) {
    char buffer[80];
    int bytes_written = 0;
    int bytes_to_write = 0;
    ssize_t result = 0;
    int fd = -1;

    memset(buffer, 0, sizeof (buffer));

    snprintf(buffer, sizeof (buffer) - 1, "%d", controller_pid);

    bytes_to_write = strlen(buffer);

    fd = open(args->pidf, O_CREAT | O_WRONLY | O_TRUNC, 0644);

    if (0 > fd) {
        log_error("Cannot open pid file %s: %s", args->pidf, strerror(errno));

        return -1;
    }

    while (bytes_written < bytes_to_write) {
        result = write(
                fd,
                buffer + bytes_written,
                bytes_to_write - bytes_written);

        if (0 > result) {
            log_error("Cannot write pid %d to file %s: %s",
                    controller_pid, args->pidf, strerror(errno));

            return -1;
        }

        bytes_written += result;
    }

    close(fd);
    fd = -1;

    log_debug("Wrote pid %d to file %s", controller_pid, args->pidf);

    return 0;
}

int delete_controller_pid_file(const arg_data *args) {
    if (0 != unlink(args->pidf)) {
        if (ENOENT == errno) {
            log_debug("Controller pid file %s already deleted", args->pidf);

            return 0;
        }

        log_error("Cannot delete controller pid file %s: %s", args->pidf,
                strerror(errno));

        return -1;
    }

    log_debug("Controller pid file %s deleted", args->pidf);

    return 0;
}

int stop_controller(const arg_data *args) {
    pid_t pid = -1;
    int i = 0;

    switch (read_controller_pid_file(args, &pid)) {
        case NO_FILE:

            log_debug("Pid file %s doesn't exist, assuming controller dead",
                    args->pidf);

            return 0;

        case ERROR:

            log_error("Cannot stop controller, cannot read pid file %s",
                    args->pidf);

            return -1;

        default:

            /* successfully read controller pid */

            break;
    }

    /* kill the process and wait until the pidfile has been
     * removed by the controler
     */

    if (0 != kill(pid, SIGTERM)) {
        log_error("Cannot kill controller: pid=%d, err=%s", pid,
                strerror(errno));

        return -1;
    }

    for (i = 0; i < STOP_TIMEOUT_SEC; ++i) {
        sleep(1);

        if (NO_FILE == read_controller_pid_file(args, &pid)) {
            log_debug("Controller has exited");

            return 0;
        }
    }

    log_error("Giving up after waiting %d seconds for controller to exit",
            STOP_TIMEOUT_SEC);

    return -1;
}

int print_java_version(const arg_data *args, const struct home_data *jvm_info) {
    bool result = false;

    if (true != java_init(args, jvm_info)) {
        log_error("Cannot initialize JVM");

        return -1;
    }

    printf("jsvc (Apache Commons Daemon) " JSVC_VERSION_STRING);
    printf("Copyright (c) 1999-2012 Apache Software Foundation.");

    result = java_version();

    if (false == JVM_destroy(result ? 0 : 1)) {
        log_error("JVM destroy failed");
    }

    return result ? 0 : -1;
}

/* These two functions can be called from within the JVM to do an orderly
 * shutdown or reload
 */

void main_reload(void) {
    log_debug("JVM requested reload");

    reload_jvm = 1;

    sem_post(&jvm_signal);
}

void main_shutdown(void) {
    log_debug("JVM requested shutdown");

    reload_jvm = 0;

    sem_post(&jvm_signal);
}

static int sem_wait_tolerate_eintr(sem_t *sem) {
    int i;

    for (i = 0; i < 100; ++i) {
        if (0 != sem_wait(sem)) {
            if (EINTR == errno) {
                continue;
            }

            log_error("sem_wait failed: %s", strerror(errno));

            return -1;
        }

        return 0;
    }

    log_error("sem_wait failed: too many interrupted system calls");

    return -1;
}


