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
 *    b. writes its own pid to an external pid file
 *    c. installs signal handlers that will forward signals it catches to the
 *       jvm process
 *    d. the controller forks a new process for the jvm.  that process calls
 *       jvm_main().
 *    e. monitors the jvm process, restarting it if it is killed by a signal
 *       other than one it forwarded or if the jvm process exits non-zero.
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

/* absolute path to cronolog file without extension must be passed on the 
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

/* Max wait for stop */
static const int STOP_TIMEOUT_SEC = 60;

/* The following variables are volatile and global to the compilation unit
 * because they are shared with signal handlers
 */
static volatile pid_t jvm_pid = -1;

/* Specific to the controller process.  
 * 
 * If set to non-zero the controller will exit.   This is only set to non-zero
 * when the controller is sent a SIGTERM or when the controller catches a
 * SIGCHLD informing it that the JVM process exited 0.
 * 
 * Note that this is checked immediately after breaking out of the sem_wait()
 * on the controller_signal.   The controller_signal is incremented only in 
 * the controller's signal handler.
 */
static volatile int shutdown_initiated = 0;

/* The exit code for the JVM.  If non-zero the daemon controller will restart
 * it automatically unless the daemon controller has been told to stop.
 */
static volatile int jvm_exit_code = 0;


static sem_t controller_signal; // initialized in controller_main()
static sem_t jvm_signal; // initialized in jvm_main()

static void controller_main(
        const arg_data *args,
        const struct home_data *jvm_info,
        const struct passwd *user,
        sem_t **sem);

static void jvm_main(
        const arg_data *args,
        const struct home_data *jvm_info,
        const struct passwd *user);

static void controller_signal_handler(int signo, siginfo_t *info, void *ctx);

static int install_controller_signal_handler(void);

static int install_jvm_signal_handler(void);

static void jvm_signal_handler(int signo, siginfo_t *info, void *ctx);

typedef enum {
    READ_SUCCESS = 0,
    READ_NO_FILE = 1,
    READ_ERROR = 2
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
    CHILD_GONE = 5,
    CHILD_ALIVE = 6
} child_status;

static child_status wait_for_child(
        const char *parent_name,
        const char *child_name,
        pid_t child_pid,
        int *exit_code,
        int *signo,
        int wait_options);

typedef enum {
    SEM_SUCCESS = 0,
    SEM_ERROR = 1,
    SEM_TIMEDOUT = 2
} sem_wait_status;

static int NUM_EXCESSIVE_EINTRS = 100;

/* Wait x seconds for the semaphore to be signalled. if 0 >= wait forever.
 * Retry up to NUM_EXCESSIVE_EINTRS interrupts before erroring out
 */
static sem_wait_status sem_wait_tolerate_eintr(sem_t *sem, int seconds);

int main(int argc, const char **argv)
{
    arg_data *args = NULL;
    struct passwd user;
    struct home_data *jvm_info = NULL;
    pid_t controller_pid = 0;
    sem_t *sem = NULL;
    char sem_name[NAME_MAX - 4]; /* NAME_MAX - 4 from manpage */

    snprintf(sem_name, sizeof (sem_name) - 1, "jsvc_sem1_%d", getpid());

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

    if (args->dtch) {
        log_debug("Detaching controller process");

        sem = sem_open(sem_name, O_CREAT, 0644, 0);

        if (SEM_FAILED == sem) {
            fprintf(stderr, "Cannot init detach semaphore: %s",
                    strerror(errno));

            return 1;
        }

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

            /* Then call controller_main() below */

        } else {
            /* In parent/original process */

            /* Wait 5 sec for the controller proc to signal it has detached */

            if (SEM_SUCCESS != sem_wait_tolerate_eintr(sem, 5)) {
                int exit_code = 0;
                int signo = 0;

                log_error("Cannot wait for controller process");

                switch (wait_for_child("main", "controller", controller_pid,
                        &exit_code, &signo, WNOHANG)) {
                case SUCCESS_EXIT:
                case ERROR_EXIT:

                    log_error("Controller exited prematurely with code %d",
                            exit_code);

                    return -1;

                case SIGNAL_EXIT:

                    log_error("Controller killed by signal %d", signo);

                    return -1;

                case INTERNAL_ERROR:

                    log_error("Cannot determine controller status");

                    kill(controller_pid, SIGTERM);

                    return -1;

                case CHILD_GONE:

                    log_error("Controller never created");

                    return -1;

                case CHILD_ALIVE:

                    log_error("Controller is jammed");

                    kill(controller_pid, SIGTERM);

                    return -1;

                default:

                    return -1;
                }
            }

            /* Once the controller has signalled the semaphore it's done.  If
             * there was an error signalling the semaphore (non SUCCESS above),
             * we don't know if the controller has signalled the semaphore or
             * not so we leave it to the operating system to reclaim.
             */

            if (sem && 0 != sem_close(sem)) {
                log_error("Cannot close controller semaphore: %s",
                        strerror(errno));
            }

            sem = 0;

            /* controller has detached */

            log_debug("Controller detached, exiting to shell");

            return 0;
        }
    }

    /* Start the monitoring process (controller).  This will signal the
     * sem semaphore the main process is waiting on after the controller
     * process forks the JVM
     */

    controller_main(args, jvm_info, &user, &sem);

    /* This will never be called, controller_main will call exit() directly. */

    log_error("Unexpected, controller_main should have called exit()");

    return 0;
}

void controller_main(
        const arg_data *args,
        const struct home_data *jvm_info,
        const struct passwd *user,
        sem_t **psem)
{
    FILE *crono_err = NULL;
    FILE *crono_out = NULL;
    int first_time = 1;
    time_t last_jvm_start_sec = 0;
    time_t now = 0;

    /* Install controller signal handlers.  */

    if (0 != install_controller_signal_handler()) {
        exit(2);
    }

    /* Redirect stderr and stdout to cronolog.   Cronlog will do log rotation.
     * Child processes (JVMs) will inherit the redirected stderr and stdout 
     */

    if (0 != redirect_stdout_stderr(args, &crono_err, &crono_out)) {
        exit(3);
    }

    if (0 != sem_init(&controller_signal, 0, 0)) {
        log_error("Cannot initialize semaphore: %s", strerror(errno));

        exit(1);
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

                exit(4);
            }

            if (0 == jvm_pid) {
                /* In jvm process */

                jvm_main(args, jvm_info, user);
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

                exit(5);
            }

            if (*psem) {
                if (0 != sem_post(*psem)) {
                    log_error("Cannot signal main process: %s",
                            strerror(errno));

                    delete_controller_pid_file(args);

                    exit(6);
                }

                /* now that we've posted the semaphore, it's up to the 
                 * parent process to notice it and then close the sem after
                 * it stops waiting for this process to detach.
                 */

                *psem = 0;
            }

            first_time = 0;
        }

        /* Wait indefinately until we catch a signal. */

        if (0 != sem_wait_tolerate_eintr(&controller_signal, 0)) {
            log_error("Controller cannot wait for signal");

            delete_controller_pid_file(args);

            exit(7);
        }

        if (shutdown_initiated) {
            break;
        }

        /* Restart the JVM unless it exited 0 or shutdown was initiated
         * by the controller.
         */
    }

    log_debug("Controller shutdown initiated");

    delete_controller_pid_file(args);

    exit(0);
}

void jvm_main(
        const arg_data *args,
        const struct home_data *jvm_info,
        const struct passwd *user)
{

    if (0 != sem_init(&jvm_signal, 0, 0)) {
        log_error("Cannot initialize semaphore: %s", strerror(errno));

        exit(1);
    }

    /* Start a new JVM via JNI */

    if (true != java_init(args, jvm_info)) {
        log_error("Cannot initialize JVM");

        exit(2);
    }

    log_debug("Initialized JVM");

    /* Call org.apache.commons.daemon.support.DaemonLoader.load() via JNI.
     * This will ultimately call org.apache.commons.daemon.Daemon.init()
     */

    if (true != java_load(args)) {
        log_error("Cannot call Daemon.init()");

        exit(4);
    }

    log_debug("Daemon.init() succeeded");

    /* Drop priviledges */

    if (0 != drop_privileges(user)) {
        log_error("Cannot perform privilege deescalation");

        exit(5);
    }

    /* Call  org.apache.commons.daemon.Daemon.start() via JNI */

    if (true != java_start()) {
        log_error("Cannot call Daemon.start()");

        exit(6);
    }

    log_debug("Daemon.start() succeeded");
    
    /* Install signal handlers.   Installing these relatively late because
     * the original jsvc installed the signal handlers after java_start().  
     * The result is that some applications (e.g., Hadoop Datanode) never
     * return from their Daemon.start() impl, but their developers never 
     * realized there was an issue because the default signal handler would 
     * terminate the process rather than initiate an orderly shutdown.  To
     * do the right thing at this point would break backwards compatability.
     */

    if (0 != install_jvm_signal_handler()) {
        log_error("Cannot install jvm signal handler");

        exit(3);
    }

    if (0 != sem_wait_tolerate_eintr(&jvm_signal, 0)) {
        log_error("JVM cannot wait for signal");
    }

    log_debug("Daemon shutting down");

    /* Call org.apache.commons.daemon.Daemon.stop() via JNI */

    if (true != java_stop()) {
        log_error("Daemon.stop() failed");

        exit(7);
    }

    log_debug("Daemon.stop() succeeded");

    /* Call org.apache.commons.daemon.Daemon.destroy() via JNI */

    if (true != java_destroy()) {
        log_error("Daemon.destroy() failed");

        exit(8);
    }

    log_debug("Daemon.destroy() succeeded");

    /* Destroy the JVM itself */

    if (true != JVM_destroy(jvm_exit_code)) {
        log_error("JVM destroy failed");

        exit(9);
    }
    
    /* This will not be reached unless JVM_destroy fails to invoke System.exit()
     */

    log_debug("Daemon shut down");

    exit(jvm_exit_code);
}

child_status wait_for_child(
        const char *parent_name,
        const char *child_name,
        pid_t child_pid,
        int *exit_code,
        int *signo,
        int wait_options)
{
    int status = 0;
    pid_t result = -1;

    *signo = -1;
    *exit_code = -1;

    while (1) {
        result = waitpid(child_pid, &status, wait_options);

        if (0 == result && (WNOHANG & wait_options)) {
            return CHILD_ALIVE;
        }

        if (-1 == result) {
            switch (errno) {
            case EINTR:

                log_debug("%s --wait--> %s:%d, interrupted by signal",
                        parent_name, child_name, child_pid);

                /* Automatically retry in case the waitpid() syscall is
                 * interrupted by a signal.
                 */

                continue;

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

            if (0 == *exit_code) {
                log_debug("%s --wait--> %s:%d, %s exited=%d",
                        parent_name, child_name, child_pid, child_name, *exit_code);

                return SUCCESS_EXIT;
            } else {
                log_error("%s --wait--> %s:%d, %s exited=%d",
                        parent_name, child_name, child_pid, child_name, *exit_code);

                return ERROR_EXIT;
            }
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

int read_and_validate_user(const char *username, struct passwd *user)
{
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
 * Redirect stderr and stdout to cronolog.
 * 
 * @param args
 * @param crono_err
 * @param crono_out
 * @return 
 */
int redirect_stdout_stderr(
        const arg_data *args,
        FILE **crono_err,
        FILE **crono_out)
{
    const char *outfile = args->outfile;
    const char *errfile = args->errfile;

    /* Close stdin/err/out first so we don't hang remote shells */

    fclose(stdin);

    fflush(stdout);

    close(1);
    close(2);

    /* The remote shell should return at exactly this point.  Now we enter
     * the time where if anything goes wrong we can't log it.
     */

    if (0 == strcmp(errfile, "/dev/null")) {
        if (NULL == freopen(errfile, "w", stderr)) {
            return -1;
        }
    } else {
        char cmd[1024];
        cmd[sizeof (cmd) - 1] = 0;

        snprintf(cmd, sizeof (cmd) - 1, CRONO_FMT, errfile, errfile);

        *crono_err = popen(cmd, "w");

        if (!*crono_err) {
            return -1;
        }

        /* turn off buffering.  stderr and stdout will do their own buffering
         * as appropriate
         */

        setbuf(*crono_err, NULL);

        /* redirect the stderr file descriptor to cronolog's stdin */

        if (-1 == dup2(fileno(*crono_err), 2)) {
            pclose(*crono_err);

            return -1;
        }
    }

    /* Now we can log errors again */

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
             */

            *crono_out = *crono_err;
        } else {
            /* Otherwise create a separate cronolog process for stdout */

            char cmd[1024];

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

            if (0 != pclose(*crono_err)) {
                log_error("Cannot close cronolog: %s", strerror(errno));
            }

            return -1;
        }
    }

    log_debug("Stderr redirected to %s", errfile);
    log_debug("stdout redirected to %s", outfile);

    return 0;
}

int install_controller_signal_handler()
{
    struct sigaction action;
    static const int signos[] = {SIGHUP, SIGUSR1, SIGUSR2, SIGTERM, SIGINT,
        SIGCHLD};
    int i;

    memset(&action, 0, sizeof (action));

    action.sa_sigaction = controller_signal_handler;
    action.sa_flags = SA_SIGINFO | SA_NOCLDSTOP | SA_NOCLDWAIT;

    for (i = 0; i < sizeof (signos) / sizeof (int); ++i) {
        if (0 != sigaction(signos[i], &action, NULL)) {
            log_error("Cannot install controller signal %d handler: %s",
                    signos[i], strerror(errno));

            return -1;
        }
    }

    return 0;
}

int install_jvm_signal_handler()
{
    struct sigaction action;
    static const int signos[] = {SIGHUP, SIGUSR1, SIGUSR2, SIGTERM, SIGINT};
    int i;

    memset(&action, 0, sizeof (action));

    action.sa_sigaction = jvm_signal_handler;
    action.sa_flags = SA_SIGINFO;

    for (i = 0; i < sizeof (signos) / sizeof (int); ++i) {
        if (0 != sigaction(signos[i], &action, NULL)) {
            log_error("Cannot install jvm signal %d handler: %s",
                    signos[i], strerror(errno));

            return -1;
        }
    }

    if (SIG_ERR == signal(SIGPIPE, SIG_IGN)) {
        log_error("Cannot set SIGPIPE to ignore: %s", strerror(errno));

        return -1;
    }

    return 0;
}

int drop_privileges(const struct passwd *user)
{
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

void controller_signal_handler(int signo, siginfo_t *info, void *ctx)
{

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
            case CLD_TRAPPED:
            case CLD_STOPPED:
            case CLD_CONTINUED:

                /* ignore */

                break;

            case CLD_EXITED:

                if (RELOAD_CODE == info->si_status) {
                    log_debug("Restarting JVM at JVM request");
                } else if (0 == info->si_status) {
                    log_debug("JVM exited with %d, exiting controller",
                            info->si_status);

                    shutdown_initiated = 1;
                } else {
                    log_error("JVM exited with %d, restarting jvm",
                            info->si_status);
                }

                jvm_pid = -1;

                sem_post(&controller_signal);

                break;

            case CLD_KILLED:
            case CLD_DUMPED:

                log_error("JVM killed by signal %d, restarting JVM",
                        info->si_status);

                jvm_pid = -1;

                sem_post(&controller_signal);

                break;

            default:

                log_error("JVM signaled for an unknown reason, exiting "
                        "controller");

                shutdown_initiated = 1;

                jvm_pid = -1;

                sem_post(&controller_signal);
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
            waitpid(jvm_pid, NULL, 0);
        }

        shutdown_initiated = 1;
        jvm_pid = -1;

        sem_post(&controller_signal);
    }
}

void jvm_signal_handler(int signo, siginfo_t *info, void *ctx)
{

    log_debug("JVM caught signal %d", signo);

    switch (signo) {
    case SIGHUP:

        jvm_exit_code = RELOAD_CODE;

        /* fall through */

    default:

        sem_post(&jvm_signal);
    }
}

read_pid_status read_controller_pid_file(
        const arg_data *args,
        pid_t *controller_pid)
{
    int fd = -1;
    int bytes_read = 0;
    ssize_t result = 0;
    char buffer[80];

    memset(buffer, 0, sizeof (buffer));

    fd = open(args->pidf, O_RDONLY, 0);

    if (0 > fd) {
        log_error("Cannot open pid file %s: %s", args->pidf, strerror(errno));

        return ENOENT == errno ? READ_NO_FILE : READ_ERROR;
    }

    while (bytes_read < sizeof (buffer) - 1) {
        result = read(fd, buffer + bytes_read, sizeof (buffer) - 1 - bytes_read);

        if (0 > result) {
            log_error("Cannot read pid from file %s: %s", args->pidf,
                    strerror(errno));

            close(fd);

            return READ_ERROR;
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

        return READ_ERROR;
    }

    log_debug("Read pid %s from file %s", buffer, args->pidf);

    *controller_pid = atoi(buffer);

    return READ_SUCCESS;
}

int write_controller_pid_file(const arg_data *args, pid_t controller_pid)
{
    char buffer[80];
    int bytes_written = 0;
    int bytes_to_write = 0;
    ssize_t result = 0;
    int fd = -1;

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

            close(fd);

            return -1;
        }

        bytes_written += result;
    }

    close(fd);
    fd = -1;

    log_debug("Wrote pid %d to file %s", controller_pid, args->pidf);

    return 0;
}

int delete_controller_pid_file(const arg_data *args)
{
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

int stop_controller(const arg_data *args)
{
    pid_t pid = -1;
    int i = 0;

    switch (read_controller_pid_file(args, &pid)) {
    case READ_NO_FILE:

        log_debug("Pid file %s doesn't exist, assuming controller dead",
                args->pidf);

        return 0;

    case READ_ERROR:

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

    sleep(0); /* yield to the process we are killing */

    for (i = 0; i < STOP_TIMEOUT_SEC; ++i) {
        if (READ_NO_FILE == read_controller_pid_file(args, &pid)) {
            log_debug("Controller has exited");

            return 0;
        }

        sleep(1);
    }

    log_error("Giving up after waiting %d seconds for controller to exit",
            STOP_TIMEOUT_SEC);

    return -1;
}

int print_java_version(const arg_data *args, const struct home_data *jvm_info)
{
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

/* This function can be called from within the JVM to do an orderly
 * shutdown or reload.
 * 
 * In Java, the Daemon.init() method will be passed a DaemonContext instance.
 * DaemonContext has a getController() method which returns a DaemonController
 * instance.   DaemonController exposes the following methods:
 * 
 * fail(...) -> prints error message + stack trace to daemon log,
 *    then calls main_shutdown(non-zero)
 * shutdown() -> calls main_shutdown(zero)
 * reload() -> calls main_shutdown(123)
 * 
 */

void main_shutdown(int exit_code)
{
    jvm_exit_code = exit_code;

    switch (exit_code) {
    case RELOAD_CODE:
        log_debug("JVM requested reload");
        break;
    case 0:
        log_debug("JVM requested shutdown");
        break;
    default:
        log_error("JVM requested restart due to error");
    }

    sem_post(&jvm_signal);
}

sem_wait_status sem_wait_tolerate_eintr(sem_t *sem, int seconds)
{
    int i;
    int result;
    struct timespec abstime;

    if (0 < seconds) {
        if (0 != clock_gettime(CLOCK_REALTIME, &abstime)) {
            log_error("clock_gettime failed: %s", strerror(errno));

            return SEM_ERROR;
        }

        abstime.tv_sec += seconds;
    }

    for (i = 0; i < NUM_EXCESSIVE_EINTRS; ++i) {
        if (0 < seconds) {
            result = sem_timedwait(sem, &abstime);
        } else {
            result = sem_wait(sem);
        }

        if (0 != result) {
            if (EINTR == errno) {
                continue;
            }

            if (ETIMEDOUT == errno) {
                return SEM_TIMEDOUT;
            }

            log_error("sem_wait failed: %s", strerror(errno));

            return SEM_ERROR;
        }

        return SEM_SUCCESS;
    }

    log_error("sem_wait failed: too many interrupted system calls");

    return SEM_ERROR;
}


