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

/* @version $Id: debug.c 1198399 2011-11-06 16:20:44Z mturk $ */
#include "jsvc.h"
#include <sys/types.h>
#include <unistd.h>
#include <time.h>

/* Whether debug is enabled or not */
bool log_debug_flag = false;

/* Wether SYSLOG logging (for stderr) is enable or not. */
bool log_stderr_syslog_flag = false;

/* Wether SYSLOG logging (for stdout) is enable or not. */
bool log_stdout_syslog_flag = false;

/* The name of the jsvc binary. */
char *log_prog = "jsvc";

void log_internal(
        FILE *file, 
        const char *level, 
        const char *format, 
        va_list *ap) {
    time_t now;
    struct tm gmtime;
    char buffer[513];

    if (NULL == format) {
        return;
    }

    buffer[sizeof (buffer) - 1] = 0;

    now = time(NULL);
    gmtime_r(&now, &gmtime);

    vsnprintf(buffer, sizeof (buffer) - 1, format, *ap);

    fprintf(file, "%d-%d-%d %d:%d:%d %s [%d] %s\n",
            1900 + gmtime.tm_year, gmtime.tm_mon + 1, gmtime.tm_mday,
            gmtime.tm_hour, gmtime.tm_min, gmtime.tm_sec,
            level, getpid(), buffer);

    if (file == stdout) {
        fflush(stdout);
    }
}

/* Dump a debug trace message to stdout */
void log_debug(const char *format, ...) {
    va_list ap;

    if (!log_debug_flag) {
        return;
    }

    va_start(ap, format);

    return log_internal(stdout, "DEBUG", format, &ap);

    va_end(ap);
}

/* Dump an error message to stderr */
void log_error(const char *format, ...) {
    va_list ap;

    va_start(ap, format);

    return log_internal(stderr, "ERROR", format, &ap);

    va_end(ap);
}



