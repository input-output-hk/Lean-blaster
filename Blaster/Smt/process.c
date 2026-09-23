#include <lean/lean.h>
#include <stdint.h>

#if !defined(_WIN32)
#include <errno.h>
#include <signal.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#endif

/* These operations deliberately do not reap. The Lean lifecycle sends its final
   group signal while the leader's PID is still reserved, then calls Child.wait. */
LEAN_EXPORT lean_obj_res blaster_process_term_group(uint32_t pid, lean_obj_arg world) {
    (void)world;
#if defined(_WIN32)
    (void)pid;
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("POSIX process-group TERM is unavailable on native Windows")));
#else
    if (pid <= 1 || pid > INT32_MAX || (pid_t)pid == getpgrp()) {
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("refusing to signal an unowned process group")));
    }
    if (kill(-(pid_t)pid, SIGTERM) == -1 && errno != ESRCH) {
        int error = errno;
        return lean_io_result_mk_error(lean_mk_io_error_other_error(
            (uint32_t)error, lean_mk_string(strerror(error))));
    }
    return lean_io_result_mk_ok(lean_box(0));
#endif
}

LEAN_EXPORT lean_obj_res blaster_process_exited(uint32_t pid, lean_obj_arg world) {
    (void)world;
#if defined(_WIN32)
    (void)pid;
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("POSIX exit observation is unavailable on native Windows")));
#else
    if (pid <= 1 || pid > INT32_MAX) {
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("invalid owned child PID")));
    }
    siginfo_t info;
    memset(&info, 0, sizeof(info));
    int result;
    do {
        result = waitid(P_PID, (id_t)pid, &info, WEXITED | WNOHANG | WNOWAIT);
    } while (result == -1 && errno == EINTR);
    if (result == -1) {
        int error = errno;
        return lean_io_result_mk_error(lean_mk_io_error_other_error(
            (uint32_t)error, lean_mk_string(strerror(error))));
    }
    return lean_io_result_mk_ok(lean_box(info.si_pid != 0));
#endif
}
