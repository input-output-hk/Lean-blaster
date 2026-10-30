/* Executable-only OS adapter. No Lean allocation, locking, or IO occurs in a signal handler. */
#define _XOPEN_SOURCE 700
#include <lean/lean.h>
#include <errno.h>
#include <locale.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <wchar.h>
#ifdef _WIN32
#include <io.h>
#include <windows.h>
#define dup _dup
#define dup2 _dup2
#define close _close
#define write _write
#define isatty _isatty
#else
#include <fcntl.h>
#include <sys/ioctl.h>
#include <unistd.h>
#endif

static int report_fd = -1;
static volatile sig_atomic_t interrupted = 0;
static void (*previous_int)(int);
static void (*previous_term)(int);

static void on_signal(int signal_number) {
    interrupted = signal_number;
}

static lean_obj_res failure(const char *action) {
    char message[256];
    snprintf(message, sizeof(message), "%s: %s", action, strerror(errno));
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

LEAN_EXPORT lean_obj_res blaster_console_open(lean_obj_arg world) {
    (void)world;
    fflush(stdout);
    report_fd = dup(1);
    if (report_fd < 0) return failure("I couldn't reserve the report output");
#ifndef _WIN32
    /* Source subprocesses inherit stderr as fd 1, but never inherit the report descriptor. */
    if (fcntl(report_fd, F_SETFD, FD_CLOEXEC) < 0) {
        close(report_fd); report_fd = -1;
        return failure("I couldn't isolate the report output");
    }
#else
    SetHandleInformation((HANDLE)_get_osfhandle(report_fd), HANDLE_FLAG_INHERIT, 0);
#endif
    if (dup2(2, 1) < 0) {
        close(report_fd); report_fd = -1;
        return failure("I couldn't redirect source output");
    }
    interrupted = 0;
    previous_int = signal(SIGINT, on_signal);
    previous_term = signal(SIGTERM, on_signal);
    setlocale(LC_CTYPE, "");
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res blaster_console_close(lean_obj_arg world) {
    (void)world;
    fflush(stdout);
    if (report_fd >= 0) { dup2(report_fd, 1); close(report_fd); report_fd = -1; }
    signal(SIGINT, previous_int);
    signal(SIGTERM, previous_term);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res blaster_report_write(b_lean_obj_arg bytes, lean_obj_arg world) {
    (void)world;
    const unsigned char *data = lean_sarray_cptr(bytes);
    size_t remaining = lean_sarray_size(bytes);
    while (remaining) {
        int count = (int)write(report_fd, data, remaining);
        if (count < 0) { if (errno == EINTR) continue; return failure("I couldn't write the report"); }
        if (count == 0) { errno = EIO; return failure("I couldn't write the report"); }
        data += count; remaining -= (size_t)count;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res blaster_report_tty(lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box(isatty(report_fd) != 0));
}

LEAN_EXPORT lean_obj_res blaster_signal(lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)interrupted));
}

LEAN_EXPORT lean_obj_res blaster_columns(lean_obj_arg world) {
    (void)world;
    uint32_t columns = 0;
#ifdef _WIN32
    CONSOLE_SCREEN_BUFFER_INFO info;
    if (GetConsoleScreenBufferInfo(GetStdHandle(STD_ERROR_HANDLE), &info))
        columns = (uint32_t)(info.srWindow.Right - info.srWindow.Left + 1);
#else
    struct winsize size;
    if (ioctl(2, TIOCGWINSZ, &size) == 0) columns = size.ws_col;
#endif
    return lean_io_result_mk_ok(lean_box_uint32(columns));
}

LEAN_EXPORT lean_obj_res blaster_clip(b_lean_obj_arg text, uint32_t width, lean_obj_arg world) {
    (void)world;
    const char *start = lean_string_cstr(text);
    const char *cursor = start;
    size_t remaining = lean_string_size(text) - 1;
    uint32_t used = 0;
    int previous_cells = 0;
    mbstate_t state = {0};
    while (remaining) {
        wchar_t character;
        size_t length = mbrtowc(&character, cursor, remaining, &state);
        if (length == (size_t)-1 || length == (size_t)-2 || length == 0) break;
#ifdef _WIN32
        int cells = character >= 0x1100 ? 2 : 1;
#else
        int cells = wcwidth(character);
#endif
        /* Emoji presentation can widen a one-cell base; overestimating a cluster is safe. */
        if (character == 0xFE0F && previous_cells == 1) cells = 1;
        /* Exclude terminal control characters, including embedded escape sequences. */
        if (cells < 0 || used + (uint32_t)cells > width) break;
        used += (uint32_t)cells;
        if (cells > 0) previous_cells = cells;
        cursor += length; remaining -= length;
    }
    return lean_io_result_mk_ok(lean_mk_string_from_bytes(start, (size_t)(cursor - start)));
}

LEAN_EXPORT lean_obj_res blaster_force_kill(uint32_t pid, lean_obj_arg world) {
    (void)world;
#ifdef _WIN32
    HANDLE process = OpenProcess(PROCESS_TERMINATE, FALSE, pid);
    if (process) { TerminateProcess(process, 1); CloseHandle(process); }
#else
    /* Supervised children start a separate session. Include solvers spawned by Lake builds. */
    if (kill(-(pid_t)pid, SIGKILL) < 0 && errno != ESRCH) return failure("I couldn't stop the check");
#endif
    return lean_io_result_mk_ok(lean_box(0));
}
