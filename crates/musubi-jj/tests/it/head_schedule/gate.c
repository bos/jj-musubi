#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>

enum phase { BEFORE_CREATE = 'C', BEFORE_UNLINK = 'U' };

static bool matches_head(int dir, const char *path, enum phase phase)
{
    const char *head = getenv("MUSUBI_TEST_HEAD_GATE_PATH");
    if (head == NULL || path == NULL)
        return false;
    const char *head_slash = strrchr(head, '/');
    const char *slash = strrchr(path, '/');
    const char *name = slash == NULL ? path : slash + 1;
    const char *old_name = head_slash + 1;
    // jj also creates a lock in this directory. Head names are hex operation IDs.
    size_t length = strlen(name);
    bool hex = length == strlen(old_name) && strspn(name, "0123456789abcdef") == length;
    // A command that merges heads, or finishes another's unlink, adds and removes heads
    // other than the old one.
    bool any = getenv("MUSUBI_TEST_HEAD_GATE_ANY") != NULL;
    if (phase == BEFORE_CREATE) {
        if (!hex || (!any && strcmp(old_name, name) == 0))
            return false;
    } else if (any ? !hex : strcmp(old_name, name) != 0) {
        return false;
    }

    // Resolve the directory so we match the entry to be changed, including a
    // relative entry named through a directory fd. Do not follow the entry itself.
    ptrdiff_t parent_length = slash == NULL ? 1 : name - path;
    if (parent_length >= PATH_MAX)
        return false;
    const char *parent = slash == NULL ? "." : path;
    char candidate[PATH_MAX];
    int written;
    if (path[0] != '/' && dir != AT_FDCWD)
        written = snprintf(candidate, sizeof(candidate), "/proc/self/fd/%d/%.*s",
                           dir, (int)parent_length, parent);
    else
        written = snprintf(candidate, sizeof(candidate), "%.*s", (int)parent_length, parent);
    if (written < 0 || (size_t)written >= sizeof(candidate))
        return false;

    char resolved[PATH_MAX];
    if (realpath(candidate, resolved) == NULL)
        return false;
    size_t resolved_length = strlen(resolved);
    size_t head_parent_length = head_slash == head ? 1 : (size_t)(head_slash - head);
    return resolved_length == head_parent_length && memcmp(head, resolved, resolved_length) == 0;
}

static void wait_for_release(enum phase phase)
{
    const char *name = getenv("MUSUBI_TEST_HEAD_GATE_SOCKET");
    struct sockaddr_un address = { .sun_family = AF_UNIX };
    if (name == NULL || strlen(name) >= sizeof(address.sun_path)) {
        fputs("invalid jj operation-head gate socket name\n", stderr);
        _exit(125);
    }
    size_t length = strlen(name);
    memcpy(address.sun_path + 1, name, length);
    socklen_t size = offsetof(struct sockaddr_un, sun_path) + 1 + length;
    int fd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (fd < 0 || connect(fd, (struct sockaddr *)&address, size) < 0) {
        perror("connect to jj operation-head gate");
        _exit(125);
    }

    // Tell the test which operation was reached, and wait for permission to run it.
    char message = phase;
    ssize_t count;
    do {
        count = write(fd, &message, sizeof(message));
    } while (count < 0 && errno == EINTR);
    if (count != 1) {
        perror("send the jj operation-head gate phase");
        _exit(125);
    }
    do {
        count = read(fd, &message, sizeof(message));
    } while (count < 0 && errno == EINTR);
    if (count != 1 || message != 1) {
        fputs("jj operation-head gate closed before release\n", stderr);
        _exit(125);
    }
    close(fd);
}

static void gate(int dir, const char *path, enum phase phase)
{
    static atomic_bool reached_create, reached_unlink;
    atomic_bool *reached = phase == BEFORE_CREATE ? &reached_create : &reached_unlink;
    int saved_errno = errno;
    if (matches_head(dir, path, phase)
        && !atomic_exchange_explicit(reached, true, memory_order_relaxed))
        wait_for_release(phase);
    errno = saved_errno;
}

// open and openat also have separate large-file entry points. Preserve the optional
// mode argument for both O_CREAT and O_TMPFILE on all four entry points.
#define OPEN_WRAPPER(name, dir_parameter, dir_argument, directory) \
    int name(dir_parameter const char *path, int flags, ...) \
    { \
        int (*real_open)(dir_parameter const char *, int, ...) = dlsym(RTLD_NEXT, #name); \
        if (real_open == NULL) { \
            fputs("resolve " #name " for jj operation-head gate\n", stderr); \
            _exit(125); \
        } \
        if (flags & O_CREAT) \
            gate(directory, path, BEFORE_CREATE); \
        if ((flags & O_CREAT) || (flags & O_TMPFILE) == O_TMPFILE) { \
            va_list args; \
            va_start(args, flags); \
            mode_t mode = va_arg(args, mode_t); \
            va_end(args); \
            return real_open(dir_argument path, flags, mode); \
        } \
        return real_open(dir_argument path, flags); \
    }

#define DIR_PARAMETER int dir,
#define DIR_ARGUMENT dir,
OPEN_WRAPPER(open, , , AT_FDCWD)
OPEN_WRAPPER(open64, , , AT_FDCWD)
OPEN_WRAPPER(openat, DIR_PARAMETER, DIR_ARGUMENT, dir)
OPEN_WRAPPER(openat64, DIR_PARAMETER, DIR_ARGUMENT, dir)

int unlink(const char *path)
{
    int (*real_unlink)(const char *) = dlsym(RTLD_NEXT, "unlink");
    if (real_unlink == NULL) {
        fputs("resolve unlink for jj operation-head gate\n", stderr);
        _exit(125);
    }
    gate(AT_FDCWD, path, BEFORE_UNLINK);
    return real_unlink(path);
}

int unlinkat(int dir, const char *path, int flags)
{
    int (*real_unlinkat)(int, const char *, int) = dlsym(RTLD_NEXT, "unlinkat");
    if (real_unlinkat == NULL) {
        fputs("resolve unlinkat for jj operation-head gate\n", stderr);
        _exit(125);
    }
    if (flags == 0)
        gate(dir, path, BEFORE_UNLINK);
    return real_unlinkat(dir, path, flags);
}
