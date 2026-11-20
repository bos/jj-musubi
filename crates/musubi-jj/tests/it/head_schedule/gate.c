#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>

static bool matches_head(int dir, const char *path)
{
    const char *head = getenv("MUSUBI_TEST_HEAD_GATE_PATH");
    if (head == NULL || path == NULL)
        return false;
    if (strcmp(head, path) == 0)
        return true;

    const char *head_slash = strrchr(head, '/');
    const char *slash = strrchr(path, '/');
    const char *name = slash == NULL ? path : slash + 1;
    if (strcmp(head_slash + 1, name) != 0)
        return false;

    // Resolve the directory so we match the entry unlink would remove, including a
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

static void wait_for_release(void)
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

    // A connection tells the test the unlink was reached. Only a release byte lets it run.
    char release;
    ssize_t count;
    do {
        count = read(fd, &release, sizeof(release));
    } while (count < 0 && errno == EINTR);
    if (count != 1 || release != 1) {
        fputs("jj operation-head gate closed before release\n", stderr);
        _exit(125);
    }
    close(fd);
}

static void gate(int dir, const char *path)
{
    static atomic_bool reached;
    int saved_errno = errno;
    if (matches_head(dir, path) && !atomic_exchange_explicit(&reached, true, memory_order_relaxed))
        wait_for_release();
    errno = saved_errno;
}

int unlink(const char *path)
{
    int (*real_unlink)(const char *) = dlsym(RTLD_NEXT, "unlink");
    if (real_unlink == NULL) {
        fputs("resolve unlink for jj operation-head gate\n", stderr);
        _exit(125);
    }
    gate(AT_FDCWD, path);
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
        gate(dir, path);
    return real_unlinkat(dir, path, flags);
}
