#define _GNU_SOURCE
#include <dlfcn.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Only supplies the executable pathname when this workspace has no procfs.
 * No Lean kernel operation or filesystem permission is changed. */
static char executable_path[PATH_MAX];
__attribute__((constructor))
static void remember_argv0(int argc, char **argv, char **envp) {
    (void)envp;
    if (argc > 0 && argv && argv[0]) {
        if (!realpath(argv[0], executable_path)) {
            const char *prefix = getenv("LEAN_SYSROOT");
            if (prefix && !strchr(argv[0], '/'))
                snprintf(executable_path, sizeof(executable_path), "%s/bin/%s", prefix, argv[0]);
        }
    }
}

ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*original)(const char *, char *, size_t);
    if (!original) original = dlsym(RTLD_NEXT, "readlink");
    ssize_t result = original(path, buf, size);
    char self[64];
    snprintf(self, sizeof(self), "/proc/%d/exe", (int)getpid());
    if (result < 0 && executable_path[0] && strcmp(path, self) == 0) {
        size_t n = strlen(executable_path);
        if (n > size) n = size;
        memcpy(buf, executable_path, n);
        return (ssize_t)n;
    }
    return result;
}
