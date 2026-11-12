// The one thing Node lacks: map(path) returns the whole file as an ArrayBuffer over a shared,
// writable mapping. The mapping is released when the ArrayBuffer is collected.

#define _GNU_SOURCE
#include <fcntl.h>
#include <node_api.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#ifndef MAP_POPULATE
#define MAP_POPULATE 0
#endif

static void unmap(napi_env env, void *data, void *hint) {
    (void)env;
    munmap(data, (size_t)(uintptr_t)hint);
}

static napi_value fail(napi_env env, const char *what) {
    napi_throw_error(env, NULL, what);
    return NULL;
}

static napi_value map(napi_env env, napi_callback_info info) {
    size_t argc = 1;
    napi_value arg;
    char path[4096];
    size_t path_len;
    if (napi_get_cb_info(env, info, &argc, &arg, NULL, NULL) != napi_ok || argc != 1 ||
        napi_get_value_string_utf8(env, arg, path, sizeof path, &path_len) != napi_ok || path_len == sizeof path - 1) {
        return fail(env, "map(path): one string, shorter than 4095 bytes");
    }
    int fd = open(path, O_RDWR | O_CLOEXEC);
    if (fd < 0) {
        return fail(env, strerror(errno));
    }
    struct stat st;
    if (fstat(fd, &st) != 0 || st.st_size <= 0) {
        close(fd);
        return fail(env, "cannot size the file, or it is empty");
    }
    size_t len = (size_t)st.st_size;
    // MAP_POPULATE: no request takes this process's first-touch faults on the arena.
    void *base = mmap(NULL, len, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, fd, 0);
    int mmap_errno = errno;
    close(fd);
    if (base == MAP_FAILED) {
        return fail(env, strerror(mmap_errno));
    }
    napi_value buffer;
    if (napi_create_external_arraybuffer(env, base, len, unmap, (void *)(uintptr_t)len, &buffer) != napi_ok) {
        munmap(base, len);
        return fail(env, "cannot wrap the mapping in an ArrayBuffer");
    }
    return buffer;
}

static napi_value init(napi_env env, napi_value exports) {
    napi_value fn;
    if (napi_create_function(env, "map", NAPI_AUTO_LENGTH, map, NULL, &fn) != napi_ok ||
        napi_set_named_property(env, exports, "map", fn) != napi_ok) {
        return fail(env, "cannot export map");
    }
    return exports;
}

NAPI_MODULE(NODE_GYP_MODULE_NAME, init)
