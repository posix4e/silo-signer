/*
Hosted platform (macOS / Linux) for Tricorder tests and simulator runs.
Provides the minimal runtime hooks (`silo_plat_heap`, `silo_plat_console`, `silo_plat_halt`,
`silo_plat_write`, `silo_plat_random`) plus private-directory file I/O for vault/inbox/outbox.
*/
#include <lean/lean.h>

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/random.h>
#include <sys/stat.h>
#include <unistd.h>

lean_object * lean_mk_io_user_error(lean_object * message);

static lean_obj_res failed(char const * what) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(what)));
}

static char const * data_root(void) {
    char const * env = getenv("TRICORDER_DATA_DIR");
    return (env != NULL && env[0] != '\0') ? env : "/tmp/tricorder-data";
}

/* Reject empty, absolute, or parent-traversing relative paths. */
static int safe_rel_path(char const * rel) {
    if (rel == NULL || rel[0] == '\0' || rel[0] == '/') return 0;
    for (char const * p = rel; *p != '\0'; p++) {
        if (p[0] == '.' && p[1] == '.' && (p == rel || p[-1] == '/') && (p[2] == '\0' || p[2] == '/'))
            return 0;
    }
    return 1;
}

static int join_path(char * buf, size_t cap, char const * rel) {
    if (!safe_rel_path(rel)) return 0;
    char const * root = data_root();
    size_t rlen = strlen(root);
    size_t llen = strlen(rel);
    if (rlen + 1 + llen + 1 > cap) return 0;
    memcpy(buf, root, rlen);
    buf[rlen] = '/';
    memcpy(buf + rlen + 1, rel, llen + 1);
    return 1;
}

static void ensure_parents(char const * full_path) {
    char tmp[1024];
    size_t len = strlen(full_path);
    if (len >= sizeof(tmp)) return;
    memcpy(tmp, full_path, len + 1);
    for (size_t i = 1; i < len; i++) {
        if (tmp[i] == '/') {
            tmp[i] = '\0';
            mkdir(tmp, 0700);
            tmp[i] = '/';
        }
    }
}

lean_obj_res silo_plat_write(b_lean_obj_arg bytes) {
    uint8_t const * at = lean_sarray_cptr(bytes);
    size_t left = lean_sarray_size(bytes);
    while (left > 0) {
        ssize_t put = write(STDOUT_FILENO, at, left);
        if (put < 0) {
            if (errno == EINTR) continue;
            return failed("write failed");
        }
        at += put;
        left -= (size_t)put;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res silo_plat_random(size_t count) {
    lean_object * bytes = lean_alloc_sarray(1, count, count);
    uint8_t * at = lean_sarray_cptr(bytes);
    size_t left = count;
    while (left > 0) {
        size_t piece = left < 256 ? left : 256;
        if (getentropy(at, piece) != 0) {
            lean_dec_ref(bytes);
            return failed("random source failed");
        }
        at += piece;
        left -= piece;
    }
    return lean_io_result_mk_ok(bytes);
}

void * silo_plat_heap(size_t * size) {
    size_t wanted = (size_t)256 << 20;
    void * region = mmap(NULL, wanted, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (region == MAP_FAILED) {
        *size = 0;
        return NULL;
    }
    *size = wanted;
    return region;
}

void silo_plat_console(char const * bytes, size_t length) {
    while (length > 0) {
        ssize_t put = write(STDERR_FILENO, bytes, length);
        if (put <= 0) return;
        bytes += put;
        length -= (size_t)put;
    }
}

_Noreturn void silo_plat_halt(int code) {
    _exit(code);
}

lean_obj_res tricorder_plat_log(b_lean_obj_arg msg) {
    silo_plat_console(lean_string_cstr(msg), lean_string_size(msg) - 1);
    silo_plat_console("\n", 1);
    return lean_io_result_mk_ok(lean_box(0));
}

static lean_obj_res mk_none(void) {
    return lean_box(0);
}

static lean_obj_res mk_some(lean_obj_arg v) {
    lean_object * o = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(o, 0, v);
    return o;
}

lean_obj_res tricorder_plat_read_file(b_lean_obj_arg rel_obj) {
    char full[1024];
    if (!join_path(full, sizeof(full), lean_string_cstr(rel_obj)))
        return failed("invalid relative path");
    int fd = open(full, O_RDONLY);
    if (fd < 0) {
        if (errno == ENOENT) return lean_io_result_mk_ok(mk_none());
        return failed("open for read failed");
    }
    struct stat st;
    if (fstat(fd, &st) != 0 || st.st_size < 0 || st.st_size > (16 << 20)) {
        close(fd);
        return failed("stat failed or file too large");
    }
    size_t sz = (size_t)st.st_size;
    lean_object * bytes = lean_alloc_sarray(1, sz, sz);
    uint8_t * dst = lean_sarray_cptr(bytes);
    size_t got_total = 0;
    while (got_total < sz) {
        ssize_t n = read(fd, dst + got_total, sz - got_total);
        if (n < 0) {
            if (errno == EINTR) continue;
            close(fd);
            lean_dec_ref(bytes);
            return failed("read failed");
        }
        if (n == 0) break;
        got_total += (size_t)n;
    }
    close(fd);
    lean_sarray_set_size(bytes, got_total);
    return lean_io_result_mk_ok(mk_some(bytes));
}

lean_obj_res tricorder_plat_write_file(b_lean_obj_arg rel_obj, b_lean_obj_arg bytes) {
    char full[1024];
    char tmp[1032];
    if (!join_path(full, sizeof(full), lean_string_cstr(rel_obj)))
        return failed("invalid relative path");
    size_t flen = strlen(full);
    if (flen + 5 >= sizeof(tmp)) return failed("path too long");
    memcpy(tmp, full, flen);
    memcpy(tmp + flen, ".tmp", 5);
    ensure_parents(full);
    int fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd < 0) return failed("open for write failed");
    uint8_t const * src = lean_sarray_cptr(bytes);
    size_t left = lean_sarray_size(bytes);
    while (left > 0) {
        ssize_t n = write(fd, src, left);
        if (n < 0) {
            if (errno == EINTR) continue;
            close(fd);
            unlink(tmp);
            return failed("write failed");
        }
        src += n;
        left -= (size_t)n;
    }
    fsync(fd);
    close(fd);
    if (rename(tmp, full) != 0) {
        unlink(tmp);
        return failed("rename failed");
    }
    return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res tricorder_plat_delete_file(b_lean_obj_arg rel_obj) {
    char full[1024];
    if (!join_path(full, sizeof(full), lean_string_cstr(rel_obj)))
        return failed("invalid relative path");
    int fd = open(full, O_WRONLY);
    if (fd >= 0) {
        struct stat st;
        if (fstat(fd, &st) == 0 && st.st_size > 0 && st.st_size <= (16 << 20)) {
            uint8_t zero[256];
            memset(zero, 0, sizeof(zero));
            size_t left = (size_t)st.st_size;
            while (left > 0) {
                size_t chunk = left < sizeof(zero) ? left : sizeof(zero);
                if (write(fd, zero, chunk) <= 0) break;
                left -= chunk;
            }
            fsync(fd);
        }
        close(fd);
    }
    unlink(full);
    return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res tricorder_plat_list_files(b_lean_obj_arg rel_obj) {
    char full[1024];
    char const * rel = lean_string_cstr(rel_obj);
    if (rel[0] == '\0') {
        char const * root = data_root();
        if (strlen(root) >= sizeof(full)) return failed("path too long");
        strcpy(full, root);
    } else if (!join_path(full, sizeof(full), rel)) {
        return failed("invalid relative path");
    }
    DIR * dir = opendir(full);
    lean_object * arr = lean_alloc_array(0, 8);
    if (dir == NULL) return lean_io_result_mk_ok(arr);
    struct dirent * ent;
    while ((ent = readdir(dir)) != NULL) {
        if (ent->d_name[0] == '.') continue;
        arr = lean_array_push(arr, lean_mk_string(ent->d_name));
    }
    closedir(dir);
    return lean_io_result_mk_ok(arr);
}
