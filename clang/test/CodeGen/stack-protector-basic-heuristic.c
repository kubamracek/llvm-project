// REQUIRES: x86-registered-target, aarch64-registered-target

// RUN: %clang_cc1 -triple x86_64-linux-gnu -stack-protector 1 -O0 -emit-obj -o /dev/null -Rpass=stack-protector -verify=common,linux,o0 %s
// RUN: %clang_cc1 -triple x86_64-linux-gnu -stack-protector 1 -O2 -emit-obj -o /dev/null -Rpass=stack-protector -verify=common,linux,o2 %s
// RUN: %clang_cc1 -triple arm64-apple-macos14 -stack-protector 1 -O0 -emit-obj -o /dev/null -Rpass=stack-protector -verify=common,darwin,o0 %s
// RUN: %clang_cc1 -triple arm64-apple-macos14 -stack-protector 1 -O2 -emit-obj -o /dev/null -Rpass=stack-protector -verify=common,darwin,o2 %s

void use(void *);

// common-remark@+1 {{function char16 due to a stack allocated buffer}}
void char16(void) { char b[16]; use(b); }

// Smaller than ssp-buffer-size.
void char4(void) { char b[4]; use(b); }

// Darwin also protects a top-level array that isn't a char array.
// darwin-remark@+1 {{function int4 due to a stack allocated buffer}}
void int4(void) { int a[4]; use(a); }
// darwin-remark@+1 {{function ptr4 due to a stack allocated buffer}}
void ptr4(void) { char *p[4]; use(p); }

// _Bool is stored as i8, so it looks like a char array.
// common-remark@+1 {{function bool16 due to a stack allocated buffer}}
void bool16(void) { _Bool b[16]; use(b); }

// The outer array's element type is an array, not i8.
// darwin-remark@+1 {{function char2d due to a stack allocated buffer}}
void char2d(void) { char a[4][4]; use(a); }

// common-remark@+1 {{function char_in_struct due to a stack allocated buffer}}
void char_in_struct(void) { struct { char c[16]; int x; } s; use(&s); }

// Inside a struct, only char arrays count, on every target.
void int_in_struct(void) { struct { int a[4]; } s; use(&s); }

// The padding is lowered as [12 x i8] and treated as a char buffer (https://github.com/llvm/llvm-project/issues/66709).
// common-remark@+1 {{function padding due to a stack allocated buffer}}
void padding(void) { struct { _Alignas(16) int a; } s; use(&s); }

// The union is lowered as { i64, [8 x i8] }; the [8 x i8] is part of c.
// common-remark@+1 {{function union_char due to a stack allocated buffer}}
void union_char(void) { union { long l; char c[12]; } u; use(&u); }

void bitfields(void) {
  struct { unsigned a : 24; unsigned b : 24; unsigned c : 24; } s;
  use(&s);
}

// Basic mode doesn't consider a variable's address being taken.
void scalar_addr(void) { int x; use(&x); }

// Every variable-length allocation is protected, whatever its element type.
// common-remark@+1 {{function vla_char due to a call to alloca or use of a variable length array}}
void vla_char(int n) { char v[n]; use(v); }
// common-remark@+1 {{function vla_int due to a call to alloca or use of a variable length array}}
void vla_int(int n) { int v[n]; use(v); }

void alloca_small(void) { use(__builtin_alloca(4)); }
// InstCombine turns the constant-size alloca into an array type at -O2.
// o0-remark@+2 {{function alloca_large due to a call to alloca or use of a variable length array}}
// o2-remark@+1 {{function alloca_large due to a stack allocated buffer}}
void alloca_large(void) { use(__builtin_alloca(16)); }
// common-remark@+1 {{function alloca_var due to a call to alloca or use of a variable length array}}
void alloca_var(int n) { use(__builtin_alloca(n)); }

void ignored(void) { __attribute__((stack_protector_ignore)) char b[16]; use(b); }

__attribute__((no_stack_protector)) void no_ssp(void) { char b[16]; use(b); }
