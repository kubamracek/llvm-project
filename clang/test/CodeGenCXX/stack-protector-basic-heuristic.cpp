// REQUIRES: x86-registered-target, aarch64-registered-target

// RUN: %clang_cc1 -triple x86_64-linux-gnu -stack-protector 1 -O0 -emit-obj -o /dev/null -Rpass=stack-protector -verify=common,o0 %s
// RUN: %clang_cc1 -triple x86_64-linux-gnu -stack-protector 1 -O2 -emit-obj -o /dev/null -Rpass=stack-protector -verify=common %s
// RUN: %clang_cc1 -triple arm64-apple-macos14 -stack-protector 1 -O0 -emit-obj -o /dev/null -Rpass=stack-protector -verify=common,o0 %s
// RUN: %clang_cc1 -triple arm64-apple-macos14 -stack-protector 1 -O2 -emit-obj -o /dev/null -Rpass=stack-protector -verify=common %s

void use(void *);
void use_ref(const void *);
struct B { char c[16]; };
struct alignas(16) Payload { float t; };
void take(B);
B make();

// Payload is lowered as { float, [12 x i8] }.
// common-remark@+1 {{function _Z13aligned_localv due to a stack allocated buffer}}
void aligned_local() { Payload p; use(&p); }

// The argument temporary is optimized away at -O2.
// o0-remark@+1 {{function _Z8arg_tempv due to a stack allocated buffer}}
void arg_temp() { take(B{}); }

// common-remark@+1 {{function _Z8ref_tempv due to a stack allocated buffer}}
void ref_temp() { const B &b = make(); use_ref(&b); }

// One remark for the array and one for the lambda's copy of it.
// common-remark@+1 2 {{function _Z11lambda_copyv due to a stack allocated buffer}}
void lambda_copy() { char a[16]; use(a); auto l = [a] { use_ref(a); }; l(); }

void scalar_only() { int x = 0; use_ref(&x); }
