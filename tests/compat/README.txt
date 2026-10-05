libgcc_s.so.1 (GCC runtime library, GPL with the GCC Runtime Library Exception) -- x86-64 Linux.

The released fift / proxy-liteserver executables (cl-ton/tests/*-linux-x86_64, AppImages) link
against libstdc++, which needs libgcc_s.so.1 from the host.  Minimal containers lack it.
builder.lisp --with-tests copies the HOST's libgcc_s.so.1 into bin/tests/compat/ when it has one,
and this copy otherwise; the fift/proxy-liteserver wrappers put bin/tests/compat/ on the loader
path only when the running host has no libgcc_s.so.1 of its own.
