# Repository instructions

All commits must include the trailer `Signed-off-by: Matteo Frigo <athena@fftw.org>`.

Before every commit, run `cargo +nightly fmt` from the Rust workspace.

Do not develop tools in Python. Use Rust.

Never use `OnceLock`. Pass explicitly owned initialization state instead.
