# BBGS E2: one-error basic decoder (experimental)

This branch adds `bbgs_basic_working.c`, a small end-to-end baseline.

## What it does

- Enumerates affine points `(x,y)` with `x != 0` satisfying the BBGS E2 equation in characteristic two.
- Uses the three evaluation checks `1, x, y` to define the linear code `C = ker(H)`.
- Constructs a codeword by solving the three parity checks.
- Injects one nonzero symbol error.
- Decodes the error from its syndrome `(e, ex, ey)`, then verifies that the original codeword was recovered.

This is deliberately a **one-error syndrome decoder**, not a full Feng–Rao / order-domain decoder. The three checks are a minimal experimental parity-check space; this is not claimed to be an optimal BBGS AG code or to attain a designed distance. It provides a runnable starting point for replacing the checks with a justified Riemann–Roch basis and extending the locator method to multiple errors.

## Build and run

```sh
cc -O2 -std=c11 -Wall -Wextra -Werror -o bbgs_basic_working bbgs_basic_working.c
./bbgs_basic_working --m 2 --seed 7
./bbgs_basic_working --m 1 --seed 7
```

`--m 2` selects GF(32), and `--m 1` selects GF(8). The program prints the support size, code dimension, injected error, decoded error, and a final PASS/FAIL result.
