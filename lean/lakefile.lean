import Lake
open Lake DSL

-- Aeneas Lean lib, pin c2015b86 (charon-pin 909ff09a, mathlib v4.31.0).
-- Replace this path with your checkout's `backends/lean`. Build Aeneas
-- once: `cd <aeneas>/backends/lean && lake exe cache get && lake build Aeneas`.
-- See ../reports/TOOLCHAIN.md.
require aeneas from "/Users/dzatona/aeneas/backends/lean"

package «cbor_nopanic» where

@[default_target] lean_lib «CborNopanic» where

@[default_target] lean_lib «NoPanic» where
