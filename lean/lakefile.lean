import Lake
open Lake DSL

-- Local Aeneas checkout used for this proof:
--   ~/aeneas @ c2015b86, charon-pin 909ff09a (v0.1.220)
-- The Aeneas lib pulls in mathlib v4.31.0. Build it once
-- (`cd ~/aeneas/backends/lean && lake exe cache get && lake build Aeneas`)
-- before building here. See ../reports/TOOLCHAIN.md.
require aeneas from "/Users/dzatona/aeneas/backends/lean"

package «cbor_nopanic» where

@[default_target] lean_lib «CborNopanic» where

@[default_target] lean_lib «NoPanic» where
