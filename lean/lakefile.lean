import Lake
open Lake DSL

-- Aeneas Lean lib, pin c2015b86 (charon-pin 909ff09a, mathlib v4.31.0).
-- Path: `$AENEAS_LEAN` if set, else `$HOME/aeneas/backends/lean`.
-- Build Aeneas once: `cd <aeneas>/backends/lean && lake exe cache get && lake build Aeneas`.
-- See ../reports/TOOLCHAIN.md.

def aeneasLean : System.FilePath := run_io do
  if let some p := (← IO.getEnv "AENEAS_LEAN") then
    return ⟨p⟩
  let home := (← IO.getEnv "HOME").getD "/"
  return System.FilePath.mk home / "aeneas" / "backends" / "lean"

require aeneas from aeneasLean

package «cose_parse_nopanic» where

@[default_target] lean_lib «CoseParseNopanic» where

@[default_target] lean_lib «NoPanic» where
