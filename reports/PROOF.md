# PROOF — `read_uint_no_panic` (step 1)

## Claim

For every hostile byte slice, the extracted canonical-CBOR unsigned-integer
decoder returns in the Aeneas `ok` monad. It does **not** prove RFC 8949
correctness.

```
∀ buf, ∃ r, read_uint buf = ok r
```

`ok (Result.Ok value)` is a canonical uint. `ok (Result.Err CodecError)` is a
normal codec rejection (truncated, wrong major type, non-canonical length,
reserved additional, indefinite). `fail` would be panic / OOB / unwrap.

Theorem: `NoPanic.read_uint_no_panic` in `lean/NoPanic.lean`. No `sorry`.

## Checklist (checklist)

1. `cargo test` in `rust/` — 6/6 green (canonical 0/23/24/255/…, non-canonical
   `[0x18, 0x05]`, empty → `UnexpectedEnd`, major ≠ 0 → `TypeMismatch`).
2. Charon exit 0 — `llbc/cbor_nopanic.llbc` (`charon cargo --preset=aeneas`).
3. Aeneas exit 0 — `lean/CborNopanic.lean`; `lake build` typechecks.
4. Theorem `read_uint_no_panic` without `sorry`.
5. `#print axioms` (below). Only standard Lean axioms.
6. `EXTRACT.md` covers `reader.rs` plus the Aeneas remodel.
7. README states the claim and reproduce commands.
8. Repo remains private.

## `#print axioms`

```
'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard Lean axioms. No `sorryAx`, no opaque `size_of`,
no unknown-external axioms. First Aeneas output *did* emit `axiom`s for
`Option::ok_or`, `slice::first`, `TryFrom<&[u8]> for [u8; N]`, integer
`TryFrom`, and `Result::map_err`. Those were removed by a loop-free Rust
remodel (`// REMODEL:` in `rust/src/lib.rs`): `match` on `checked_add` /
`slice::get` instead of `ok_or`/`first`/`try_into`. Semantics of the test
vectors are unchanged.

Aeneas's own stdlib contains `sorry` in unused `get_unchecked` models; they
are not in this theorem's axiom set.

## Reproduce

```sh
cd rust && cargo test
export PATH="$HOME/charon/bin:$PATH"
charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
eval $(opam env --switch=5.3.0)
~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cbor_nopanic.llbc
cd ../lean && lake build
# axioms:
lake env lean --stdin <<'EOF'
import NoPanic
#print axioms NoPanic.read_uint_no_panic
EOF
```

See `TOOLCHAIN.md` for pins and install.
