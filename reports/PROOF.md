# PROOF — `parse_sign1_no_panic` (finale)

Current proof. Earlier layer transcripts: [`history/`](history/).

## Claim

For every hostile byte slice, the extracted `COSE_Sign1` envelope parse
(`verify` minus crypto) returns in the Aeneas `ok` monad. It does **not**
prove RFC 9052 / RFC 9053 correctness, Ed25519, or product `Typ` meaning.

```
∀ bytes, ∃ r, parse_sign1 bytes = ok r
```

`ok` includes `Err(CoseError)`. `ok (Result.Ok Parsed)` is kid + typ +
payload after envelope + protected header + `Sig_structure`.
`ok (Result.Err CoseError)` is a normal rejection:

- array count ≠ 4 → `MalformedEnvelope`
- unprotected map nonempty → `NonEmptyUnprotectedHeader`
- protected map not `{1:-8, 4:kid16, 100:typ}` → `MalformedProtectedHeader`
  / `UnsupportedAlgorithm` / `UnknownTyp`
- truncated / trailing / non-canonical slots → `Codec(...)`
- reconstructed `Sig_structure` does not fit `[u8; 4096]` →
  `Codec(BufferTooSmall)`

`fail` would be panic / OOB / unwrap.

Not `∀ pubkey`. Not `SignatureInvalid` / `InvalidPublicKey`. Those are
dalek, outside `parse_sign1`. This proves `cose_parse_nopanic`, not
`kntrl-license-core` in place.

Theorem in `lean/NoPanic.lean`: `NoPanic.parse_sign1_no_panic`. No `sorry`.
Layer theorems still hold: `read_uint_no_panic`, `read_bstr_no_panic`,
`read_bstr_fixed_64_no_panic`, `read_array_header_no_panic`,
`read_map_header_no_panic`, `read_sign1_envelope_no_panic`,
`decode_protected_header_no_panic`, `build_sig_structure_no_panic`.
Leaves are `@[step]` specs; composites use `step*`; `read_head` is
`step*` then `split` on the additional-info match.

## Canonicity (`read_uint_ok_is_canonical`)

Decode-only. If `read_uint buf = ok (Result.Ok n)`, the first byte is
major type 0 and RFC 8949 §4.2.1 additional-info is smallest-form for
`n`:

- AI 0..=23: `n = ai`
- AI 24: `24 ≤ n ≤ 255`
- AI 25: `256 ≤ n ≤ 65535` (u16, not fitting u8)
- AI 26: `65536 ≤ n ≤ 4294967295` (u32, not fitting u16)
- AI 27: `n ≥ 4294967296` (not fitting u32)

The 2/4/8-byte cuts are the `value <= u8::MAX` / `u16::MAX` /
`u32::MAX` branches in `read_head`, unfolded in
`read_head_ok_smallest_form`. Reserved 28..=31 cannot be `Ok`.
Extra-width `[0x18, 0x05]` is `Err(NonCanonicalLength)`, not `Ok`.
`read_head_ai0_23` is the converse on 1-byte heads.

Does **not** claim: full RFC 8949, or encode-then-decode (`write_head`
then `read_head`).

Theorems: `NoPanic.read_head_ok_smallest_form`,
`NoPanic.read_uint_ok_is_canonical`. No `sorry`. Axioms: `propext`,
`Classical.choice`, `Quot.sound` (same as `read_uint_no_panic`).
Only handwritten `lean/NoPanic.lean` changed; `PROOF.sha256` of
Rust/llbc/generated Lean is unchanged.

## Live run

Crate **0.17.0**. Pins: Charon `909ff09a` v0.1.220, Aeneas `c2015b86`,
Lean 4.31.0. `Debug` is `#[cfg_attr(test, derive(Debug))]` so Charon
does not extract `core.fmt`. Generated Lean has no `CoreFmtDebug`.

Binding file: [`PROOF.sha256`](PROOF.sha256). CI runs `sha256sum -c`
on it.

### Inputs (sha256, before Charon)

```
$ shasum -a 256 rust/src/lib.rs rust/Cargo.toml rust/Cargo.lock
9fe042cbe12eac3b75f1f79b0889c35abdb844b1ad901ca642d0b8be537063e1  rust/src/lib.rs
86deeb84fdfcb00317d445ef4c658da32783854bda5eda7509cd5e1923c33d53  rust/Cargo.toml
c28273dfeca7732d4c63dd53ab5000d1031c2dfb73494ce7ee0983bcbca7da5e  rust/Cargo.lock
```

### `cargo test`

```
$ cargo test
   Compiling cose_parse_nopanic v0.15.0
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.57s
test result: ok. 46 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
CARGO_TEST_EXIT:0
```

### Charon

```
$ charon version
0.1.220

$ charon cargo --preset=aeneas --dest-file ../llbc/cose_parse_nopanic.llbc
   Compiling cose_parse_nopanic v0.15.0
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.77s
CHARON_EXIT:0
```

### Aeneas

```
$ ~/aeneas/bin/aeneas -version
aeneas c2015b86

$ ~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cose_parse_nopanic.llbc
[Info ] Imported: ../llbc/cose_parse_nopanic.llbc
[Info ] Generated: ../lean/CoseParseNopanic.lean
[Warn ] The crate contains extracted external, unknown definitions: we advise using the option -split-files to allow manually providing these definitions in separate files.
[Info ] Total execution time: 2.149315 seconds
AENEAS_EXIT:0
```

Handwritten `NoPanic.lean` was not overwritten.

### Outputs (sha256, after Charon + Aeneas)

```
$ shasum -a 256 llbc/cose_parse_nopanic.llbc lean/CoseParseNopanic.lean
dc13d5679ff3b2ff558b46b726c2f43a2d721ce61bcc5ffb753ce8dfe814fb0d  llbc/cose_parse_nopanic.llbc
411267ea74ecb7a05ea1a3950a4b9e8f3da41816481a37032cf491539c22f450  lean/CoseParseNopanic.lean
```

### `lake build` / axioms

CI is the witness (Lean 4.31.0, Aeneas @ `c2015b86`, axiom grep):
https://github.com/dzatona/cose-parse-nopanic/actions/runs/33041618859
(`827a165`, job `lean`). Local line numbers in an old transcript would
drift; Charon/Aeneas stay local because CI does not run them.

Aeneas stdlib has `sorry` in unused `get_unchecked` / `StringIter`
models; they are not in these theorems' axiom sets.

## Reproduce

```sh
sha256sum -c reports/PROOF.sha256
cd rust && cargo test
export PATH="$HOME/charon/bin:$PATH"
charon cargo --preset=aeneas --dest-file ../llbc/cose_parse_nopanic.llbc
eval $(opam env --switch=5.3.0)
~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cose_parse_nopanic.llbc
cd ../lean && lake build
lake env lean --stdin <<'EOF'
import NoPanic
#print axioms NoPanic.parse_sign1_no_panic
EOF
```

See `TOOLCHAIN.md` for pins. Layer transcripts: `history/`.
