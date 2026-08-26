# cose-parse-nopanic

Machine-checked no-panic proof of a `COSE_Sign1` envelope parse: the
pre-crypto prefix of `verify`. Not Ed25519. Not RFC 8949 / RFC 8152
correctness.

Not the KNTRL product tree. Not a Runtime Verification repository.
Work and name: Dmitrii Zatona.

**Proved:** for every `&[u8]`, `parse_sign1` returns Aeneas `ok _` — a
`Parsed` envelope or a normal `CoseError`. It does not panic.

That path is: array of 4, protected/payload/signature bstrs, empty
unprotected map, protected header `{1: -8, 4: kid, 100: typ}`, then
`Sig_structure` into `[u8; 4096]`. `BufferTooSmall` is `ok(Err)`.

**Not proved:** signature verification, `verify_strict`, public keys,
payload decode, trust-set.

The Rust crate and Lean namespace are still `cbor_nopanic` (layer-1
extraction name). Reports below are the proof artifacts.

Reports: [`reports/PROOF-parse.md`](reports/PROOF-parse.md)
(finale), [`reports/EXTRACT.md`](reports/EXTRACT.md),
[`reports/TOOLCHAIN.md`](reports/TOOLCHAIN.md). Layer proofs:
[`PROOF.md`](reports/PROOF.md),
[`PROOF-bstr.md`](reports/PROOF-bstr.md),
[`PROOF-envelope.md`](reports/PROOF-envelope.md),
[`PROOF-header.md`](reports/PROOF-header.md),
[`PROOF-sig.md`](reports/PROOF-sig.md).

## Reproduce

Pin Charon `909ff09a` / Aeneas `c2015b86` / Lean 4.31.0 — install
notes in [`reports/TOOLCHAIN.md`](reports/TOOLCHAIN.md). Then point
`lean/lakefile.lean` at your Aeneas `backends/lean` checkout and:

```sh
cd rust && cargo test
export PATH="$HOME/charon/bin:$PATH"
charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
eval $(opam env --switch=5.3.0)
aeneas -backend lean -dest ../lean ../llbc/cbor_nopanic.llbc
cd ../lean && lake build
```
