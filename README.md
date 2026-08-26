# cose-parse-nopanic

Machine-checked no-panic proof for one loop-free path in a hand-written
RFC 8949 deterministic CBOR decoder (the layer under `COSE_Sign1`).

Not the KNTRL product tree. Not a Runtime Verification repository.
Work and name: Dmitrii Zatona. GitHub `dzatona/cose-parse-nopanic`.
Crate/Lean remain `cbor_nopanic` until the next extraction.

**Proved:** for every `&[u8]`, `read_uint` returns Aeneas `ok _` (a decoded
`u64` or a normal `CodecError`); it does not panic. Not RFC 8949 correctness.
Layer 2 is also proved: `read_bstr` and `read_bstr_fixed_64` return `ok _`
(a slice / 64-byte array or a normal `CodecError`) for every `&[u8]`.
Layer 3 is also proved: `read_sign1_envelope` returns `ok _` (the array-of-4
slots or a normal `CodecError`) for every `&[u8]`.
**Goal:** no-panic of the COSE_Sign1 envelope parse (array4 + bstrs + protected
map + `Sig_structure` into `[u8; 4096]`). Signature / Ed25519 is not proved.

Reports: [`reports/PROOF.md`](reports/PROOF.md),
[`reports/PROOF-bstr.md`](reports/PROOF-bstr.md),
[`reports/PROOF-envelope.md`](reports/PROOF-envelope.md),
[`reports/EXTRACT.md`](reports/EXTRACT.md),
[`reports/TOOLCHAIN.md`](reports/TOOLCHAIN.md).

## Reproduce

```sh
cd rust && cargo test
# Charon 909ff09a / Aeneas c2015b86 / Lean 4.31.0 — see reports/TOOLCHAIN.md
charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
aeneas -backend lean -dest ../lean ../llbc/cbor_nopanic.llbc
cd ../lean && lake build
```
