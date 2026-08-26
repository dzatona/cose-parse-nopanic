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
slots or a normal `CoseError`) for every `&[u8]`.
Layer 4 is also proved: `decode_protected_header` returns `ok _` (kid +
`Typ`, or a normal `CoseError`) for every `&[u8]`. The `{1,4,100}` map is
three `next_map_key` calls, not a walker.
Layer 5 is also proved: `build_sig_structure` returns `ok _` (a filled
`[u8; 4096]` `Sig_structure`, or a normal `CoseError`) for every `Typ` and
pair of `&[u8]`. `BufferTooSmall` is `ok(Err)`.
**Finale:** `parse_sign1` does not panic on any `&[u8]`. That is the
envelope parse (`verify` minus crypto): array4 + bstrs + protected map +
`Sig_structure` into `[u8; 4096]`. Signature / Ed25519 is not proved.

Reports: [`reports/PROOF.md`](reports/PROOF.md),
[`reports/PROOF-bstr.md`](reports/PROOF-bstr.md),
[`reports/PROOF-envelope.md`](reports/PROOF-envelope.md),
[`reports/PROOF-header.md`](reports/PROOF-header.md),
[`reports/PROOF-sig.md`](reports/PROOF-sig.md),
[`reports/PROOF-parse.md`](reports/PROOF-parse.md),
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
