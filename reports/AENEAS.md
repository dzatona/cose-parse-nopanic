# AENEAS — layer 5 remodel

Verbatim Aeneas output from when the crate was still named
`cbor_nopanic`. The crate is now `cose_parse_nopanic`.

Binder trap: record the Aeneas refusal verbatim, then change Rust only with
`// EXTRACT:` / `// REMODEL:`.

Pins: Charon `909ff09a` v0.1.220, Aeneas `c2015b86`.

## Attempt 1 — borrowed `&mut [u8; 4096]` + `as_bytes` + `&str`

`SliceSink` wrapped `&mut [u8]`. `build_sig_structure` allocated
`let mut buf = [0_u8; MAX_MESSAGE_LEN]`, lent it to the sink, then
`buf.get(..written_len)`. `write_text` took `&str`. `SigStructure::as_bytes`
returned `self.buf.get(..self.len)`.

```
[Error] Unreachable
Source: 'src/lib.rs', lines 793:30-793:47
[Warn ] Could not translate the body of function 'cbor_nopanic::build_sig_structure
[Error] There should be no bottoms in the value
Source: 'src/lib.rs', lines 766:4-771:5
[Warn ] Could not translate the body of function 'cbor_nopanic::{cbor_nopanic::SigStructure}::as_bytes
AENEAS_EXIT:1
```

Generated Lean also emitted `axiom core.str.Str.as_bytes`.

This is the Binder trap trap (`FnOnce` + `&mut [u8; N]`), plus an unknown-external
`str::as_bytes`.

## Attempt 2 — owned array, still `'static` AAD while sink is live

`SliceSink` owned `[u8; MAX_MESSAGE_LEN]`. `write_text` took `&[u8]`.
`as_bytes` was dropped. `build_sig_structure` still called
`write_bstr(&mut sink, external_aad(typ))`.

```
[Error] Unreachable
Source: 'src/lib.rs', lines 783:26-783:43
[Warn ] Could not translate the body of function 'cbor_nopanic::build_sig_structure
AENEAS_EXIT:1
```

Span was `external_aad(typ)` (then, after hoisting, the local `aad` slice)
while `&mut SliceSink` was live. Aeneas refused mixing a `'static` global
slice with the mutable owned array.

## Close (Binder trap, one remodel)

Owned `[u8; MAX_MESSAGE_LEN]` sink, return filled `SigStructure`. Write
`"Signature1"` and the four AAD tokens as byte literals. Length check
instead of re-slicing the array. `copy_from_slice` kept, behind
`dest.len() != bytes.len()` → `BufferTooSmall`.

Aeneas then exited 0. `copy_from_slice` stayed the stdlib primitive
(`ok src` iff lengths equal), not a loop. No second copy remodel. No
loop lemma. No `STOP.md`.
