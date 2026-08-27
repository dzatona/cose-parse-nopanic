-- Handwritten no-panic theorem. Aeneas generates `CoseParseNopanic.lean` from
-- `llbc/cose_parse_nopanic.llbc`; this file is not Aeneas output.
--
-- Panic model (Binder spike): Aeneas puts every function in the `Result`
-- monad `ok v | fail e | div`. A panic (overflow, OOB index, unwrap, ...) is
-- exactly `fail`. No-panic is `∀ inputs, ∃ v, f inputs = ok v`. A codec
-- rejection is `ok (Result.Err CodecError)` (or `CoseError` on the envelope
-- path) — still `ok`.
--
-- `f ⦃ _ => True ⦄` is `spec f (fun _ => True)` ≡ `∃ v, f = ok v`.
-- Leaf extracted functions are tagged `@[step]` so `step*` can chain them.
-- `Reader.read_head`: `nstep` to the additional-info `U8` match, `split` that
-- match, then `nstep` per arm. Unbounded `step*` does not split this match
-- in bounded time.
-- This theorem does not claim RFC 8949 correctness.

import CoseParseNopanic

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open cose_parse_nopanic

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace NoPanic

/-- No-panic `step*`: postcondition is `True`, so skip grind. -/
macro "nstep" : tactic => `(tactic| step* -grind -threadGrindState)

/-- `spec m (fun _ => True)` is exactly “the panic monad returned `ok`”. -/
theorem of_spec {α} {m : Result α} (h : m ⦃ _ => True ⦄) : ∃ v, m = ok v := by
  cases m with
  | ok v => exact ⟨v, rfl⟩
  | fail _ => simp [spec, theta] at h
  | div => simp [spec, theta] at h

theorem spec_of_exists {α} {m : Result α} (h : ∃ v, m = ok v) : m ⦃ _ => True ⦄ := by
  obtain ⟨v, hv⟩ := h
  simp [hv]

/-- The Aeneas panic monad returns `ok`, never `fail`/`div`. -/
abbrev AlwaysOk {α : Type _} (m : Result α) : Prop := ∃ v, m = ok v

theorem AlwaysOk.of_ok {α} (v : α) : AlwaysOk (ok v) := ⟨v, rfl⟩

theorem AlwaysOk.of_lift {α} (x : α) : AlwaysOk (lift x) := ⟨x, rfl⟩

theorem AlwaysOk.bind {α β} {m : Result α} {f : α → Result β}
    (hm : AlwaysOk m) (hf : ∀ a, AlwaysOk (f a)) :
    AlwaysOk (do let x ← m; f x) := by
  obtain ⟨a, rfl⟩ := hm
  simpa [bind_tc_ok] using hf a

theorem AlwaysOk.ite {α} (c : Prop) [Decidable c] {t e : Result α}
    (ht : AlwaysOk t) (he : AlwaysOk e) :
    AlwaysOk (if c then t else e) := by
  split <;> assumption

/-! # Stdlib / extracted leaves -/

@[step]
theorem lift_spec {α} (x : α) : lift x ⦃ _ => True ⦄ := by
  simp [lift]

@[step]
theorem slice_range_get_spec {T} (s : Slice T) (r : core.ops.range.Range Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice T) s r
      ⦃ _ => True ⦄ := by
  change core.slice.index.SliceIndexRangeUsizeSlice.get r s ⦃ _ => True ⦄
  unfold core.slice.index.SliceIndexRangeUsizeSlice.get
  split <;> simp

@[step]
theorem slice_usize_get_spec {T} (s : Slice T) (i : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T) s i
      ⦃ _ => True ⦄ := by
  unfold core.slice.Slice.get
  simp only [core.slice.index.Usize.get]
  simp

@[step]
theorem slice_range_get_mut_spec {T} (s : Slice T) (r : core.ops.range.Range Usize) :
    core.slice.Slice.get_mut (core.slice.index.SliceIndexRangeUsizeSlice T) s r
      ⦃ o _ =>
        match o with
        | none => True
        | some dest =>
          r.start.val ≤ r.end.val ∧
            r.end.val ≤ s.length ∧
            dest.length = r.end.val - r.start.val ⦄ := by
  unfold core.slice.Slice.get_mut
  change core.slice.index.SliceIndexRangeUsizeSlice.get_mut r s ⦃ o _ =>
    match o with
    | none => True
    | some dest =>
      r.start.val ≤ r.end.val ∧
        r.end.val ≤ s.length ∧
        dest.length = r.end.val - r.start.val ⦄
  unfold core.slice.index.SliceIndexRangeUsizeSlice.get_mut
  split
  · rename_i hcond
    simp only [spec_ok, uncurry']
    obtain ⟨hle, hbound⟩ := hcond
    have hle' : r.start.val ≤ r.end.val := (UScalar.le_equiv r.start r.end).mp hle
    refine ⟨hle', hbound, ?_⟩
    change (s.val.slice r.start.val r.end.val).length = r.end.val - r.start.val
    rw [List.slice_length]
    exact Nat.min_eq_right (Nat.sub_le_sub_right hbound r.start.val)
  · simp

@[step]
theorem from_residual_from_same_spec {T E}
    (residual : core.result.Result core.convert.Infallible E) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      T (core.convert.FromSame E) residual ⦃ r => ∃ e, r = core.result.Result.Err e ⦄ := by
  unfold core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  spec_split
  · rename_i x; nomatch x
  · simp [core.convert.FromSame]

@[step]
theorem from_residual_codec_to_cose_spec {T}
    (residual : core.result.Result core.convert.Infallible CodecError) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      T CoseError.Insts.CoreConvertFromCodecError residual
      ⦃ r => ∃ e, r = core.result.Result.Err e ⦄ := by
  unfold core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  spec_split
  · rename_i x; nomatch x
  · simp [CoseError.Insts.CoreConvertFromCodecError,
      CoseError.Insts.CoreConvertFromCodecError.from]

@[step]
theorem new_spec (buf : Slice U8) : Reader.new buf ⦃ _ => True ⦄ := by
  unfold Reader.new
  simp

@[step]
theorem is_empty_spec (self : Reader) : Reader.is_empty self ⦃ _ => True ⦄ := by
  unfold Reader.is_empty
  simp

@[step]
theorem take_spec (self : Reader) (n : Usize) :
    Reader.take self n ⦃ _ => True ⦄ := by
  unfold Reader.take
  nstep

@[step]
theorem get_u8_spec (bytes : Slice U8) (i : Usize) :
    get_u8 bytes i ⦃ _ => True ⦄ := by
  unfold get_u8
  nstep

@[step]
theorem finish_spec (self : Reader) : Reader.finish self ⦃ _ => True ⦄ := by
  unfold Reader.finish
  nstep

theorem take_no_panic (self : Reader) (n : Usize) : AlwaysOk (Reader.take self n) :=
  of_spec (take_spec self n)

theorem get_u8_no_panic (bytes : Slice U8) (i : Usize) : AlwaysOk (get_u8 bytes i) :=
  of_spec (get_u8_spec bytes i)

theorem branch_no_panic {T E} (r : core.result.Result T E) :
    AlwaysOk (core.result.Result.Insts.CoreOpsTry.branch r) := by
  cases r <;> exact ⟨_, rfl⟩

theorem from_residual_no_panic {T}
    (residual : core.result.Result core.convert.Infallible CodecError) :
    AlwaysOk
      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        T (core.convert.FromSame CodecError) residual) :=
  of_spec (spec_mono (from_residual_from_same_spec residual) (fun _ _ => trivial))

/-! # `read_head` (U8 additional-info match; split before `nstep` per arm) -/

theorem read_head_always_ok (self : Reader) (major_base : U8) :
    AlwaysOk (Reader.read_head self major_base) := by
  apply of_spec
  unfold Reader.read_head
  step* 10 -grind -threadGrindState
  · nstep
  · split
    · nstep
    · nstep
    · nstep
    · nstep
    · nstep

@[step]
theorem read_head_spec (self : Reader) (major_base : U8) :
    Reader.read_head self major_base ⦃ _ => True ⦄ :=
  spec_of_exists (read_head_always_ok self major_base)

@[step]
theorem Reader_read_uint_spec (self : Reader) :
    Reader.read_uint self ⦃ _ => True ⦄ := by
  unfold Reader.read_uint
  nstep

@[step]
theorem Reader_read_bstr_spec (self : Reader) :
    Reader.read_bstr self ⦃ _ => True ⦄ := by
  unfold Reader.read_bstr
  nstep

@[step]
theorem Reader_read_bstr_fixed_64_spec (self : Reader) :
    Reader.read_bstr_fixed_64 self ⦃ _ => True ⦄ := by
  unfold Reader.read_bstr_fixed_64
  nstep

@[step]
theorem Reader_read_bstr_fixed_16_spec (self : Reader) :
    Reader.read_bstr_fixed_16 self ⦃ _ => True ⦄ := by
  unfold Reader.read_bstr_fixed_16
  nstep

@[step]
theorem Reader_read_array_header_spec (self : Reader) :
    Reader.read_array_header self ⦃ _ => True ⦄ := by
  unfold Reader.read_array_header
  nstep

@[step]
theorem Reader_read_map_header_spec (self : Reader) :
    Reader.read_map_header self ⦃ _ => True ⦄ := by
  unfold Reader.read_map_header
  nstep

@[step]
theorem read_fixed_byte_spec (self : Reader) (expected : U8) :
    Reader.read_fixed_byte self expected ⦃ _ => True ⦄ := by
  unfold Reader.read_fixed_byte
  nstep

@[step]
theorem next_map_key_spec (self : Reader) (last_key : Option U64) :
    Reader.next_map_key self last_key ⦃ _ => True ⦄ := by
  unfold Reader.next_map_key
  nstep

theorem Typ_from_u64_always_ok (value : U64) : AlwaysOk (Typ.from_u64 value) := by
  unfold Typ.from_u64
  split <;> exact ⟨_, rfl⟩

@[step]
theorem Typ_from_u64_spec (value : U64) : Typ.from_u64 value ⦃ _ => True ⦄ :=
  spec_of_exists (Typ_from_u64_always_ok value)

/-! # Public parse theorems -/

/-- For every byte slice, `read_uint` returns `ok _` (decoded `u64` or `CodecError`). -/
theorem read_uint_no_panic (buf : Slice U8) : ∃ r, read_uint buf = ok r := by
  apply of_spec
  unfold read_uint
  nstep

/-- For every byte slice, `read_bstr` returns `ok _` (a slice or `CodecError`). -/
theorem read_bstr_no_panic (buf : Slice U8) : ∃ r, read_bstr buf = ok r := by
  apply of_spec
  unfold read_bstr
  nstep

/-- For every byte slice, `read_bstr_fixed_64` returns `ok _` (64 bytes or `CodecError`). -/
theorem read_bstr_fixed_64_no_panic (buf : Slice U8) :
    ∃ r, read_bstr_fixed_64 buf = ok r := by
  apply of_spec
  unfold read_bstr_fixed_64
  nstep

/-- For every byte slice, `read_array_header` returns `ok _` (a count or `CodecError`). -/
theorem read_array_header_no_panic (buf : Slice U8) :
    ∃ r, read_array_header buf = ok r := by
  apply of_spec
  unfold read_array_header
  nstep

/-- For every byte slice, `read_map_header` returns `ok _` (a count or `CodecError`). -/
theorem read_map_header_no_panic (buf : Slice U8) :
    ∃ r, read_map_header buf = ok r := by
  apply of_spec
  unfold read_map_header
  nstep

@[step]
theorem read_sign1_envelope_spec (buf : Slice U8) :
    read_sign1_envelope buf ⦃ _ => True ⦄ := by
  unfold read_sign1_envelope
  nstep

/-- For every byte slice, `read_sign1_envelope` returns `ok _` (`Envelope` or `CoseError`). -/
theorem read_sign1_envelope_no_panic (buf : Slice U8) :
    ∃ r, read_sign1_envelope buf = ok r :=
  of_spec (read_sign1_envelope_spec buf)

@[step]
theorem decode_protected_header_spec (bytes : Slice U8) :
    decode_protected_header bytes ⦃ _ => True ⦄ := by
  unfold decode_protected_header
  nstep

/-- For every byte slice, `decode_protected_header` returns `ok _`
    (`([u8; 16], Typ)` or `CoseError`). -/
theorem decode_protected_header_no_panic (bytes : Slice U8) :
    ∃ r, decode_protected_header bytes = ok r :=
  of_spec (decode_protected_header_spec bytes)

/-! # `Sig_structure` writer -/

@[step]
theorem SliceSink_new_spec : SliceSink.new ⦃ s => s.len ≤ MAX_MESSAGE_LEN ⦄ := by
  unfold SliceSink.new
  simp [spec_ok]

@[step]
theorem SliceSink_len_spec (self : SliceSink) :
    SliceSink.impl.len self ⦃ n => n = self.len ⦄ := by
  unfold SliceSink.impl.len
  simp

/-- After `get_mut(self.len .. end)` returns `some dest` with
    `end = self.len + bytes.len()`, `dest.len = bytes.len`.
    The remodel `if dest.len() != bytes.len()` branch is therefore dead. -/
theorem write_bytes_dest_len_eq
    (self : SliceSink) (bytes : Slice U8) (end1 : Usize) (s dest : Slice U8)
    (back : Option (Slice U8) → Slice U8)
    (hadd : Usize.checked_add self.len (Slice.len bytes) = some end1)
    (hget :
      core.slice.Slice.get_mut (core.slice.index.SliceIndexRangeUsizeSlice U8) s
        { start := self.len, «end» := end1 } = ok (some dest, back)) :
    Slice.len dest = Slice.len bytes := by
  have hpost := slice_range_get_mut_spec s { start := self.len, «end» := end1 }
  rw [hget] at hpost
  simp only [spec_ok, uncurry'] at hpost
  obtain ⟨_, _, hdestlen⟩ := hpost
  have hadd' := Usize.checked_add_bv_spec self.len (Slice.len bytes)
  simp only [hadd] at hadd'
  obtain ⟨_, hend, _⟩ := hadd'
  apply UScalar.val_eq_imp
  rw [Slice.len_val dest, hdestlen, hend]
  omega

/-- `write_bytes` preserves `len ≤ MAX_MESSAGE_LEN` unconditionally (`Ok` or
    `Err`). `len` only advances after `get_mut` succeeds with
    `end ≤ buf.len()` and `buf` is `[u8; MAX_MESSAGE_LEN]`; on `Err`, `len`
    is unchanged. -/
@[step]
theorem write_bytes_spec (self : SliceSink) (bytes : Slice U8)
    (hlen : self.len ≤ MAX_MESSAGE_LEN) :
    SliceSink.write_bytes self bytes ⦃ _ sink' =>
      sink'.len ≤ MAX_MESSAGE_LEN ⦄ := by
  unfold SliceSink.write_bytes
  step* -threadGrindState
  have ho1 : o1 = some dest := by assumption
  simp only [ho1] at o1_post
  have hs : s.val.length = 4096 := by
    simpa [Array.length_eq] using congrArg List.length s_post1
  unfold MAX_MESSAGE_LEN
  scalar_tac

@[step]
theorem be_byte_spec (be : Array U8 8#usize) (i : Usize) :
    be_byte be i ⦃ _ => True ⦄ := by
  unfold be_byte
  nstep

@[step]
theorem write_head_spec (sink : SliceSink) (major_base : U8) (arg : U64)
    (hlen : sink.len ≤ MAX_MESSAGE_LEN) :
    write_head sink major_base arg ⦃ _ sink' =>
      sink'.len ≤ MAX_MESSAGE_LEN ⦄ := by
  unfold write_head
  step* -threadGrindState

@[step]
theorem write_bstr_spec (sink : SliceSink) (bytes : Slice U8)
    (hlen : sink.len ≤ MAX_MESSAGE_LEN) :
    write_bstr sink bytes ⦃ _ sink' =>
      sink'.len ≤ MAX_MESSAGE_LEN ⦄ := by
  unfold write_bstr
  step* -threadGrindState

@[step]
theorem write_text_spec (sink : SliceSink) (text : Slice U8)
    (hlen : sink.len ≤ MAX_MESSAGE_LEN) :
    write_text sink text ⦃ _ sink' =>
      sink'.len ≤ MAX_MESSAGE_LEN ⦄ := by
  unfold write_text
  step* -threadGrindState

@[step]
theorem write_array_header_spec (sink : SliceSink) (len : U64)
    (hlen : sink.len ≤ MAX_MESSAGE_LEN) :
    write_array_header sink len ⦃ _ sink' =>
      sink'.len ≤ MAX_MESSAGE_LEN ⦄ := by
  unfold write_array_header
  step* -threadGrindState

/-- The remodel `if written_len > MAX_MESSAGE_LEN` then-branch is not taken:
    given `sink.len ≤ MAX_MESSAGE_LEN` (the `new` + `write_bytes` invariant),
    `SliceSink.len` returns that field, so the comparison is false. The `Err`
    postcondition is `False`: that branch would return `Err BufferTooSmall`. -/
theorem sig_structure_len_le_max (sink : SliceSink)
    (hlen : sink.len ≤ MAX_MESSAGE_LEN) :
    (do
      let written_len ← SliceSink.impl.len sink
      if written_len > MAX_MESSAGE_LEN then
        ok (core.result.Result.Err (CoseError.Codec CodecError.BufferTooSmall))
      else
        ok (core.result.Result.Ok
          ({ buf := sink.buf, len := written_len } : SigStructure)))
      ⦃ r =>
        match r with
        | core.result.Result.Ok ss => ss.len ≤ MAX_MESSAGE_LEN
        | core.result.Result.Err _ => False ⦄ := by
  unfold SliceSink.impl.len
  simp [bind_tc_ok, spec_ok]
  split
  · unfold MAX_MESSAGE_LEN at *
    scalar_tac
  · simpa using hlen

@[step]
theorem build_sig_structure_spec (typ : Typ) (protected1 payload : Slice U8) :
    build_sig_structure typ protected1 payload ⦃ _ => True ⦄ := by
  unfold build_sig_structure
  step* -threadGrindState

/-- For every `Typ` and pair of byte slices, `build_sig_structure` returns `ok _`
    (`SigStructure` or `CoseError`). -/
theorem build_sig_structure_no_panic (typ : Typ) (protected1 payload : Slice U8) :
    ∃ r, build_sig_structure typ protected1 payload = ok r :=
  of_spec (build_sig_structure_spec typ protected1 payload)

@[step]
theorem parse_sign1_spec (bytes : Slice U8) :
    parse_sign1 bytes ⦃ _ => True ⦄ := by
  unfold parse_sign1
  nstep
  try rcases val with ⟨kid, typ⟩
  nstep

/-- For every byte slice, `parse_sign1` returns `ok _` (`Parsed` or `CoseError`).
    Composition of envelope + protected header + `Sig_structure`. Not `∀ pubkey`.
    Signature verification is outside this function. -/
theorem parse_sign1_no_panic (bytes : Slice U8) :
    ∃ r, parse_sign1 bytes = ok r :=
  of_spec (parse_sign1_spec bytes)

/-! # RFC 8949 §4.2.1 smallest-form round-trip (`write_head` then `read_head`)

`write_head` emits a canonical head; `read_head` rejects extra-width forms.
`major_base` must be a clean major type (low 5 bits clear), matching
`MAJOR_UNSIGNED` / `MAJOR_BSTR` / `MAJOR_TEXT` / `MAJOR_ARRAY` / `MAJOR_MAP`.
The 2-byte / 4-byte / 8-byte argument forms are left unproved: `to_be_bytes`
plus the unrolled `be_byte` ladder is a larger extracted term than the
inline (0..=23) and 1-byte (24..=255) cases. -/

/-- Written prefix of a `SliceSink`. Length is bounded by the array width. -/
def written_bytes (sink : SliceSink) : Slice U8 :=
  ⟨sink.buf.val.slice 0 sink.len.val, by
    have hle := List.slice_length_le (α := U8) 0 sink.len.val sink.buf.val
    have heq := Array.length_eq sink.buf
    scalar_tac⟩

/-- Empty sink, same as a successful `SliceSink.new`. -/
def empty_sink : SliceSink :=
  { buf := Array.repeat 4096#usize 0#u8, len := 0#usize }

theorem empty_sink_new : SliceSink.new = ok empty_sink := by
  unfold SliceSink.new empty_sink
  simp

theorem additional_mask_val : ADDITIONAL_MASK.val = 31 := by
  unfold ADDITIONAL_MASK
  rfl

theorem major_mask_val : MAJOR_MASK.val = 224 := by
  unfold MAJOR_MASK
  rfl

theorem u8_and_val (x y : U8) : (x &&& y).val = x.val &&& y.val :=
  BitVec.toNat_and x.bv y.bv

theorem u8_or_val (x y : U8) : (x ||| y).val = x.val ||| y.val :=
  BitVec.toNat_or x.bv y.bv

theorem and_31_of_lt_32 (x : Nat) (h : x < 32) : x &&& 31 = x := by
  have : 31 = 2 ^ 5 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

theorem and_255_of_lt_256 (x : Nat) (h : x < 256) : x &&& 255 = x := by
  have : 255 = 2 ^ 8 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

theorem and_224_of_and_31_zero (x : Nat) (hx : x < 256) (h : x &&& 31 = 0) :
    x &&& 224 = x := by
  have h255 : x &&& 255 = x := and_255_of_lt_256 x hx
  have hsplit : 31 ||| 224 = 255 := by decide
  have hdist := Nat.and_or_distrib_left x 31 224
  rw [hsplit, h255] at hdist
  rw [h, Nat.zero_or] at hdist
  exact hdist.symm

theorem and_224_of_lt_32 (x : Nat) (h : x < 32) : x &&& 224 = 0 := by
  have h31 : x &&& 31 = x := and_31_of_lt_32 x h
  have hdis : 31 &&& 224 = 0 := by decide
  calc
    x &&& 224 = (x &&& 31) &&& 224 := by rw [h31]
    _ = x &&& (31 &&& 224) := by rw [Nat.and_assoc]
    _ = x &&& 0 := by rw [hdis]
    _ = 0 := Nat.and_zero x

/-- Low 5 bits of `major_base` are clear: it is a CBOR major-type tag. -/
def CleanMajor (major_base : U8) : Prop :=
  (major_base &&& ADDITIONAL_MASK) = 0#u8

theorem clean_major_val (major_base : U8) (h : CleanMajor major_base) :
    major_base.val &&& 31 = 0 := by
  unfold CleanMajor at h
  have h0 := congrArg UScalar.val h
  simpa [u8_and_val, additional_mask_val] using h0

theorem clean_major_and_mask (major_base : U8) (h : CleanMajor major_base) :
    (major_base &&& MAJOR_MASK) = major_base := by
  apply UScalar.val_eq_imp
  simp only [u8_and_val, major_mask_val]
  exact and_224_of_and_31_zero major_base.val (by scalar_tac) (clean_major_val major_base h)

theorem extra_lt_32_and_major (extra : U8) (h : extra.val < 32) :
    extra.val &&& 224 = 0 :=
  and_224_of_lt_32 extra.val h

theorem or_and_major (major extra : U8) (hmajor : CleanMajor major)
    (hextra : extra.val < 32) :
    ((major ||| extra) &&& MAJOR_MASK) = major := by
  apply UScalar.val_eq_imp
  simp only [u8_and_val, u8_or_val, major_mask_val]
  have hmajv : major.val &&& 224 = major.val := by
    have := clean_major_and_mask major hmajor
    have := congrArg UScalar.val this
    simpa [u8_and_val, major_mask_val] using this
  have hex : extra.val &&& 224 = 0 := extra_lt_32_and_major extra hextra
  rw [Nat.and_or_distrib_right, hex, Nat.or_zero, hmajv]

theorem or_and_additional (major extra : U8) (hmajor : CleanMajor major)
    (hextra : extra.val < 32) :
    ((major ||| extra) &&& ADDITIONAL_MASK) = extra := by
  apply UScalar.val_eq_imp
  simp only [u8_and_val, u8_or_val, additional_mask_val]
  have h0 : major.val &&& 31 = 0 := clean_major_val major hmajor
  have hextra31 : extra.val &&& 31 = extra.val := and_31_of_lt_32 extra.val hextra
  rw [Nat.and_or_distrib_right, h0, Nat.zero_or, hextra31]

theorem usize_checked_add_zero (n : Usize) :
    Usize.checked_add 0#usize n = some n := by
  have h := Usize.checked_add_bv_spec (0#usize) n
  cases hc : Usize.checked_add 0#usize n with
  | none =>
    simp only [hc] at h
    have hz : (0#usize).val = 0 := rfl
    have hn : n.val ≤ Usize.max := by scalar_tac
    scalar_tac
  | some z =>
    simp only [hc] at h
    obtain ⟨_, hv, _⟩ := h
    apply congrArg some
    apply UScalar.val_eq_imp
    have hz : (0#usize).val = 0 := rfl
    omega

theorem take_ok (self : Reader) (n : Usize)
    (hbound : self.pos.val + n.val ≤ self.buf.length) :
    Reader.take self n ⦃ r reader' =>
      ∃ (out : Slice U8) (end1 : Usize),
        Usize.checked_add self.pos n = some end1 ∧
        r = core.result.Result.Ok out ∧
        reader' = { buf := self.buf, pos := end1 } ∧
        out.val = self.buf.val.slice self.pos.val end1.val ⦄ := by
  unfold Reader.take
  simp only [lift, bind_tc_ok]
  cases hca : Usize.checked_add self.pos n with
  | none =>
    have hadd := Usize.checked_add_bv_spec self.pos n
    simp only [hca] at hadd
    have hlen := Slice.length_ineq self.buf
    have heq : self.buf.length = self.buf.val.length := rfl
    scalar_tac
  | some end1 =>
    have hadd := Usize.checked_add_bv_spec self.pos n
    simp only [hca] at hadd
    obtain ⟨_, hend, _⟩ := hadd
    simp only [bind_tc_ok, core.slice.Slice.get]
    unfold core.slice.index.SliceIndexRangeUsizeSlice.get
    have hle : self.pos ≤ end1 := (UScalar.le_equiv self.pos end1).mpr (by omega)
    split
    · simp only [bind_tc_ok, spec_ok, hca]
      refine ⟨⟨self.buf.val.slice self.pos.val end1.val, by
        have := List.slice_length_le (α := U8) self.pos.val end1.val self.buf.val
        have := Slice.length_ineq self.buf
        scalar_tac⟩, end1, rfl, rfl, rfl, rfl⟩
    · rename_i hcond
      have : self.pos ≤ end1 ∧ end1 ≤ self.buf.length :=
        ⟨hle, by
          have : end1.val ≤ self.buf.length := by omega
          simpa [UScalar.le_equiv] using this⟩
      exact (hcond this).elim

theorem get_u8_ok (bytes : Slice U8) (i : Usize) (hi : i.val < bytes.length) :
    get_u8 bytes i ⦃ r => r = core.result.Result.Ok (bytes[i]'hi) ⦄ := by
  unfold get_u8
  simp only [core.slice.Slice.get, core.slice.index.Usize.get, bind_tc_ok]
  have hsome : bytes[i]? = some (bytes[i]'hi) := by
    simp only [Slice.getElem?_Usize_eq, Slice.getElem_Usize_eq]
    exact List.getElem?_eq_getElem hi
  simp [hsome, spec_ok]

theorem take_ok_eq (self : Reader) (n : Usize)
    (hbound : self.pos.val + n.val ≤ self.buf.length) :
    ∃ (out : Slice U8) (end1 : Usize),
      Usize.checked_add self.pos n = some end1 ∧
      Reader.take self n =
        ok (core.result.Result.Ok out, { buf := self.buf, pos := end1 }) ∧
      out.val = self.buf.val.slice self.pos.val end1.val := by
  have h := take_ok self n hbound
  cases ht : Reader.take self n with
  | fail _ => simp [spec, theta, ht] at h
  | div => simp [spec, theta, ht] at h
  | ok vr =>
    rcases vr with ⟨r, reader'⟩
    simp [spec, theta, wp_return, ht, uncurry'] at h
    obtain ⟨out, end1, hca, hr, hrdr, hslice⟩ := h
    refine ⟨out, end1, hca, ?_, hslice⟩
    simp [ht, hr, hrdr]

theorem get_u8_ok_eq (bytes : Slice U8) (i : Usize) (hi : i.val < bytes.length) :
    get_u8 bytes i = ok (core.result.Result.Ok (bytes[i]'hi)) := by
  have h := get_u8_ok bytes i hi
  cases hg : get_u8 bytes i with
  | fail _ => simp [spec, theta, hg] at h
  | div => simp [spec, theta, hg] at h
  | ok r =>
    simp [spec, theta, wp_return, hg] at h
    simp [hg, h]

/-- Canonical 1-byte head: additional-info `arg` with `arg < 24`. -/
def canon_ai0_23 (major_base : U8) (arg : U64) : Slice U8 :=
  Array.to_slice (Array.make 1#usize [major_base ||| UScalar.cast .U8 arg])

/-- Canonical 2-byte head: additional-info 24, argument in `24..=255`. -/
def canon_ai24 (major_base : U8) (arg : U64) : Slice U8 :=
  Array.to_slice
    (Array.make 2#usize [major_base ||| 24#u8, UScalar.cast .U8 arg])

theorem canon_ai0_23_length (major_base : U8) (arg : U64) :
    (canon_ai0_23 major_base arg).length = 1 := by
  simp [canon_ai0_23, Array.to_slice, Array.make]

theorem canon_ai24_length (major_base : U8) (arg : U64) :
    (canon_ai24 major_base arg).length = 2 := by
  simp [canon_ai24, Array.to_slice, Array.make]

theorem canon_ai0_23_get (major_base : U8) (arg : U64) :
    (canon_ai0_23 major_base arg).val[0]'(by simp [canon_ai0_23_length]) =
      major_base ||| UScalar.cast .U8 arg := by
  simp [canon_ai0_23, Array.to_slice, Array.make]

theorem canon_ai24_get0 (major_base : U8) (arg : U64) :
    (canon_ai24 major_base arg).val[0]'(by simp [canon_ai24_length]) =
      major_base ||| 24#u8 := by
  simp [canon_ai24, Array.to_slice, Array.make]

theorem canon_ai24_get1 (major_base : U8) (arg : U64) :
    (canon_ai24 major_base arg).val[1]'(by simp [canon_ai24_length]) =
      UScalar.cast .U8 arg := by
  simp [canon_ai24, Array.to_slice, Array.make]

theorem cast_u8_of_lt_256 (arg : U64) (h : arg.val ≤ 255) :
    (UScalar.cast .U8 arg).val = arg.val := by
  simp only [UScalar.cast_val_eq]
  have : 2 ^ (UScalarTy.U8).numBits = 256 := by simp
  rw [this]
  exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le h)

theorem from_u8_cast_id (arg : U64) (h : arg.val ≤ 255) :
    core.convert.num.FromU64U8.from (UScalar.cast .U8 arg) = arg := by
  apply UScalar.val_eq_imp
  simp only [core.convert.num.FromU64U8.from_val_eq, cast_u8_of_lt_256 arg h]

theorem write_head_ai0_23_eq (sink : SliceSink) (major_base : U8) (arg : U64)
    (harg : arg < 24#u64) :
    write_head sink major_base arg =
      SliceSink.write_bytes sink (canon_ai0_23 major_base arg) := by
  unfold write_head canon_ai0_23
  simp [harg, lift, bind_tc_ok]

theorem list_slice_zero_one (s : List U8) (h : 0 < s.length) :
    s.slice 0 1 = [s[0]] := by
  cases s with
  | nil => cases h
  | cons b rest => simp [List.slice_zero_j]

/-- `read_head` on a 1-byte smallest-form encoding recovers `arg`. -/
theorem read_head_ai0_23 (major_base : U8) (arg : U64)
    (hmajor : CleanMajor major_base) (harg : arg < 24#u64) :
    ∃ rdr,
      Reader.read_head
          { buf := canon_ai0_23 major_base arg, pos := 0#usize } major_base =
        ok (core.result.Result.Ok arg, rdr) := by
  have hargn : arg.val < 24 := (UScalar.lt_equiv arg 24#u64).mp harg
  have hextra : (UScalar.cast .U8 arg).val < 32 := by
    rw [cast_u8_of_lt_256 arg (by omega)]
    omega
  have hhead :
      ((major_base ||| UScalar.cast .U8 arg) &&& MAJOR_MASK) = major_base :=
    or_and_major major_base (UScalar.cast .U8 arg) hmajor hextra
  have hadd :
      ((major_base ||| UScalar.cast .U8 arg) &&& ADDITIONAL_MASK) =
        UScalar.cast .U8 arg :=
    or_and_additional major_base (UScalar.cast .U8 arg) hmajor hextra
  set rdr0 : Reader := { buf := canon_ai0_23 major_base arg, pos := 0#usize }
  obtain ⟨out, end1, hca, htakeeq, hslice⟩ :=
    take_ok_eq rdr0 1#usize (by simp [canon_ai0_23_length, rdr0])
  unfold Reader.read_head
  rw [htakeeq]
  unfold core.result.Result.Insts.CoreOpsTry.branch
  simp [bind_tc_ok]
  have hpos0 : rdr0.pos = 0#usize := by simp [rdr0]
  have hbuf0 : rdr0.buf = canon_ai0_23 major_base arg := by simp [rdr0]
  have hend : end1 = 1#usize := by
    rw [hpos0, usize_checked_add_zero] at hca
    exact Option.some.inj hca.symm
  have houtval : out.val = [major_base ||| UScalar.cast .U8 arg] := by
    rw [hslice, hend, hpos0, hbuf0]
    have h0 : (0#usize).val = 0 := rfl
    have h1 : (1#usize).val = 1 := rfl
    simp only [h0, h1]
    have hlen0 : 0 < (canon_ai0_23 major_base arg).val.length := by
      simp [canon_ai0_23_length]
    rw [list_slice_zero_one _ hlen0, canon_ai0_23_get]
  have houtlen : out.length = 1 := by simp [Slice.length, houtval]
  have hgeteq := get_u8_ok_eq out 0#usize (by simp [houtlen])
  rw [hgeteq]
  simp [bind_tc_ok, lift]
  have hb : out[0#usize]'(by simp [houtlen]) =
      major_base ||| UScalar.cast .U8 arg := by
    simp only [Slice.getElem_Usize_eq, houtval]
    rfl
  have hmask :
      (out[0#usize]'(by simp [houtlen]) &&& MAJOR_MASK) = major_base := by
    simpa [hb] using hhead
  split
  · have haddb :
        (out[0#usize]'(by simp [houtlen]) &&& ADDITIONAL_MASK) =
          UScalar.cast .U8 arg := by
      simpa [hb] using hadd
    have hlt : UScalar.cast .U8 arg < 24#u8 :=
      (UScalar.lt_equiv _ _).mpr (by
        have h24 : (24#u8).val = 24 := rfl
        rw [cast_u8_of_lt_256 arg (by omega), h24]
        omega)
    have hidx : out[0#usize]'(by simp [houtlen]) =
        out.val[0]'(by simp [houtval]) := by
      simp [Slice.getElem_Usize_eq]
    split
    · refine ⟨{ buf := rdr0.buf, pos := end1 }, ?_⟩
      simp [Prod.mk.injEq]
      apply UScalar.val_eq_imp
      simp only [core.convert.num.FromU64U8.from_val_eq, u8_and_val, additional_mask_val]
      have hconn := congrArg UScalar.val haddb
      simp only [u8_and_val, additional_mask_val, hidx] at hconn ⊢
      have hcast := cast_u8_of_lt_256 arg (by omega)
      omega
    · rename_i hnlt
      have hval := congrArg UScalar.val hadd
      simp only [u8_and_val, additional_mask_val, u8_or_val] at hval
      simp [houtval, u8_and_val, additional_mask_val, u8_or_val] at hnlt
      have hcast := cast_u8_of_lt_256 arg (by omega)
      have hmod : arg.val % 256 = arg.val := Nat.mod_eq_of_lt (by omega)
      rw [hcast] at hval
      rw [hmod] at hnlt
      rw [hval] at hnlt
      omega
  · rename_i hne
    exact (hne (congrArg UScalar.val hmask)).elim

theorem clean_major_unsigned : CleanMajor MAJOR_UNSIGNED := by
  unfold CleanMajor MAJOR_UNSIGNED ADDITIONAL_MASK
  native_decide

/-- WP form of `read_head_ai0_23`. -/
@[step]
theorem read_head_ai0_23_spec (major_base : U8) (arg : U64)
    (hmajor : CleanMajor major_base) (harg : arg < 24#u64) :
    Reader.read_head
      { buf := canon_ai0_23 major_base arg, pos := 0#usize } major_base
    ⦃ r _ => r = core.result.Result.Ok arg ⦄ := by
  obtain ⟨rdr, h⟩ := read_head_ai0_23 major_base arg hmajor harg
  simp [h, spec_ok, uncurry']

-- Encode-then-decode for AI 0..=23 still needs `written_bytes = canon_ai0_23`
-- after `write_bytes` into `empty_sink` (extracted mutation). Not claimed.

-- Expected: propext, Classical.choice, Quot.sound. See reports/PROOF.md.
#print axioms read_uint_no_panic
#print axioms read_bstr_no_panic
#print axioms read_bstr_fixed_64_no_panic
#print axioms read_array_header_no_panic
#print axioms read_map_header_no_panic
#print axioms read_sign1_envelope_no_panic
#print axioms decode_protected_header_no_panic
#print axioms build_sig_structure_no_panic
#print axioms parse_sign1_no_panic
#print axioms write_bytes_dest_len_eq
#print axioms sig_structure_len_le_max
#print axioms read_head_ai0_23
#print axioms read_head_ai0_23_spec
#print axioms write_head_ai0_23_eq
#print axioms take_ok_eq

end NoPanic
