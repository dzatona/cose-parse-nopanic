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
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace NoPanic

/-- No-panic `step*`: postcondition is `True`, so skip grind. -/
macro "nstep" : tactic => `(tactic| step* -grind -threadGrindState)

theorem let_prod_mk {α β γ} (a : α) (b : β) (f : α → β → γ) :
    (let (x, y) := (a, b); f x y) = f a b := rfl

theorem match_prod_mk {α β γ} (a : α) (b : β) (f : α → β → γ) :
    (match (a, b) with | (x, y) => f x y) = f a b := rfl

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

theorem take_err (self : Reader) (n : Usize)
    (hbound : ¬ (self.pos.val + n.val ≤ self.buf.length)) :
    Reader.take self n =
      ok (core.result.Result.Err CodecError.UnexpectedEnd, self) := by
  unfold Reader.take
  simp only [lift, bind_tc_ok]
  cases hca : Usize.checked_add self.pos n with
  | none => rfl
  | some end1 =>
    have hadd := Usize.checked_add_bv_spec self.pos n
    simp only [hca] at hadd
    obtain ⟨_, hend, _⟩ := hadd
    simp only [bind_tc_ok, core.slice.Slice.get]
    unfold core.slice.index.SliceIndexRangeUsizeSlice.get
    split
    · rename_i hcond
      have : end1.val ≤ self.buf.length := by
        have := hcond.2
        scalar_tac
      omega
    · rfl

theorem checked_add_val (p n end1 : Usize)
    (h : Usize.checked_add p n = some end1) :
    end1.val = p.val + n.val := by
  have hadd := Usize.checked_add_bv_spec p n
  simp only [h] at hadd
  obtain ⟨_, hend, _⟩ := hadd
  exact hend

theorem take_out_length (self : Reader) (n : Usize) (out : Slice U8) (end1 : Usize)
    (hca : Usize.checked_add self.pos n = some end1)
    (hslice : out.val = self.buf.val.slice self.pos.val end1.val)
    (hbound : self.pos.val + n.val ≤ self.buf.length) :
    out.length = n.val := by
  have hend := checked_add_val self.pos n end1 hca
  have hlen : self.buf.length = self.buf.val.length := rfl
  simp only [Slice.length, hslice, List.slice_length, hend, hlen] at *
  omega

theorem list_slice_one {α} (s : List α) (i : Nat) (hi : i < s.length) :
    s.slice i (i + 1) = [s[i]] := by
  induction s generalizing i with
  | nil => cases hi
  | cons x xs ih =>
    cases i with
    | zero => simp [List.slice]
    | succ j =>
      have hj : j < xs.length := by
        simp at hi
        omega
      simpa [List.slice] using ih j hj

/-- `?` on `Err` cannot yield `Ok n`. -/
theorem try_err_ne_ok {T} (e : CodecError) (self rdr : Reader) (n : U64)
    (cont : T → Result ((core.result.Result U64 CodecError) × Reader))
    (h :
      (do
        let cf ← core.result.Result.Insts.CoreOpsTry.branch
          (core.result.Result.Err e : core.result.Result T CodecError)
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val => cont val
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              U64 (core.convert.FromSame CodecError) residual
          ok (r, self)) = ok (core.result.Result.Ok n, rdr)) : False := by
  simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_tc_ok] at h

/-- `?` on `Ok v` continues with `v`. -/
theorem try_ok_reduce {T} (v : T) (self : Reader)
    (cont : T → Result ((core.result.Result U64 CodecError) × Reader)) :
    (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch
        (core.result.Result.Ok v : core.result.Result T CodecError)
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val => cont val
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            U64 (core.convert.FromSame CodecError) residual
        ok (r, self)) = cont v := by
  simp [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]

theorem u8_max_val : core.num.U8.MAX.val = 255 := rfl

theorem u16_max_val : core.num.U16.MAX.val = 65535 := rfl

theorem u32_max_val : core.num.U32.MAX.val = 4294967295 := rfl

theorem from_u8_max_val :
    (core.convert.num.FromU64U8.from core.num.U8.MAX).val = 255 := by
  rw [core.convert.num.FromU64U8.from_val_eq, u8_max_val]

theorem from_u16_max_val :
    (core.convert.num.FromU64U16.from core.num.U16.MAX).val = 65535 := by
  rw [core.convert.num.FromU64U16.from_val_eq, u16_max_val]

theorem from_u32_max_val :
    (core.convert.num.FromU64U32.from core.num.U32.MAX).val = 4294967295 := by
  rw [core.convert.num.FromU64U32.from_val_eq, u32_max_val]

theorem not_le_u64 {x y : U64} (h : ¬ x ≤ y) : y.val < x.val := by
  have := (UScalar.le_equiv x y).not.mp h
  omega

theorem ok_err_ne_ok (e : CodecError) (n : U64) (r1 r2 : Reader)
    (h : ok (core.result.Result.Err e, r1) = ok (core.result.Result.Ok n, r2)) :
    False := by
  injection h with h'
  nomatch h'

theorem decLe_rec_eq_ite {α} {n m : Nat} (e t : α) :
    Decidable.rec (motive := fun _ => α) (fun _ => e) (fun _ => t) (Nat.decLe n m) =
      if n ≤ m then t else e := by
  by_cases h : n ≤ m
  · simp [h]
    cases hm : Nat.decLe n m with
    | isTrue ht => rfl
    | isFalse hf => exact (hf h).elim
  · simp [h]
    cases hm : Nat.decLe n m with
    | isTrue ht => exact (h ht).elim
    | isFalse hf => rfl

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

/-! # RFC 8949 §4.2.1 canonicity (`Ok n` ⇒ smallest-form additional-info)

`read_head_ai0_23` is the converse on 1-byte heads (canonical encoding → `Ok`).
This section is decode-only: a successful `Ok n` used additional-info
0..=23 / 24 / 25 / 26 / 27 with the min-width cuts in `read_head`
(`value <= u8::MAX` / `u16::MAX` / `u32::MAX`). Not encode-then-decode.
Not full RFC 8949. -/

/-- Additional-info `ai` is RFC 8949 §4.2.1 smallest-form width for `n`.
    AI 25/26/27 include the 2/4/8-byte min-width cuts: the argument does not
    fit the next-smaller encoding. Reserved 28..=31 are excluded. -/
def SmallestFormAi (n : U64) (ai : Nat) : Prop :=
  (ai < 24 ∧ n.val = ai) ∨
  (ai = 24 ∧ 24 ≤ n.val ∧ n.val ≤ 255) ∨
  (ai = 25 ∧ 256 ≤ n.val ∧ n.val ≤ 65535) ∨
  (ai = 26 ∧ 65536 ≤ n.val ∧ n.val ≤ 4294967295) ∨
  (ai = 27 ∧ 4294967296 ≤ n.val)

theorem smallest_form_ai0_23 (additional : U8) (n : U64)
    (hlt : additional < 24#u8)
    (hn : n = core.convert.num.FromU64U8.from additional) :
    SmallestFormAi n additional.val := by
  refine Or.inl ⟨?_, ?_⟩
  · have h24 : (24#u8).val = 24 := rfl
    have := (UScalar.lt_equiv additional 24#u8).mp hlt
    simpa [h24] using this
  · rw [hn, core.convert.num.FromU64U8.from_val_eq]

theorem smallest_form_ai24 (byte : U8) (n : U64)
    (hge : ¬ byte < 24#u8)
    (hn : n = core.convert.num.FromU64U8.from byte) :
    SmallestFormAi n 24 := by
  refine Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)
  · have h24 : (24#u8).val = 24 := rfl
    have hnv : n.val = byte.val := by
      rw [hn, core.convert.num.FromU64U8.from_val_eq]
    have := (UScalar.lt_equiv byte 24#u8).not.mp hge
    have : 24 ≤ byte.val := by simpa [h24] using (Nat.not_lt.mp this)
    omega
  · have hnv : n.val = byte.val := by
      rw [hn, core.convert.num.FromU64U8.from_val_eq]
    have hmax : byte.val ≤ 255 := by scalar_tac
    omega

theorem smallest_form_ai25 (n : U64)
    (hlo : 256 ≤ n.val) (hhi : n.val ≤ 65535) :
    SmallestFormAi n 25 :=
  Or.inr (Or.inr (Or.inl ⟨rfl, hlo, hhi⟩))

theorem smallest_form_ai26 (n : U64)
    (hlo : 65536 ≤ n.val) (hhi : n.val ≤ 4294967295) :
    SmallestFormAi n 26 :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hlo, hhi⟩)))

theorem smallest_form_ai27 (n : U64) (hlo : 4294967296 ≤ n.val) :
    SmallestFormAi n 27 :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hlo⟩)))

theorem from_u16_le_max (x : U16) :
    (core.convert.num.FromU64U16.from x).val ≤ 65535 := by
  rw [core.convert.num.FromU64U16.from_val_eq]
  have : x.val ≤ U16.max := by scalar_tac
  simpa [U16.max_eq] using this

theorem from_u32_le_max (x : U32) :
    (core.convert.num.FromU64U32.from x).val ≤ 4294967295 := by
  rw [core.convert.num.FromU64U32.from_val_eq]
  have : x.val ≤ U32.max := by scalar_tac
  simpa [U32.max_eq] using this

/-- Close `ok (Err _, _) = ok (Ok n, _)` after a `?` residual. -/
theorem residual_ne_ok (e : CodecError) (self rdr : Reader) (n : U64)
    (h :
      (do
        let r ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            U64 (core.convert.FromSame CodecError) (core.result.Result.Err e)
        ok (r, self)) = ok (core.result.Result.Ok n, rdr)) : False := by
  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_tc_ok] at h

/-- Peel `take` + `?` from a `read_head` additional-info arm.
    Truncation is `Err UnexpectedEnd`, so it cannot be `Ok n`. -/
theorem peel_take_continue
    {self : Reader} {nbytes : Usize} {n : U64} {rdr : Reader}
    {cont : Slice U8 → Reader → Result ((core.result.Result U64 CodecError) × Reader)}
    (h :
      (do
        let (r2, self2) ← Reader.take self nbytes
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 => cont val2 self2
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              U64 (core.convert.FromSame CodecError) residual
          ok (r3, self2)) = ok (core.result.Result.Ok n, rdr)) :
    ∃ (out : Slice U8) (self2 : Reader),
      self2.buf = self.buf ∧
      out.length = nbytes.val ∧
      cont out self2 = ok (core.result.Result.Ok n, rdr) := by
  by_cases hbound : self.pos.val + nbytes.val ≤ self.buf.length
  · obtain ⟨out, end1, hca, htakeeq, hslice⟩ := take_ok_eq self nbytes hbound
    have hlen := take_out_length self nbytes out end1 hca hslice hbound
    refine ⟨out, { buf := self.buf, pos := end1 }, rfl, hlen, ?_⟩
    rw [htakeeq] at h
    simp only [bind_tc_ok, lift, let_prod_mk, match_prod_mk,
      core.result.Result.Insts.CoreOpsTry.branch] at h
    exact h
  · have hte := take_err self nbytes hbound
    rw [hte] at h
    simp only [bind_tc_ok, lift, let_prod_mk, match_prod_mk,
      core.result.Result.Insts.CoreOpsTry.branch] at h
    exact (residual_ne_ok CodecError.UnexpectedEnd self rdr n h).elim

/-- Peel `get_u8` + `?`. An in-bounds index is `Ok`; it cannot be the
    residual that would make the arm `Err`. -/
theorem peel_get_u8_continue
    {bytes : Slice U8} {i : Usize} {self2 rdr : Reader} {n : U64}
    {cont : U8 → Result ((core.result.Result U64 CodecError) × Reader)}
    (hi : i.val < bytes.length)
    (h :
      (do
        let r3 ← get_u8 bytes i
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 => cont val3
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              U64 (core.convert.FromSame CodecError) residual
          ok (r4, self2)) = ok (core.result.Result.Ok n, rdr)) :
    cont (bytes[i]'hi) = ok (core.result.Result.Ok n, rdr) := by
  have hget := get_u8_ok_eq bytes i hi
  rw [hget] at h
  simp only [bind_tc_ok, lift, let_prod_mk, match_prod_mk,
    core.result.Result.Insts.CoreOpsTry.branch] at h
  exact h

/-- The AI-25 `value <= u8::MAX` cut: then-branch is `NonCanonicalLength`. -/
theorem min_width_if_u8
    (value : U64) (self2 rdr : Reader) (n : U64)
    (hhi : value.val ≤ 65535)
    (h :
      (if value ≤ core.convert.num.FromU64U8.from core.num.U8.MAX then
         ok (core.result.Result.Err CodecError.NonCanonicalLength, self2)
       else
         ok (core.result.Result.Ok value, self2)) =
      ok (core.result.Result.Ok n, rdr)) :
    256 ≤ n.val ∧ n.val ≤ 65535 := by
  split at h
  · exact (ok_err_ne_ok _ _ _ _ h).elim
  · rename_i hgt
    injection h with h'
    injection h' with hn _
    injection hn with hneq
    subst hneq
    refine ⟨?_, hhi⟩
    have := not_le_u64 hgt
    have := from_u8_max_val
    omega

/-- The AI-26 `value <= u16::MAX` cut. -/
theorem min_width_if_u16
    (value : U64) (self2 rdr : Reader) (n : U64)
    (hhi : value.val ≤ 4294967295)
    (h :
      (if value ≤ core.convert.num.FromU64U16.from core.num.U16.MAX then
         ok (core.result.Result.Err CodecError.NonCanonicalLength, self2)
       else
         ok (core.result.Result.Ok value, self2)) =
      ok (core.result.Result.Ok n, rdr)) :
    65536 ≤ n.val ∧ n.val ≤ 4294967295 := by
  split at h
  · exact (ok_err_ne_ok _ _ _ _ h).elim
  · rename_i hgt
    injection h with h'
    injection h' with hn _
    injection hn with hneq
    subst hneq
    refine ⟨?_, hhi⟩
    have := not_le_u64 hgt
    have := from_u16_max_val
    omega

/-- The AI-27 `value <= u32::MAX` cut. -/
theorem min_width_if_u32
    (value : U64) (self2 rdr : Reader) (n : U64)
    (h :
      (if value ≤ core.convert.num.FromU64U32.from core.num.U32.MAX then
         ok (core.result.Result.Err CodecError.NonCanonicalLength, self2)
       else
         ok (core.result.Result.Ok value, self2)) =
      ok (core.result.Result.Ok n, rdr)) :
    4294967296 ≤ n.val := by
  split at h
  · exact (ok_err_ne_ok _ _ _ _ h).elim
  · rename_i hgt
    injection h with h'
    injection h' with hn _
    injection hn with hneq
    subst hneq
    have := not_le_u64 hgt
    have := from_u32_max_val
    omega

/-- Successful `read_head` used RFC 8949 §4.2.1 smallest-form additional-info
    for `n`, including the 2/4/8-byte min-width cuts. Does not claim the
    argument payload bytes, encode-then-decode, or the rest of RFC 8949. -/
theorem read_head_ok_smallest_form
    (self : Reader) (major_base : U8) (n : U64) (rdr : Reader)
    (h : Reader.read_head self major_base = ok (core.result.Result.Ok n, rdr)) :
    ∃ (head : U8),
      self.buf.val[self.pos.val]? = some head ∧
      (head &&& MAJOR_MASK) = major_base ∧
      SmallestFormAi n (head &&& ADDITIONAL_MASK).val := by
  by_cases hbound : self.pos.val + (1#usize).val ≤ self.buf.length
  · obtain ⟨out, end1, hca, htakeeq, hslice⟩ := take_ok_eq self 1#usize hbound
    have houtlen : out.length = 1 :=
      take_out_length self 1#usize out end1 hca hslice hbound
    have hget := get_u8_ok_eq out 0#usize (by simp [houtlen])
    have hlen : self.buf.length = self.buf.val.length := rfl
    have h1 : (1#usize).val = 1 := rfl
    have hpos : self.pos.val < self.buf.val.length := by
      rw [hlen, h1] at hbound
      omega
    have hendval := checked_add_val self.pos 1#usize end1 hca
    have hhead_eq :
        out[0#usize]'(by simp [houtlen]) = self.buf.val[self.pos.val]'hpos := by
      simp only [Slice.getElem_Usize_eq]
      have hs : out.val = self.buf.val.slice self.pos.val (self.pos.val + 1) := by
        simpa [hendval, h1] using hslice
      have hs1 : out.val = [self.buf.val[self.pos.val]'hpos] := by
        rw [hs, list_slice_one _ _ hpos]
      simp [hs1]
    set head := out[0#usize]'(by simp [houtlen])
    have hsome : self.buf.val[self.pos.val]? = some head := by
      rw [List.getElem?_eq_getElem hpos, hhead_eq]
    conv at h =>
      lhs
      unfold Reader.read_head
      rw [htakeeq]
      simp [bind_tc_ok, lift, let_prod_mk, match_prod_mk,
        core.result.Result.Insts.CoreOpsTry.branch]
    try rw [hget] at h
    try simp only [bind_tc_ok, lift, let_prod_mk, match_prod_mk,
        core.result.Result.Insts.CoreOpsTry.branch] at h
    split at h
    · rename_i hmajor
      have hmajor' : (head &&& MAJOR_MASK) = major_base := by
        apply UScalar.val_eq_imp
        simpa [head, u8_and_val, major_mask_val] using hmajor
      set additional := head &&& ADDITIONAL_MASK
      split at h
      · rename_i hlt
        injection h with h'
        injection h' with hn _
        have hn' : n = core.convert.num.FromU64U8.from additional := by
          simpa [additional, head] using hn.symm
        refine ⟨head, hsome, hmajor', ?_⟩
        simpa [additional] using smallest_form_ai0_23 additional n hlt hn'
      · rename_i hge
        have hlo : 24 ≤ additional.val := by
          simp only [additional, u8_and_val, additional_mask_val] at hge ⊢
          omega
        have hhi : additional.val ≤ 31 := by
          simp only [additional, u8_and_val, additional_mask_val]
          exact Nat.and_le_right
        have hv :
            additional.val = 24 ∨ additional.val = 25 ∨ additional.val = 26 ∨
              additional.val = 27 ∨ additional.val = 28 ∨ additional.val = 29 ∨
              additional.val = 30 ∨ additional.val = 31 := by omega
        rcases hv with hv | hv | hv | hv | hv | hv | hv | hv
        · have hai : additional = 24#u8 := by
            apply UScalar.val_eq_imp
            have : (24#u8).val = 24 := rfl
            omega
          simp [hai] at h
          by_cases hbound2 :
              ({ buf := self.buf, pos := end1 } : Reader).pos.val + (1#usize).val ≤
                ({ buf := self.buf, pos := end1 } : Reader).buf.length
          · obtain ⟨out2, end2, hca2, htake2, hslice2⟩ :=
              take_ok_eq { buf := self.buf, pos := end1 } 1#usize hbound2
            have hlen2 : out2.length = 1 :=
              take_out_length { buf := self.buf, pos := end1 } 1#usize out2 end2
                hca2 hslice2 hbound2
            have hget2 := get_u8_ok_eq out2 0#usize (by simp [hlen2])
            conv at h =>
              lhs
              rw [htake2]
              simp [bind_tc_ok, lift, let_prod_mk, match_prod_mk,
                core.result.Result.Insts.CoreOpsTry.branch]
            try rw [hget2] at h
            try simp only [bind_tc_ok, lift, let_prod_mk, match_prod_mk,
                core.result.Result.Insts.CoreOpsTry.branch] at h
            by_cases hbyte : (out2[0#usize]'(by simp [hlen2])).val < 24
            · rw [if_pos hbyte] at h
              exact (ok_err_ne_ok _ _ _ _ h).elim
            · rw [if_neg hbyte] at h
              injection h with h'
              injection h' with hn _
              have hn' : n = core.convert.num.FromU64U8.from
                  (out2[0#usize]'(by simp [hlen2])) := by
                injection hn with hn1
                exact hn1.symm
              have hsf :=
                smallest_form_ai24 (out2[0#usize]'(by simp [hlen2])) n
                  (by
                    have h24 : (24#u8).val = 24 := rfl
                    intro hlt
                    have := (UScalar.lt_equiv (out2[0#usize]'(by simp [hlen2])) 24#u8).mp hlt
                    exact hbyte (by simpa [h24] using this)) hn'
              have : (head &&& ADDITIONAL_MASK).val = 24 := by
                have h24 : (24#u8).val = 24 := rfl
                simpa [additional, h24] using congrArg UScalar.val hai
              refine ⟨head, hsome, hmajor', ?_⟩
              simpa [this] using hsf
          · have hte :=
              take_err { buf := self.buf, pos := end1 } 1#usize hbound2
            rw [hte] at h
            simp only [bind_tc_ok, lift, let_prod_mk, match_prod_mk,
        core.result.Result.Insts.CoreOpsTry.branch] at h
            exact (residual_ne_ok CodecError.UnexpectedEnd
              { buf := self.buf, pos := end1 } rdr n h).elim
        · have hai : additional = 25#u8 := by
            apply UScalar.val_eq_imp
            have : (25#u8).val = 25 := rfl
            omega
          have hai_val : (head &&& ADDITIONAL_MASK).val = 25 := by
            have h25 : (25#u8).val = 25 := rfl
            simpa [additional, h25] using congrArg UScalar.val hai
          simp [hai] at h
          obtain ⟨out2, self2, -, hlen2, h⟩ := peel_take_continue h
          have h := peel_get_u8_continue (i := 0#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 1#usize) (hi := by simp [hlen2]) h
          try simp only [lift, bind_tc_ok] at h
          have hbounds := min_width_if_u8 _ self2 rdr n (from_u16_le_max _) h
          refine ⟨head, hsome, hmajor', ?_⟩
          simpa [hai_val] using smallest_form_ai25 n hbounds.1 hbounds.2
        · have hai : additional = 26#u8 := by
            apply UScalar.val_eq_imp
            have : (26#u8).val = 26 := rfl
            omega
          have hai_val : (head &&& ADDITIONAL_MASK).val = 26 := by
            have h26 : (26#u8).val = 26 := rfl
            simpa [additional, h26] using congrArg UScalar.val hai
          simp [hai] at h
          obtain ⟨out2, self2, -, hlen2, h⟩ := peel_take_continue h
          have h := peel_get_u8_continue (i := 0#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 1#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 2#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 3#usize) (hi := by simp [hlen2]) h
          try simp only [lift, bind_tc_ok] at h
          have hbounds := min_width_if_u16 _ self2 rdr n (from_u32_le_max _) h
          refine ⟨head, hsome, hmajor', ?_⟩
          simpa [hai_val] using smallest_form_ai26 n hbounds.1 hbounds.2
        · have hai : additional = 27#u8 := by
            apply UScalar.val_eq_imp
            have : (27#u8).val = 27 := rfl
            omega
          have hai_val : (head &&& ADDITIONAL_MASK).val = 27 := by
            have h27 : (27#u8).val = 27 := rfl
            simpa [additional, h27] using congrArg UScalar.val hai
          simp [hai] at h
          obtain ⟨out2, self2, -, hlen2, h⟩ := peel_take_continue h
          have h := peel_get_u8_continue (i := 0#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 1#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 2#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 3#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 4#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 5#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 6#usize) (hi := by simp [hlen2]) h
          have h := peel_get_u8_continue (i := 7#usize) (hi := by simp [hlen2]) h
          try simp only [lift, bind_tc_ok] at h
          have hlo := min_width_if_u32 _ self2 rdr n h
          refine ⟨head, hsome, hmajor', ?_⟩
          simpa [hai_val] using smallest_form_ai27 n hlo
        · -- 28..=31: reserved / indefinite. Reduce the match, then `Err`.
          have hai : additional = 28#u8 := by
            apply UScalar.val_eq_imp
            have : (28#u8).val = 28 := rfl
            omega
          simp [hai] at h
          conv at h =>
            lhs
            whnf
          rw [decLe_rec_eq_ite] at h
          split at h <;> (try split at h) <;>
            exact (ok_err_ne_ok _ _ _ _ h).elim
        · have hai : additional = 29#u8 := by
            apply UScalar.val_eq_imp
            have : (29#u8).val = 29 := rfl
            omega
          simp [hai] at h
          conv at h =>
            lhs
            whnf
          rw [decLe_rec_eq_ite] at h
          split at h <;> (try split at h) <;>
            exact (ok_err_ne_ok _ _ _ _ h).elim
        · have hai : additional = 30#u8 := by
            apply UScalar.val_eq_imp
            have : (30#u8).val = 30 := rfl
            omega
          simp [hai] at h
          conv at h =>
            lhs
            whnf
          rw [decLe_rec_eq_ite] at h
          split at h <;> (try split at h) <;>
            exact (ok_err_ne_ok _ _ _ _ h).elim
        · have hai : additional = 31#u8 := by
            apply UScalar.val_eq_imp
            have : (31#u8).val = 31 := rfl
            omega
          simp [hai] at h
          conv at h =>
            lhs
            whnf
          rw [decLe_rec_eq_ite] at h
          split at h <;> (try split at h) <;>
            exact (ok_err_ne_ok _ _ _ _ h).elim
    · exact (ok_err_ne_ok _ _ _ _ h).elim
  · have hte := take_err self 1#usize hbound
    unfold Reader.read_head at h
    rw [hte] at h
    simp only [bind_tc_ok, lift, let_prod_mk, match_prod_mk,
        core.result.Result.Insts.CoreOpsTry.branch] at h
    exact (residual_ne_ok CodecError.UnexpectedEnd self rdr n h).elim

/-- If `read_uint buf` returns `Ok n`, the first byte is major type 0.
    Additional-info is RFC 8949 §4.2.1 min-width for `n`: 0..=23, 24
    (`24..=255`), 25 (`256..=65535`), 26 (`65536..=4294967295`), 27
    (`≥ 4294967296`). The 2/4/8-byte cuts are the `value <= u8::MAX` /
    `u16::MAX` / `u32::MAX` branches in `read_head`. Reserved 28..=31
    cannot be `Ok`. Extra-width 1-byte forms such as `[0x18, 0x05]`
    are `Err(NonCanonicalLength)`, not `Ok`. Not encode-then-decode.
    Not full RFC 8949. -/
theorem read_uint_ok_is_canonical (buf : Slice U8) (n : U64)
    (h : read_uint buf = ok (core.result.Result.Ok n)) :
    ∃ (head : U8),
      buf.val[0]? = some head ∧
      (head &&& MAJOR_MASK) = MAJOR_UNSIGNED ∧
      SmallestFormAi n (head &&& ADDITIONAL_MASK).val := by
  simp only [read_uint, Reader.new, Reader.read_uint, lift, bind_tc_ok] at h
  cases hrh : Reader.read_head { buf := buf, pos := 0#usize } MAJOR_UNSIGNED with
  | fail _ =>
    simp [hrh] at h
  | div =>
    simp [hrh] at h
  | ok vr =>
    rcases vr with ⟨r, rdr⟩
    simp [hrh, bind_tc_ok] at h
    obtain ⟨head, hsome, hmajor, hsf⟩ :=
      read_head_ok_smallest_form { buf := buf, pos := 0#usize } MAJOR_UNSIGNED n rdr
        (by simp [hrh, h])
    have h0 : ({ buf := buf, pos := 0#usize } : Reader).pos.val = 0 := rfl
    refine ⟨head, ?_, hmajor, hsf⟩
    simpa [h0] using hsome

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
#print axioms read_head_ok_smallest_form
#print axioms read_uint_ok_is_canonical

end NoPanic
