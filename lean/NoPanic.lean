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

end NoPanic
