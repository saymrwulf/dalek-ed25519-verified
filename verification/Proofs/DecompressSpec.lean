/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/DecompressSpec.lean — phase 2, the constructive decompress chain,
   part 1: the arithmetic ingredients of `sqrt_ratio_i`.

   · `pow_p58_spec`     — a^((p−5)/8) via the pow22501 chain (Fermat-style,
                          the invert_spec pattern with exponent 2²⁵² − 3);
   · √−1               — already certified (ConstSpecs.sqrt_m1_spec);
   · `fe_ct_eq_spec`    — the constant-time field comparison decides
                          denotational equality: to_bytes is CANONICAL
                          (to_bytes_spec), so byte equality is residue
                          equality in both directions.

   Part 2 (sequel): the sqrt_ratio_i success-case walk, from_bytes, and
   `decompress_of_canonical` — the constructive upgrade of the point-level
   verification equation.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.PointEqSpec
import Proofs.InvertSpec
open Aeneas Aeneas.Std Result
open curve25519_dalek

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 600

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- a^((p−5)/8) = a^(2²⁵² − 3): the pow22501 chain squared twice and folded
    once more with a — the invert_spec pattern. -/
theorem pow_p58_spec (a : Fe) (hba : Bnd a (2^54)) :
    field.FieldElement51.pow_p58 a ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ ^ (2^252 - 3) ⦄ := by
  unfold field.FieldElement51.pow_p58
  let* ⟨ t19, t3, h1, h2, h3, h4 ⟩ ← pow22501_spec by bnd
  let* ⟨ t20, t20_post1, t20_post2 ⟩ ← pow2k_spec' by bnd
  let* ⟨ r, r_post1, r_post2 ⟩ ← mul_spec' by bnd
  refine ⟨by bnd, ?_⟩
  rw [r_post2, t20_post2, h3]
  rw [← pow_mul, ← pow_succ']
  congr 1

/- √−1: `sqrt_m1_spec` (ConstSpecs.lean) already pins the SQRT_M1 constant:
   Bnd s (2⁵²) ∧ ⟪s⟫·⟪s⟫ = −1 — reused as-is by the sqrt walk below. -/

/-- Byte-array value equality forces list equality (the converse of congr):
    little-endian digits are unique. -/
theorem bytesVal_inj (sa sb : Std.Array Std.U8 32#usize)
    (h : bytesVal sa = bytesVal sb) : (↑sa : List Std.U8) = (↑sb : List Std.U8) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
    e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31,
    hel⟩ := Bytes32.exists_bytes sa
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
    r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31,
    hrl⟩ := Bytes32.exists_bytes sb
  have hrq := (rangeEq_iff_bytesVal sa sb).mpr h
  have hpt : ∀ j, j < 32 → sa.val[j]! = sb.val[j]! := fun j hj => hrq j (Nat.zero_le _) hj
  have h0 : e0 = r0 := by simpa [hel, hrl] using hpt 0 (by norm_num)
  have h1 : e1 = r1 := by simpa [hel, hrl] using hpt 1 (by norm_num)
  have h2 : e2 = r2 := by simpa [hel, hrl] using hpt 2 (by norm_num)
  have h3 : e3 = r3 := by simpa [hel, hrl] using hpt 3 (by norm_num)
  have h4 : e4 = r4 := by simpa [hel, hrl] using hpt 4 (by norm_num)
  have h5 : e5 = r5 := by simpa [hel, hrl] using hpt 5 (by norm_num)
  have h6 : e6 = r6 := by simpa [hel, hrl] using hpt 6 (by norm_num)
  have h7 : e7 = r7 := by simpa [hel, hrl] using hpt 7 (by norm_num)
  have h8 : e8 = r8 := by simpa [hel, hrl] using hpt 8 (by norm_num)
  have h9 : e9 = r9 := by simpa [hel, hrl] using hpt 9 (by norm_num)
  have h10 : e10 = r10 := by simpa [hel, hrl] using hpt 10 (by norm_num)
  have h11 : e11 = r11 := by simpa [hel, hrl] using hpt 11 (by norm_num)
  have h12 : e12 = r12 := by simpa [hel, hrl] using hpt 12 (by norm_num)
  have h13 : e13 = r13 := by simpa [hel, hrl] using hpt 13 (by norm_num)
  have h14 : e14 = r14 := by simpa [hel, hrl] using hpt 14 (by norm_num)
  have h15 : e15 = r15 := by simpa [hel, hrl] using hpt 15 (by norm_num)
  have h16 : e16 = r16 := by simpa [hel, hrl] using hpt 16 (by norm_num)
  have h17 : e17 = r17 := by simpa [hel, hrl] using hpt 17 (by norm_num)
  have h18 : e18 = r18 := by simpa [hel, hrl] using hpt 18 (by norm_num)
  have h19 : e19 = r19 := by simpa [hel, hrl] using hpt 19 (by norm_num)
  have h20 : e20 = r20 := by simpa [hel, hrl] using hpt 20 (by norm_num)
  have h21 : e21 = r21 := by simpa [hel, hrl] using hpt 21 (by norm_num)
  have h22 : e22 = r22 := by simpa [hel, hrl] using hpt 22 (by norm_num)
  have h23 : e23 = r23 := by simpa [hel, hrl] using hpt 23 (by norm_num)
  have h24 : e24 = r24 := by simpa [hel, hrl] using hpt 24 (by norm_num)
  have h25 : e25 = r25 := by simpa [hel, hrl] using hpt 25 (by norm_num)
  have h26 : e26 = r26 := by simpa [hel, hrl] using hpt 26 (by norm_num)
  have h27 : e27 = r27 := by simpa [hel, hrl] using hpt 27 (by norm_num)
  have h28 : e28 = r28 := by simpa [hel, hrl] using hpt 28 (by norm_num)
  have h29 : e29 = r29 := by simpa [hel, hrl] using hpt 29 (by norm_num)
  have h30 : e30 = r30 := by simpa [hel, hrl] using hpt 30 (by norm_num)
  have h31 : e31 = r31 := by simpa [hel, hrl] using hpt 31 (by norm_num)
  rw [hel, hrl, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
      h28, h29, h30, h31]

/-- Lists determine `bytesVal`. -/
theorem bytesVal_congr {sa sb : Std.Array Std.U8 32#usize}
    (h : (↑sa : List Std.U8) = ↑sb) : bytesVal sa = bytesVal sb := by
  unfold bytesVal
  rw [h]

/-- **The canonical-bytes bridge**: for canonical serializations, byte-list
    equality IS denotational equality. -/
theorem bytes_eq_iff_denote {a b : Fe} {sa sb : Std.Array Std.U8 32#usize}
    (hsa : bytesVal sa = feVal a % P) (hsb : bytesVal sb = feVal b % P) :
    (↑sa : List Std.U8) = ↑sb ↔ ⟪a⟫ = ⟪b⟫ := by
  haveI : NeZero P := ⟨by unfold P; norm_num⟩
  have hmod : ⟪a⟫ = ⟪b⟫ ↔ feVal a % P = feVal b % P := by
    unfold denote
    rw [ZMod.natCast_eq_natCast_iff]
    exact ⟨fun h => h, fun h => h⟩
  constructor
  · intro h
    rw [hmod, ← hsa, ← hsb]
    exact bytesVal_congr h
  · intro h
    apply bytesVal_inj
    rw [hsa, hsb]
    exact hmod.mp h

/-- **The constant-time field comparison decides denotational equality**:
    to_bytes is canonical, so byte equality IS residue equality. -/
theorem fe_ct_eq_spec (a b : Fe) :
    backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq.ct_eq a b
      ⦃ c => (c.val = 0 ∨ c.val = 1) ∧ (c.val = 1 ↔ ⟪a⟫ = ⟪b⟫) ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq.ct_eq
  step with (to_bytes_spec' a) as ⟨sa, hsa⟩
  step as ⟨la, hla⟩
  step with (to_bytes_spec' b) as ⟨sb, hsb⟩
  step as ⟨lb, hlb⟩
  simp only [Slice.Insts.SubtleConstantTimeEq.ct_eq]
  try simp only [spec_ok]
  have hlav : la.val = sa.val := by rw [hla]; rfl
  have hlbv : lb.val = sb.val := by rw [hlb]; rfl
  rw [hlav, hlbv]
  have hbridge := bytes_eq_iff_denote hsa hsb
  by_cases heq : (↑sa : List Std.U8) = ↑sb
  · rw [if_pos heq]
    exact ⟨Or.inr rfl, fun _ => hbridge.mp heq, fun _ => rfl⟩
  · rw [if_neg heq]
    refine ⟨Or.inl rfl, fun h01 => absurd h01 (by norm_num), fun hab => ?_⟩
    exact absurd (hbridge.mpr hab) heq

end CurveFieldProofs
