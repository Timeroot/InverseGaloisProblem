/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Multiquadratic
import InverseGalois.CFT.SqrtRamification
import InverseGalois.CFT.Global.SquarefreeCRT

/-!
# A square root of an integer congruent to one modulo four never leaves the odd factor

Enlarging a number field by roots of unity of two-power order can create new square roots of
rational numbers, and the question is which ones.  For an integer congruent to `1` modulo `4` the
answer is none: a square root of such an integer in a compositum of a field unramified at `2` with
a field ramified only at `2`, the two meeting in the rationals, already lies in the first factor.

The argument splits the square root between the two factors — the sign character of the square root
is the sum of a character trivial on one factor and a character trivial on the other, and each
summand is realized by a square root of its own — and then compares squarefree parts.  A squarefree
integer becoming a square in a field unramified at `2` is congruent to `1` modulo `4`, and one
becoming a square in a field ramified only at `2` divides `2`.  Multiplying the given integer by
the two squarefree parts produces an integer that is a rational square, hence a perfect square, and
a perfect square is congruent to `0` or `1` modulo `4`; the three squarefree parts `-1`, `2` and
`-2` are excluded by that congruence, so the second factor contributes only a rational number.

## Main results

* `InverseGalois.CFT.mem_of_sq_eq_intCast_of_inf_eq_bot`: **a square root of an integer congruent
  to one modulo four lying in the compositum of a field unramified at two with a field ramified
  only at two, the two meeting in the rationals, lies in the first field.**

## Tags

square root, compositum, ramification, squarefree, cyclotomic field
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-- A square root of a rational integer lying in a subfield is a square root there. -/
theorem sq_eq_intCast_coe {L : Type*} [Field L] [CharZero L] (A : IntermediateField ℚ L) {w : L}
    (hw : w ∈ A) {s : ℤ} (h : w ^ 2 = (s : L)) : (⟨w, hw⟩ : ↥A) ^ 2 = (s : ↥A) := by
  apply Subtype.ext
  push_cast
  exact h

set_option maxHeartbeats 1000000 in
/-- **A square root of an integer congruent to one modulo four lying in the compositum of a field
unramified at two with a field ramified only at two, the two meeting in the rationals, lies in the
first field.**  The square root splits as a product of a square root from each factor; the
squarefree part of the first is congruent to one modulo four and the squarefree part of the second
divides two, and the product of the integer with the two squarefree parts is a perfect square,
which rules out every squarefree part of the second factor except one. -/
theorem mem_of_sq_eq_intCast_of_inf_eq_bot {L : Type*} [Field L] [CharZero L]
    (A B : IntermediateField ℚ L) [NumberField ↥A] [NumberField ↥B]
    [FiniteDimensional ℚ ↥(A ⊔ B)] [IsGalois ℚ ↥(A ⊔ B)] [IsGalois ℚ ↥A] [IsGalois ℚ ↥B]
    (hinf : A ⊓ B = ⊥) (hA2 : 2 ∉ ramifiedSet ↥A) (hB2 : ramifiedSet ↥B ⊆ {2}) {m : ℤ}
    (hm : m % 4 = 1) {x : L} (hx : x ∈ A ⊔ B) (hxm : x ^ 2 = (m : L)) : x ∈ A := by
  classical
  have hinj : Function.Injective (algebraMap ℚ L) := (algebraMap ℚ L).injective
  have hm0 : m ≠ 0 := by omega
  have hmL : ((m : L)) ≠ 0 := Int.cast_ne_zero.mpr hm0
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hxm
    exact hmL hxm.symm
  have hb : x ^ 2 = algebraMap ℚ L ((m : ℚ)) := by rw [hxm, map_intCast]
  obtain ⟨y, hyA, z, hzB, hxyz, ⟨c, hc⟩, ⟨d, hd⟩⟩ :=
    exists_mul_eq_of_sq_mem_sup A B hinf hx hb
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hxyz, zero_mul])
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hxyz, mul_zero])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, pow_eq_zero_iff two_ne_zero] at hc
    exact hy0 hc
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero, pow_eq_zero_iff two_ne_zero] at hd
    exact hz0 hd
  have hcd : ((m : ℚ)) = c * d := by
    refine hinj ?_
    rw [← hb, hxyz, mul_pow, hc, hd, map_mul]
  -- the squarefree parts of the two factors
  obtain ⟨sc, tc, hsc0, hscsf, htc0, hceq⟩ := exists_squarefree_intCast_mul_sq hc0
  obtain ⟨sd, td, hsd0, hsdsf, htd0, hdeq⟩ := exists_squarefree_intCast_mul_sq hd0
  have htcL : algebraMap ℚ L tc ≠ 0 := (map_ne_zero_iff _ hinj).mpr htc0
  have htdL : algebraMap ℚ L td ≠ 0 := (map_ne_zero_iff _ hinj).mpr htd0
  -- the square root of the squarefree part of the first factor lies in the first field
  have hwA : y / algebraMap ℚ L tc ∈ A := div_mem hyA (A.algebraMap_mem tc)
  have hw2 : (y / algebraMap ℚ L tc) ^ 2 = ((sc : ℤ) : L) := by
    rw [div_pow, hc, ← map_pow, ← map_div₀,
      show c / tc ^ 2 = ((sc : ℚ)) from by rw [hceq]; field_simp, map_intCast]
  have hscmod : sc % 4 = 1 :=
    emod_four_eq_one_of_sq_eq_intCast (K := ↥A) hscsf (sq_eq_intCast_coe A hwA hw2) hA2
  -- the square root of the squarefree part of the second factor lies in the second field
  have hvB : z / algebraMap ℚ L td ∈ B := div_mem hzB (B.algebraMap_mem td)
  have hv2 : (z / algebraMap ℚ L td) ^ 2 = ((sd : ℤ) : L) := by
    rw [div_pow, hd, ← map_pow, ← map_div₀,
      show d / td ^ 2 = ((sd : ℚ)) from by rw [hdeq]; field_simp, map_intCast]
  have hsddvd : sd ∣ 2 :=
    dvd_two_of_sq_eq_intCast (K := ↥B) hsdsf (sq_eq_intCast_coe B hvB hv2) hB2
  -- the integer times the two squarefree parts is a perfect square
  have hmcd : ((m : ℚ)) = (sc : ℚ) * tc ^ 2 * ((sd : ℚ) * td ^ 2) := by rw [hcd, ← hceq, ← hdeq]
  have hmr : ((m * sc * sd : ℤ) : ℚ) = ((sc : ℚ) * (sd : ℚ) * tc * td) ^ 2 := by
    push_cast
    linear_combination ((sc : ℚ) * (sd : ℚ)) * hmcd
  obtain ⟨k, hk⟩ := exists_sq_eq_of_sq_eq_ratCast hmr
  have hkk : m * sc * sd = k * k := by rw [hk]; ring
  have hksq : k * k % 4 = 0 ∨ k * k % 4 = 1 := by
    have h := Int.mul_emod k k 4
    have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases h4 with h4 | h4 | h4 | h4 <;> rw [h4] at h <;> omega
  have hmsc : m * sc % 4 = 1 := by
    have h := Int.mul_emod m sc 4
    rw [hm, hscmod] at h
    omega
  -- the squarefree part of the second factor is one
  have hsd1 : sd = 1 := by
    have hnat : sd.natAbs ∣ 2 := by
      have h := Int.natAbs_dvd_natAbs.mpr hsddvd
      simpa using h
    have hle : sd.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num) hnat
    have hcases : sd = 1 ∨ sd = -1 ∨ sd = 2 ∨ sd = -2 := by omega
    rcases hcases with h | h | h | h
    · exact h
    · rw [h] at hkk; omega
    · rw [h] at hkk; omega
    · rw [h] at hkk; omega
  -- so the second factor is rational
  have hzA : z ∈ A := by
    have hd' : d = td ^ 2 := by rw [hdeq, hsd1]; norm_num
    have hz2 : z ^ 2 = (algebraMap ℚ L td) ^ 2 := by rw [hd, hd', map_pow]
    have hfac : (z - algebraMap ℚ L td) * (z + algebraMap ℚ L td) = 0 := by linear_combination hz2
    rcases mul_eq_zero.mp hfac with h | h
    · rw [sub_eq_zero.mp h]
      exact A.algebraMap_mem td
    · rw [eq_neg_of_add_eq_zero_left h]
      exact neg_mem (A.algebraMap_mem td)
  rw [hxyz]
  exact mul_mem hyA hzA

end InverseGalois.CFT
