/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.RadicandLevel

/-!
# Square classes at a dyadic place of residue degree one

At a place of a number field lying over two with ramification index and residue degree both one the
local field is the field of two-adic numbers, whose square classes are represented by the eight
units `±1, ±2, ±5, ±10`.  Only the congruence which makes a radical unramified is needed here, and
it is the statement that the four rational representatives `±1, ±2` already exhaust the square
classes of the two-adic units modulo the squares of the classes congruent to one modulo four.

The proof is a valuation computation which needs nothing beyond the two properties singled out
below: that two is a uniformizer, and that the residue field has two elements.  Any nonzero element
is a unit times a power of two, so multiplying by one or two makes the exponent even; and for a unit
`u` exactly one of `(u + 1) / 2` and `(u - 1) / 2` lies in the place, because their difference is
one and the residue field has no room for two distinct nonzero residues, so that one of `u` and
`-u` is congruent to one modulo the square of the uniformizer.

## Main results

* `InverseGalois.CFT.exists_sign_valuation_sub_one_le`: **one of a unit and its negative is
  congruent to one modulo the square of two** at a dyadic place with residue field of order two.
* `InverseGalois.CFT.exists_isCongrPow_mul_intCast`: **every nonzero element becomes, after
  multiplication by one of `±1, ±2`, a unit congruent to one modulo four times a square.**

## Tags

valuation, dyadic place, square class, uniformizer, residue field, Kummer theory
-/

namespace InverseGalois.CFT

variable {Z Γ : Type*} [Field Z] [LinearOrderedCommGroupWithZero Γ] {v : Valuation Z Γ}

/-! ### The sign adjustment -/

section Sign

variable (hv2 : v 2 < 1) (h20 : (2 : Z) ≠ 0)
  (h2u : ∀ x : Z, v x < 1 → v x ≤ v 2)
  (hres : ∀ x : Z, v x ≤ 1 → v x < 1 ∨ v (x - 1) < 1)

include hv2 h20 h2u hres

/-- **One of a unit and its negative is congruent to one modulo the square of two.**  The residue
field has two elements, so a unit is congruent to one modulo the place and both `u + 1` and `u - 1`
lie in it; dividing by the uniformizer two leaves two elements differing by one, of which exactly
one lies in the place again. -/
theorem exists_sign_valuation_sub_one_le {u : Z} (hu : v u = 1) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ v ((s : Z) * u) = 1 ∧ v ((s : Z) * u - 1) ≤ v 2 ^ 2 := by
  have hv20 : (0 : Γ) < v 2 := lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff v).mpr h20))
  -- a unit is congruent to one modulo the place, so both neighbours lie in the place
  have hsub : v (u - 1) < 1 := by
    rcases hres u hu.le with h | h
    · exact absurd hu h.ne
    · exact h
  have hadd : v (u + 1) < 1 := by
    have hrw : u + 1 = u - 1 + 2 := by ring
    rw [hrw]
    exact lt_of_le_of_lt (v.map_add _ _) (max_lt hsub hv2)
  -- the two halves differ by one
  have ht1 : v ((u - 1) / 2) ≤ 1 := by
    rw [map_div₀, div_le_one₀ hv20]
    exact h2u _ hsub
  rcases hres _ ht1 with h | h
  · -- the lower half lies in the place: `u` itself is congruent to one
    refine ⟨1, Or.inl rfl, by simpa using hu, ?_⟩
    have hfac : u - 1 = 2 * ((u - 1) / 2) := by field_simp
    have hval : v (u - 1) = v 2 * v ((u - 1) / 2) := by
      conv_lhs => rw [hfac]
      rw [map_mul]
    rw [Int.cast_one, one_mul, hval, sq]
    exact mul_le_mul_right (h2u _ h) _
  · -- the upper half lies in the place: `-u` is congruent to one
    have hup : v ((u + 1) / 2) < 1 := by
      have hrw : (u + 1) / 2 = ((u - 1) / 2 - 1) + 2 := by
        field_simp
        ring
      rw [hrw]
      exact lt_of_le_of_lt (v.map_add _ _) (max_lt h hv2)
    refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · rw [Int.cast_neg, Int.cast_one, neg_one_mul, Valuation.map_neg]
      exact hu
    · have hfac : u + 1 = 2 * ((u + 1) / 2) := by field_simp
      have hval : v (u + 1) = v 2 * v ((u + 1) / 2) := by
        conv_lhs => rw [hfac]
        rw [map_mul]
      have hrw : ((-1 : ℤ) : Z) * u - 1 = -(u + 1) := by push_cast; ring
      rw [hrw, Valuation.map_neg, hval, sq]
      exact mul_le_mul_right (h2u _ hup) _

end Sign

/-! ### The four rational square classes -/

section Class

variable (hv2 : v 2 < 1) (h20 : (2 : Z) ≠ 0)
  (h2u : ∀ x : Z, v x < 1 → v x ≤ v 2)
  (hunif : ∀ x : Z, x ≠ 0 → ∃ (m : ℤ) (u : Z), v u = 1 ∧ x = u * 2 ^ m)
  (hres : ∀ x : Z, v x ≤ 1 → v x < 1 ∨ v (x - 1) < 1)

include hv2 h20 h2u hunif hres

/-- **Every nonzero element becomes, after multiplication by one of `1, -1, 2, -2`, a unit
congruent to one modulo four times a square.**  Multiplying by one or two makes the exponent of the
uniformizer even, so that the power of two is a square, and multiplying by a sign then makes the
remaining unit congruent to one modulo the square of the uniformizer. -/
theorem exists_isCongrPow_mul_intCast {β : Z} (hβ : β ≠ 0) :
    ∃ d : ℤ, (d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2) ∧ IsCongrPow 2 v (-2) (β * (d : Z)) := by
  obtain ⟨m, u, hu, hβm⟩ := hunif β hβ
  obtain ⟨s, hs, hsu, hsub⟩ := exists_sign_valuation_sub_one_le hv2 h20 h2u hres hu
  -- absorb the power of the uniformizer into a square at the cost of a factor of two
  have hsq : ∃ (n : ℤ) (γ : Z), (n = 1 ∨ n = 2) ∧ γ ≠ 0 ∧ (2 : Z) ^ m * (n : Z) = γ ^ 2 := by
    rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨1, (2 : Z) ^ j, Or.inl rfl, zpow_ne_zero _ h20, ?_⟩
      rw [hj, zpow_add₀ h20]
      push_cast
      ring
    · refine ⟨2, (2 : Z) ^ j * 2, Or.inr rfl, mul_ne_zero (zpow_ne_zero _ h20) h20, ?_⟩
      rw [hj, two_mul, zpow_add₀ h20, zpow_add₀ h20, zpow_one]
      push_cast
      ring
  obtain ⟨n, γ, hn, hγ, hγsq⟩ := hsq
  refine ⟨s * n, ?_, (s : Z) * u, γ, hγ, hsu, ?_, ?_⟩
  · rcases hs with rfl | rfl <;> rcases hn with rfl | rfl <;> norm_num
  · rw [Valuation.map_neg]
    exact hsub
  · rw [← hγsq, hβm]
    push_cast
    ring

end Class

end InverseGalois.CFT
