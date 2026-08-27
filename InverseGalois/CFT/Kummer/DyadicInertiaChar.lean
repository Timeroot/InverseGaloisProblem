/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.DyadicPlace
import InverseGalois.CFT.Kummer.InertiaBound

/-!
# A square root agrees with a rational one on the inertia group at two

Let `M / Z` be an extension of number fields, let `W` be a place of `M` whose place below is a
dyadic place of `Z` with ramification index and residue degree both one, and let `y` be a square
root in `M` of an element of `Z`.  If `M` contains the eighth roots of unity then there is a square
root `δ` of one of `1, -1, 2, -2` for which `y` and `δ` are moved in exactly the same way by the
inertia group at `W`.

The two square roots therefore determine the same quadratic character of that inertia group, and
the character of `y` can be corrected by a character which is ramified only at two.  This is the
step of the Scholz–Reichardt construction at which the prime two behaves differently from an odd
prime: a radicand at an odd prime can be corrected inside the base field, whereas at two the
correction must be allowed to use the four rational square classes.

The proof multiplies the radicand by the rational number supplied by the square class computation,
so that it becomes a unit congruent to one modulo four times a square; the radical of such a
radicand is fixed by the inertia group, and that fixing is the required agreement.

## Main results

* `InverseGalois.CFT.exists_sq_intCast_eqOn_inertia`: **a square root over a number field agrees on
  the inertia group at an unramified dyadic place with a square root of one of `1, -1, 2, -2`.**

## Tags

number field, Kummer theory, inertia, dyadic place, square class, quadratic character
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

variable {Z M : Type*} [Field Z] [NumberField Z] [Field M] [NumberField M] [Algebra Z M]

/-- **A square root over a number field agrees on the inertia group at an unramified dyadic place
with a square root of one of `1, -1, 2, -2`.**  Multiplying the radicand by the rational number
which makes it a unit congruent to one modulo four times a square produces a radical fixed by the
inertia group, and the fixed radical is the product of the two square roots. -/
theorem exists_sq_intCast_eqOn_inertia (W : HeightOneSpectrum (𝓞 M))
    [(primeUnder (𝓞 Z) W).asIdeal.LiesOver (Ideal.span {((2 : ℕ) : ℤ)})]
    (he : Ideal.ramificationIdx (algebraMap ℤ (𝓞 Z)) (Ideal.span {((2 : ℕ) : ℤ)})
      (primeUnder (𝓞 Z) W).asIdeal = 1)
    (hf : (Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg (primeUnder (𝓞 Z) W).asIdeal = 1)
    (hi : ∃ i : M, i ^ 2 = -1) (hr : ∃ r : M, r ^ 2 = 2)
    {y : M} (hy : y ≠ 0) {β : Z} (hβ : y ^ 2 = algebraMap Z M β) :
    ∃ δ : M, δ ≠ 0 ∧ (δ ^ 2 = 1 ∨ δ ^ 2 = -1 ∨ δ ^ 2 = 2 ∨ δ ^ 2 = -2) ∧
      ∀ σ : Gal(M/Z), σ ∈ Ideal.inertia Gal(M/Z) W.asIdeal → σ y * δ = y * σ δ := by
  obtain ⟨i, hi2⟩ := hi
  obtain ⟨r, hr2⟩ := hr
  have hβ0 : β ≠ 0 := by
    intro h
    exact hy (pow_eq_zero_iff two_ne_zero |>.mp (by rw [hβ, h, map_zero]))
  obtain ⟨d, hd, hcp⟩ :=
    exists_isCongrPow_mul_intCast_dyadic (primeUnder (𝓞 Z) W) he hf hβ0
  -- a square root of the rational number provided by the square class computation
  obtain ⟨δ, hδ⟩ : ∃ δ : M, δ ^ 2 = ((d : ℤ) : M) := by
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨1, by norm_num⟩
    · exact ⟨i, by rw [hi2]; norm_num⟩
    · exact ⟨r, by rw [hr2]; norm_num⟩
    · exact ⟨i * r, by rw [mul_pow, hi2, hr2]; norm_num⟩
  have hd0 : ((d : ℤ) : M) ≠ 0 := by
    rcases hd with rfl | rfl | rfl | rfl <;> norm_num
  have hδ0 : δ ≠ 0 := fun h => hd0 (by rw [← hδ, h]; ring)
  refine ⟨δ, hδ0, ?_, ?_⟩
  · rw [hδ]
    rcases hd with rfl | rfl | rfl | rfl
    · exact Or.inl (by norm_num)
    · exact Or.inr (Or.inl (by norm_num))
    · exact Or.inr (Or.inr (Or.inl (by norm_num)))
    · exact Or.inr (Or.inr (Or.inr (by norm_num)))
  · intro σ hσ
    -- the product of the two square roots is a radical of a radicand congruent to one
    have hζ : IsPrimitiveRoot (-1 : Z) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
    have hcp' : IsCongrPow 2 ((primeUnder (𝓞 Z) W).valuation Z) ((-1 : Z) - 1) (β * (d : Z)) := by
      have hrw : (-1 : Z) - 1 = -2 := by norm_num
      rw [hrw]
      exact hcp
    have hα : (y * δ) ^ 2 = algebraMap Z M (β * (d : Z)) := by
      rw [mul_pow, hβ, hδ, map_mul, map_intCast]
    have hfix := eq_of_isCongrPow Nat.prime_two hζ W hcp' hα hσ
    have h1 : σ y * σ δ = y * δ := by rw [← map_mul]; exact hfix
    have h2 : (σ δ) ^ 2 = δ ^ 2 := by rw [← map_pow, hδ, map_intCast]
    have hkey : σ y * δ * δ = y * σ δ * δ := by
      calc σ y * δ * δ = σ y * δ ^ 2 := by ring
        _ = σ y * (σ δ) ^ 2 := by rw [h2]
        _ = σ y * σ δ * σ δ := by ring
        _ = y * δ * σ δ := by rw [h1]
        _ = y * σ δ * δ := by ring
    exact mul_right_cancel₀ hδ0 hkey

end InverseGalois.CFT
