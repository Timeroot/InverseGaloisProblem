/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.IntegralModel

/-!
# Integral Model Construction via scaleRoots

This file constructs the integral model for a monic irreducible bivariate polynomial
`f ∈ ℚ[T][X]` using Mathlib's `Polynomial.scaleRoots`.

## Main Result

`integral_model_construction`: For a monic irreducible `f ∈ ℚ[T][X]`, there exists
a monic irreducible `F ∈ ℤ[T][X]` of the same degree with a factor correspondence.

1. Use `exists_common_denominator` to get `D > 0` clearing denominators.
2. Form `f.scaleRoots (C (D : ℚ))`, which is monic in `ℚ[T][X]` and has integral coefficients.
3. Lift to `F ∈ ℤ[T][X]`.
4. Show `F` is irreducible via Gauss's lemma.
5. Establish factor correspondence using `scaleRoots_dvd` and Gauss's lemma for monic ℤ-polys. -/

open Polynomial

noncomputable section

/-!
## Helper 1: scaleRoots of monic polynomial has integral coefficients
-/

/-
Each coefficient of `f.scaleRoots(C D)` is in the image of `ℤ[T] → ℚ[T]`,
when `D` clears denominators of `f`'s coefficients.
-/
lemma scaleRoots_integral_coeffs
    (f : Polynomial (Polynomial ℚ)) (hf_monic : f.Monic) (D : ℕ) (_hD : 0 < D)
    (hD_clears : ∀ i, ∃ b : Polynomial ℤ,
      (D : ℚ) • f.coeff i = b.map (Int.castRingHom ℚ)) :
    ∀ i, ∃ b : Polynomial ℤ,
      (f.scaleRoots (Polynomial.C (D : ℚ))).coeff i =
        b.map (Int.castRingHom ℚ) := by
  intro i
  by_cases hi : i > f.natDegree
  · rw [coeff_scaleRoots, coeff_eq_zero_of_natDegree_lt hi]
    exact ⟨0, by norm_num⟩
  · by_cases hi' : i < f.natDegree
    · obtain ⟨b, hb⟩ := hD_clears i
      use C (D ^ (f.natDegree - i - 1) : ℤ) * b
      simp_all [coeff_scaleRoots, Polynomial.map_mul, Polynomial.map_pow]
      rw [← hb]
      ring_nf
      rw [← Nat.sub_add_cancel (Nat.sub_pos_of_lt hi'), pow_succ, mul_comm]
      norm_num [mul_assoc, mul_comm, mul_left_comm]
      norm_num [Algebra.smul_def]
    · simp_all [le_antisymm (le_of_not_gt hi) (le_of_not_gt hi'), coeff_scaleRoots]
      exact ⟨1, by norm_num⟩

/-!
## Helper 2: Lift integral polynomial to ℤ[T][X]
-/

/-
A polynomial in `ℚ[T][X]` whose coefficients are all in the image of `ℤ[T] → ℚ[T]`
can be lifted to `ℤ[T][X]`.
-/
lemma lift_integral_poly (g : Polynomial (Polynomial ℚ))
    (hg : ∀ i, ∃ b : Polynomial ℤ, g.coeff i = b.map (Int.castRingHom ℚ)) :
    ∃ F : Polynomial (Polynomial ℤ),
      F.map (mapRingHom (Int.castRingHom ℚ)) = g := by
  refine ⟨∑ i ∈ g.support, monomial i (Classical.choose (hg i)), ext fun i ↦ ?_⟩
  simp [coeff_monomial]
  split_ifs with hi
  · simp [hi]
  · rw [← Classical.choose_spec (hg i)]

/-!
## Helper 3: scaleRoots by a unit preserves irreducibility
-/

/- -/
set_option maxHeartbeats 400000 in
lemma scaleRoots_unit_irreducible
    {R : Type*} [CommRing R] [IsDomain R]
    (f : Polynomial R) (c : R) (hc : IsUnit c)
    (hf : Irreducible f) : Irreducible (f.scaleRoots c) := by
  have h_scale_dvd : ∀ p : R[X], p ∣ f.scaleRoots c → ∃ q : R[X], q ∣ f ∧ p = q.scaleRoots c := by
    intro p hp
    obtain ⟨q, hq⟩ : ∃ q : R[X], p = q.scaleRoots c := by
      use p.scaleRoots (hc.unit.inv)
      ext
      simp [coeff_scaleRoots, mul_assoc, ← mul_pow]
    simp_all [scaleRoots_dvd_iff]
    exact ⟨q, hp, rfl⟩
  have h_scale_surjective : ∀ p q : R[X], f.scaleRoots c = p * q → (IsUnit p ∨ IsUnit q) := by
    intro p q hpq
    obtain ⟨r, hr⟩ := h_scale_dvd p (dvd_of_mul_right_eq _ hpq.symm)
    obtain ⟨s, hs⟩ := h_scale_dvd q (dvd_of_mul_left_eq _ hpq.symm)
    have h_inj {p q : R[X]} (hpq : p.scaleRoots c = q.scaleRoots c) : p = q := by
      refine ext fun i ↦ ?_
      have h_coeff_eq : p.coeff i * c ^ (p.natDegree - i) = q.coeff i * c ^ (q.natDegree - i) := by
        convert congr_arg (fun p ↦ p.coeff i) hpq using 1 <;> simp [coeff_scaleRoots]
      apply_fun natDegree at hpq
      rw [natDegree_scaleRoots, natDegree_scaleRoots] at hpq
      aesop
    have h_div : r * s = f := by
      apply h_inj
      grind only [mul_scaleRoots_of_noZeroDivisors]
    clear h_inj
    rcases hf.2 h_div.symm with (⟨u, hu⟩ | ⟨u, hu⟩) <;> simp_all [isUnit_iff]
    · rcases isUnit_iff.mp u.isUnit with ⟨k, hk⟩
      refine Or.inl ⟨k, hk.1, ?_⟩
      simpa [← hu] using congr_arg (fun p ↦ p.scaleRoots c) hk.2
    · rcases isUnit_iff.mp u.isUnit with ⟨k, hk⟩
      aesop
  constructor
  · intro h_unit
    obtain ⟨q, hq⟩ : ∃ q : R[X], f.scaleRoots c * q = 1 := h_unit.exists_right_inv
    have h_deg : f.natDegree = 0 := by
      have := congr_arg natDegree hq
      rw [natDegree_mul'] at this <;> simp_all [natDegree_scaleRoots]
      refine ⟨hf.ne_zero, ?_⟩
      rintro rfl
      simp at hq
    obtain ⟨r, hr⟩ : ∃ r : R, f = C r :=
      ⟨f.coeff 0, eq_C_of_natDegree_eq_zero h_deg⟩
    have h_unit_r : IsUnit r := by
      replace hq := congr_arg (Polynomial.eval 0) hq
      simp_all [Polynomial.eval]
    exact absurd (hr.symm ▸ isUnit_C.mpr h_unit_r) hf.not_isUnit
  · exact h_scale_surjective

/-!
## Helper 4: Gauss's lemma for ℤ[T][X]
-/

/-
A monic polynomial `F ∈ ℤ[T][X]` is irreducible over `ℤ[T]` if and only if
`F` mapped to `ℚ[T][X]` is irreducible over `ℚ[T]`.
-/
lemma gauss_lemma_bivariate (F : Polynomial (Polynomial ℤ)) (hF_monic : F.Monic)
    (hF_irr_frac : Irreducible (F.map (mapRingHom (Int.castRingHom ℚ)))) :
    Irreducible F := by
  contrapose! hF_irr_frac
  by_cases hF : F = 0 <;> by_cases hF' : F = 1
  · aesop
  · aesop
  · aesop
  · obtain ⟨a, b, ha, hb, h⟩ : ∃ a b : Polynomial ℤ[X], F = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
      rw [irreducible_iff] at hF_irr_frac
      by_cases h : IsUnit F <;> simp_all
      rw [isUnit_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp_all [Monic.def]
    simp_all [irreducible_mul_iff]
    constructor <;> intro H <;> simp_all [Monic.def, leadingCoeff_mul]
    · intro H'
      have := degree_eq_zero_of_isUnit H'
      rw [degree_map_eq_of_leadingCoeff_ne_zero] at this <;> simp_all [degree_eq_natDegree]
      · rw [eq_C_of_natDegree_eq_zero this] at h hF_monic
        simp_all [leadingCoeff_C]
        exact h (isUnit_of_dvd_one <| hF_monic ▸ dvd_mul_left _ _)
      · intro H
        simp_all [ext_iff]
        specialize H (natDegree (leadingCoeff b))
        simp_all [coeff_natDegree]
    · intro H'
      have := natDegree_eq_zero_of_isUnit H'
      rw [natDegree_map_of_leadingCoeff_ne_zero] at this <;>
        simp_all [natDegree_eq_zero_iff_degree_le_zero]
      · rw [eq_C_of_degree_le_zero this] at hb hF_monic ha
        simp_all
        exact hb (isUnit_of_dvd_one <| hF_monic ▸ dvd_mul_right _ _)
      · intro H''
        replace hF_monic := congr_arg (Polynomial.map (Int.castRingHom ℚ)) hF_monic
        simp_all [Polynomial.map_mul]

/-!
## Helper 5: Specialization commutes with scaleRoots for monic polynomials
-/

/-
For monic `f ∈ ℚ[T][X]`, specialization at `t` commutes with `scaleRoots`:
`(f.scaleRoots(C D))(t, X) = f(t, X).scaleRoots(D)`.
-/
set_option maxHeartbeats 400000 in
lemma specialize_scaleRoots_comm
    (f : Polynomial (Polynomial ℚ)) (hf_monic : f.Monic)
    (D : ℚ) (t : ℤ) :
    (f.scaleRoots (Polynomial.C D)).map (evalRingHom (t : ℚ)) =
    (f.map (evalRingHom (t : ℚ))).scaleRoots D := by
  ext i
  by_cases hi : i ≤ f.natDegree <;> simp_all [coeff_scaleRoots]

/-!
## Helper 6: Monic lift has matching specializations
-/

/-
If `F` lifts `g` (i.e., `F.map(ℤ→ℚ) = g`), then `F(t).map(ℤ→ℚ) = g(t)`.
-/
lemma lift_specialize_comm
    (F : Polynomial (Polynomial ℤ)) (g : Polynomial (Polynomial ℚ))
    (hFg : F.map (mapRingHom (Int.castRingHom ℚ)) = g) (t : ℤ) :
    (F.map (evalRingHom t)).map (Int.castRingHom ℚ) =
    g.map (evalRingHom (t : ℚ)) := by
  induction F using Polynomial.induction_on' <;> aesop

end
