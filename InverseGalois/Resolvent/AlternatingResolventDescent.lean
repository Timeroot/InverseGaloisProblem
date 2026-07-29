/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Resolvent.AlternatingResolvent
import InverseGalois.Resolvent.AlternatingInvariants

/-!
# Descent of the alternating-orbit resolvent (work in progress)

The `Aₙ`-analogue of the descent in `ResolventFamily` (`fullResolventProduct_isSymmetric` →
`exists_esymm_lift_rat` → `fullResolvent_identity`).  We show that every coefficient of the
`Aₙ`-orbit resolvent is `Aₙ`-invariant (`altResolventProduct_coeff_alternating_invariant`) and,
using the fundamental theorem of `Aₙ`-invariants
(`AlternatingInvariants.exists_symm_add_vander_mul_symm`, invariants `= ℚ[e][δ]`), that each
coefficient decomposes as `s + δ · t` with `s, t` symmetric
(`altResolventProduct_coeff_symm_add_vander_mul_symm`).  After the fundamental theorem of
symmetric polynomials this expresses the coefficients as polynomials in the elementary symmetric
functions (the coefficients of the base polynomial) and the Vandermonde `δ = √disc`, giving the
descent of the orbit resolvent to `ℚ(T)[δ]`.
-/

open Polynomial MvPolynomial

noncomputable section

namespace AlternatingResolvent

open ResolventFamily

/-- **`Aₙ`-invariance of the orbit-resolvent coefficients.**

Over `MvPolynomial (Fin n) ℚ` with generic roots `Xᵢ`, every coefficient of the `Aₙ`-orbit
resolvent `altResolventProduct n X` is invariant under renaming the variables by any
`e ∈ Aₙ`: renaming reindexes the `Aₙ`-orbit factors bijectively via `σ ↦ e·σ` (which preserves
`Aₙ` since `e ∈ Aₙ`).  This is the `Aₙ`-analogue of
`ResolventFamily.fullResolventProduct_isSymmetric`. -/
theorem altResolventProduct_coeff_alternating_invariant (n k : ℕ) (e : Equiv.Perm (Fin n))
    (he : e ∈ alternatingGroup (Fin n)) :
    MvPolynomial.rename e
        ((altResolventProduct n (fun i ↦ (X i : MvPolynomial (Fin n) ℚ))).coeff k)
      = (altResolventProduct n (fun i ↦ (X i : MvPolynomial (Fin n) ℚ))).coeff k := by
  convert congr_arg (fun p ↦ Polynomial.coeff p k)
    (show (altResolventProduct n fun i ↦ rename e (X i))
      = altResolventProduct n fun i ↦ X i from ?_) using 1
  · convert congr_arg (fun p : Polynomial (MvPolynomial (Fin n) ℚ) ↦ p.coeff k)
      (altResolventProduct_map (rename e).toRingHom n fun i ↦ X i)
      using 1
    simp [Polynomial.coeff_map]
  · apply Finset.prod_bij (fun σ _ ↦ (⟨e, he⟩ : alternatingGroup (Fin n)) * σ)
    · exact fun _ _ ↦ Finset.mem_univ _
    · exact fun a _ b _ hab ↦ mul_left_cancel hab
    · exact fun b _ ↦ ⟨(⟨e, he⟩ : alternatingGroup (Fin n))⁻¹ * b, Finset.mem_univ _, by group⟩
    · intro σ _
      simp only [genForm, rename_X, Subgroup.coe_mul, Equiv.Perm.mul_apply]

/-- **Descent of an orbit-resolvent coefficient to `ℚ[e][δ]`.**

Combining the `Aₙ`-invariance of the coefficients with the fundamental theorem of `Aₙ`-invariants
(`AlternatingInvariants.exists_symm_add_vander_mul_symm`), every coefficient of the `Aₙ`-orbit
resolvent is `s + δ · t` with `s, t` symmetric polynomials in the roots (`δ` the Vandermonde, a
square root of the discriminant).  This is the algebraic heart of the descent of the orbit
resolvent to `ℚ(T)[δ]`. -/
theorem altResolventProduct_coeff_symm_add_vander_mul_symm (n k : ℕ) (hn : 2 ≤ n) :
    ∃ s t : MvPolynomial (Fin n) ℚ, s.IsSymmetric ∧ t.IsSymmetric ∧
      (altResolventProduct n (fun i ↦ (X i : MvPolynomial (Fin n) ℚ))).coeff k
        = s + AlternatingInvariants.vander n * t := by
  exact AlternatingInvariants.exists_symm_add_vander_mul_symm hn
    (altResolventProduct_coeff_alternating_invariant n k)

end AlternatingResolvent

end
