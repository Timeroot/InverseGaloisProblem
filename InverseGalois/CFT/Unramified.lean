import Mathlib

/-!
# `ℚ` admits no unramified extension

The rational field has no extension that is unramified at every finite prime. The proof is
Minkowski's: an everywhere unramified extension has different ideal `⊤`, hence discriminant of
absolute value `1`, while every number field of degree greater than one has discriminant of
absolute value greater than `2`.

## Main results

* `NumberField.differentIdeal_eq_top_of_isUnramifiedAt`: an extension of `ℤ` unramified at every
  prime has trivial different ideal.
* `NumberField.finrank_eq_one_of_isUnramifiedAt`: a number field unramified at every finite prime
  is `ℚ` itself.
* `NumberField.exists_isPrime_not_isUnramifiedAt`: equivalently, every number field of degree
  greater than one is ramified at some finite prime.

This is the input to the deduction of the Kronecker–Weber theorem from its local form: an abelian
extension of `ℚ` becomes unramified everywhere after adjoining enough roots of unity, so it is
absorbed by the cyclotomic field.
-/

open scoped NumberField

namespace NumberField

variable (L : Type*) [Field L] [NumberField L]

/-- An extension of `ℤ` that is unramified at every prime of the upper ring has trivial different
ideal. -/
theorem differentIdeal_eq_top_of_isUnramifiedAt
    (h : ∀ P : Ideal (𝓞 L), ∀ _ : P.IsPrime, Algebra.IsUnramifiedAt ℤ P) :
    differentIdeal ℤ (𝓞 L) = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hne
  haveI : P.IsPrime := hPmax.isPrime
  exact (not_dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 L) (P := P)).mpr (h P inferInstance)
    (Ideal.dvd_iff_le.mpr hPle)

/-- **Minkowski's theorem**: a number field unramified at every finite prime equals `ℚ`. -/
theorem finrank_eq_one_of_isUnramifiedAt
    (h : ∀ P : Ideal (𝓞 L), ∀ _ : P.IsPrime, Algebra.IsUnramifiedAt ℤ P) :
    Module.finrank ℚ L = 1 := by
  by_contra hne
  have hlt : 1 < Module.finrank ℚ L :=
    lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne') (Ne.symm hne)
  have hdiscr : (discr L).natAbs = 1 := by
    have := absNorm_differentIdeal L (𝓞 L)
    rw [differentIdeal_eq_top_of_isUnramifiedAt L h] at this
    simpa using this.symm
  have h2 : (2 : ℤ) < |discr L| := abs_discr_gt_two hlt
  rw [Int.abs_eq_natAbs, hdiscr] at h2
  norm_num at h2

/-- Every number field of degree greater than one is ramified at some finite prime. -/
theorem exists_isPrime_not_isUnramifiedAt (h : 1 < Module.finrank ℚ L) :
    ∃ P : Ideal (𝓞 L), ∃ _ : P.IsPrime, ¬ Algebra.IsUnramifiedAt ℤ P := by
  by_contra hcon
  push_neg at hcon
  exact absurd (finrank_eq_one_of_isUnramifiedAt L fun P hP => hcon P hP) h.ne'

end NumberField
