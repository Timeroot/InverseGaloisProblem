/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Subspaces of a finite product of copies of a field are cut out by coefficient vectors

A linear form on a finite product `ι → K` of copies of a field is the pairing with a vector of
coefficients, obtained by evaluating the form at the standard basis.  A subspace being the
annihilator of its annihilator, a vector lies in a subspace as soon as it is killed by every
coefficient vector killing the subspace.  This is the shape in which the duality is used: the
coefficient vectors are the data of an arithmetic construction, and membership in the span of a
family of vectors is what has to be decided.

## Main results

* `InverseGalois.CFT.exists_forall_eq_sum_mul`: a linear form on a finite product of copies of a
  field is the pairing with a vector of coefficients.
* `InverseGalois.CFT.mem_of_forall_dualCoeff`: **a vector killed by every coefficient vector
  killing a subspace lies in that subspace.**

## Tags

dual space, annihilator, linear form, finite product
-/

namespace InverseGalois.CFT

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- A linear form on a finite product of copies of a field is the pairing with the vector of its
values at the standard basis. -/
theorem exists_forall_eq_sum_mul (φ : Module.Dual K (ι → K)) :
    ∃ a : ι → K, ∀ x : ι → K, φ x = ∑ i, x i * a i :=
  ⟨fun i => φ (Pi.single i 1), fun x => by
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]⟩

/-- **A vector killed by every coefficient vector killing a subspace lies in that subspace.** -/
theorem mem_of_forall_dualCoeff (V : Submodule K (ι → K)) (t : ι → K)
    (h : ∀ a : ι → K, (∀ w ∈ V, ∑ i, w i * a i = 0) → ∑ i, t i * a i = 0) : t ∈ V := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff V t]
  intro φ hφ
  obtain ⟨a, ha⟩ := exists_forall_eq_sum_mul φ
  rw [Submodule.mem_dualAnnihilator] at hφ
  rw [ha t]
  exact h a fun w hw => by rw [← ha w]; exact hφ w hw

end InverseGalois.CFT
