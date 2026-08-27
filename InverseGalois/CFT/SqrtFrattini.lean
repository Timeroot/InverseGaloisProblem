/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.RestrictLE

/-!
# A square root of a base element descends along a Frattini subextension

An element whose square lies in the base field is moved to at most its own negative by an
automorphism, so the automorphisms fixing it form a subgroup of index at most two.  Such a subgroup
is either everything or a maximal subgroup, and in both cases it contains the Frattini subgroup.
Consequently a square root of a base element is fixed by every automorphism lying in the Frattini
subgroup, and therefore already lies in every intermediate field whose automorphisms exhaust that
subgroup.

## Main results

* `InverseGalois.CFT.frattini_le_stabilizer_of_sq_eq`: **the Frattini subgroup fixes every square
  root of an element of the base field.**
* `InverseGalois.CFT.mem_of_sq_eq_of_ker_le_frattini`: **a square root of an element of the base
  field lying in a Galois extension already lies in a subextension cut out by a subgroup of the
  Frattini subgroup.**

## Tags

Frattini subgroup, square root, Galois correspondence, intermediate field
-/

namespace InverseGalois.CFT

open IntermediateField

/-! ### The Frattini subgroup fixes square roots of the base -/

/-- **The Frattini subgroup fixes every square root of an element of the base field.**  An
automorphism sends such a square root to itself or to its negative, so the automorphisms fixing it
form a subgroup which is either everything or maximal: any automorphism moving the square root
generates the rest of the group over it. -/
theorem frattini_le_stabilizer_of_sq_eq {F E : Type*} [Field F] [Field E] [Algebra F E] {u : E}
    {m : F} (hm : u ^ 2 = algebraMap F E m) :
    frattini Gal(E/F) ≤ MulAction.stabilizer Gal(E/F) u := by
  have hpm : ∀ σ : Gal(E/F), σ • u = u ∨ σ • u = -u := by
    intro σ
    have h : (σ u) ^ 2 = u ^ 2 := by rw [← map_pow, hm, σ.commutes]
    have hfac : (σ u - u) * (σ u + u) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  by_cases htop : MulAction.stabilizer Gal(E/F) u = ⊤
  · rw [htop]
    exact le_top
  refine frattini_le_coatom ⟨htop, fun H hH => ?_⟩
  obtain ⟨σ, hσH, hσK⟩ := SetLike.exists_of_lt hH
  have hσu : σ • u = -u := (hpm σ).resolve_left fun h => hσK (MulAction.mem_stabilizer_iff.mpr h)
  have hσinv : σ⁻¹ • u = -u := by
    have h1 : σ⁻¹ • (σ • u) = u := inv_smul_smul σ u
    rw [hσu, smul_neg] at h1
    exact neg_eq_iff_eq_neg.mp h1
  refine (Subgroup.eq_top_iff' H).mpr fun τ => ?_
  rcases hpm τ with h | h
  · exact hH.le (MulAction.mem_stabilizer_iff.mpr h)
  · have hmem : σ⁻¹ * τ ∈ MulAction.stabilizer Gal(E/F) u :=
      MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, h, smul_neg, hσinv, neg_neg])
    simpa using mul_mem hσH (hH.le hmem)

/-! ### Descent along a Frattini subextension -/

/-- **A square root of an element of the base field lying in a Galois extension already lies in a
subextension cut out by a subgroup of the Frattini subgroup.**  The automorphisms fixing the
subextension pointwise lie in the Frattini subgroup, which fixes the square root, so the square root
lies in the fixed field of those automorphisms, which is the subextension. -/
theorem mem_of_sq_eq_of_ker_le_frattini {F L : Type*} [Field F] [Field L] [Algebra F L]
    {A E : IntermediateField F L} [Normal F ↥A] [FiniteDimensional F ↥E] [IsGalois F ↥E]
    (hAE : A ≤ E) (hfr : (galRestrictLE hAE).ker ≤ frattini Gal(↥E/F)) {u : L} (hu : u ∈ E)
    {m : F} (hm : u ^ 2 = algebraMap F L m) : u ∈ A := by
  have hm' : (⟨u, hu⟩ : ↥E) ^ 2 = algebraMap F ↥E m := by
    refine Subtype.ext ?_
    rw [show ((algebraMap F ↥E m : ↥E) : L) = algebraMap F L m from
      (IsScalarTower.algebraMap_apply F ↥E L m).symm]
    simpa using hm
  have hstab := hfr.trans (frattini_le_stabilizer_of_sq_eq hm')
  have hmem : (⟨u, hu⟩ : ↥E) ∈ IntermediateField.fixedField (galRestrictLE hAE).ker :=
    (IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ =>
      MulAction.mem_stabilizer_iff.mp (hstab hσ)
  rw [fixedField_ker_galRestrictLE hAE] at hmem
  exact (IntermediateField.mem_restrict hAE _).mp hmem

end InverseGalois.CFT
