/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitFiltration

/-!
# The trace of an integral element is integral

A finite group acting faithfully on a field makes the field a Galois extension of the subfield it
fixes, and the automorphisms over that subfield are exactly the elements of the group.  If the
group acts by isometries then so does every automorphism over the fixed field, and the trace of an
element of the valuation ring, being the sum of its conjugates, again lies in the valuation ring.
This is what makes the coefficients of an element of the valuation ring with respect to the dual of
a basis integral.

## Main definitions

* `InverseGalois.CFT.fixedInt`: the elements of the fixed field lying in the valuation ring.

## Main results

* `InverseGalois.CFT.valued_algEquiv`: **an automorphism over the fixed field preserves the
  valuation.**
* `InverseGalois.CFT.trace_mem_fixedInt`: **the trace of an element of the valuation ring is an
  integral element of the fixed field.**

## Tags

valued field, fixed field, trace, valuation ring
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {G A : Type*} [Group G] [Finite G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  [FaithfulSMul G A]

/-! ### The integers of the fixed field -/

variable (G A) in
/-- **The elements of the fixed field lying in the valuation ring.** -/
def fixedInt : AddSubgroup ↥(FixedPoints.subfield G A) :=
  (valAddSubgroup A 0).comap ((algebraMap ↥(FixedPoints.subfield G A) A).toAddMonoidHom)

omit [Finite G] [FaithfulSMul G A] in
@[simp]
theorem mem_fixedInt {a : ↥(FixedPoints.subfield G A)} :
    a ∈ fixedInt G A ↔ Valued.v (algebraMap ↥(FixedPoints.subfield G A) A a) ≤ 1 := by
  rw [fixedInt, AddSubgroup.mem_comap, mem_valAddSubgroup]
  simp

omit [Finite G] [FaithfulSMul G A] in
/-- An integral element of the fixed field lies in the valuation ring. -/
theorem algebraMap_mem_valAddSubgroup {a : ↥(FixedPoints.subfield G A)} (ha : a ∈ fixedInt G A) :
    algebraMap ↥(FixedPoints.subfield G A) A a ∈ valAddSubgroup A 0 := by
  rw [mem_valAddSubgroup]
  simpa using mem_fixedInt.mp ha

/-! ### Isometry of the automorphisms over the fixed field -/

variable (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

include hv

/-- **An automorphism over the fixed field preserves the valuation**, because every such
automorphism comes from an element of the group. -/
theorem valued_algEquiv (σ : A ≃ₐ[↥(FixedPoints.subfield G A)] A) (x : A) :
    Valued.v (σ x) = Valued.v x := by
  obtain ⟨g, rfl⟩ := (FixedPoints.toAlgAut_bijective G A).surjective σ
  exact hv g x

/-- An automorphism over the fixed field preserves the valuation ring. -/
theorem algEquiv_mem_valAddSubgroup (σ : A ≃ₐ[↥(FixedPoints.subfield G A)] A) {x : A}
    (hx : x ∈ valAddSubgroup A 0) : σ x ∈ valAddSubgroup A 0 := by
  rw [mem_valAddSubgroup, valued_algEquiv hv σ x]
  exact hx

/-! ### Integrality of the trace -/

/-- **The trace of an element of the valuation ring is an integral element of the fixed field**: it
is the sum of the conjugates of the element, and each conjugate has the same valuation. -/
theorem trace_mem_fixedInt {x : A} (hx : Valued.v x ≤ 1) :
    Algebra.trace ↥(FixedPoints.subfield G A) A x ∈ fixedInt G A := by
  rw [mem_fixedInt, trace_eq_sum_automorphisms]
  have hmem : ∀ σ : A ≃ₐ[↥(FixedPoints.subfield G A)] A, σ x ∈ valAddSubgroup A 0 := by
    intro σ
    refine algEquiv_mem_valAddSubgroup hv σ ?_
    rw [mem_valAddSubgroup]
    simpa using hx
  have hsum := AddSubgroup.sum_mem (valAddSubgroup A 0)
    (fun σ (_ : σ ∈ (Finset.univ : Finset (A ≃ₐ[↥(FixedPoints.subfield G A)] A))) => hmem σ)
  rw [mem_valAddSubgroup] at hsum
  simpa using hsum

end InverseGalois.CFT
