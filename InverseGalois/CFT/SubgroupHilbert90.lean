/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Hilbert's theorem ninety for a subgroup of the Galois group

A subgroup of the Galois group of a finite extension is the group of automorphisms over its own
fixed field, by Artin's theorem, and the extension over that fixed field is again finite.  Hilbert's
theorem ninety therefore applies verbatim to the subgroup: a one cocycle defined on the subgroup is
the coboundary of a single unit.

The point of packaging the statement this way is that the cochain is a function on the whole Galois
group, only required to satisfy the cocycle identity on the subgroup, which is exactly the shape in
which the vanishing of the first cohomology enters the inflation restriction sequence.

## Main results

* `InverseGalois.CFT.exists_smul_div_eq_of_mem_subgroup`: **a one cocycle on a subgroup of the
  Galois group of a finite extension is a coboundary.**

## Tags

Hilbert ninety, Galois group, subgroup, fixed field, one cocycle, coboundary
-/

namespace InverseGalois.CFT

open IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]

/-- **A one cocycle on a subgroup of the Galois group of a finite extension is a coboundary.**  By
Artin's theorem the subgroup is the whole group of automorphisms over its fixed field, over which
the extension is still finite, so Hilbert's theorem ninety applies. -/
theorem exists_smul_div_eq_of_mem_subgroup (N : Subgroup (K ≃ₐ[k] K))
    {f : (K ≃ₐ[k] K) → Kˣ} (hf : ∀ x ∈ N, ∀ y ∈ N, f (x * y) = x • f y * f x) :
    ∃ t : Kˣ, ∀ x ∈ N, x • t / t = f x := by
  have hfix : fixingSubgroup (fixedField N) = N := fixingSubgroup_fixedField N
  have hmem : ∀ φ : K ≃ₐ[↥(fixedField N)] K, φ.restrictScalars k ∈ N := by
    intro φ
    have h : φ.restrictScalars k ∈ fixingSubgroup (fixedField N) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun y hy => φ.commutes ⟨y, hy⟩
    rwa [hfix] at h
  haveI : FiniteDimensional ↥(fixedField N) K := FiniteDimensional.right k _ K
  have hcoc : groupCohomology.IsMulCocycle₁
      (fun φ : K ≃ₐ[↥(fixedField N)] K => f (φ.restrictScalars k)) := by
    intro φ ψ
    have hmul : (φ * ψ).restrictScalars k = φ.restrictScalars k * ψ.restrictScalars k :=
      AlgEquiv.ext fun _ => rfl
    show f ((φ * ψ).restrictScalars k) = φ • f (ψ.restrictScalars k) * f (φ.restrictScalars k)
    rw [hmul, hf _ (hmem φ) _ (hmem ψ)]
    congr 1
  obtain ⟨t, ht0⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hcoc
  replace ht0 : ∀ φ : K ≃ₐ[↥(fixedField N)] K, φ • t / t = f (φ.restrictScalars k) := ht0
  refine ⟨t, fun x hx => ?_⟩
  have hx' : x ∈ fixingSubgroup (fixedField N) := by rw [hfix]; exact hx
  have h := ht0 (fixingSubgroupEquiv (fixedField N) ⟨x, hx'⟩)
  rw [show (fixingSubgroupEquiv (fixedField N) ⟨x, hx'⟩ :
      K ≃ₐ[↥(fixedField N)] K).restrictScalars k = x from AlgEquiv.ext fun _ => rfl] at h
  rw [← h]
  congr 1

end InverseGalois.CFT
