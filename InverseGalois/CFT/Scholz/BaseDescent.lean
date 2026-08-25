/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CoprimeDescent

/-!
# Descending a solved embedding problem along the base field

A central embedding problem posed over a field `F` may only be solvable after enlarging the base to
a field `k`, because the criterion needs roots of unity that `F` does not contain.  The automorphism
group of a Galois extension `E / F` over `k` is a subgroup of the automorphism group over `F`, of
index the degree of `k` over `F`.  So if that degree is coprime to the order of the kernel, the
group-theoretic descent along a subgroup of coprime index applies and the problem is solved over `F`
after all.

## Main definitions

* `InverseGalois.CFT.galRestrictScalars`: an automorphism over the enlarged base, viewed as an
  automorphism over the original base.

## Main results

* `InverseGalois.CFT.index_range_galRestrictScalars`: **the automorphisms over the enlarged base
  form a subgroup of index the degree of the enlargement.**
* `InverseGalois.CFT.exists_surjective_hom_of_coprime_finrank`: **a central Frattini embedding
  problem solved over the enlarged base is solved over the original base**, provided the degree of
  the enlargement is coprime to the order of the kernel.

## Tags

embedding problem, base change, coprime index, descent, Galois group
-/

namespace InverseGalois.CFT

open Module

variable {F k E : Type*} [Field F] [Field k] [Field E] [Algebra F k] [Algebra k E] [Algebra F E]
  [IsScalarTower F k E]

variable (F) in
/-- **An automorphism of the top field over the enlarged base, viewed as an automorphism over the
original base.** -/
def galRestrictScalars : Gal(E/k) →* Gal(E/F) where
  toFun σ := σ.restrictScalars F
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem galRestrictScalars_apply (σ : Gal(E/k)) (x : E) : galRestrictScalars F σ x = σ x := rfl

theorem galRestrictScalars_injective :
    Function.Injective (galRestrictScalars F : Gal(E/k) →* Gal(E/F)) :=
  fun _ _ h => AlgEquiv.restrictScalars_injective F h

/-- The automorphisms over the enlarged base, as a subgroup of the automorphisms over the original
base. -/
noncomputable def galOverEquivRange :
    Gal(E/k) ≃* ↥(galRestrictScalars F : Gal(E/k) →* Gal(E/F)).range :=
  MonoidHom.ofInjective (galRestrictScalars_injective (F := F) (k := k) (E := E))

@[simp]
theorem coe_galOverEquivRange (σ : Gal(E/k)) :
    ((galOverEquivRange (F := F) (k := k) (E := E) σ :
        ↥(galRestrictScalars F : Gal(E/k) →* Gal(E/F)).range) : Gal(E/F))
      = galRestrictScalars F σ := rfl

/-- **The automorphisms over the enlarged base form a subgroup of index the degree of the
enlargement.**  Its order is the degree of the top field over the enlarged base, and the two degrees
multiply to the order of the whole group. -/
theorem index_range_galRestrictScalars [FiniteDimensional F E] [IsGalois F E] :
    (galRestrictScalars F : Gal(E/k) →* Gal(E/F)).range.index = finrank F k := by
  haveI : FiniteDimensional F k := FiniteDimensional.left F k E
  haveI : FiniteDimensional k E := FiniteDimensional.right F k E
  haveI : IsGalois k E := IsGalois.tower_top_of_isGalois F k E
  have hcard : Nat.card ↥(galRestrictScalars F : Gal(E/k) →* Gal(E/F)).range
      = finrank k E := by
    rw [← IsGalois.card_aut_eq_finrank k E]
    exact Nat.card_congr (galOverEquivRange (F := F) (k := k) (E := E)).symm.toEquiv
  have h := Subgroup.index_mul_card (galRestrictScalars F : Gal(E/k) →* Gal(E/F)).range
  rw [hcard, IsGalois.card_aut_eq_finrank F E, ← finrank_mul_finrank F k E] at h
  exact Nat.eq_of_mul_eq_mul_right finrank_pos h

set_option maxHeartbeats 400000 in
/-- **A central Frattini embedding problem solved over the enlarged base is solved over the original
base**, provided the degree of the enlargement is coprime to the order of the kernel.  The
automorphisms over the enlarged base are a subgroup of that index, so the group-theoretic descent
applies verbatim. -/
theorem exists_surjective_hom_of_coprime_finrank [FiniteDimensional F E] [IsGalois F E]
    {G H : Type*} [Group G] [Group H] [Finite G] {f : G →* H} (hf : Function.Surjective f)
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcop : Nat.Coprime (finrank F k) (Nat.card ↥f.ker))
    {π : Gal(E/F) →* H} (hπ : Function.Surjective π) (s : Gal(E/k) →* G)
    (hs : ∀ u : Gal(E/k), f (s u) = π (galRestrictScalars F u)) :
    ∃ ψ : Gal(E/F) →* G, Function.Surjective ψ ∧ ∀ x, f (ψ x) = π x := by
  refine exists_surjective_hom_comp_eq_of_coprime_index hf hZ hfr hπ
    (U := (galRestrictScalars F : Gal(E/k) →* Gal(E/F)).range)
    (by rwa [index_range_galRestrictScalars])
    (s.comp (galOverEquivRange (F := F) (k := k) (E := E)).symm.toMonoidHom) fun u => ?_
  have hu : galRestrictScalars F
      ((galOverEquivRange (F := F) (k := k) (E := E)).symm u) = (u : Gal(E/F)) := by
    rw [← coe_galOverEquivRange, MulEquiv.apply_symm_apply]
  simpa [hu] using hs ((galOverEquivRange (F := F) (k := k) (E := E)).symm u)

end InverseGalois.CFT
