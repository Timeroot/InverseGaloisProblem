/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RationalDeck

/-!
# Branch cycles of a Galois family, read inside the group

The monodromy group of an irreducible complex family carrying a group of root formulas of the
right size is a copy of that group.  Transporting the analytic branch cycles — the monodromy of
the loops around the punctures and around infinity — along that isomorphism produces a tuple of
elements of the group itself.

The two relations of the Riemann existence correspondence come along for free.  The ordered
product of the loops is contractible on the punctured sphere, so the branch cycles multiply to
one; and the loops generate the fundamental group of the punctured plane, so the branch cycles
generate the whole group.

## Main definitions

* `Rigidity.RET.Analytic.RationalDeck.deckBranchCycle` — the branch cycles as elements of the
  group.

## Main results

* `Rigidity.RET.Analytic.RationalDeck.prod_deckBranchCycle` — they multiply to one.
* `Rigidity.RET.Analytic.RationalDeck.closure_range_deckBranchCycle` — they generate the group.
* `Rigidity.RET.Analytic.RationalDeck.exists_branchCycles` — the packaged statement.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ} {G : Type} [Group G]

/-! ### The two monodromy ranges agree -/

/-- The sphere presentation group surjects onto the fundamental group of the punctured plane, so
the two monodromy representations have the same image. -/
theorem range_sphereMonodromy_eq (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) :
    (sphereMonodromy hP hS hz₀).range = (monodromyHom hP hS hz₀).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some y, ?_⟩
    show monodromyHom hP hS hz₀ ((pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some.symm
      ((pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some y)) = _
    rw [MulEquiv.symm_apply_apply]

/-- Every branch cycle lies in the monodromy group. -/
theorem branchCycle_mem_range (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) (i : Fin (S.card + 1)) :
    branchCycle hP hS hz₀ i ∈ (monodromyHom hP hS hz₀).range :=
  range_sphereMonodromy_eq hP hS hz₀ ▸ ⟨PresentedGroup.of i, rfl⟩

/-- The branch cycles, viewed inside the monodromy group. -/
def rangeBranchCycle (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) (i : Fin (S.card + 1)) : ↥(monodromyHom hP hS hz₀).range :=
  ⟨branchCycle hP hS hz₀ i, branchCycle_mem_range hP hS hz₀ i⟩

theorem prod_rangeBranchCycle (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) :
    (List.ofFn (rangeBranchCycle hP hS hz₀)).prod = 1 := by
  refine Subtype.ext ?_
  have h := map_list_prod (Subgroup.subtype (monodromyHom hP hS hz₀).range)
    (List.ofFn (rangeBranchCycle hP hS hz₀))
  rw [List.map_ofFn] at h
  show (Subgroup.subtype (monodromyHom hP hS hz₀).range)
    (List.ofFn (rangeBranchCycle hP hS hz₀)).prod = 1
  rw [h]
  exact prod_branchCycle hP hS hz₀

/-- **The branch cycles generate the monodromy group**, stated inside that group. -/
theorem closure_range_rangeBranchCycle (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) :
    Subgroup.closure (Set.range (rangeBranchCycle hP hS hz₀)) = ⊤ := by
  refine Subgroup.map_injective
    (Subgroup.subtype_injective (monodromyHom hP hS hz₀).range) ?_
  rw [MonoidHom.map_closure, ← Set.range_comp,
    show (Subgroup.subtype (monodromyHom hP hS hz₀).range) ∘ rangeBranchCycle hP hS hz₀
      = branchCycle hP hS hz₀ from rfl,
    ← range_sphereMonodromy hP hS hz₀, range_sphereMonodromy_eq hP hS hz₀,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

namespace RationalDeck

/-- **The branch cycles of the family, as elements of the group.** -/
def deckBranchCycle (D : RationalDeck P S G) [Finite G] (hP : P.Monic) (hdeg : 0 < P.natDegree)
    (hirr : Irreducible P)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) (i : Fin (S.card + 1)) : G :=
  D.monodromyEquiv hP hdeg hirr hS hz₀ hcard e₀ (rangeBranchCycle hP hS hz₀ i)

/-- **The branch cycles multiply to one in the group.** -/
theorem prod_deckBranchCycle (D : RationalDeck P S G) [Finite G] (hP : P.Monic)
    (hdeg : 0 < P.natDegree) (hirr : Irreducible P) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    (List.ofFn (D.deckBranchCycle hP hdeg hirr hS hz₀ hcard e₀)).prod = 1 := by
  have hmap : List.ofFn (D.deckBranchCycle hP hdeg hirr hS hz₀ hcard e₀)
      = (List.ofFn (rangeBranchCycle hP hS hz₀)).map
        (D.monodromyEquiv hP hdeg hirr hS hz₀ hcard e₀ : _ →* G) := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, ← map_list_prod, prod_rangeBranchCycle hP hS hz₀, map_one]

/-- **The branch cycles generate the group.** -/
theorem closure_range_deckBranchCycle (D : RationalDeck P S G) [Finite G] (hP : P.Monic)
    (hdeg : 0 < P.natDegree) (hirr : Irreducible P) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    Subgroup.closure (Set.range (D.deckBranchCycle hP hdeg hirr hS hz₀ hcard e₀)) = ⊤ := by
  have hrange : Set.range (D.deckBranchCycle hP hdeg hirr hS hz₀ hcard e₀)
      = (D.monodromyEquiv hP hdeg hirr hS hz₀ hcard e₀ : _ →* G) ''
        Set.range (rangeBranchCycle hP hS hz₀) :=
    Set.range_comp _ _
  rw [hrange, ← MonoidHom.map_closure, closure_range_rangeBranchCycle hP hS hz₀,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact (D.monodromyEquiv hP hdeg hirr hS hz₀ hcard e₀).surjective

/-- **An irreducible complex family carrying a group of root formulas of the right size has a
branch-cycle system in that group**: one element for each puncture and one for infinity, with
product one, generating the group. -/
theorem exists_branchCycles (D : RationalDeck P S G) [Finite G] (hP : P.Monic)
    (hdeg : 0 < P.natDegree)
    (hirr : Irreducible P) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) (hcard : Nat.card G = P.natDegree) :
    ∃ g : Fin (S.card + 1) → G, (List.ofFn g).prod = 1 ∧ Subgroup.closure (Set.range g) = ⊤ := by
  have hpos : 0 < Nat.card (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) := by
    rw [card_puncturedFiber hP hS hz₀]; exact hdeg
  obtain ⟨e₀⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨D.deckBranchCycle hP hdeg hirr hS hz₀ hcard e₀,
    D.prod_deckBranchCycle hP hdeg hirr hS hz₀ hcard e₀,
    D.closure_range_deckBranchCycle hP hdeg hirr hS hz₀ hcard e₀⟩

end RationalDeck

end Rigidity.RET.Analytic

end
