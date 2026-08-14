/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.DeckCycles
import InverseGalois.Rigidity.RET.Pi1.Topological.MonodromyNat
import InverseGalois.Rigidity.RET.Pi1.Topological.PuncturedSurjective

/-!
# Discarding the parameters at which nothing happens

The group of root formulas attached to a Galois extension of the field of rational functions is
only defined away from the zeros of a denominator, and those zeros are in general many more than
the parameters at which the family actually degenerates.  The branch cycles produced from the
formulas are therefore indexed by a set that is too large.

The extra parameters can be removed.  The root cover is already a covering space over the
complement of the *smaller* set — separability is all that is needed for that — and the inclusion
of the smaller punctured plane's complement induces a surjection of fundamental groups, because
filling in a puncture only kills loops.  Monodromy is natural, so the two representations have the
same image up to the relabelling of the fibre, and the branch cycles of the smaller set already
generate.

## Main results

* `Rigidity.RET.Analytic.range_monodromyHom_eq_map` — the two monodromy groups agree up to
  relabelling the fibre.
* `Rigidity.RET.Analytic.RationalDeck.exists_branchCycles_shrink` — branch cycles indexed by any
  set of parameters outside of which the family stays separable.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S S' : Finset ℂ} {G : Type} [Group G]

/-! ### The parameters at which the family degenerates -/

/-- The set of parameters at which the fibre of the family is smaller than the degree: the
specialization has a repeated root there. -/
def degenLocus (P : Polynomial (Polynomial ℂ)) : Set ℂ := {z : ℂ | ¬ (spec P z).Separable}

theorem degenLocus_subset (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) :
    degenLocus P ⊆ (S : Set ℂ) := fun _ hz => by
  by_contra h
  exact hz (hS _ h)

theorem finite_degenLocus (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) :
    (degenLocus P).Finite :=
  S.finite_toSet.subset (degenLocus_subset hS)

theorem separable_of_notMem_degenLocus {z : ℂ} (hz : z ∉ degenLocus P) : (spec P z).Separable :=
  not_not.mp hz

/-! ### Restricting the root cover to a larger punctured plane -/

/-- The inclusion of the smaller punctured plane into the larger one. -/
def baseIncl (hsub : (S' : Set ℂ) ⊆ (S : Set ℂ)) :
    C(↥((S : Set ℂ)ᶜ), ↥((S' : Set ℂ)ᶜ)) :=
  ⟨fun z => ⟨z.1, fun hc => z.2 (hsub hc)⟩, continuous_subtype_val.subtype_mk _⟩

/-- The inclusion of the root cover over the smaller punctured plane into the one over the larger
punctured plane. -/
def totalIncl (P : Polynomial (Polynomial ℂ)) (hsub : (S' : Set ℂ) ⊆ (S : Set ℂ)) :
    C(↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)), ↥(rootProj P ⁻¹' ((S' : Set ℂ)ᶜ))) :=
  ⟨fun e => ⟨e.1, fun hc => e.2 (hsub hc)⟩, continuous_subtype_val.subtype_mk _⟩

theorem puncturedProj_totalIncl (P : Polynomial (Polynomial ℂ))
    (hsub : (S' : Set ℂ) ⊆ (S : Set ℂ)) (e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) :
    puncturedProj P S' (totalIncl P hsub e) = baseIncl hsub (puncturedProj P S e) :=
  Subtype.ext rfl

/-- The fibre of the root cover does not depend on which parameters have been removed. -/
def fibreIncl (P : Polynomial (Polynomial ℂ)) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hz₀' : z₀ ∉ (S' : Set ℂ)) :
    (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) ≃
      (puncturedProj P S' ⁻¹' {(⟨z₀, hz₀'⟩ : ↥((S' : Set ℂ)ᶜ))}) :=
  (puncturedFiberEquiv P S hz₀).trans (puncturedFiberEquiv P S' hz₀').symm

/-- Filling in punctures induces a surjection of fundamental groups. -/
theorem surjective_map_baseIncl (hsub : (S' : Set ℂ) ⊆ (S : Set ℂ)) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) :
    Function.Surjective
      (FundamentalGroup.map (baseIncl hsub) (⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))) :=
  surjective_pi1Punct S.finite_toSet hsub hz₀

/-! ### The two monodromy representations -/

/-- **The monodromy representations over the two punctured planes are the same representation.**
Pushing a loop of the smaller punctured plane into the larger one and acting on the relabelled
fibre is acting on the fibre and relabelling. -/
theorem monodromyHom_comp_map (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    (hS' : ∀ z ∉ (S' : Set ℂ), (spec P z).Separable) (hsub : (S' : Set ℂ) ⊆ (S : Set ℂ))
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) (hz₀' : z₀ ∉ (S' : Set ℂ)) :
    (monodromyHom hP hS' hz₀').comp
        (FundamentalGroup.map (baseIncl hsub) (⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ)))
      = (Equiv.permCongrHom (fibreIncl P hz₀ hz₀')).toMonoidHom.comp
        (monodromyHom hP hS hz₀) := by
  refine MonoidHom.ext fun γ => Equiv.ext fun e => ?_
  obtain ⟨d, rfl⟩ := (fibreIncl P hz₀ hz₀').surjective e
  show monodromyHom hP hS' hz₀' (FundamentalGroup.map (baseIncl hsub) _ γ)
      (fibreIncl P hz₀ hz₀' d)
    = Equiv.permCongrHom (fibreIncl P hz₀ hz₀') (monodromyHom hP hS hz₀ γ)
      (fibreIncl P hz₀ hz₀' d)
  rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  refine Subtype.ext ?_
  exact monodromyHom_naturality (isCoveringMap_puncturedProj hP hS)
    (isCoveringMap_puncturedProj hP hS') (baseIncl hsub) (totalIncl P hsub)
    (puncturedProj_totalIncl P hsub) γ d _

/-- **The two monodromy groups agree**, up to the relabelling of the fibre.  Filling in the
parameters at which the family stays separable does not change the monodromy group, because it
does not change the image of the fundamental group. -/
theorem range_monodromyHom_eq_map (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    (hS' : ∀ z ∉ (S' : Set ℂ), (spec P z).Separable) (hsub : (S' : Set ℂ) ⊆ (S : Set ℂ))
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) (hz₀' : z₀ ∉ (S' : Set ℂ)) :
    (monodromyHom hP hS' hz₀').range
      = (monodromyHom hP hS hz₀).range.map
        (Equiv.permCongrHom (fibreIncl P hz₀ hz₀')).toMonoidHom := by
  have hcomp := monodromyHom_comp_map hP hS hS' hsub hz₀ hz₀'
  have hsurj := surjective_map_baseIncl hsub hz₀
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨w, rfl⟩ := hsurj y
    exact ⟨monodromyHom hP hS hz₀ w, ⟨w, rfl⟩, (congrFun (congrArg DFunLike.coe hcomp) w).symm⟩
  · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
    exact ⟨FundamentalGroup.map (baseIncl hsub) _ w,
      congrFun (congrArg DFunLike.coe hcomp) w⟩

/-- The monodromy group over the smaller punctured plane, transported to the larger one. -/
def monodromyRangeMulEquiv (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    (hS' : ∀ z ∉ (S' : Set ℂ), (spec P z).Separable) (hsub : (S' : Set ℂ) ⊆ (S : Set ℂ))
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) (hz₀' : z₀ ∉ (S' : Set ℂ)) :
    (monodromyHom hP hS' hz₀').range ≃* (monodromyHom hP hS hz₀).range :=
  (MulEquiv.subgroupCongr (range_monodromyHom_eq_map hP hS hS' hsub hz₀ hz₀')).trans
    (Subgroup.equivMapOfInjective _ _
      (Equiv.permCongrHom (fibreIncl P hz₀ hz₀')).injective).symm

/-! ### Branch cycles over the smaller set of parameters -/

/-- A product-one generating tuple stays one along an isomorphism. -/
theorem prod_and_closure_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (a : Fin n → A) (hp : (List.ofFn a).prod = 1)
    (hc : Subgroup.closure (Set.range a) = ⊤) :
    (List.ofFn fun i => e (a i)).prod = 1 ∧
      Subgroup.closure (Set.range fun i => e (a i)) = ⊤ := by
  constructor
  · rw [show List.ofFn (fun i => e (a i)) = (List.ofFn a).map (e : A →* B) by
      rw [List.map_ofFn]; rfl, ← map_list_prod, hp, map_one]
  · rw [show (Set.range fun i => e (a i)) = (e : A →* B) '' Set.range a from Set.range_comp _ _,
      ← MonoidHom.map_closure, hc, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact e.surjective

namespace RationalDeck

/-- **Branch cycles over any set of parameters outside of which the family stays separable.**

The group of root formulas is only available away from a possibly larger set of parameters, but the
branch-cycle system it produces can be indexed by the smaller one: the covering space is already
defined there, and the two monodromy representations have the same image. -/
theorem exists_branchCycles_shrink (D : RationalDeck P S G) [Finite G] (hP : P.Monic)
    (hdeg : 0 < P.natDegree) (hirr : Irreducible P)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) (hsub : (S' : Set ℂ) ⊆ (S : Set ℂ))
    (hS' : ∀ z ∉ (S' : Set ℂ), (spec P z).Separable) (hcard : Nat.card G = P.natDegree) :
    ∃ g : Fin (S'.card + 1) → G,
      (List.ofFn g).prod = 1 ∧ Subgroup.closure (Set.range g) = ⊤ := by
  obtain ⟨z₀, hz₀S⟩ := Infinite.exists_notMem_finset S
  have hz₀ : z₀ ∉ (S : Set ℂ) := fun hmem => hz₀S (Finset.mem_coe.mp hmem)
  have hz₀' : z₀ ∉ (S' : Set ℂ) := fun hmem => hz₀ (hsub hmem)
  have hpos : 0 < Nat.card (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) := by
    rw [card_puncturedFiber hP hS hz₀]; exact hdeg
  obtain ⟨e₀⟩ := (Nat.card_pos_iff.mp hpos).1
  set E : (monodromyHom hP hS hz₀).range ≃* G :=
    D.monodromyEquiv hP hdeg hirr hS hz₀ hcard e₀ with hE
  set F : (monodromyHom hP hS' hz₀').range ≃* (monodromyHom hP hS hz₀).range :=
    monodromyRangeMulEquiv hP hS hS' hsub hz₀ hz₀' with hF
  obtain ⟨hp, hc⟩ := prod_and_closure_map (F.trans E) (rangeBranchCycle hP hS' hz₀')
    (prod_rangeBranchCycle hP hS' hz₀') (closure_range_rangeBranchCycle hP hS' hz₀')
  exact ⟨_, hp, hc⟩

/-- **Branch cycles indexed by the degeneration locus of the family.**

The number of branch cycles is not an artefact of the presentation: it is one more than the number
of parameters at which the family actually degenerates. -/
theorem exists_branchCycles_degen (D : RationalDeck P S G) [Finite G] (hP : P.Monic)
    (hdeg : 0 < P.natDegree) (hirr : Irreducible P)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) (hcard : Nat.card G = P.natDegree) :
    ∃ g : Fin ((degenLocus P).ncard + 1) → G,
      (List.ofFn g).prod = 1 ∧ Subgroup.closure (Set.range g) = ⊤ := by
  have hfin : (degenLocus P).Finite := finite_degenLocus hS
  have hcards : hfin.toFinset.card = (degenLocus P).ncard :=
    (Set.ncard_eq_toFinset_card _ hfin).symm
  have hsub : ((hfin.toFinset : Finset ℂ) : Set ℂ) ⊆ (S : Set ℂ) := by
    rw [hfin.coe_toFinset]
    exact degenLocus_subset hS
  have hS' : ∀ z ∉ ((hfin.toFinset : Finset ℂ) : Set ℂ), (spec P z).Separable := by
    intro z hz
    rw [hfin.coe_toFinset] at hz
    exact separable_of_notMem_degenLocus hz
  rw [← hcards]
  exact D.exists_branchCycles_shrink hP hdeg hirr hS hsub hS' hcard

/-- **Branch cycles over the degeneration locus, with the locus named as a finite set.** -/
theorem exists_branchCycles_eq_degen (D : RationalDeck P S G) [Finite G] (hP : P.Monic)
    (hdeg : 0 < P.natDegree) (hirr : Irreducible P)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) (hcard : Nat.card G = P.natDegree) :
    ∃ S₀ : Finset ℂ, (S₀ : Set ℂ) = degenLocus P ∧
      ∃ g : Fin (S₀.card + 1) → G,
        (List.ofFn g).prod = 1 ∧ Subgroup.closure (Set.range g) = ⊤ := by
  have hfin : (degenLocus P).Finite := finite_degenLocus hS
  refine ⟨hfin.toFinset, hfin.coe_toFinset, ?_⟩
  have hsub : ((hfin.toFinset : Finset ℂ) : Set ℂ) ⊆ (S : Set ℂ) := by
    rw [hfin.coe_toFinset]
    exact degenLocus_subset hS
  have hS' : ∀ z ∉ ((hfin.toFinset : Finset ℂ) : Set ℂ), (spec P z).Separable := by
    intro z hz
    rw [hfin.coe_toFinset] at hz
    exact separable_of_notMem_degenLocus hz
  exact D.exists_branchCycles_shrink hP hdeg hirr hS hsub hS' hcard

end RationalDeck

end Rigidity.RET.Analytic

end
