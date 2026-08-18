/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.PrimitiveElement
import InverseGalois.Rigidity.RET.Analytic.SeparatePoints
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverSolvable
import InverseGalois.Rigidity.RET.Analytic.Wall
import InverseGalois.Rigidity.RET.Pi1.Topological.CoverOrdered
import InverseGalois.Rigidity.RET.Pi1.Topological.PuncturedPlane
import InverseGalois.Rigidity.RET.Transfer.Present

/-!
# The polynomial presentation of a complex covering

A covering of a punctured plane is presented here by two monic equations, in such a way that the
two equations degenerate at no common point outside the punctures.

One equation is not enough.  A generator of the function field satisfies a monic equation whose
degeneracy locus contains the punctures, but may contain more: the generator is chosen to separate
the points of the fibres outside a finite set, and that finite set is in general larger than the
set of punctures.  The remedy is to choose a second generator that separates the fibres over the
extra points of the first.  Each such extra point carries a fibre; a function of moderate growth
separating the finitely many pairs of points of those finitely many fibres at once exists, and the
finite set attached to it misses every one of the extra points.  Between the two equations, then,
every point outside the punctures is a point at which one of them stays separable.

## Main results

* `Rigidity.RET.exists_coverDatum_complex` — a covering of a punctured plane, with a faithful
  transitive finite group of deck transformations, has a polynomial presentation whose degeneracy
  is located at the punctures.
* `Rigidity.RET.exists_coverDatum_of_prodOne` — a generating product-one tuple in a finite group
  yields such a presentation over the complex numbers, with the prescribed points for its
  degeneracy.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

attribute [local instance] FractionRing.liftAlgebra ratFuncAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A covering of a punctured plane has a polynomial presentation whose degeneracy is located at
the punctures.**

A first generator of the function field separates the fibres outside a finite set containing the
punctures; a second one is chosen to separate the fibres over the finitely many points of that set
which are not punctures, and the finite set attached to it therefore avoids them.  Every point
outside the punctures escapes one of the two finite sets, so one of the two equations stays
separable there, and the two degeneracy loci meet only at the punctures. -/
theorem exists_coverDatum_complex (S : Finset ℂ) (Y : Type) [TopologicalSpace Y] [Nonempty Y]
    [PreconnectedSpace Y] (q : Y → ↥((S : Set ℂ)ᶜ)) (hq : IsCoveringMap q)
    (hf : IsLocalHomeomorph fun y => ((q y : ℂ)))
    (hrange : Set.range (fun y => ((q y : ℂ))) = (↑S : Set ℂ)ᶜ)
    (H : Type) [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y] [FaithfulSMul H Y]
    [IsOverBase H fun y => ((q y : ℂ))]
    (htrans : ∀ y y' : Y, (q y : ℂ) = (q y' : ℂ) → ∃ b : H, y' = b • y)
    {r : ℕ} (t : Fin r → ℂ) (hts : Set.range t = (S : Set ℂ)) :
    Nonempty (CoverDatum ℂ H t) := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  haveI : T2Space Y := t2Space_of_isCoveringMap hq
  -- every nontrivial deck transformation moves a function of moderate growth
  have hne : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y :=
    hasEnoughFunctions S Y q hq hf hrange H htrans
  -- a first generator, and the finite set outside which it separates the fibres
  obtain ⟨F₁, hF₁, y₁, hinj₁⟩ := hasSeparatingFunction_of_forall_ne (H := H) hf hne
  have hne₁ : ∀ c : H, c ≠ 1 → ∃ y : Y, F₁ (c • y) ≠ F₁ y := fun c hc =>
    ⟨y₁, fun h => hc (hinj₁ c 1 (by simpa using h))⟩
  obtain ⟨S₁, hS₁, hsepF₁, -⟩ := exists_finset_separating (H := H) hf htrans hrange hF₁ hne₁
  -- a point of the covering over each point of that set which is not a puncture
  have hptex : ∀ z : ↥(S₁ \ S), ∃ y : Y, ((q y : ℂ)) = (z : ℂ) := by
    rintro ⟨z, hz⟩
    rw [Finset.mem_sdiff] at hz
    have hmem : z ∈ ((S : Set ℂ))ᶜ := fun hc => hz.2 (Finset.mem_coe.1 hc)
    rw [← hrange] at hmem
    exact hmem
  choose pt hpt using hptex
  -- a single function separating the points of those fibres, and of one further fibre
  have hsep₂ : ∀ i : {p : H × H // p.1 ≠ p.2} × Option ↥(S₁ \ S),
      ∃ F ∈ coverRing hf S,
        F (i.1.1.1 • i.2.elim y₁ pt) ≠ F (i.1.1.2 • i.2.elim y₁ pt) := by
    rintro ⟨⟨⟨a, b⟩, hab⟩, o⟩
    have hab1 : a * b⁻¹ ≠ 1 := fun h => hab (mul_inv_eq_one.1 h)
    obtain ⟨F, hF, hFne⟩ := exists_ne_at S Y q hq hf H htrans (a * b⁻¹) (b • o.elim y₁ pt)
      (smul_ne_self hf hab1 (b • o.elim y₁ pt))
    refine ⟨F, hF, ?_⟩
    rwa [smul_smul, inv_mul_cancel_right] at hFne
  obtain ⟨F₂, hF₂, hF₂ne⟩ := exists_forall_ne_of_pairs hf hsep₂
  have hne₂ : ∀ c : H, c ≠ 1 → ∃ y : Y, F₂ (c • y) ≠ F₂ y := by
    intro c hc
    exact ⟨y₁, by simpa using hF₂ne (⟨(c, 1), hc⟩, none)⟩
  obtain ⟨S₂, hS₂, hsepF₂, hthird₂⟩ := exists_finset_separating (H := H) hf htrans hrange hF₂ hne₂
  -- the second finite set misses the extra points of the first
  have hZ : ∀ z : ↥(S₁ \ S), (z : ℂ) ∉ (S₂ : Set ℂ) := by
    intro z
    have hsepz : ∀ a b : H, a ≠ b → F₂ (a • pt z) ≠ F₂ (b • pt z) := by
      intro a b hab
      simpa using hF₂ne (⟨(a, b), hab⟩, some z)
    have hy := hthird₂ (pt z) hsepz
    rwa [hpt z] at hy
  -- the two equations
  letI := coverRatFuncAlgebra hf hrange
  obtain ⟨P₁, hm₁, hd₁, hsp₁, -, hirr₁, α₁, hr₁, hg₁⟩ :=
    exists_primitive_of_separating (H := H) hf hrange htrans hne hS₁ hF₁ hsepF₁
  obtain ⟨P₂, hm₂, hd₂, hsp₂, -, -, α₂, hr₂, hg₂⟩ :=
    exists_primitive_of_separating (H := H) hf hrange htrans hne hS₂ hF₂ hsepF₂
  -- outside the punctures one of the two equations stays separable
  have hsep : ∀ z ∉ Set.range t, (P₁.map (evalRingHom z)).Separable ∨
      (P₂.map (evalRingHom z)).Separable := by
    intro z hz
    rw [hts] at hz
    by_cases h₁ : z ∈ (S₁ : Set ℂ)
    · exact Or.inr (hsp₂ z (hZ ⟨z, Finset.mem_sdiff.2 ⟨Finset.mem_coe.1 h₁, fun hm => hz hm⟩⟩))
    · exact Or.inl (hsp₁ z h₁)
  exact exists_coverDatum
    (mulEquivAlgEquiv_ratFunc_coverRing hf hrange htrans hne).toMonoidHom
    (mulEquivAlgEquiv_ratFunc_coverRing hf hrange htrans hne).injective α₁ α₂ P₁ P₂ hm₁ hm₂
    hd₁ hd₂ hirr₁ hr₁ hr₂ hg₁ hg₂ hsep

/-- **A generating product-one tuple in a finite group presents a cover of the plane branched at
prescribed points.**

The tuple is the monodromy of a connected covering of the plane punctured at those points, and the
covering has a polynomial presentation degenerating only there. -/
theorem exists_coverDatum_of_prodOne (S : Finset ℂ) (pt : Fin S.card → ℂ)
    (hpt : Set.range pt = (S : Set ℂ)) {H : Type} [Group H] [Finite H] (h : Fin S.card → H)
    (hprod : (List.ofFn h).prod = 1) (hgen : Subgroup.closure (Set.range h) = ⊤) :
    Nonempty (CoverDatum ℂ H pt) := by
  classical
  obtain ⟨z₀, hz₀⟩ := Infinite.exists_notMem_finset S
  have hz₀' : z₀ ∈ ((S : Set ℂ))ᶜ := hz₀
  haveI : PathConnectedSpace ↥((S : Set ℂ))ᶜ :=
    pathConnectedSpace_punctured S.finite_toSet.countable
  obtain ⟨-, -, D, -, -, hcov, hconn, hinj, htrans, -, -⟩ :=
    exists_cover_of_prodOne_ordered S hz₀' pt hpt h hprod hgen
  haveI := hconn
  have hX : IsOpen ((S : Set ℂ))ᶜ := (S.finite_toSet.isClosed).isOpen_compl
  have hf : IsLocalHomeomorph fun y => ((D.proj y : ℂ)) := D.isLocalHomeomorph_projC hX hcov
  have hrange : Set.range (fun y => ((D.proj y : ℂ))) = (↑S : Set ℂ)ᶜ :=
    D.range_projC D.surjective_proj
  letI : MulAction H D.Total := MulAction.compHom D.Total D.deckHom
  haveI : ContinuousConstSMul H D.Total := ⟨fun a => D.continuous_deck a⁻¹⟩
  haveI : FaithfulSMul H D.Total := ⟨fun {a b} hab => hinj (Equiv.ext hab)⟩
  haveI : IsOverBase H fun y => ((D.proj y : ℂ)) := ⟨fun _ _ => rfl⟩
  have htrans' : ∀ y y' : D.Total, (D.proj y : ℂ) = (D.proj y' : ℂ) → ∃ b : H, y' = b • y := by
    intro y y' hyy
    obtain ⟨a, ha⟩ := htrans y y' (Subtype.coe_injective hyy)
    refine ⟨a⁻¹, ?_⟩
    show y' = D.deck a⁻¹⁻¹ y
    rw [inv_inv, ha]
  exact exists_coverDatum_complex S D.Total D.proj hcov hf hrange H htrans' pt hpt

/-- **A generating tuple in a finite group presents a cover of the plane branched at prescribed
points, one for each entry of the tuple.**

The fundamental group of the plane punctured at those points is free on as many generators as there
are punctures, so the tuple names a connected covering; nothing is asked of the behaviour of the
covering at infinity, and correspondingly no relation is asked of the tuple. -/
theorem exists_coverDatum_of_generating (S : Finset ℂ) (pt : Fin S.card → ℂ)
    (hpt : Set.range pt = (S : Set ℂ)) {H : Type} [Group H] [Finite H] (h : Fin S.card → H)
    (hgen : Subgroup.closure (Set.range h) = ⊤) :
    Nonempty (CoverDatum ℂ H pt) := by
  classical
  obtain ⟨z₀, hz₀⟩ := Infinite.exists_notMem_finset S
  have hz₀' : z₀ ∈ ((S : Set ℂ))ᶜ := hz₀
  haveI : PathConnectedSpace ↥((S : Set ℂ))ᶜ :=
    pathConnectedSpace_punctured S.finite_toSet.countable
  -- the fundamental group is free on the punctures, so the tuple names a surjection onto the group
  obtain ⟨e⟩ := pi1_compl_finset S z₀ hz₀
  have hsurj0 : Function.Surjective (FreeGroup.lift h) :=
    MonoidHom.range_eq_top.1 (by rw [FreeGroup.range_lift_eq_closure, hgen])
  set φ : FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀'⟩ →* H :=
    (FreeGroup.lift h).comp e.toMonoidHom with hφdef
  have hsurj : Function.Surjective φ := hsurj0.comp e.surjective
  have hX : IsOpen ((S : Set ℂ))ᶜ := (S.finite_toSet.isClosed).isOpen_compl
  set D : MonodromyData (X := ((S : Set ℂ))ᶜ) ⟨z₀, hz₀'⟩ H := MonodromyData.ofHom hX φ with hDdef
  have hcov : IsCoveringMap D.proj := MonodromyData.isCoveringMap_proj_ofHom hX φ
  haveI hconn : PathConnectedSpace D.Total :=
    MonodromyData.pathConnectedSpace_total_ofHom hX φ hsurj
  have hinj : Function.Injective D.deckHom := MonodromyData.deckHom_injective_ofHom hX φ
  have htrans : ∀ y z : D.Total, D.proj y = D.proj z → ∃ a : H, D.deck a y = z := by
    intro y z hyz
    exact D.exists_deck_eq_of_proj_eq y z hyz
      (Classical.choice (MonodromyData.nonempty_quotient_of_pathConnected
        (x₀ := (⟨z₀, hz₀'⟩ : ↥((S : Set ℂ))ᶜ)) _))
  have hf : IsLocalHomeomorph fun y => ((D.proj y : ℂ)) := D.isLocalHomeomorph_projC hX hcov
  have hrange : Set.range (fun y => ((D.proj y : ℂ))) = (↑S : Set ℂ)ᶜ :=
    D.range_projC D.surjective_proj
  letI : MulAction H D.Total := MulAction.compHom D.Total D.deckHom
  haveI : ContinuousConstSMul H D.Total := ⟨fun a => D.continuous_deck a⁻¹⟩
  haveI : FaithfulSMul H D.Total := ⟨fun {a b} hab => hinj (Equiv.ext hab)⟩
  haveI : IsOverBase H fun y => ((D.proj y : ℂ)) := ⟨fun _ _ => rfl⟩
  have htrans' : ∀ y y' : D.Total, (D.proj y : ℂ) = (D.proj y' : ℂ) → ∃ b : H, y' = b • y := by
    intro y y' hyy
    obtain ⟨a, ha⟩ := htrans y y' (Subtype.coe_injective hyy)
    refine ⟨a⁻¹, ?_⟩
    show y' = D.deck a⁻¹⁻¹ y
    rw [inv_inv, ha]
  exact exists_coverDatum_complex S D.Total D.proj hcov hf hrange H htrans' pt hpt

end Rigidity.RET

end
