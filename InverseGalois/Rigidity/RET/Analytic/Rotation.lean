/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RationalDeck

/-!
# Comparing two continuous families of roots by one formula

A group of formulas acting simply transitively on the roots of a family lets any two continuous
families of roots over the same parameters be compared: at each parameter exactly one group element
carries the first root to the second, and that element cannot jump, because the sets on which the
different elements do the job are closed and cover a connected parameter space.  So a single group
element does the job everywhere.

This is the mechanism that turns a local statement about one point of a punctured disc — the value
of the monodromy of the generating loop — into a statement about the whole branch, which is what an
algebraic comparison of the two roots needs.

## Main results

* `Rigidity.RET.Analytic.RationalDeck.exists_act_eq` — the formulas act transitively on the roots
  over a good parameter.
* `Rigidity.RET.Analytic.RationalDeck.exists_act_eq_of_preconnected` — over a connected parameter
  space one formula compares two continuous families of roots.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

namespace RationalDeck

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ} {G : Type} [Group G]
  (D : RationalDeck P S G)

/-! ### Transitivity on the roots over one parameter -/

/-- **The formulas act transitively on the roots over a good parameter** once the group is as large
as the degree: they act injectively, and there are as many roots as group elements. -/
theorem exists_act_eq [Finite G] (hP : P.Monic) (hcard : Nat.card G = P.natDegree) {z : ℂ}
    (hz : z ∉ (S : Set ℂ)) (hsep : (spec P z).Separable) {w w' : ℂ} (hw : (spec P z).IsRoot w)
    (hw' : (spec P z).IsRoot w') : ∃ τ : G, D.act τ z w = w' := by
  classical
  haveI : Finite ↥(rootProj P ⁻¹' {z}) := (finite_fiber hP z).to_subtype
  haveI : Finite {y : ℂ // (spec P z).eval y = 0} := Finite.of_equiv _ (fiberEquivRoots P z)
  have hcard' : Nat.card G = Nat.card {y : ℂ // (spec P z).eval y = 0} := by
    rw [hcard, ← card_fiber hP hsep, Nat.card_congr (fiberEquivRoots P z)]
  have hinj : Function.Injective fun g : G => (⟨D.act g z w, D.isRoot g hz hw⟩ :
      {y : ℂ // (spec P z).eval y = 0}) :=
    fun g h hgh => D.injOn hz hw (congrArg Subtype.val hgh)
  have hbij := (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hcard'⟩
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨w', hw'⟩
  exact ⟨τ, congrArg Subtype.val hτ⟩

/-! ### One formula over a connected parameter space -/

/-- **Over a connected parameter space a single formula compares two continuous families of
roots.**  The parameters at which a given formula does the job form a closed set, distinct formulas
never do the job at the same parameter, and finitely many of them cover everything; so each of these
sets is also open, and a connected space is covered by just one of them. -/
theorem exists_act_eq_of_preconnected [Finite G] {X : Type} [TopologicalSpace X]
    [PreconnectedSpace X] [Nonempty X] {w f₁ f₂ : X → ℂ} (hw : Continuous w)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (hmem : ∀ v, w v ∉ (S : Set ℂ))
    (hroot : ∀ v, (spec P (w v)).IsRoot (f₁ v))
    (hex : ∀ v, ∃ τ : G, D.act τ (w v) (f₁ v) = f₂ v) :
    ∃ τ : G, ∀ v, D.act τ (w v) (f₁ v) = f₂ v := by
  classical
  -- the parameters at which `τ` does the job
  set A : G → Set X := fun τ => {v : X | D.act τ (w v) (f₁ v) = f₂ v} with hA
  have hcont : ∀ τ : G, Continuous fun v : X => D.act τ (w v) (f₁ v) := fun τ =>
    (D.continuousOn τ).comp_continuous (hw.prodMk hf₁) fun v => hmem v
  have hclosed : ∀ τ : G, IsClosed (A τ) := fun τ => isClosed_eq (hcont τ) hf₂
  -- distinct formulas never do the job at the same parameter
  have hdisj : ∀ {τ τ' : G} {v : X}, v ∈ A τ → v ∈ A τ' → τ = τ' := by
    intro τ τ' v hv hv'
    exact D.injOn (hmem v) (hroot v) (hv.trans hv'.symm)
  obtain ⟨v₀⟩ := ‹Nonempty X›
  obtain ⟨τ₀, hτ₀⟩ := hex v₀
  have hcompl : (A τ₀)ᶜ = ⋃ τ ∈ ({τ₀}ᶜ : Set G), A τ := by
    ext v
    constructor
    · intro hv
      obtain ⟨τ, hτ⟩ := hex v
      refine Set.mem_biUnion (fun (hτeq : τ ∈ ({τ₀} : Set G)) => hv ?_) hτ
      rw [Set.mem_singleton_iff] at hτeq
      exact hτeq ▸ hτ
    · intro hv hv₀
      obtain ⟨τ, hτmem, hτ⟩ := Set.mem_iUnion₂.mp hv
      exact hτmem (Set.mem_singleton_iff.mpr (hdisj hτ hv₀))
  have hopen : IsOpen (A τ₀) := by
    rw [← isClosed_compl_iff, hcompl]
    exact Set.Finite.isClosed_biUnion (Set.toFinite _) fun τ _ => hclosed τ
  have huniv : A τ₀ = Set.univ :=
    (IsClopen.eq_univ ⟨hclosed τ₀, hopen⟩) ⟨v₀, hτ₀⟩
  exact ⟨τ₀, fun v => (Set.eq_univ_iff_forall.mp huniv) v⟩

/-- **Two continuous families of roots over a connected parameter space differ by one formula.**
Transitivity supplies a formula at each parameter, and connectedness makes the choice global. -/
theorem exists_act_eq_of_isRoot [Finite G] (hP : P.Monic) (hcard : Nat.card G = P.natDegree)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {X : Type} [TopologicalSpace X]
    [PreconnectedSpace X] [Nonempty X] {w f₁ f₂ : X → ℂ} (hw : Continuous w)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (hmem : ∀ v, w v ∉ (S : Set ℂ))
    (hroot₁ : ∀ v, (spec P (w v)).IsRoot (f₁ v)) (hroot₂ : ∀ v, (spec P (w v)).IsRoot (f₂ v)) :
    ∃ τ : G, ∀ v, D.act τ (w v) (f₁ v) = f₂ v :=
  D.exists_act_eq_of_preconnected hw hf₁ hf₂ hmem hroot₁ fun v =>
    D.exists_act_eq hP hcard (hmem v) (hS _ (hmem v)) (hroot₁ v) (hroot₂ v)

end RationalDeck

end Rigidity.RET.Analytic

end
