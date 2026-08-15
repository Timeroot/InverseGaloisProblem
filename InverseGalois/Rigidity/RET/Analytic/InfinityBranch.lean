/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootMonodromy
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureLoop

/-!
# Branches of the roots in the parameter at infinity

A continuous branch of the roots of a family, read in the parameter `T = (uᵈ)⁻¹` at infinity, is a
section of the punctured root cover over the punctured disc of the variable `u`.  Two such sections
lie over the same map of the punctured disc into the line, so the uniqueness of lifts through a
covering map applies: a punctured disc is connected, hence two branches that agree at one point of
it agree at every point.

## Main results

* `Rigidity.RET.Analytic.eqOn_of_root_inv` — two continuous branches of the roots in the parameter
  at infinity that agree at one point of a punctured disc agree throughout it.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ}

/-- **Two branches of the roots in the parameter at infinity that meet coincide.**  Each branch is
a continuous section of the punctured root cover over the punctured disc; the two sections lie over
one and the same map, and a punctured disc is connected, so lifts through a covering map that agree
somewhere agree everywhere. -/
theorem eqOn_of_root_inv (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    {ρ : ℝ} {d : ℕ} {g₁ g₂ : ℂ → ℂ} (hρ : 0 < ρ)
    (hmem : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, ((u ^ d)⁻¹) ∉ (S : Set ℂ))
    (hc₁ : ContinuousOn g₁ (puncturedDisc (0 : ℂ) ρ))
    (hc₂ : ContinuousOn g₂ (puncturedDisc (0 : ℂ) ρ))
    (hr₁ : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (spec P ((u ^ d)⁻¹)).eval (g₁ u) = 0)
    (hr₂ : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (spec P ((u ^ d)⁻¹)).eval (g₂ u) = 0)
    {u₁ : ℂ} (hu₁ : u₁ ∈ puncturedDisc (0 : ℂ) ρ) (heq : g₁ u₁ = g₂ u₁) :
    Set.EqOn g₁ g₂ (puncturedDisc (0 : ℂ) ρ) := by
  haveI : PathConnectedSpace ↥(puncturedDisc (0 : ℂ) ρ) := pathConnectedSpace_puncturedDisc 0 hρ
  have hcov := isCoveringMap_puncturedProj (P := P) (S := S) hP hS
  have hfst : Continuous fun u : ↥(puncturedDisc (0 : ℂ) ρ) => (((u : ℂ) ^ d)⁻¹) :=
    (continuous_subtype_val.pow d).inv₀ fun u => pow_ne_zero _ (mem_puncturedDisc.mp u.2).2
  set F₁ : ↥(puncturedDisc (0 : ℂ) ρ) → ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) :=
    fun u => ⟨⟨((((u : ℂ) ^ d)⁻¹), g₁ (u : ℂ)), hr₁ u u.2⟩, hmem u u.2⟩ with hF₁
  set F₂ : ↥(puncturedDisc (0 : ℂ) ρ) → ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) :=
    fun u => ⟨⟨((((u : ℂ) ^ d)⁻¹), g₂ (u : ℂ)), hr₂ u u.2⟩, hmem u u.2⟩ with hF₂
  have hcont₁ : Continuous F₁ :=
    Continuous.subtype_mk (Continuous.subtype_mk (hfst.prodMk hc₁.restrict) _) _
  have hcont₂ : Continuous F₂ :=
    Continuous.subtype_mk (Continuous.subtype_mk (hfst.prodMk hc₂.restrict) _) _
  have hcomp : puncturedProj P S ∘ F₁ = puncturedProj P S ∘ F₂ := funext fun _ => Subtype.ext rfl
  have hFeq : F₁ = F₂ :=
    hcov.eq_of_comp_eq hcont₁ hcont₂ hcomp ⟨u₁, hu₁⟩
      (Subtype.ext (Subtype.ext (by
        show ((((u₁ : ℂ) ^ d)⁻¹), g₁ u₁) = ((((u₁ : ℂ) ^ d)⁻¹), g₂ u₁)
        rw [heq])))
  intro u hu
  exact congrArg (fun x : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) => ((x : rootVariety P) : ℂ × ℂ).2)
    (congrFun hFeq ⟨u, hu⟩)

end Rigidity.RET.Analytic

end
