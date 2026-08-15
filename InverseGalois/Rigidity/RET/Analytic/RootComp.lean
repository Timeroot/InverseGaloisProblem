/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootSection

/-!
# Holomorphy of a continuous root along a holomorphic change of parameter

A continuous root of a monic family is holomorphic wherever the root it follows is simple.  The
same is true of a continuous root of the family read along a holomorphic reparametrisation of the
line: the straightening chart of the family at a simple root is a local biholomorphism, and
composing its inverse with the reparametrisation exhibits the root as a holomorphic function of the
new parameter.

Reading the family along a reparametrisation is what happens at every local analysis of a cover.
Near a point of the line the reparametrisation is the Kummer coordinate `T = s + uᵉ`; near the
point at infinity it is `T = u⁻ᵈ`, which is not a polynomial substitution, so the family read in
the new parameter is no longer a polynomial family and the plain criterion no longer applies.
Keeping the change of parameter as an arbitrary holomorphic function covers both.

## Main results

* `Rigidity.RET.Analytic.differentiableAt_of_isRoot_comp` — a continuous root of a family read
  along a holomorphic change of parameter is holomorphic at every simple root.
* `Rigidity.RET.Analytic.differentiableOn_of_isRoot_comp` — the same over the separable locus.
-/

open Polynomial Topology Filter

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {w g : ℂ → ℂ} {V : Set ℂ}

/-- **A continuous root of a family read along a holomorphic change of parameter is holomorphic at
every simple root.**  The straightening chart at the point has a differentiable inverse, whose
second coordinate is a root of the family; the chart is injective, so the given continuous root
agrees near the point with that branch, read along the change of parameter. -/
theorem differentiableAt_of_isRoot_comp (hV : IsOpen V) (hw : ContinuousOn w V)
    (hg : ContinuousOn g V) (hroot : ∀ u ∈ V, (spec P (w u)).eval (g u) = 0)
    {u₁ : ℂ} (hu₁ : u₁ ∈ V) (hwdiff : DifferentiableAt ℂ w u₁)
    (hsimple : (spec P (w u₁)).derivative.eval (g u₁) ≠ 0) :
    DifferentiableAt ℂ g u₁ := by
  obtain ⟨φ, hsrc, hcoe, hdiff⟩ := exists_graphChart P hsimple
  have h0 : biEval P (w u₁, g u₁) = 0 := hroot u₁ hu₁
  rw [h0] at hdiff
  have hpair : DifferentiableAt ℂ (fun u : ℂ ↦ ((w u, (0 : ℂ)) : ℂ × ℂ)) u₁ :=
    hwdiff.prodMk (differentiableAt_const 0)
  have hgdiff : DifferentiableAt ℂ (fun u : ℂ ↦ (φ.symm (w u, 0)).2) u₁ :=
    (hdiff.comp u₁ hpair).snd
  have hVnhds : V ∈ 𝓝 u₁ := hV.mem_nhds hu₁
  have hpc : ContinuousAt (fun u : ℂ ↦ ((w u, g u) : ℂ × ℂ)) u₁ :=
    (hw.continuousAt hVnhds).prodMk (hg.continuousAt hVnhds)
  have hev : (fun u : ℂ ↦ ((w u, g u) : ℂ × ℂ)) ⁻¹' φ.source ∈ 𝓝 u₁ :=
    hpc.preimage_mem_nhds (φ.open_source.mem_nhds hsrc)
  have heq : g =ᶠ[𝓝 u₁] fun u : ℂ ↦ (φ.symm (w u, 0)).2 := by
    filter_upwards [hev, hVnhds] with u hu huV
    have hφz : φ (w u, g u) = (w u, 0) := by
      rw [hcoe]
      exact Prod.ext rfl (hroot u huV)
    have hlin := φ.left_inv hu
    rw [hφz] at hlin
    exact (congrArg Prod.snd hlin).symm
  exact hgdiff.congr_of_eventuallyEq heq

/-- **A continuous root of a family read along a holomorphic change of parameter is holomorphic
over the separable locus.** -/
theorem differentiableOn_of_isRoot_comp (hV : IsOpen V) (hw : DifferentiableOn ℂ w V)
    (hg : ContinuousOn g V) (hroot : ∀ u ∈ V, (spec P (w u)).eval (g u) = 0)
    (hsep : ∀ u ∈ V, (spec P (w u)).Separable) : DifferentiableOn ℂ g V := fun u hu =>
  (differentiableAt_of_isRoot_comp hV hw.continuousOn hg hroot hu
    ((hw u hu).differentiableAt (hV.mem_nhds hu))
    (Polynomial.Separable.aeval_derivative_ne_zero (hsep u hu)
      (hroot u hu))).differentiableWithinAt

end Rigidity.RET.Analytic

end
