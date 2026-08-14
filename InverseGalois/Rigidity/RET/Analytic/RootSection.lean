/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootCover

/-!
# Local holomorphic branches of the roots of a complex family

Near a simple root the straightening chart of a monic family of equations has a differentiable
inverse, so the root can be followed as a holomorphic function of the parameter.  This file records
the two forms of that statement.

The first is a criterion: a *continuous* root of the family, defined on an open set of parameters,
is automatically holomorphic at every parameter where the root is simple.  Continuity is enough
because the straightening chart is injective, so the continuous root has to agree near the point
with the branch produced by the chart, and that branch is differentiable.

The second is existence: at any simple root there is a local branch, an open neighbourhood of the
parameter and a continuous root on it taking the prescribed value, and by the criterion this branch
is holomorphic wherever the specialized equation is separable.

These local branches are the analytic functions whose symmetric combinations are the coefficients
of the factors of the family over the field of holomorphic functions on the punctured line.

## Main results

* `Rigidity.RET.Analytic.differentiableAt_of_isRoot` — a continuous root is holomorphic at a simple
  root.
* `Rigidity.RET.Analytic.differentiableOn_of_isRoot` — a continuous root is holomorphic over the
  separable locus.
* `Rigidity.RET.Analytic.exists_root_section` — a local branch through any simple root.
-/

open Polynomial Topology Filter

noncomputable section

namespace Rigidity.RET.Analytic

/-- **A continuous root of a family is holomorphic at every simple root.**  The straightening chart
at the point has a differentiable inverse, whose second coordinate is a root of the family; the
chart is injective, so the given continuous root agrees with it near the point. -/
theorem differentiableAt_of_isRoot {P : Polynomial (Polynomial ℂ)} {f : ℂ → ℂ} {V : Set ℂ}
    (hV : IsOpen V) (hf : ContinuousOn f V) (hroot : ∀ z ∈ V, (spec P z).eval (f z) = 0)
    {z₁ : ℂ} (hz₁ : z₁ ∈ V) (hsimple : (spec P z₁).derivative.eval (f z₁) ≠ 0) :
    DifferentiableAt ℂ f z₁ := by
  obtain ⟨φ, hsrc, hcoe, hdiff⟩ := exists_graphChart P hsimple
  have h0 : biEval P (z₁, f z₁) = 0 := hroot z₁ hz₁
  rw [h0] at hdiff
  have hpair : DifferentiableAt ℂ (fun z : ℂ ↦ ((z, (0 : ℂ)) : ℂ × ℂ)) z₁ :=
    differentiableAt_id.prodMk (differentiableAt_const 0)
  have hgdiff : DifferentiableAt ℂ (fun z : ℂ ↦ (φ.symm (z, 0)).2) z₁ :=
    (hdiff.comp z₁ hpair).snd
  have hVnhds : V ∈ 𝓝 z₁ := hV.mem_nhds hz₁
  have hpc : ContinuousAt (fun z : ℂ ↦ ((z, f z) : ℂ × ℂ)) z₁ :=
    continuousAt_id.prodMk (hf.continuousAt hVnhds)
  have hev : (fun z : ℂ ↦ ((z, f z) : ℂ × ℂ)) ⁻¹' φ.source ∈ 𝓝 z₁ :=
    hpc.preimage_mem_nhds (φ.open_source.mem_nhds hsrc)
  have heq : f =ᶠ[𝓝 z₁] fun z : ℂ ↦ (φ.symm (z, 0)).2 := by
    filter_upwards [hev, hVnhds] with z hz hzV
    have hφz : φ (z, f z) = (z, 0) := by
      rw [hcoe]
      exact Prod.ext rfl (hroot z hzV)
    have hlin := φ.left_inv hz
    rw [hφz] at hlin
    exact (congrArg Prod.snd hlin).symm
  exact hgdiff.congr_of_eventuallyEq heq

/-- **A continuous root of a family is holomorphic over the separable locus.** -/
theorem differentiableOn_of_isRoot {P : Polynomial (Polynomial ℂ)} {f : ℂ → ℂ} {V : Set ℂ}
    (hV : IsOpen V) (hf : ContinuousOn f V) (hroot : ∀ z ∈ V, (spec P z).eval (f z) = 0)
    (hsep : ∀ z ∈ V, (spec P z).Separable) : DifferentiableOn ℂ f V := fun z hz =>
  (differentiableAt_of_isRoot hV hf hroot hz
    (Polynomial.Separable.aeval_derivative_ne_zero (hsep z hz)
      (hroot z hz))).differentiableWithinAt

/-- **Every simple root of a specialized equation extends to a local branch of the family.**  The
branch is a continuous root on a neighbourhood of the parameter, holomorphic at the parameter
itself. -/
theorem exists_root_section (P : Polynomial (Polynomial ℂ)) {z₀ w₀ : ℂ}
    (hroot : (spec P z₀).eval w₀ = 0) (hsimple : (spec P z₀).derivative.eval w₀ ≠ 0) :
    ∃ (V : Set ℂ) (f : ℂ → ℂ), IsOpen V ∧ z₀ ∈ V ∧ f z₀ = w₀ ∧ ContinuousOn f V ∧
      (∀ z ∈ V, (spec P z).eval (f z) = 0) ∧ DifferentiableAt ℂ f z₀ := by
  obtain ⟨φ, hsrc, hcoe, hdiff⟩ := exists_graphChart P hsimple
  have h0 : biEval P (z₀, w₀) = 0 := hroot
  have hφz₀ : φ (z₀, w₀) = (z₀, 0) := by
    rw [hcoe]
    exact Prod.ext rfl h0
  refine ⟨{z : ℂ | ((z, (0 : ℂ)) : ℂ × ℂ) ∈ φ.target}, fun z ↦ (φ.symm (z, 0)).2,
    φ.open_target.preimage (by fun_prop), ?_, ?_, ?_, ?_, ?_⟩
  · show ((z₀, (0 : ℂ)) : ℂ × ℂ) ∈ φ.target
    rw [← hφz₀]
    exact φ.map_source hsrc
  · have hlin := φ.left_inv hsrc
    rw [hφz₀] at hlin
    exact congrArg Prod.snd hlin
  · refine ContinuousOn.snd (φ.continuousOn_symm.comp (by fun_prop) fun z hz ↦ hz)
  · intro z hz
    have hrin := φ.right_inv hz
    rw [hcoe] at hrin
    have h1 : (φ.symm (z, 0)).1 = z := (Prod.ext_iff.mp hrin).1
    have h2 : biEval P (φ.symm (z, 0)) = 0 := (Prod.ext_iff.mp hrin).2
    have hpt : ((z, (φ.symm (z, 0)).2) : ℂ × ℂ) = φ.symm (z, 0) := Prod.ext h1.symm rfl
    show biEval P (z, (φ.symm (z, 0)).2) = 0
    rw [hpt]
    exact h2
  · rw [h0] at hdiff
    exact (hdiff.comp z₀ (differentiableAt_id.prodMk (differentiableAt_const 0))).snd

end Rigidity.RET.Analytic

end
