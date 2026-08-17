/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverCalc

/-!
# Regularity of the operators on the total space of a covering

A function of the total space that is continuously differentiable in every local coordinate has
continuous derivatives, and if it is twice continuously differentiable its derivatives are again
continuously differentiable; a derivative also vanishes wherever the function vanishes on a
neighbourhood, so it inherits compact support.  These are the facts that let the integrals of the
`L²` theory on a covering be formed at all.

## Main results

* `Rigidity.RET.continuous_of_isC1At` — a function differentiable in local coordinates is
  continuous.
* `Rigidity.RET.continuous_dbarY`, `Rigidity.RET.continuous_dzY`,
  `Rigidity.RET.continuous_deltaOpY` — the derivatives are continuous.
* `Rigidity.RET.hasCompactSupport_dbarY`, `Rigidity.RET.hasCompactSupport_dzY`,
  `Rigidity.RET.hasCompactSupport_deltaOpY` — the derivatives inherit compact support.
* `Rigidity.RET.isC1At_dbarY`, `Rigidity.RET.isC1At_dzY`, `Rigidity.RET.isC1At_deltaOpY` — each
  derivative costs one degree of smoothness.
-/

open Topology ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f u v : Y → ℂ} {y : Y} {Φ : ℂ → ℂ}
  {e : OpenPartialHomeomorph Y ℂ} {hlh : IsLocalHomeomorph f}

/-! ### Reading a function of the total space in a coordinate -/

/-- **Read in a coordinate, a differentiable function of the total space is a differentiable
function of a complex variable.** -/
theorem contDiffAt_symm_of_isC1At (hu : ∀ y', IsC1At f u y') (hfe : f = ⇑e) {w : ℂ}
    (hw : w ∈ e.target) : ContDiffAt ℝ 1 (fun w' => u (e.symm w')) w := by
  have h := (hu (e.symm w)).of_isChartAt (isChartAt_symm hfe hw)
  rwa [apply_symm_of_isChartAt hfe hw] at h

/-- Near a point, a function of the total space is its reading in a coordinate. -/
theorem eventuallyEq_comp_symm_comp (he : IsChartAt f e y) (u : Y → ℂ) :
    u =ᶠ[𝓝 y] fun y' => u (e.symm (f y')) := by
  filter_upwards [e.open_source.mem_nhds he.1] with y' hy'
  rw [congrFun he.2 y', e.left_inv hy']

/-! ### Continuity -/

/-- **A function differentiable in every local coordinate is continuous.** -/
theorem continuous_of_isC1At (hlh : IsLocalHomeomorph f) (hu : ∀ y, IsC1At f u y) :
    Continuous u := by
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨e, hy, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  refine ContinuousAt.congr ?_ (eventuallyEq_comp_symm_comp he u).symm
  have h : ContinuousAt ((fun w => u (e.symm w)) ∘ f) y :=
    (((hu y).of_isChartAt he).continuousAt).comp hlh.continuous.continuousAt
  simpa [Function.comp_def] using h

/-- The operator on the total space, read near a point in a coordinate. -/
theorem eventuallyEq_dbarY (he : IsChartAt f e y) (u : Y → ℂ) :
    (fun y' => dbar (fun w => u (e.symm w)) (f y')) =ᶠ[𝓝 y] dbarY hlh u := by
  filter_upwards [e.open_source.mem_nhds he.1] with y' hy'
  exact (dbarY_eq ⟨hy', he.2⟩ u).symm

/-- The holomorphic derivative on the total space, read near a point in a coordinate. -/
theorem eventuallyEq_dzY (he : IsChartAt f e y) (u : Y → ℂ) :
    (fun y' => dz (fun w => u (e.symm w)) (f y')) =ᶠ[𝓝 y] dzY hlh u := by
  filter_upwards [e.open_source.mem_nhds he.1] with y' hy'
  exact (dzY_eq ⟨hy', he.2⟩ u).symm

/-- **The derivative of a function differentiable in every local coordinate is continuous.** -/
theorem continuous_dbarY (hlh : IsLocalHomeomorph f) (hu : ∀ y, IsC1At f u y) :
    Continuous (dbarY hlh u) := by
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨e, hy, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  refine ContinuousAt.congr ?_ (eventuallyEq_dbarY he u)
  have h : ContinuousAt ((dbar fun w => u (e.symm w)) ∘ f) y :=
    (continuousAt_dbar_local e.open_target he.mem_target
      fun w hw => contDiffAt_symm_of_isC1At hu hfe hw).comp hlh.continuous.continuousAt
  simpa [Function.comp_def] using h

/-- **The holomorphic derivative of a function differentiable in every local coordinate is
continuous.** -/
theorem continuous_dzY (hlh : IsLocalHomeomorph f) (hu : ∀ y, IsC1At f u y) :
    Continuous (dzY hlh u) := by
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨e, hy, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  refine ContinuousAt.congr ?_ (eventuallyEq_dzY he u)
  have h : ContinuousAt ((dz fun w => u (e.symm w)) ∘ f) y :=
    (continuousAt_dz_local e.open_target he.mem_target
      fun w hw => contDiffAt_symm_of_isC1At hu hfe hw).comp hlh.continuous.continuousAt
  simpa [Function.comp_def] using h

/-- **The weighted adjoint of a function differentiable in every local coordinate is
continuous.** -/
theorem continuous_deltaOpY (hlh : IsLocalHomeomorph f) (hΦ : ContDiff ℝ 1 Φ)
    (hu : ∀ y, IsC1At f u y) : Continuous (deltaOpY hlh Φ u) :=
  (continuous_dzY hlh hu).neg.add
    (((continuous_dz hΦ).comp hlh.continuous).mul (continuous_of_isC1At hlh hu))

/-! ### Compact support -/

/-- A derivative vanishes wherever the function vanishes on a neighbourhood. -/
theorem dbarY_eq_zero_of_notMem_tsupport (hlh : IsLocalHomeomorph f) {y : Y}
    (hy : y ∉ tsupport u) : dbarY hlh u y = 0 := by
  obtain ⟨e, hy0, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy0, hfe⟩
  have hpre : ∀ᶠ w in 𝓝 (f y), e.symm w ∈ (tsupport u)ᶜ := by
    have hca : ContinuousAt e.symm (f y) := e.continuousAt_symm he.mem_target
    refine hca.preimage_mem_nhds ?_
    rw [he.symm_apply]
    exact (isClosed_tsupport u).isOpen_compl.mem_nhds hy
  have hev : (fun w => u (e.symm w)) =ᶠ[𝓝 (f y)] fun _ => (0 : ℂ) := by
    filter_upwards [hpre] with w hw using image_eq_zero_of_notMem_tsupport hw
  rw [dbarY_eq he u, dbar_congr hev]
  simp [dbar]

/-- A derivative vanishes wherever the function vanishes on a neighbourhood. -/
theorem dzY_eq_zero_of_notMem_tsupport (hlh : IsLocalHomeomorph f) {y : Y}
    (hy : y ∉ tsupport u) : dzY hlh u y = 0 := by
  obtain ⟨e, hy0, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy0, hfe⟩
  have hpre : ∀ᶠ w in 𝓝 (f y), e.symm w ∈ (tsupport u)ᶜ := by
    have hca : ContinuousAt e.symm (f y) := e.continuousAt_symm he.mem_target
    refine hca.preimage_mem_nhds ?_
    rw [he.symm_apply]
    exact (isClosed_tsupport u).isOpen_compl.mem_nhds hy
  have hev : (fun w => u (e.symm w)) =ᶠ[𝓝 (f y)] fun _ => (0 : ℂ) := by
    filter_upwards [hpre] with w hw using image_eq_zero_of_notMem_tsupport hw
  rw [dzY_eq he u, dz_congr hev]
  simp [dz]

/-- **The derivative inherits compact support.** -/
theorem hasCompactSupport_dbarY (hlh : IsLocalHomeomorph f) (hs : HasCompactSupport u) :
    HasCompactSupport (dbarY hlh u) := by
  have hsub : Function.support (dbarY hlh u) ⊆ tsupport u := fun y hy => by
    by_contra hno
    exact hy (dbarY_eq_zero_of_notMem_tsupport hlh hno)
  exact hs.of_isClosed_subset isClosed_closure (closure_minimal hsub (isClosed_tsupport u))

/-- **The holomorphic derivative inherits compact support.** -/
theorem hasCompactSupport_dzY (hlh : IsLocalHomeomorph f) (hs : HasCompactSupport u) :
    HasCompactSupport (dzY hlh u) := by
  have hsub : Function.support (dzY hlh u) ⊆ tsupport u := fun y hy => by
    by_contra hno
    exact hy (dzY_eq_zero_of_notMem_tsupport hlh hno)
  exact hs.of_isClosed_subset isClosed_closure (closure_minimal hsub (isClosed_tsupport u))

/-- **The weighted adjoint inherits compact support.** -/
theorem hasCompactSupport_deltaOpY (hlh : IsLocalHomeomorph f) (hs : HasCompactSupport u) :
    HasCompactSupport (deltaOpY hlh Φ u) :=
  (hasCompactSupport_dzY hlh hs).neg.add hs.mul_left

/-! ### One degree of smoothness -/

/-- **The derivative of a twice differentiable function is continuously differentiable.** -/
theorem isC1At_dbarY (hlh : IsLocalHomeomorph f) (hu : ∀ y', IsC2At f u y') (y : Y) :
    IsC1At f (dbarY hlh u) y := by
  obtain ⟨e, hy, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  refine ⟨e, he, ?_⟩
  refine ContDiffAt.congr_of_eventuallyEq ?_ (eventuallyEq_dbarY_symm he u)
  exact contDiffAt_dbar_local e.open_target he.mem_target
    fun w hw => contDiffAt_symm_of_isC2At hu hfe hw

/-- **The holomorphic derivative of a twice differentiable function is continuously
differentiable.** -/
theorem isC1At_dzY (hlh : IsLocalHomeomorph f) (hu : ∀ y', IsC2At f u y') (y : Y) :
    IsC1At f (dzY hlh u) y := by
  obtain ⟨e, hy, hfe⟩ := hlh y
  have he : IsChartAt f e y := ⟨hy, hfe⟩
  refine ⟨e, he, ?_⟩
  refine ContDiffAt.congr_of_eventuallyEq ?_ (eventuallyEq_dzY_symm he u)
  exact contDiffAt_dz_local e.open_target he.mem_target
    fun w hw => contDiffAt_symm_of_isC2At hu hfe hw

/-- **The weighted adjoint of a twice differentiable function is continuously differentiable.** -/
theorem isC1At_deltaOpY (hlh : IsLocalHomeomorph f) (hΦ : ContDiff ℝ 2 Φ)
    (hu : ∀ y', IsC2At f u y') (y : Y) : IsC1At f (deltaOpY hlh Φ u) y := by
  have h1 : IsC1At f (fun y' => -dzY hlh u y') y := by
    obtain ⟨e, he, hc⟩ := isC1At_dzY hlh hu y
    exact ⟨e, he, hc.neg⟩
  have h2 : IsC1At f (fun y' => dz Φ (f y')) y :=
    isC1At_comp hlh (contDiff_one_dz hΦ).contDiffAt
  exact h1.add (h2.mul (hu y).isC1At)

end Rigidity.RET

end
