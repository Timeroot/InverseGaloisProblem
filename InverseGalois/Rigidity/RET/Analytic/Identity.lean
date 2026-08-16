/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverHolo

/-!
# The identity theorem on a covering

A holomorphic function on the total space of a covering which vanishes near one point vanishes
everywhere, provided the total space is connected.  The proof is the usual one: the set of points
near which the function vanishes identically is open by definition, and closed because in a local
coordinate the function is analytic on a ball, where Riemann's identity principle applies.

The consequence that matters is that the holomorphic functions on a connected covering have no zero
divisors: a product of two of them vanishes only if one of them does.  That is what makes it
possible to speak of the *field* of functions of a covering.

## Main results

* `Rigidity.RET.IsHoloAt.continuousAt` — a holomorphic function is continuous.
* `Rigidity.RET.isClosed_setOf_eventuallyEq_zero` — the set of points near which a holomorphic
  function vanishes identically is closed.
* `Rigidity.RET.IsHolo.eq_zero_of_eventuallyEq_zero` — the identity theorem.
* `Rigidity.RET.IsHolo.eq_of_eventuallyEq` — two holomorphic functions agreeing near a point agree.
* `Rigidity.RET.IsHolo.eq_zero_or_eq_zero_of_mul_eq_zero` — no zero divisors.
-/

open Topology Set

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f g g₁ g₂ : Y → ℂ} {y : Y}

/-- **A holomorphic function is continuous**: in a local coordinate it is analytic, and the
coordinate is the projection, which is continuous. -/
theorem IsHoloAt.continuousAt (hf : IsLocalHomeomorph f) (h : IsHoloAt f g y) :
    ContinuousAt g y := by
  obtain ⟨e, he, ha⟩ := h
  have hcomp : ContinuousAt (fun y' => g (e.symm (f y'))) y :=
    ha.continuousAt.comp hf.continuous.continuousAt
  refine hcomp.congr ?_
  filter_upwards [e.open_source.mem_nhds he.1] with y' hy'
  show g (e.symm (f y')) = g y'
  rw [congrFun he.2 y', e.left_inv hy']

/-- A holomorphic function is continuous. -/
theorem IsHolo.continuous (hf : IsLocalHomeomorph f) (h : IsHolo f g) : Continuous g :=
  continuous_iff_continuousAt.2 fun y => (h y).continuousAt hf

/-- **The set of points near which a holomorphic function vanishes identically is closed.**

In a local coordinate at a limit point of that set the function is analytic on a ball, and it
vanishes near a point of the ball, so Riemann's identity principle makes it vanish on the whole
ball. -/
theorem isClosed_setOf_eventuallyEq_zero (hf : IsLocalHomeomorph f) (hg : IsHolo f g) :
    IsClosed {y : Y | g =ᶠ[𝓝 y] 0} := by
  refine isClosed_of_closure_subset fun y hy => ?_
  obtain ⟨e, hy₀, he⟩ := hf y
  have hchart : IsChartAt f e y := ⟨hy₀, he⟩
  have hsymm : ∀ y' ∈ e.source, e.symm (f y') = y' := by
    intro y' hy'
    rw [congrFun he y']; exact e.left_inv hy'
  have hana : AnalyticOnNhd ℂ (fun w => g (e.symm w)) e.target := by
    intro w hw
    have hz : e.symm w ∈ e.source := e.map_target hw
    have hfz : f (e.symm w) = w := by rw [congrFun he]; exact e.right_inv hw
    have := (hg (e.symm w)).analyticAt_of_chart (f := f) ⟨hz, he⟩
    rwa [hfz] at this
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 e.open_target (f y) hchart.mem_target
  have hanaB : AnalyticOnNhd ℂ (fun w => g (e.symm w)) (Metric.ball (f y) ρ) :=
    fun w hw => hana w (hball hw)
  have hVopen : IsOpen (e.source ∩ f ⁻¹' Metric.ball (f y) ρ) :=
    e.open_source.inter (Metric.isOpen_ball.preimage hf.continuous)
  have hyV : y ∈ e.source ∩ f ⁻¹' Metric.ball (f y) ρ := ⟨hy₀, Metric.mem_ball_self hρ⟩
  obtain ⟨z, hzV, hz⟩ := mem_closure_iff.1 hy _ hVopen hyV
  have hzt : f z ∈ e.target := by rw [congrFun he z]; exact e.map_source hzV.1
  have hev : (fun w => g (e.symm w)) =ᶠ[𝓝 (f z)] 0 := by
    have htend : Filter.Tendsto (⇑e.symm) (𝓝 (f z)) (𝓝 (e.symm (f z))) := e.continuousAt_symm hzt
    rw [hsymm z hzV.1] at htend
    filter_upwards [htend.eventually hz] with w hw using hw
  have hEq : EqOn (fun w => g (e.symm w)) 0 (Metric.ball (f y) ρ) :=
    hanaB.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (f y) ρ).isPreconnected hzV.2 hev
  filter_upwards [hVopen.mem_nhds hyV] with y' hy'
  have hval := hEq hy'.2
  simp only [Pi.zero_apply] at hval ⊢
  rwa [hsymm y' hy'.1] at hval

/-- **The identity theorem**: a holomorphic function on a connected covering which vanishes near
one point vanishes everywhere. -/
theorem IsHolo.eq_zero_of_eventuallyEq_zero [PreconnectedSpace Y] (hf : IsLocalHomeomorph f)
    (hg : IsHolo f g) {y₀ : Y} (h₀ : g =ᶠ[𝓝 y₀] 0) : g = 0 := by
  have hcl := isClosed_setOf_eventuallyEq_zero hf hg
  have hop : IsOpen {y : Y | g =ᶠ[𝓝 y] 0} := isOpen_setOf_eventually_nhds
  rcases isClopen_iff.1 ⟨hcl, hop⟩ with h | h
  · have hmem : y₀ ∈ {y : Y | g =ᶠ[𝓝 y] 0} := h₀
    rw [h] at hmem
    simp at hmem
  · funext y
    have hmem : y ∈ {y : Y | g =ᶠ[𝓝 y] 0} := by rw [h]; trivial
    exact hmem.self_of_nhds

/-- **Two holomorphic functions on a connected covering agreeing near a point agree.** -/
theorem IsHolo.eq_of_eventuallyEq [PreconnectedSpace Y] (hf : IsLocalHomeomorph f)
    (hg₁ : IsHolo f g₁) (hg₂ : IsHolo f g₂) {y₀ : Y} (h₀ : g₁ =ᶠ[𝓝 y₀] g₂) : g₁ = g₂ := by
  have hsub : IsHolo f fun y => g₁ y - g₂ y := fun y => (hg₁ y).sub (hg₂ y)
  have hz : (fun y => g₁ y - g₂ y) =ᶠ[𝓝 y₀] 0 := by
    filter_upwards [h₀] with y hy
    simp [hy]
  have := hsub.eq_zero_of_eventuallyEq_zero hf hz
  funext y
  have := congrFun this y
  simpa [sub_eq_zero] using this

/-- **A holomorphic function on a connected covering which is not identically zero vanishes only on
a set with empty interior**, in the form that is used: it does not vanish near any point where it
is nonzero. -/
theorem IsHolo.eq_zero_or_eq_zero_of_mul_eq_zero [PreconnectedSpace Y] (hf : IsLocalHomeomorph f)
    (hg₁ : IsHolo f g₁) (hg₂ : IsHolo f g₂) (h : (fun y => g₁ y * g₂ y) = 0) :
    g₁ = 0 ∨ g₂ = 0 := by
  by_cases h1 : g₁ = 0
  · exact Or.inl h1
  refine Or.inr ?_
  obtain ⟨y₀, hy₀⟩ : ∃ y, g₁ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h1 (funext hc)
  have hne : ∀ᶠ y in 𝓝 y₀, g₁ y ≠ 0 := ((hg₁ y₀).continuousAt hf).eventually_ne hy₀
  refine hg₂.eq_zero_of_eventuallyEq_zero hf (y₀ := y₀) ?_
  filter_upwards [hne] with y hy
  have hmul := congrFun h y
  simp only [Pi.zero_apply] at hmul ⊢
  exact (mul_eq_zero.1 hmul).resolve_left hy

end Rigidity.RET

end
