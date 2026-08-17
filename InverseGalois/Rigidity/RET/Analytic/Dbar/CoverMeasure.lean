/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.FibreSum

/-!
# A measure on the total space of a covering

Integrating the fibre sum of a compactly supported function over the plane is a positive linear
functional on the compactly supported continuous functions of the total space, and the
Riesz–Markov–Kakutani representation theorem turns such a functional into a measure.  The measure
so obtained is the one that reads an integral over the total space as an integral of fibre sums
over the base, which is what the `L²` theory for the Cauchy–Riemann operator on a covering needs.

## Main definitions

* `Rigidity.RET.coverFunctional` — the fibre-sum functional on compactly supported continuous
  functions.
* `Rigidity.RET.coverMeasure` — the measure it represents.

## Main results

* `Rigidity.RET.t2Space_of_isSeparatedMap`, `Rigidity.RET.weaklyLocallyCompactSpace_of_isLocalHomeomorph`
  — the total space of a separated local homeomorphism to the plane is Hausdorff and locally
  compact.
* `Rigidity.RET.integral_coverMeasure` — integration against the measure is integration of fibre
  sums over the plane.
-/

open MeasureTheory Topology CompactlySupported

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ}

/-! ### Separation and local compactness -/

/-- **A separated map to a Hausdorff space has a Hausdorff domain.** -/
theorem t2Space_of_isSeparatedMap {X : Type*} [TopologicalSpace X] [T2Space X] {g : Y → X}
    (hc : Continuous g) (hsep : IsSeparatedMap g) : T2Space Y := by
  refine ⟨fun y₁ y₂ hne => ?_⟩
  by_cases h : g y₁ = g y₂
  · exact hsep y₁ y₂ h hne
  · obtain ⟨U, V, hU, hV, h1, h2, hd⟩ := t2_separation h
    exact ⟨g ⁻¹' U, g ⁻¹' V, hU.preimage hc, hV.preimage hc, h1, h2, hd.preimage g⟩

/-- **The total space of a local homeomorphism to the plane is weakly locally compact.**  A local
coordinate carries a closed disc back to a compact neighbourhood of the point. -/
theorem weaklyLocallyCompactSpace_of_isLocalHomeomorph (hf : IsLocalHomeomorph f) :
    WeaklyLocallyCompactSpace Y := by
  refine ⟨fun y => ?_⟩
  obtain ⟨e, hy, -⟩ := hf y
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 e.open_target (e y) (e.map_source hy)
  have hhalf : (0 : ℝ) < r / 2 := by linarith
  have hsub : Metric.closedBall (e y) (r / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  refine ⟨e.symm '' Metric.closedBall (e y) (r / 2), ?_, ?_⟩
  · exact (isCompact_closedBall (e y) (r / 2)).image_of_continuousOn (e.continuousOn_symm.mono hsub)
  · have hnb : e ⁻¹' Metric.ball (e y) (r / 2) ∈ 𝓝 y :=
      (e.continuousAt hy).preimage_mem_nhds (Metric.ball_mem_nhds _ hhalf)
    filter_upwards [hnb, e.open_source.mem_nhds hy] with v hv1 hv2
    exact ⟨e v, Metric.ball_subset_closedBall hv1, e.left_inv hv2⟩

/-! ### The fibre-sum functional -/

section Functional

variable (hfin : ∀ z, (f ⁻¹' {z}).Finite)
  (hcov : ∀ z ∈ Set.range f, IsEvenlyCovered f z (f ⁻¹' {z})) (hf : Continuous f)

include hfin hcov hf in
/-- The fibre sum of a compactly supported continuous function is integrable. -/
theorem integrable_fibreSum {F : Y → ℝ} (hFc : Continuous F) (hFs : HasCompactSupport F) :
    Integrable (fibreSum f F) :=
  (continuous_fibreSum hfin hcov hf hFc hFs).integrable_of_hasCompactSupport
    (hasCompactSupport_fibreSum hf hFs)

variable (f) in
/-- **The fibre-sum functional**: a compactly supported continuous function on the total space is
sent to the plane integral of its fibre sum. -/
def coverFunctional : C_c(Y, ℝ) →ₚ[ℝ] ℝ where
  toFun H := ∫ z : ℂ, fibreSum f (⇑H) z
  map_add' H₁ H₂ := by
    have hpt : ∀ z, fibreSum f (⇑(H₁ + H₂)) z = fibreSum f (⇑H₁) z + fibreSum f (⇑H₂) z := by
      intro z
      have hco : (⇑(H₁ + H₂) : Y → ℝ) = fun y => H₁ y + H₂ y := rfl
      rw [hco]
      exact fibreSum_add (hfin z) _ _
    simp only [hpt]
    exact integral_add (integrable_fibreSum hfin hcov hf (map_continuous H₁) H₁.hasCompactSupport)
      (integrable_fibreSum hfin hcov hf (map_continuous H₂) H₂.hasCompactSupport)
  map_smul' c H := by
    have hpt : ∀ z, fibreSum f (⇑(c • H)) z = c * fibreSum f (⇑H) z := by
      intro z
      have hco : (⇑(c • H) : Y → ℝ) = fun y => c * H y := rfl
      rw [hco]
      exact fibreSum_const_mul c _
    simp only [hpt, RingHom.id_apply, smul_eq_mul]
    exact integral_const_mul c _
  monotone' H₁ H₂ hle := by
    refine integral_mono
      (integrable_fibreSum hfin hcov hf (map_continuous H₁) H₁.hasCompactSupport)
      (integrable_fibreSum hfin hcov hf (map_continuous H₂) H₂.hasCompactSupport) fun z => ?_
    exact fibreSum_mono (hfin z) fun y => hle y

@[simp]
theorem coverFunctional_apply (H : C_c(Y, ℝ)) :
    coverFunctional f hfin hcov hf H = ∫ z : ℂ, fibreSum f (⇑H) z := rfl

/-! ### The measure -/

variable [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

variable (f) in
/-- **The measure of a covering**: the measure that the fibre-sum functional represents. -/
def coverMeasure : Measure Y := RealRMK.rieszMeasure (coverFunctional f hfin hcov hf)

/-- **Integration over the total space is integration of fibre sums over the plane.** -/
theorem integral_coverMeasure (H : C_c(Y, ℝ)) :
    ∫ y, H y ∂(coverMeasure f hfin hcov hf) = ∫ z : ℂ, fibreSum f (⇑H) z :=
  RealRMK.integral_rieszMeasure _ H

end Functional

end Rigidity.RET

end
