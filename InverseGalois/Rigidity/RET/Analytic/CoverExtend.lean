/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Transport
import InverseGalois.Rigidity.RET.Analytic.PunctureExtend

/-!
# A model over a smaller plane still sees the deck group

A covering cut out by an equation carries the functions of moderate growth that the requirement of
`RET/Analytic/Wall.lean` asks for, and so does any covering homeomorphic over the plane to one.
The algebraization of a covering produces such a model, but only over the complement of a *larger*
finite set: finitely many further parameters are discarded, at which the equation found may
degenerate although the covering does not.  Over those parameters the coordinate of the model is
not defined, so the transported function is not a function on the covering at all.

The gap closes.  Multiply the coordinate by a polynomial in the base coordinate vanishing at the
discarded parameters and extend the product by zero: the product is bounded near a discarded fibre,
because the roots of a monic equation are bounded by its coefficients, and it tends to zero there,
because the damping factor does.  Riemann's theorem on removable singularities then makes the
extension holomorphic across the discarded fibre, in the local coordinate the projection supplies,
and the value zero prescribed there is the right one.  Growth conditions do not see the extension:
they are conditions in the base coordinate, and the extension only adds points over finitely many
parameters.

The damping does not spoil what the function was for.  At a parameter outside the larger set the
damping factor is not zero, so the extended function still separates the points of the fibre, and
a deck transformation moving any point of the covering moves a point over such a parameter: the
points it moves are not confined to finitely many fibres, since a point of the total space has
arbitrarily close neighbours over other parameters.

## Main definitions

* `Rigidity.RET.dampPoly` — the polynomial vanishing at the discarded parameters.
* `Rigidity.RET.dampedCoord` — the coordinate of the model, damped and extended by zero.

## Main results

* `Rigidity.RET.IsHoloAt.of_subtype`, `Rigidity.RET.IsModerate.of_subtype_of_zero` — holomorphy and
  moderate growth transfer from a piece of the total space to the whole of it.
* `Rigidity.RET.dampedCoord_mem_coverRing` — the damped coordinate is a function of moderate growth
  on the whole covering.
* `Rigidity.RET.exists_ne_of_homeo_rootTotal_of_subset` — a covering with an algebraic model over a
  smaller plane has its deck group moved by functions of moderate growth.
-/

open Polynomial Topology

noncomputable section

namespace Rigidity.RET

open Analytic

/-! ### Transfer from a piece of the total space -/

section Subtype

variable {Y : Type*} {f F : Y → ℂ} {S : Finset ℂ}

/-- **Holomorphy at a point of a piece of the total space is holomorphy there.**  A local
coordinate on the piece and a local coordinate on the whole space both invert the projection, so
they agree near the point, and holomorphy may be tested in either. -/
theorem IsHoloAt.of_subtype [TopologicalSpace Y] {U : Set Y} (hf : IsLocalHomeomorph f) {y : Y}
    (hy : y ∈ U)
    (h : IsHoloAt (fun u : ↥U => f (u : Y)) (fun u : ↥U => F (u : Y)) ⟨y, hy⟩) :
    IsHoloAt f F y := by
  obtain ⟨e', he', hana⟩ := h
  obtain ⟨e, hye, hfe⟩ := hf y
  have hchart : IsChartAt f e y := ⟨hye, hfe⟩
  refine ⟨e, hchart, hana.congr ?_⟩
  have hval : ∀ u : ↥U, f (u : Y) = e' u := fun u => congrFun he'.2 u
  have htgt : f y ∈ e'.target := he'.mem_target
  have hy' : ((e'.symm (f y) : ↥U) : Y) = y := congrArg Subtype.val he'.symm_apply
  have hcont : ContinuousAt (fun w : ℂ => ((e'.symm w : ↥U) : Y)) (f y) :=
    continuous_subtype_val.continuousAt.comp (e'.continuousAt_symm htgt)
  have h1 : ∀ᶠ w in 𝓝 (f y), w ∈ e.target :=
    e.open_target.mem_nhds hchart.mem_target
  have h2 : ∀ᶠ w in 𝓝 (f y), w ∈ e'.target := e'.open_target.mem_nhds htgt
  have h3 : ∀ᶠ w in 𝓝 (f y), ((e'.symm w : ↥U) : Y) ∈ e.source := by
    refine hcont.preimage_mem_nhds ?_
    rw [hy']
    exact e.open_source.mem_nhds hye
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  have hfw : f ((e'.symm w : ↥U) : Y) = w := by
    rw [hval (e'.symm w)]
    exact e'.right_inv hw2
  have hfw' : f (e.symm w) = w := by
    rw [congrFun hfe]
    exact e.right_inv hw1
  have heq : ((e'.symm w : ↥U) : Y) = e.symm w := by
    refine e.injOn hw3 (e.map_target hw1) ?_
    rw [← congrFun hfe, ← congrFun hfe, hfw, hfw']
  rw [heq]

/-- **Moderate growth on a piece of the total space, and nothing elsewhere, is moderate growth.**
The estimates are estimates in the base coordinate, and where the function vanishes they hold
outright. -/
theorem IsModerate.of_subtype_of_zero {U : Set Y}
    (h : IsModerate (fun u : ↥U => f (u : Y)) S (fun u : ↥U => F (u : Y)))
    (hzero : ∀ y ∉ U, F y = 0) : IsModerate f S F where
  punct := by
    intro s hs
    obtain ⟨ρ, hρ, C, hC, N, hb⟩ := h.punct s hs
    refine ⟨ρ, hρ, C, hC, N, fun y hy => ?_⟩
    by_cases hyU : y ∈ U
    · exact hb ⟨y, hyU⟩ hy
    · rw [hzero y hyU]
      simpa using hC
  infty := by
    obtain ⟨A, R₀, m, hA, hb⟩ := h.infty
    refine ⟨A, R₀, m, hA, fun y hy => ?_⟩
    by_cases hyU : y ∈ U
    · exact hb ⟨y, hyU⟩ hy
    · rw [hzero y hyU]
      have : (0 : ℝ) ≤ A * ‖f y‖ ^ m := by positivity
      simpa using this

/-- **Fewer punctures is a weaker condition**: the estimates asked at a puncture are asked of a
smaller set of them. -/
theorem IsModerate.mono {S' : Finset ℂ} (hSS : S ⊆ S') (h : IsModerate f S' F) :
    IsModerate f S F where
  punct := fun s hs => h.punct s (hSS hs)
  infty := h.infty

end Subtype

/-! ### The damping factor -/

section Damp

variable {S S' : Finset ℂ}

/-- **The polynomial vanishing at the parameters an algebraic model discards**, and nowhere else.
-/
def dampPoly (S S' : Finset ℂ) : ℂ[X] := ∏ s ∈ S' \ S, (X - C s)

theorem dampPoly_eval (z : ℂ) : (dampPoly S S').eval z = ∏ s ∈ S' \ S, (z - s) := by
  simp [dampPoly, eval_prod]

/-- Outside the larger set of parameters the damping factor does not vanish. -/
theorem dampPoly_eval_ne_zero {z : ℂ} (hz : z ∉ (S' : Set ℂ)) : (dampPoly S S').eval z ≠ 0 := by
  rw [dampPoly_eval]
  refine Finset.prod_ne_zero_iff.2 fun s hs => sub_ne_zero.2 fun hzs => hz ?_
  rw [hzs]
  exact_mod_cast (Finset.mem_sdiff.1 hs).1

/-- At a discarded parameter the damping factor vanishes. -/
theorem dampPoly_eval_eq_zero {z : ℂ} (hz : z ∈ S') (hz' : z ∉ S) :
    (dampPoly S S').eval z = 0 := by
  rw [dampPoly_eval]
  exact Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨hz, hz'⟩) (by ring)

end Damp

/-! ### The damped coordinate -/

section Damped

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {S S' : Finset ℂ}
  {P : Polynomial (Polynomial ℂ)}

open scoped Classical in
/-- **The coordinate of an algebraic model over a smaller plane, damped and extended by zero**: on
the part of the covering the model describes it is the coordinate of the model, multiplied by a
polynomial in the base coordinate vanishing at the parameters the model discards, and over those
parameters it is zero. -/
def dampedCoord (P : Polynomial (Polynomial ℂ)) (S S' : Finset ℂ) (f : Y → ℂ)
    (Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) → RootTotal P S') (y : Y) : ℂ :=
  if hy : y ∈ f ⁻¹' ((S' : Set ℂ)ᶜ) then
    (dampPoly S S').eval (f y) * rootCoord P S' (Φ ⟨y, hy⟩) else 0

variable {Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) → RootTotal P S'}

omit [TopologicalSpace Y] in
theorem dampedCoord_of_mem {y : Y} (hy : y ∈ f ⁻¹' ((S' : Set ℂ)ᶜ)) :
    dampedCoord P S S' f Φ y = (dampPoly S S').eval (f y) * rootCoord P S' (Φ ⟨y, hy⟩) := by
  simp only [dampedCoord, dif_pos hy]

omit [TopologicalSpace Y] in
theorem dampedCoord_of_notMem {y : Y} (hy : y ∉ f ⁻¹' ((S' : Set ℂ)ᶜ)) :
    dampedCoord P S S' f Φ y = 0 := by
  simp only [dampedCoord, dif_neg hy]

omit [TopologicalSpace Y] in
/-- **The damped coordinate is bounded by a polynomial in the base coordinate**, the damping factor
times the Cauchy bound for the roots of the equation. -/
theorem norm_dampedCoord_le (hP : P.Monic)
    (hcomm : ∀ u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)), rootBase P S' (Φ u) = f (u : Y)) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ y : Y,
      ‖dampedCoord P S S' f Φ y‖ ≤ ‖(dampPoly S S').eval (f y)‖ * (C * (1 + ‖f y‖) ^ d) := by
  obtain ⟨C, d, hC, hbd⟩ := exists_root_bound_of_monic hP
  refine ⟨C, d, hC, fun y => ?_⟩
  by_cases hy : y ∈ f ⁻¹' ((S' : Set ℂ)ᶜ)
  · rw [dampedCoord_of_mem hy, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hroot := spec_eval_rootCoord (Φ ⟨y, hy⟩)
    rw [hcomm ⟨y, hy⟩] at hroot
    exact hbd _ _ hroot
  · rw [dampedCoord_of_notMem hy, norm_zero]
    have : (0 : ℝ) ≤ C * (1 + ‖f y‖) ^ d := by positivity
    positivity

omit [TopologicalSpace Y] in
/-- On the part of the covering the model describes, the damped coordinate is the coordinate of
the model times the damping factor. -/
theorem dampedCoord_comp_val :
    (fun u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) => dampedCoord P S S' f Φ (u : Y))
      = fun u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) =>
        (dampPoly S S').eval (f (u : Y)) * rootCoord P S' (Φ u) :=
  funext fun u => dampedCoord_of_mem u.2

/-- **The damped coordinate is of moderate growth**: the coordinate of the model is, the damping
factor is a polynomial in the base coordinate, and the extension by zero adds nothing to estimate.
-/
theorem isModerate_dampedCoord (hSS : S ⊆ S') (hP : P.Monic)
    (Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S')
    (hcomm : ∀ u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)), rootBase P S' (Φ u) = f (u : Y)) :
    IsModerate f S (dampedCoord P S S' f Φ) := by
  refine IsModerate.of_subtype_of_zero ?_ fun y hy => dampedCoord_of_notMem hy
  have hdamp : IsModerate (fun u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) => f (u : Y)) S
      fun u => (dampPoly S S').eval (f (u : Y)) :=
    isModerate_polynomial _ S (dampPoly S S')
  have hcoord : IsModerate (fun u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) => f (u : Y)) S
      fun u => rootCoord P S' (Φ u) :=
    ((isModerate_rootCoord (S := S') hP).comp_homeo Φ hcomm).mono hSS
  rw [dampedCoord_comp_val]
  exact hdamp.mul hcoord

/-! ### Holomorphy of the damped coordinate -/

/-- The part of the covering an algebraic model describes is open. -/
theorem isOpen_preimage_compl (hf : IsLocalHomeomorph f) (S' : Finset ℂ) :
    IsOpen (f ⁻¹' ((S' : Set ℂ)ᶜ)) :=
  (S'.finite_toSet.isClosed.isOpen_compl).preimage hf.continuous

/-- The projection restricted to the part an algebraic model describes is again a local
homeomorphism. -/
theorem isLocalHomeomorph_val (hf : IsLocalHomeomorph f) (S' : Finset ℂ) :
    IsLocalHomeomorph fun u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) => f (u : Y) :=
  hf.comp (isOpen_preimage_compl hf S').isOpenEmbedding_subtypeVal.isLocalHomeomorph

/-- **Over a parameter the model keeps, the damped coordinate is holomorphic**: it is the
coordinate of the model, which is holomorphic there, times a polynomial in the base coordinate. -/
theorem isHoloAt_dampedCoord_of_mem (hf : IsLocalHomeomorph f) (hP : P.Monic)
    (hsep : ∀ z ∉ (S' : Set ℂ), (spec P z).Separable)
    (Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S')
    (hcomm : ∀ u, rootBase P S' (Φ u) = f (u : Y))
    {y : Y} (hy : y ∈ f ⁻¹' ((S' : Set ℂ)ᶜ)) :
    IsHoloAt f (dampedCoord P S S' f Φ) y := by
  refine IsHoloAt.of_subtype hf hy ?_
  rw [dampedCoord_comp_val]
  have hf' := isLocalHomeomorph_val hf S'
  have h₁ : IsHoloAt (fun u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) => f (u : Y))
      (fun u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) => (dampPoly S S').eval (f (u : Y))) ⟨y, hy⟩ :=
    isHoloAt_comp_of_analyticAt hf' ((dampPoly S S').differentiable.analyticAt _)
  have h₂ : IsHoloAt (fun u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) => f (u : Y))
      (fun u : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) => rootCoord P S' (Φ u)) ⟨y, hy⟩ :=
    (isHolo_rootCoord hP hsep).comp_homeo Φ hcomm ⟨y, hy⟩
  exact h₁.mul h₂

/-- **Over a parameter the model discards, the damped coordinate is holomorphic too.**

In the local coordinate the projection supplies, the damped coordinate is a holomorphic function on
a punctured disc, bounded there because the roots of a monic equation are bounded by its
coefficients; Riemann's theorem on removable singularities extends it analytically across the
puncture, and the extension takes the value zero there because the damping factor does. -/
theorem isHoloAt_dampedCoord_of_notMem (hf : IsLocalHomeomorph f) (hP : P.Monic)
    (hsep : ∀ z ∉ (S' : Set ℂ), (spec P z).Separable)
    (Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S')
    (hcomm : ∀ u, rootBase P S' (Φ u) = f (u : Y))
    (hS : ∀ y : Y, f y ∉ (S : Set ℂ)) {y₀ : Y} (hy₀ : y₀ ∉ f ⁻¹' ((S' : Set ℂ)ᶜ)) :
    IsHoloAt f (dampedCoord P S S' f Φ) y₀ := by
  classical
  set z₀ := f y₀ with hz₀def
  have hz₀ : z₀ ∈ (S' : Set ℂ) := by simpa using hy₀
  obtain ⟨e, hye, hfe⟩ := hf y₀
  have hchart : IsChartAt f e y₀ := ⟨hye, hfe⟩
  refine ⟨e, hchart, ?_⟩
  set c : ℂ → ℂ := fun w => dampedCoord P S S' f Φ (e.symm w) with hcdef
  -- a punctured disc around the discarded parameter, inside the chart and missing the others
  have hVopen : IsOpen (e.target ∩ ((S' : Set ℂ) \ {z₀})ᶜ) :=
    e.open_target.inter S'.finite_toSet.diff.isClosed.isOpen_compl
  have hz₀V : z₀ ∈ e.target ∩ ((S' : Set ℂ) \ {z₀})ᶜ :=
    ⟨hchart.mem_target, fun h => h.2 rfl⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hVopen z₀ hz₀V
  have hmemtgt : ∀ w ∈ Metric.ball z₀ ρ, w ∈ e.target := fun w hw => (hball hw).1
  have hfsymm : ∀ w ∈ Metric.ball z₀ ρ, f (e.symm w) = w := fun w hw => by
    rw [congrFun hfe]; exact e.right_inv (hmemtgt w hw)
  have hgood : ∀ w ∈ Metric.ball z₀ ρ \ {z₀}, e.symm w ∈ f ⁻¹' ((S' : Set ℂ)ᶜ) := by
    intro w hw
    have : f (e.symm w) = w := hfsymm w hw.1
    simp only [Set.mem_preimage, this, Set.mem_compl_iff]
    exact fun hwS => (hball hw.1).2 ⟨hwS, by simpa using hw.2⟩
  -- the damped coordinate is holomorphic off the puncture
  have hd : DifferentiableOn ℂ c (Metric.ball z₀ ρ \ {z₀}) := by
    intro w hw
    have hsrc : e.symm w ∈ e.source := e.map_target (hmemtgt w hw.1)
    have hcw : IsChartAt f e (e.symm w) := ⟨hsrc, hfe⟩
    have := (isHoloAt_dampedCoord_of_mem (S := S) hf hP hsep Φ hcomm
      (hgood w hw)).analyticAt_of_chart hcw
    rw [hfsymm w hw.1] at this
    exact this.differentiableAt.differentiableWithinAt
  -- and bounded there, by the damping factor times the Cauchy bound for the roots
  obtain ⟨C, d, hC, hbd⟩ := norm_dampedCoord_le (S := S) (Φ := Φ) hP hcomm
  set K : ℝ := C * (1 + (‖z₀‖ + ρ)) ^ d with hKdef
  have hK : 0 ≤ K := by positivity
  have hbound : ∀ w ∈ Metric.ball z₀ ρ, ‖c w‖ ≤ ‖(dampPoly S S').eval w‖ * K := by
    intro w hw
    have h₁ := hbd (e.symm w)
    rw [hfsymm w hw] at h₁
    refine h₁.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have hwR : ‖w‖ ≤ ‖z₀‖ + ρ := by
      have : ‖w - z₀‖ < ρ := by simpa [Complex.dist_eq] using Metric.mem_ball.1 hw
      calc ‖w‖ = ‖z₀ + (w - z₀)‖ := by ring_nf
        _ ≤ ‖z₀‖ + ‖w - z₀‖ := norm_add_le _ _
        _ ≤ ‖z₀‖ + ρ := by linarith
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) d) hC
  obtain ⟨B, hB⟩ := (isCompact_closedBall z₀ ρ).exists_bound_of_continuousOn
    (Polynomial.continuous (dampPoly S S')).continuousOn
  have hbdd : BddAbove (norm ∘ c '' (Metric.ball z₀ ρ \ {z₀})) := by
    refine ⟨B * K, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    refine (hbound w hw.1).trans (mul_le_mul_of_nonneg_right ?_ hK)
    exact hB w (Metric.ball_subset_closedBall hw.1)
  obtain ⟨c', hc'A, hc'eq⟩ := exists_analyticAt_of_bddAbove hρ hd hbdd
  -- the value the extension takes at the puncture is zero, the value prescribed there
  have hcz₀ : c z₀ = 0 := by
    have : e.symm z₀ = y₀ := hchart.symm_apply
    rw [hcdef]
    simp only [this]
    exact dampedCoord_of_notMem hy₀
  have hpunct : Metric.ball z₀ ρ \ {z₀} ∈ 𝓝[≠] z₀ := by
    refine Filter.inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hρ)) ?_
    exact self_mem_nhdsWithin
  have htend : Filter.Tendsto c' (𝓝[≠] z₀) (𝓝 0) := by
    have hzero : Filter.Tendsto (fun w => ‖(dampPoly S S').eval w‖ * K) (𝓝[≠] z₀) (𝓝 0) := by
      have hcont : Filter.Tendsto (fun w => ‖(dampPoly S S').eval w‖ * K) (𝓝 z₀)
          (𝓝 (‖(dampPoly S S').eval z₀‖ * K)) :=
        (((Polynomial.continuous (dampPoly S S')).norm).continuousAt).mul tendsto_const_nhds
      have hev : (dampPoly S S').eval z₀ = 0 :=
        dampPoly_eval_eq_zero (by exact_mod_cast hz₀) (by simpa using hS y₀)
      rw [hev] at hcont
      simpa using hcont.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [hpunct] with w hw
    rw [hc'eq w hw]
    exact hbound w hw.1
  have hc'z₀ : c' z₀ = 0 := by
    have hcont : Filter.Tendsto c' (𝓝[≠] z₀) (𝓝 (c' z₀)) :=
      hc'A.continuousAt.continuousWithinAt
    exact tendsto_nhds_unique hcont htend
  -- so the extension agrees with the damped coordinate near the puncture
  refine hc'A.congr ?_
  filter_upwards [Metric.ball_mem_nhds z₀ hρ] with w hw
  by_cases hwz : w = z₀
  · rw [hwz, hc'z₀, hcz₀]
  · exact hc'eq w ⟨hw, hwz⟩

/-- **The damped coordinate is holomorphic on the whole covering.** -/
theorem isHolo_dampedCoord (hf : IsLocalHomeomorph f) (hP : P.Monic)
    (hsep : ∀ z ∉ (S' : Set ℂ), (spec P z).Separable)
    (Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S')
    (hcomm : ∀ u, rootBase P S' (Φ u) = f (u : Y))
    (hS : ∀ y : Y, f y ∉ (S : Set ℂ)) :
    IsHolo f (dampedCoord P S S' f Φ) := by
  intro y
  by_cases hy : y ∈ f ⁻¹' ((S' : Set ℂ)ᶜ)
  · exact isHoloAt_dampedCoord_of_mem hf hP hsep Φ hcomm hy
  · exact isHoloAt_dampedCoord_of_notMem hf hP hsep Φ hcomm hS hy

/-- **The damped coordinate is a function of moderate growth on the covering.** -/
theorem dampedCoord_mem_coverRing (hf : IsLocalHomeomorph f) (hSS : S ⊆ S') (hP : P.Monic)
    (hsep : ∀ z ∉ (S' : Set ℂ), (spec P z).Separable)
    (Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S')
    (hcomm : ∀ u, rootBase P S' (Φ u) = f (u : Y))
    (hS : ∀ y : Y, f y ∉ (S : Set ℂ)) :
    dampedCoord P S S' f Φ ∈ coverRing hf S :=
  ⟨isHolo_dampedCoord hf hP hsep Φ hcomm hS, isModerate_dampedCoord hSS hP Φ hcomm⟩

end Damped

/-! ### The deck group of a covering with a model over a smaller plane -/

section Deck

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {S S' : Finset ℂ}
  {P : Polynomial (Polynomial ℂ)}
variable {H : Type*} [Group H] [MulAction H Y] [ContinuousConstSMul H Y]

/-- **A deck transformation of a connected covering fixing one point is the identity.**  The two
lifts of the projection it compares — the transformation and the identity — agree at that point,
and the projection is separated and locally injective, so they agree everywhere. -/
theorem smul_ne_self_of_ne_one [PreconnectedSpace Y] (hf : IsLocalHomeomorph f)
    (hsepmap : IsSeparatedMap f) [FaithfulSMul H Y] [IsOverBase H f] {a : H} (ha : a ≠ 1)
    (y : Y) : a • y ≠ y := by
  intro hy
  refine ha ?_
  have heq : (fun y : Y => a • y) = id :=
    hsepmap.eq_of_comp_eq hf.isLocallyInjective (continuous_const_smul a) continuous_id
      (funext fun y' => IsOverBase.smul_eq (f := f) a y') y hy
  exact eq_of_smul_eq_smul (α := Y) fun y' => by rw [one_smul]; exact congrFun heq y'

/-- **A covering with an algebraic model over a smaller plane has its deck group moved by functions
of moderate growth.**

The coordinate of the model, damped and extended by zero, is such a function, and over a parameter
the model keeps the damping factor does not vanish, so the function still distinguishes the points
of that fibre; a deck transformation of a connected covering that is not the identity moves every
point, in particular one over such a parameter. -/
theorem exists_ne_of_homeo_rootTotal_of_subset [PreconnectedSpace Y] (hf : IsLocalHomeomorph f)
    (hsepmap : IsSeparatedMap f) (hrange : Set.range f = ((S : Set ℂ))ᶜ) (hSS : S ⊆ S')
    (hP : P.Monic) (hsep : ∀ z ∉ (S' : Set ℂ), (spec P z).Separable)
    (Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S')
    (hcomm : ∀ u, rootBase P S' (Φ u) = f (u : Y))
    [FaithfulSMul H Y] [IsOverBase H f] (a : H) (ha : a ≠ 1) :
    ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y := by
  have hS : ∀ y : Y, f y ∉ (S : Set ℂ) := fun y => by
    have : f y ∈ Set.range f := ⟨y, rfl⟩
    rwa [hrange] at this
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset S'
  obtain ⟨y, rfl⟩ : ∃ y : Y, f y = z := by
    have : z ∈ Set.range f := by
      rw [hrange]
      exact fun h => hz (hSS (by exact_mod_cast h))
    exact this
  have hy : y ∈ f ⁻¹' ((S' : Set ℂ)ᶜ) := fun h => hz (by exact_mod_cast h)
  have hfa : f (a • y) = f y := IsOverBase.smul_eq (f := f) a y
  have hay : a • y ∈ f ⁻¹' ((S' : Set ℂ)ᶜ) := by
    simp only [Set.mem_preimage, hfa]
    exact hy
  refine ⟨dampedCoord P S S' f Φ, dampedCoord_mem_coverRing hf hSS hP hsep Φ hcomm hS, y,
    fun hval => smul_ne_self_of_ne_one (H := H) hf hsepmap ha y ?_⟩
  rw [dampedCoord_of_mem hay, dampedCoord_of_mem hy, hfa] at hval
  have hcoord := mul_left_cancel₀ (dampPoly_eval_ne_zero (S := S) hy) hval
  have hbase : rootBase P S' (Φ ⟨a • y, hay⟩) = rootBase P S' (Φ ⟨y, hy⟩) := by
    rw [hcomm, hcomm]
    exact hfa
  exact congrArg Subtype.val (Φ.injective (eq_of_rootBase_eq_of_rootCoord_eq hbase hcoord))

end Deck

end Rigidity.RET

end
