/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Growth

/-!
# Holomorphic extension across a finite set

A function holomorphic away from a finite set of points and bounded near each of them extends
holomorphically across the whole set: this is the removable singularity theorem applied one point
at a time.  The extension is canonical — at each removed point the value is the limit of the
function along the punctured neighbourhood — so it can be written down as a single function rather
than produced by an induction.

Combined with the fact that an entire function of polynomial growth is a polynomial, this gives the
criterion used to recover algebra from analysis: a function holomorphic off a finite set, locally
bounded at each of those points, and of polynomial growth at infinity, agrees off the finite set
with a polynomial.

## Main results

* `Rigidity.RET.Analytic.differentiable_fillIn` — the canonical extension across a finite set is
  entire.
* `Rigidity.RET.Analytic.exists_polynomial_of_bounded_of_growth` — holomorphic off a finite set,
  locally bounded there, and of polynomial growth, implies polynomial.
-/

open Filter Topology

noncomputable section

namespace Rigidity.RET.Analytic

open scoped Classical in
/-- The **canonical extension** of a function across a set: at each point of the set the value is
replaced by the limit of the function along the punctured neighbourhood of that point. -/
def fillIn (S : Set ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if z ∈ S then limUnder (𝓝[≠] z) f else f z

/-- Away from the set, the canonical extension is the original function. -/
theorem fillIn_of_notMem {S : Set ℂ} {f : ℂ → ℂ} {z : ℂ} (hz : z ∉ S) : fillIn S f z = f z := by
  simp only [fillIn, if_neg hz]

/-- **The canonical extension across a finite set is entire** as soon as the function is
holomorphic off the set and bounded near each of its points. -/
theorem differentiable_fillIn {S : Set ℂ} (hS : S.Finite) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Sᶜ)
    (hbdd : ∀ c ∈ S, ∃ C ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball c ε, z ≠ c → ‖f z‖ ≤ C) :
    Differentiable ℂ (fillIn S f) := by
  have hSc : IsOpen (Sᶜ) := hS.isClosed.isOpen_compl
  intro x
  by_cases hx : x ∈ S
  · obtain ⟨C, ε, hε, hCε⟩ := hbdd x hx
    have hclosed : IsClosed (S \ {x}) := (hS.subset Set.diff_subset).isClosed
    obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl x (by simp)
    have hr0 : 0 < min ε δ := lt_min hε hδ
    have hsub : Metric.ball x (min ε δ) \ {x} ⊆ Sᶜ := by
      rintro z ⟨hz, hzx⟩
      have hzδ := hδS (Metric.ball_subset_ball (min_le_right ε δ) hz)
      simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_singleton_iff, not_and,
        not_not] at hzδ
      intro hzS
      exact hzx (hzδ hzS)
    have hs : Metric.ball x (min ε δ) ∈ 𝓝 x := Metric.ball_mem_nhds x hr0
    have hd : DifferentiableOn ℂ f (Metric.ball x (min ε δ) \ {x}) := hf.mono hsub
    have hb : BddAbove (norm ∘ f '' (Metric.ball x (min ε δ) \ {x})) := by
      refine ⟨C, ?_⟩
      rintro y ⟨z, ⟨hz, hzx⟩, rfl⟩
      exact hCε z (Metric.ball_subset_ball (min_le_left ε δ) hz) hzx
    have H := Complex.differentiableOn_update_limUnder_of_bddAbove hs hd hb
    have heq : fillIn S f =ᶠ[𝓝 x] Function.update f x (limUnder (𝓝[≠] x) f) := by
      filter_upwards [hs] with z hz
      by_cases hzx : z = x
      · subst hzx
        simp [fillIn, hx]
      · have hzS : z ∉ S := hsub ⟨hz, hzx⟩
        simp [fillIn, hzS, hzx]
    exact (H.differentiableAt hs).congr_of_eventuallyEq heq
  · have hmem : Sᶜ ∈ 𝓝 x := hSc.mem_nhds hx
    have heq : fillIn S f =ᶠ[𝓝 x] f := by
      filter_upwards [hmem] with z hz
      exact fillIn_of_notMem hz
    exact (hf.differentiableAt hmem).congr_of_eventuallyEq heq

/-- **Holomorphic off a finite set, locally bounded there, and of polynomial growth implies
polynomial.**  The removable singularities are filled in, and the resulting entire function of
polynomial growth is a polynomial. -/
theorem exists_polynomial_of_bounded_of_growth {S : Set ℂ} (hS : S.Finite) {f : ℂ → ℂ}
    {Cg R : ℝ} {n : ℕ} (hf : DifferentiableOn ℂ f Sᶜ)
    (hbdd : ∀ c ∈ S, ∃ C ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball c ε, z ≠ c → ‖f z‖ ≤ C)
    (hgrowth : ∀ z ∉ S, R ≤ ‖z‖ → ‖f z‖ ≤ Cg * (1 + ‖z‖) ^ n) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ ∀ z ∉ S, f z = p.eval z := by
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.1 hS.isBounded
  have hgrow' : ∀ z : ℂ, max R (R₀ + 1) ≤ ‖z‖ → ‖fillIn S f z‖ ≤ Cg * (1 + ‖z‖) ^ n := by
    intro z hz
    have hzS : z ∉ S := by
      intro h
      have h1 := hR₀ z h
      have h2 : R₀ + 1 ≤ ‖z‖ := le_trans (le_max_right R (R₀ + 1)) hz
      linarith
    rw [fillIn_of_notMem hzS]
    exact hgrowth z hzS (le_trans (le_max_left R (R₀ + 1)) hz)
  obtain ⟨p, hpdeg, hp⟩ :=
    exists_polynomial_of_growth_le (differentiable_fillIn hS hf hbdd) hgrow'
  exact ⟨p, hpdeg, fun z hz => (fillIn_of_notMem hz).symm.trans (hp z)⟩

end Rigidity.RET.Analytic

end
