/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.PunctureExtend
import InverseGalois.Rigidity.RET.Analytic.Rational

/-!
# From growth conditions to rationality

Two criteria, both stated for a bare function of a complex variable, turn growth conditions into
rationality.

The local one is that a function analytic on a punctured disc, with some fixed power of the
distance to the puncture times it bounded there, is meromorphic at the puncture: the product with
that power extends analytically across the puncture by Riemann's theorem, and dividing back gives
exactly the form of a meromorphic germ.

The global one assembles the local statement over a finite set of punctures with polynomial growth
at infinity: such a function is a quotient of two polynomials.  Growth is only ever assumed away
from the punctures, where the function is analytic; shrinking each disc so that it meets no other
puncture, and pushing the threshold at infinity past all of them, is enough to see that this is no
weaker.

## Main results

* `Rigidity.RET.meromorphicAt_of_growth` — moderate growth at a puncture makes an analytic function
  meromorphic there.
* `Rigidity.RET.exists_rational_of_growth` — a function analytic off a finite set, of moderate
  growth at each of its points and at infinity, is a quotient of two polynomials.
-/

open Topology Polynomial

noncomputable section

namespace Rigidity.RET

/-- **Moderate growth at a puncture makes an analytic function meromorphic there**: a fixed power
of the distance to the puncture times the function is bounded, hence extends analytically across
it. -/
theorem meromorphicAt_of_growth {c : ℂ → ℂ} {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hana : ∀ z ∈ Metric.ball s ρ \ {s}, AnalyticAt ℂ c z)
    {B : ℝ} {N : ℕ} (hbdd : ∀ z ∈ Metric.ball s ρ \ {s}, ‖c z‖ * ‖z - s‖ ^ N ≤ B) :
    MeromorphicAt c s := by
  have hdiff : DifferentiableOn ℂ (fun z => (z - s) ^ N * c z) (Metric.ball s ρ \ {s}) := by
    intro z hz
    refine AnalyticAt.differentiableAt ?_ |>.differentiableWithinAt
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul (hana z hz)
  have hbd : BddAbove (norm ∘ (fun z => (z - s) ^ N * c z) '' (Metric.ball s ρ \ {s})) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    calc ‖(z - s) ^ N * c z‖ = ‖c z‖ * ‖z - s‖ ^ N := by
          rw [norm_mul, norm_pow]
          ring
      _ ≤ B := hbdd z hz
  obtain ⟨c', hc'A, hc'eq⟩ := exists_analyticAt_of_bddAbove hρ hdiff hbd
  refine ⟨N + 1, ?_⟩
  have hagree : ∀ z ∈ Metric.ball s ρ, (z - s) ^ (N + 1) • c z = (z - s) * c' z := by
    intro z hz
    by_cases hzs : z = s
    · subst hzs
      simp
    · rw [hc'eq z ⟨hz, by simpa using hzs⟩, smul_eq_mul, pow_succ]
      ring
  refine AnalyticAt.congr (f := fun z => (z - s) * c' z)
    ((analyticAt_id.sub analyticAt_const).mul hc'A) ?_
  filter_upwards [Metric.ball_mem_nhds s hρ] with z hz
  exact (hagree z hz).symm

/-- **A function analytic off a finite set, of moderate growth at each of its points and at
infinity, is rational.**

The denominator is a monic polynomial vanishing only on the finite set, and the identity
`q z * c z = p z` holds at every point of the plane. -/
theorem exists_rational_of_growth (S : Finset ℂ) {c : ℂ → ℂ}
    (hana : ∀ z ∉ S, AnalyticAt ℂ c z)
    (hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ (B : ℝ) (N : ℕ),
      ∀ z ∈ Metric.ball s ρ \ {s}, z ∉ S → ‖c z‖ * ‖z - s‖ ^ N ≤ B)
    {A R₀ : ℝ} {m : ℕ} (hinf : ∀ z : ℂ, R₀ ≤ ‖z‖ → z ∉ S → ‖c z‖ ≤ A * ‖z‖ ^ m) :
    ∃ p q : ℂ[X], q.Monic ∧ (∀ z ∉ S, q.eval z ≠ 0) ∧ ∀ z : ℂ, q.eval z * c z = p.eval z := by
  -- At a puncture the function is meromorphic, once the disc is shrunk to miss the other punctures.
  have hmero : ∀ s ∈ S, MeromorphicAt c s := by
    intro s hs
    obtain ⟨ρ, hρ, B, N, hbdd⟩ := hpunct s hs
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.1 (S.erase s).finite_toSet.isClosed.isOpen_compl s
      (by simp)
    have hρ' : 0 < min ρ ρ₀ := lt_min hρ hρ₀
    have hnotS : ∀ z ∈ Metric.ball s (min ρ ρ₀) \ ({s} : Set ℂ), z ∉ S := by
      intro z hz hzS
      have h1 : z ∉ (S.erase s : Set ℂ) :=
        hball (Metric.ball_subset_ball (min_le_right _ _) hz.1)
      refine h1 ?_
      simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨hzS, by simpa using hz.2⟩
    refine meromorphicAt_of_growth hρ' (fun z hz => hana z (hnotS z hz)) (B := B) (N := N) ?_
    intro z hz
    exact hbdd z ⟨Metric.ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩ (hnotS z hz)
  -- Far enough out there are no punctures left, so the growth bound holds unconditionally.
  obtain ⟨Bs, hBs⟩ := (S.image fun s : ℂ => ‖s‖).exists_le
  have hgrowth : ∀ z : ℂ, max R₀ (Bs + 1) ≤ ‖z‖ → ‖c z‖ ≤ A * ‖z‖ ^ m := by
    intro z hz
    refine hinf z (le_trans (le_max_left _ _) hz) fun hzS => ?_
    have h1 : ‖z‖ ≤ Bs := hBs _ (Finset.mem_image_of_mem (fun s : ℂ => ‖s‖) hzS)
    have h2 : Bs + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
    linarith
  exact exists_rational_of_meromorphic_of_growth S hana hmero hgrowth

end Rigidity.RET

end
