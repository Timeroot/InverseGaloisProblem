/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Rotation
import InverseGalois.Rigidity.RET.Local.BranchRotation
import InverseGalois.Rigidity.RET.Local.PuiseuxAssembly
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureLoop

/-!
# Inertia from a branch of the roots on a punctured disc

A holomorphic branch of the roots of the equation of a cover, read in the Kummer coordinate
`z = s + uᵉ` on a punctured disc, comes with a companion: rotate the variable by an `e`-th root of
unity and the parameter `z` does not move, so the rotated branch is a second branch of the roots
over exactly the same parameters.  Two such branches differ by a single deck transformation,
because the formulas of the deck group act simply transitively on the roots and the punctured disc
is connected.  That deck transformation is an inertia element at the point.

No topology enters the identification of the deck transformation — the punctured disc is connected,
and that is all the argument uses.  What the topology is still needed for is the *order* of the
element; here only its membership in the inertia group is established.

## Main results

* `Rigidity.RET.LineCover.card_deck_eq_natDegree_complexEquation` — the deck group has as many
  elements as the equation of the cover has roots.
* `Rigidity.RET.LineCover.exists_isInertiaAt_of_branch` — a branch of the roots on a punctured disc
  in the Kummer coordinate produces an inertia element at the point, realized by a formula carrying
  the branch to its rotation.
-/

open Polynomial Filter Topology GeomAKLB

noncomputable section

namespace Rigidity.RET

/-! ### Shrinking the disc away from the exceptional parameters -/

/-- **A small enough punctured disc in the Kummer coordinate avoids any prescribed finite set of
parameters.**  Away from the centre the finite set is closed, so it misses a ball about the centre,
and the Kummer coordinate contracts a disc of radius at most one. -/
theorem exists_puncturedDisc_kummer_avoiding {S : Set ℂ} (hS : S.Finite) (s : ℂ) {e : ℕ}
    (he : 0 < e) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ puncturedDisc (0 : ℂ) ρ, s + u ^ e ∉ S := by
  have hclosed : IsClosed (S \ {s}) := (hS.diff).isClosed
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds (fun h => h.2 rfl))
  refine ⟨min 1 δ, lt_min one_pos hδ, fun u hu => ?_⟩
  rw [mem_puncturedDisc, sub_zero] at hu
  have hune : u ≠ 0 := by simpa using hu.2
  have hle : ‖u‖ ^ e ≤ ‖u‖ :=
    (pow_le_pow_of_le_one (norm_nonneg u) (hu.1.trans_le (min_le_left _ _)).le he).trans_eq
      (pow_one _)
  have hin : s + u ^ e ∈ Metric.ball s δ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_pow]
    exact hle.trans_lt (hu.1.trans_le (min_le_right _ _))
  have hne : s + u ^ e ≠ s := fun h =>
    pow_ne_zero e hune (by simpa using congrArg (fun x => x - s) h)
  exact fun hmem => hball hin ⟨hmem, hne⟩

namespace LineCover

variable (L : LineCover) [Algebra k ℂ] {s : k} {α : L.M}

/-! ### Counting the deck group -/

/-- **The deck group has as many elements as the equation of the cover has roots.**  Both count the
degree of a primitive element over the rational function field. -/
theorem card_deck_eq_natDegree_complexEquation (hα : IsIntegral (Polynomial k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤) :
    Nat.card L.deck = (complexEquation α).natDegree := by
  have h1 : Nat.card L.deck = Module.finrank (RatFunc k) L.M :=
    IsGalois.card_aut_eq_finrank (RatFunc k) L.M
  have h2 : Module.finrank (RatFunc k) L.M = (minpoly (RatFunc k) α).natDegree := by
    rw [← IntermediateField.adjoin.finrank hα.tower_top, hgen, IntermediateField.finrank_top']
  have h3 : (minpoly (RatFunc k) α).natDegree = (minpoly (Polynomial k) α).natDegree := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc k) hα]
    exact (minpoly.monic hα).natDegree_map _
  rw [h1, h2, h3, natDegree_complexEquation]

/-! ### Rotating a punctured disc -/

omit [Algebra k ℂ] in
theorem mul_mem_puncturedDisc {ζ u : ℂ} (hζ : ‖ζ‖ = 1) (hζ0 : ζ ≠ 0) {ρ : ℝ}
    (hu : u ∈ puncturedDisc (0 : ℂ) ρ) : ζ * u ∈ puncturedDisc (0 : ℂ) ρ := by
  rw [mem_puncturedDisc] at hu ⊢
  refine ⟨?_, mul_ne_zero hζ0 (by simpa using hu.2)⟩
  simpa [norm_mul, hζ] using hu.1

/-! ### The inertia element -/

/-- **A branch of the roots on a punctured disc in the Kummer coordinate produces an inertia element
at the point.**  Rotating the variable by an `e`-th root of unity leaves the parameter fixed, so the
rotated branch is a second branch of the roots over the same parameters; a single formula of the
deck group compares the two over the connected punctured disc, and a formula that rotates the branch
rescales the Puiseux expansion of a primitive element, which is what it means to lie in the inertia
group at the point. -/
theorem exists_isInertiaAt_of_branch (D : DeckData α) (hα : IsIntegral (Polynomial k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤) {e : ℕ} (he : 0 < e)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζe : ζ ^ e = 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hbad : ∀ u ∈ puncturedDisc (0 : ℂ) ρ,
      algebraMap k ℂ s + u ^ e ∉ (D.badSetC : Set ℂ))
    {g : ℂ → ℂ} (hcont : ContinuousOn g (puncturedDisc (0 : ℂ) ρ))
    (hroot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ,
      (Analytic.spec (complexEquation α) (algebraMap k ℂ s + u ^ e)).eval (g u) = 0) :
    ∃ τ : L.deck, L.IsInertiaAt s τ ∧ ∀ u ∈ puncturedDisc (0 : ℂ) ρ,
      D.toIntegralDeck.act τ (algebraMap k ℂ s + u ^ e) (g u) = g (ζ * u) := by
  have hζ0 : ζ ≠ 0 := fun h => by simp [h] at hζ
  have hrot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, ζ * u ∈ puncturedDisc (0 : ℂ) ρ :=
    fun _ hu => mul_mem_puncturedDisc hζ hζ0 hu
  have hsep : ∀ u ∈ puncturedDisc (0 : ℂ) ρ,
      (Analytic.spec (complexEquation α) (algebraMap k ℂ s + u ^ e)).Separable :=
    fun u hu => D.separable_spec (hbad u hu)
  -- the branch extends to a germ carrying a primitive element to its Puiseux expansion
  obtain ⟨G, ψ, hGeq, hψ⟩ :=
    exists_germ_puiseuxEmbedding_of_branch s he α hα hgen hρ hsep hcont hroot
  -- one formula compares the branch with its rotation
  haveI : PathConnectedSpace ↥(puncturedDisc (0 : ℂ) ρ) :=
    pathConnectedSpace_puncturedDisc 0 hρ
  haveI : Nonempty ↥(puncturedDisc (0 : ℂ) ρ) := PathConnectedSpace.nonempty
  have hpow : ∀ u : ℂ, (ζ * u) ^ e = u ^ e := fun u => by rw [mul_pow, hζe, one_mul]
  obtain ⟨τ, hτ⟩ := D.toIntegralDeck.toRationalDeck.exists_act_eq_of_isRoot
    (monic_complexEquation hα)
    (L.card_deck_eq_natDegree_complexEquation hα hgen)
    (fun _ hz => D.separable_spec hz)
    (X := ↥(puncturedDisc (0 : ℂ) ρ))
    (w := fun v => algebraMap k ℂ s + (v : ℂ) ^ e)
    (f₁ := fun v => g (v : ℂ)) (f₂ := fun v => g (ζ * (v : ℂ)))
    (by fun_prop) ((continuousOn_iff_continuous_restrict.mp hcont))
    (((continuousOn_iff_continuous_restrict.mp hcont)).comp
      (Continuous.subtype_mk (continuous_const.mul continuous_subtype_val)
        fun v => hrot v v.2))
    (fun v => hbad v v.2) (fun v => hroot v v.2)
    (fun v => by
      have h := hroot (ζ * (v : ℂ)) (hrot v v.2)
      rwa [hpow] at h)
  refine ⟨τ, ?_, fun u hu => hτ ⟨u, hu⟩⟩
  -- a formula that rotates the branch is an inertia element
  refine L.isInertiaAt_of_act_rotate D ψ hψ hα.tower_top hgen hζ0 hζ.le hζe τ ?_ ?_
  · filter_upwards [puncturedDisc_mem_nhdsNE hρ] with u hu
    exact D.eval_ne_zero_of_notMem D.den_dvd (hbad u hu)
  · filter_upwards [puncturedDisc_mem_nhdsNE hρ] with u hu
    rw [hGeq u hu, hGeq _ (hrot u hu)]
    exact hτ ⟨u, hu⟩

end LineCover

end Rigidity.RET

end
