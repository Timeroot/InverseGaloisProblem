/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverSymm

/-!
# The equation of a bounded function extends across a puncture

The coefficients of the equation satisfied by a holomorphic function on a covering are analytic
wherever the covering is, and no further: at a puncture there is nothing to evaluate them at.  If
the function is *bounded* near the puncture, however, so are the coefficients — each is, up to
sign, an elementary symmetric function of finitely many of its values — and a bounded analytic
function on a punctured disc extends analytically across the puncture, by Riemann's theorem on
removable singularities.

So a holomorphic function bounded near a puncture satisfies an equation whose coefficients are
analytic on the *whole* disc.  This is the local half of the statement that the equation of a tame
cover is algebraic: what remains is the behaviour at infinity.

## Main results

* `Rigidity.RET.norm_esymm_le` — an elementary symmetric function of bounded numbers is bounded.
* `Rigidity.RET.norm_coeff_multiset_prod_X_sub_C_le`, `Rigidity.RET.norm_coeff_prod_X_sub_C_le` —
  the coefficients of a monic product of linear factors with bounded roots are bounded.
* `Rigidity.RET.exists_analyticAt_of_bddAbove` — Riemann's removable singularity theorem, in the
  form used here.
* `Rigidity.RET.exists_analyticAt_coeff_of_bounded` — the coefficients of the equation satisfied by
  a function bounded near a puncture extend analytically across it.
-/

open Topology Polynomial

noncomputable section

namespace Rigidity.RET

/-! ### Bounds on symmetric functions -/

/-- A product of numbers of norm at most `M` has norm at most a power of `M`. -/
theorem norm_multiset_prod_le_pow {M : ℝ} (hM : 0 ≤ M) (t : Multiset ℂ) :
    (∀ r ∈ t, ‖r‖ ≤ M) → ‖t.prod‖ ≤ M ^ Multiset.card t := by
  refine Multiset.induction_on t (fun _ => by simp) ?_
  intro a s ih h
  rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
  have h1 : ‖a‖ ≤ M := h a (Multiset.mem_cons_self a s)
  have h2 : ‖s.prod‖ ≤ M ^ Multiset.card s := ih fun r hr => h r (Multiset.mem_cons_of_mem hr)
  calc ‖a‖ * ‖s.prod‖ ≤ M * M ^ Multiset.card s := mul_le_mul h1 h2 (norm_nonneg _) hM
    _ = M ^ Multiset.card s * M := mul_comm _ _

/-- **An elementary symmetric function of numbers of norm at most `M` is bounded** by the number of
its terms times a power of `M`. -/
theorem norm_esymm_le {M : ℝ} (hM : 0 ≤ M) {s : Multiset ℂ} (h : ∀ r ∈ s, ‖r‖ ≤ M) (k : ℕ) :
    ‖s.esymm k‖ ≤ (Multiset.card s).choose k * M ^ k := by
  rw [Multiset.esymm]
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  refine (Multiset.sum_le_card_nsmul _ (M ^ k) ?_).trans ?_
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hx
    have hcard : Multiset.card t = k := (Multiset.mem_powersetCard.1 ht).2
    have hle := norm_multiset_prod_le_pow hM t fun r hr =>
      h r (Multiset.mem_of_le (Multiset.mem_powersetCard.1 ht).1 hr)
    rw [hcard] at hle
    exact hle
  · rw [Multiset.card_map, Multiset.card_powersetCard, nsmul_eq_mul]

/-- **The coefficients of a monic product of linear factors with bounded roots are bounded**, by a
bound depending only on the number of factors and on the bound on the roots. -/
theorem norm_coeff_multiset_prod_X_sub_C_le {t : Multiset ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ r ∈ t, ‖r‖ ≤ M) (k : ℕ) :
    ‖((t.map fun r => X - C r).prod).coeff k‖
      ≤ 2 ^ Multiset.card t * max M 1 ^ Multiset.card t := by
  have hM1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  have hbound : ∀ j ≤ Multiset.card t,
      ‖t.esymm j‖ ≤ 2 ^ Multiset.card t * max M 1 ^ Multiset.card t := by
    intro j hj
    refine (norm_esymm_le hM h j).trans ?_
    have h1 : ((Multiset.card t).choose j : ℝ) ≤ 2 ^ Multiset.card t := by
      exact_mod_cast Nat.choose_le_two_pow (Multiset.card t) j
    have hone : (1 : ℝ) ≤ max M 1 ^ (Multiset.card t - j) := by
      simpa using pow_le_pow_left₀ zero_le_one hM1 (Multiset.card t - j)
    have hsplit : max M 1 ^ Multiset.card t
        = max M 1 ^ j * max M 1 ^ (Multiset.card t - j) := by
      rw [← pow_add]
      congr 1
      omega
    have h2 : M ^ j ≤ max M 1 ^ Multiset.card t :=
      (pow_le_pow_left₀ hM (le_max_left M 1) j).trans
        (hsplit ▸ le_mul_of_one_le_right (pow_nonneg (le_trans zero_le_one hM1) j) hone)
    exact mul_le_mul h1 h2 (pow_nonneg hM j) (by positivity)
  by_cases hk : k ≤ Multiset.card t
  · rw [Multiset.prod_X_sub_C_coeff _ hk, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hbound _ (by omega)
  · have hdeg : ((t.map fun r => X - C r).prod).natDegree = Multiset.card t :=
      natDegree_multiset_prod_X_sub_C_eq_card t
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega), norm_zero]
    positivity

/-- **The coefficients of a monic product of linear factors indexed by a finite set with bounded
roots are bounded.** -/
theorem norm_coeff_prod_X_sub_C_le {ι : Type*} (e : Finset ι) (r : ι → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i ∈ e, ‖r i‖ ≤ M) (k : ℕ) :
    ‖(∏ i ∈ e, (X - C (r i))).coeff k‖ ≤ 2 ^ e.card * max M 1 ^ e.card := by
  have hrw : (∏ i ∈ e, (X - C (r i))) = ((e.val.map r).map fun w => X - C w).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  have hmem : ∀ w ∈ e.val.map r, ‖w‖ ≤ M := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hw
    exact h i hi
  rw [hrw]
  simpa using norm_coeff_multiset_prod_X_sub_C_le hM hmem k

section Coeff

variable {Y : Type*} {g : Y → ℂ} {H : Type*} [Group H] [Fintype H] [MulAction H Y]

/-- **The coefficients of the orbit polynomial of a bounded function are bounded**, by a bound
depending only on the order of the group and on the bound on the function. -/
theorem norm_coeff_orbitPoly_le {y : Y} {M : ℝ} (hM : 0 ≤ M) (hb : ∀ a : H, ‖g (a • y)‖ ≤ M)
    (k : ℕ) :
    ‖(orbitPoly H g y).coeff k‖ ≤ 2 ^ Fintype.card H * max M 1 ^ Fintype.card H := by
  have hval : ∀ r ∈ orbitValues H g y, ‖r‖ ≤ M := by
    intro r hr
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hr
    exact hb a
  rw [orbitPoly]
  simpa [card_orbitValues] using norm_coeff_multiset_prod_X_sub_C_le hM hval k

end Coeff

/-! ### Removable singularities -/

/-- **Riemann's removable singularity theorem**: a function differentiable on a punctured disc and
bounded there agrees, off the puncture, with a function analytic at the puncture. -/
theorem exists_analyticAt_of_bddAbove {c : ℂ → ℂ} {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ c (Metric.ball s ρ \ {s}))
    (hb : BddAbove (norm ∘ c '' (Metric.ball s ρ \ {s}))) :
    ∃ c' : ℂ → ℂ, AnalyticAt ℂ c' s ∧ ∀ z ∈ Metric.ball s ρ \ {s}, c' z = c z := by
  have hnhds : Metric.ball s ρ ∈ 𝓝 s := Metric.ball_mem_nhds s hρ
  refine ⟨Function.update c s (limUnder (𝓝[≠] s) c), ?_, fun z hz => ?_⟩
  · exact (Complex.differentiableOn_update_limUnder_of_bddAbove hnhds hd hb).analyticAt hnhds
  · exact Function.update_of_ne (by simpa using hz.2) _ _

/-! ### The equation of a bounded function near a puncture -/

section Bounded

variable {Y : Type*} [TopologicalSpace Y] {f g : Y → ℂ}
variable {H : Type*} [Group H] [Fintype H] [MulAction H Y] [ContinuousConstSMul H Y]

/-- **The coefficients of the equation satisfied by a function bounded near a puncture extend
analytically across the puncture.**

Over a punctured disc entirely covered by the total space, the coefficients of the orbit polynomial
of a bounded holomorphic function are bounded analytic functions, so Riemann's theorem fills the
puncture in. -/
theorem exists_analyticAt_coeff_of_bounded (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsurj : Metric.ball s ρ \ {s} ⊆ Set.range f)
    {M : ℝ} (hM : 0 ≤ M) (hbdd : ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖g y‖ ≤ M) (k : ℕ) :
    ∃ c : ℂ → ℂ, AnalyticAt ℂ c s ∧
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → (orbitPoly H g y).coeff k = c (f y) := by
  obtain ⟨c₀, hc₀, hac₀⟩ := exists_analytic_orbitPoly_coeff hf hover htrans hg k
  have hana : ∀ z ∈ Metric.ball s ρ \ {s}, AnalyticAt ℂ c₀ z := by
    intro z hz
    obtain ⟨y, rfl⟩ := hsurj hz
    exact hac₀ y
  have hd : DifferentiableOn ℂ c₀ (Metric.ball s ρ \ {s}) := fun z hz =>
    ((hana z hz).differentiableAt).differentiableWithinAt
  have hb : BddAbove (norm ∘ c₀ '' (Metric.ball s ρ \ {s})) := by
    refine ⟨2 ^ Fintype.card H * max M 1 ^ Fintype.card H, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, rfl⟩ := hsurj hz
    rw [Function.comp_apply, ← hc₀ y]
    exact norm_coeff_orbitPoly_le hM (fun a => hbdd _ (by rw [hover a y]; exact hz)) k
  obtain ⟨c, hcA, hceq⟩ := exists_analyticAt_of_bddAbove hρ hd hb
  exact ⟨c, hcA, fun y hy => by rw [hc₀ y, hceq _ hy]⟩

end Bounded

end Rigidity.RET

end
