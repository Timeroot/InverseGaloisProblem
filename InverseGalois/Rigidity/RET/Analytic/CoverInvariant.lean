/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverSymm
import InverseGalois.Rigidity.RET.Analytic.RationalGrowth

/-!
# An invariant function of moderate growth comes from the base

A holomorphic function on a covering which is constant along the fibres is a function of the base
point alone, analytic where the covering is.  If it is of moderate growth at the punctures and at
infinity, that function of the base point is a quotient of two polynomials: the invariant function
is a rational function of the base coordinate.

This is the half of the Galois correspondence that costs nothing: the functions fixed by the whole
deck group are the rational functions of the base.  The denominator produced here does not vanish
anywhere over the region covered, so the quotient is defined at every point of the total space.

## Main results

* `Rigidity.RET.exists_rational_of_invariant_of_growth` — an invariant holomorphic function of
  moderate growth satisfies `q(f y) · F y = p(f y)` for polynomials `p`, `q` with `q` monic and
  nonvanishing over the base region.
* `Rigidity.RET.exists_eq_div_of_invariant_of_growth` — the same, written as a quotient.
* `Rigidity.RET.monic_dvd_prod_pow_of_roots_subset` — a monic polynomial vanishing only on a finite
  set divides a power of the product of the linear factors of that set.
* `Rigidity.RET.exists_eq_div_prod_of_invariant_of_growth` — the invariant function as a polynomial
  divided by a power of the product of the distances to the punctures.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-! ### Polynomials vanishing only on the punctures -/

/-- A product of elements each dividing a fixed one divides its power. -/
theorem multiset_prod_dvd_pow {R : Type*} [CommMonoid R] (t : Multiset R) {D : R} :
    (∀ x ∈ t, x ∣ D) → t.prod ∣ D ^ Multiset.card t := by
  refine Multiset.induction_on t (fun _ => by simp) ?_
  intro a s ih h
  have hs : s.prod ∣ D ^ Multiset.card s := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
  have ha : a ∣ D := h a (Multiset.mem_cons_self a s)
  rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
  exact (mul_dvd_mul ha hs).trans (dvd_of_eq (mul_comm D (D ^ Multiset.card s)))

/-- **A monic polynomial vanishing only on a finite set divides a power of the product of the
linear factors of that set.** -/
theorem monic_dvd_prod_pow_of_roots_subset {S : Finset ℂ} {q : ℂ[X]} (hq : q.Monic)
    (hne : ∀ z ∉ S, q.eval z ≠ 0) {n : ℕ} (hn : q.natDegree ≤ n) :
    q ∣ (∏ s ∈ S, (X - C s)) ^ n := by
  classical
  have hsplits : q.Splits := IsAlgClosed.splits q
  have hcard : Multiset.card q.roots = q.natDegree := splits_iff_card_roots.1 hsplits
  have heq : q = (q.roots.map fun r => X - C r).prod := hsplits.eq_prod_roots_of_monic hq
  have hmem : ∀ x ∈ q.roots.map fun r => X - C r, x ∣ ∏ s ∈ S, (X - C s) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    have hrS : r ∈ S := by
      by_contra hrS
      exact hne r hrS (isRoot_of_mem_roots hr)
    exact Finset.dvd_prod_of_mem _ hrS
  have hdvd := multiset_prod_dvd_pow _ hmem
  rw [Multiset.card_map, hcard] at hdvd
  calc q = (q.roots.map fun r => X - C r).prod := heq
    _ ∣ (∏ s ∈ S, (X - C s)) ^ q.natDegree := hdvd
    _ ∣ (∏ s ∈ S, (X - C s)) ^ n := pow_dvd_pow _ hn

section Invariant

variable {Y : Type*} [TopologicalSpace Y] {f F : Y → ℂ}
variable {H : Type*} [Group H] [MulAction H Y]

/-- **An invariant holomorphic function of moderate growth is a rational function of the base
coordinate.**

Constancy along the fibres makes it a function of the base point, analytic off the punctures; the
growth conditions then make that function a quotient of two polynomials. -/
theorem exists_rational_of_invariant_of_growth (hf : IsLocalHomeomorph f)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hF : IsHolo f F) (hinv : ∀ (a : H) (y : Y), F (a • y) = F y)
    (S : Finset ℂ) (hrange : Set.range f = (↑S)ᶜ)
    (hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖F y‖ * ‖f y - s‖ ^ N ≤ C)
    {A R₀ : ℝ} {m : ℕ} (hinf : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖F y‖ ≤ A * ‖f y‖ ^ m) :
    ∃ p q : ℂ[X], q.Monic ∧ (∀ z ∉ S, q.eval z ≠ 0) ∧
      ∀ y : Y, q.eval (f y) * F y = p.eval (f y) := by
  obtain ⟨c, hc, hac⟩ := exists_analytic_of_isHolo_of_invariant hf hF (fun y y' hyy => by
    obtain ⟨b, rfl⟩ := htrans y y' hyy
    exact (hinv b y).symm)
  have hmemrange : ∀ z : ℂ, z ∉ S → ∃ y : Y, f y = z := by
    intro z hz
    have : z ∈ Set.range f := by rw [hrange]; simpa using hz
    exact this
  have hana : ∀ z ∉ S, AnalyticAt ℂ c z := by
    intro z hz
    obtain ⟨y, rfl⟩ := hmemrange z hz
    exact hac y
  have hpunct' : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ (B : ℝ) (N : ℕ),
      ∀ z ∈ Metric.ball s ρ \ {s}, z ∉ S → ‖c z‖ * ‖z - s‖ ^ N ≤ B := by
    intro s hs
    obtain ⟨ρ, hρ, C, -, N, hbdd⟩ := hpunct s hs
    refine ⟨ρ, hρ, C, N, ?_⟩
    intro z hz hzS
    obtain ⟨y, rfl⟩ := hmemrange z hzS
    rw [← hc y]
    exact hbdd y hz
  have hinf' : ∀ z : ℂ, R₀ ≤ ‖z‖ → z ∉ S → ‖c z‖ ≤ A * ‖z‖ ^ m := by
    intro z hz hzS
    obtain ⟨y, rfl⟩ := hmemrange z hzS
    rw [← hc y]
    exact hinf y hz
  obtain ⟨p, q, hqm, hqne, hpq⟩ := exists_rational_of_growth S hana hpunct' hinf'
  exact ⟨p, q, hqm, hqne, fun y => by rw [hc y]; exact hpq (f y)⟩

/-- **An invariant holomorphic function of moderate growth is a quotient of two polynomials in the
base coordinate**, with a denominator that does not vanish over the base region. -/
theorem exists_eq_div_of_invariant_of_growth (hf : IsLocalHomeomorph f)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hF : IsHolo f F) (hinv : ∀ (a : H) (y : Y), F (a • y) = F y)
    (S : Finset ℂ) (hrange : Set.range f = (↑S)ᶜ)
    (hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖F y‖ * ‖f y - s‖ ^ N ≤ C)
    {A R₀ : ℝ} {m : ℕ} (hinf : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖F y‖ ≤ A * ‖f y‖ ^ m) :
    ∃ p q : ℂ[X], q.Monic ∧ (∀ y : Y, q.eval (f y) ≠ 0) ∧
      ∀ y : Y, F y = p.eval (f y) / q.eval (f y) := by
  obtain ⟨p, q, hqm, hqne, hpq⟩ :=
    exists_rational_of_invariant_of_growth (H := H) hf htrans hF hinv S hrange hpunct hinf
  have hnotS : ∀ y : Y, f y ∉ S := by
    intro y
    have hmem : f y ∈ (↑S : Set ℂ)ᶜ := hrange ▸ Set.mem_range_self y
    simpa using hmem
  refine ⟨p, q, hqm, fun y => hqne (f y) (hnotS y), fun y => ?_⟩
  rw [eq_div_iff (hqne (f y) (hnotS y)), mul_comm]
  exact hpq y

/-- **An invariant holomorphic function of moderate growth is a regular function on the punctured
plane**: a polynomial in the base coordinate divided by a power of the product of the distances to
the punctures.

The denominator of the rational function produced above vanishes only on the punctures, so it
divides a power of that product. -/
theorem exists_eq_div_prod_of_invariant_of_growth (hf : IsLocalHomeomorph f)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hF : IsHolo f F) (hinv : ∀ (a : H) (y : Y), F (a • y) = F y)
    (S : Finset ℂ) (hrange : Set.range f = (↑S)ᶜ)
    (hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖F y‖ * ‖f y - s‖ ^ N ≤ C)
    {A R₀ : ℝ} {m : ℕ} (hinf : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖F y‖ ≤ A * ‖f y‖ ^ m) :
    ∃ (p : ℂ[X]) (e : ℕ), ∀ y : Y, (∏ s ∈ S, (f y - s)) ^ e * F y = p.eval (f y) := by
  obtain ⟨p, q, hqm, hqne, hpq⟩ :=
    exists_rational_of_invariant_of_growth (H := H) hf htrans hF hinv S hrange hpunct hinf
  obtain ⟨h, hh⟩ := monic_dvd_prod_pow_of_roots_subset hqm hqne (le_refl q.natDegree)
  refine ⟨h * p, q.natDegree, fun y => ?_⟩
  have hev : (∏ s ∈ S, (f y - s)) ^ q.natDegree
      = q.eval (f y) * h.eval (f y) := by
    have := congrArg (Polynomial.eval (f y)) hh
    simpa [eval_prod] using this
  rw [hev, eval_mul, mul_assoc, mul_comm (h.eval (f y)), ← mul_assoc, hpq y]
  ring

end Invariant

end Rigidity.RET

end
