/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Smooth separable reduction (squarefree part) of a bivariate real polynomial family

This file provides the algebraic reduction underlying
`InverseGalois.Hilbert.Analytic.DorgeBauer.exists_smooth_separable_reduction`.

Given a polynomial `F : ℝ[x][Y]` that is monic in `Y` of `Y`-degree `≥ 2`, we produce a
`C^ω` (real-analytic, `ContDiff ℝ ⊤`) family `R x` of monic real polynomials of some fixed
degree `d ≥ 1` such that, on a tail `[T₀, ∞)`, `R x` is *separable* and has *exactly the
same real roots* as the specialization `F(x, ·)`.

The construction is the **squarefree part / radical of `F` in the UFD `ℝ[x][Y]`**.  Because
`F` is monic in `Y`, Gauss's lemma guarantees the distinct monic irreducible factors of `F`
lie in `ℝ[x][Y]` (polynomial coefficients, no denominators), so the radical `s := radical F`
is a *monic* polynomial in `ℝ[x][Y]` whose coefficients are honest polynomials in `x`.  Its
specialization `R x := s.map (evalRingHom x)` is therefore monic of a fixed degree and its
bivariate evaluation is a genuine two-variable polynomial, hence real-analytic on all of `ℝ²`.

The three algebraic facts that make everything work:
* `s ∣ F` (so every root of `R x` is a root of `F(x, ·)`), from `radical_dvd_self`;
* `F ∣ s ^ m` for some `m ≥ 1` (so every root of `F(x, ·)` is a root of `R x`);
* a Bezout identity `A * s + B * s' = C w0` with `w0 ∈ ℝ[x]` nonzero (so past the finitely
  many real zeros of `w0`, `R x` is separable), coming from squarefreeness of `s`.
-/

open Polynomial UniqueFactorizationMonoid
open scoped Classical

noncomputable section

namespace SmoothSeparableReduction

/-
The radical of a monic polynomial over `ℝ[x]` is monic.

`radical F` is a product of *normalized* prime factors, hence itself normalized, so its
leading coefficient equals its own normalization.  Since `radical F ∣ F` and `F` is monic,
that leading coefficient divides `1`, i.e. is a unit of `ℝ[x]`; a normalized unit is `1`.
-/
lemma radical_monic {F : Polynomial (Polynomial ℝ)} (hF : F.Monic) :
    (radical F).Monic := by
  -- Since `radical F ∣ F` and `F` is monic, that leading coefficient divides `1`, i.e. is a unit of `ℝ[x]`.
  have h_leading_coeff_unit : IsUnit ((radical F).leadingCoeff : Polynomial ℝ) := by
    have h_leading_coeff_div : (radical F).leadingCoeff ∣ (F).leadingCoeff :=
      Polynomial.leadingCoeff_dvd_leadingCoeff radical_dvd_self
    rw [hF.leadingCoeff] at h_leading_coeff_div
    exact isUnit_of_dvd_one h_leading_coeff_div
  -- Since `radical F` is a product of normalized prime factors, it is itself normalized.
  have h_radical_normalized : normalize (radical F) = radical F := by
    simp [radical]
    refine Finset.prod_congr rfl ?_
    simp +contextual [primeFactors]
    exact normalize_normalized_factor
  rw [Polynomial.Monic, ← h_radical_normalized, Polynomial.leadingCoeff_normalize]
  exact normalize_eq_one.mpr h_leading_coeff_unit

/-
A nonzero element of `ℝ[x][Y]` divides some positive power of its radical.

In the UFD `ℝ[x][Y]`, `F` is (up to a unit) the product of its prime factors with
multiplicities all bounded by, say, the total number of prime factors `m`; `radical F` is
the product of the same primes to the first power, so `F ∣ (radical F) ^ m`.
-/
lemma dvd_radical_pow {F : Polynomial (Polynomial ℝ)} (hF0 : F ≠ 0) :
    ∃ m, 1 ≤ m ∧ F ∣ (radical F) ^ m := by
  by_contra h_contra
  -- Since `F ≠ 0`, we can use the fact that `F` is relatively prime to the set of its prime divisors.
  have h_prime_divisors :
      ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors F, p ∣ radical F := by
    intro p hp
    have h_prime_divisor : p ∈ primeFactors F := by
      simp_all [primeFactors]
    exact Finset.dvd_prod_of_mem _ h_prime_divisor
  -- Since `F` is relatively prime to the set of its prime divisors, we can use the fact that `F` divides the product of its prime divisors raised to the power of their multiplicities.
  have h_divides_product :
      F ∣ Multiset.prod (Multiset.map (fun p ↦ p) (UniqueFactorizationMonoid.normalizedFactors F)) := by
    simpa using (UniqueFactorizationMonoid.prod_normalizedFactors hF0).symm.dvd
  refine h_contra ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors F) + 1,
    Nat.succ_pos _, dvd_trans h_divides_product ?_⟩
  apply dvd_trans (Multiset.prod_dvd_prod_of_dvd _ _ h_prime_divisors)
  norm_num [pow_succ']

/-
A squarefree primitive polynomial over `ℝ[x]` stays squarefree over the fraction field
`ℝ(x)`.  (Gauss's lemma: primitive irreducible factors stay irreducible and pairwise
non-associate over the fraction field.)
-/
set_option maxHeartbeats 1000000 in
lemma squarefree_map_frac {s : Polynomial (Polynomial ℝ)}
    (hs : Squarefree s) (hmon : s.Monic) :
    Squarefree (s.map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)))) := by
  intro x hx
  -- Let `xm := x * C (x.leadingCoeff)⁻¹`, the monic associate of `x`.
  set xm := x * Polynomial.C (Polynomial.leadingCoeff x)⁻¹ with hxm_def
  have hxm_monic : xm.Monic := by
    by_cases hx0 : x = 0 <;> simp_all [Polynomial.Monic]
    rw [Polynomial.map_eq_zero_iff] at hx <;>
      aesop (config := {introsTransparency? := some .default})
  have hxm_assoc : Associated x xm := by
    by_cases hx : x = 0 <;> simp_all [Polynomial.Monic.def]
    refine associated_of_dvd_dvd ?_ ?_ <;> norm_num [hx]
  have hxm_dvd : xm ∣ Polynomial.map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))) s :=
    dvd_trans hxm_assoc.symm.dvd (dvd_of_mul_left_dvd hx)
  have hxm_sq_dvd : xm * xm ∣ Polynomial.map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))) s := by
    convert dvd_trans _ hx using 1
    ring_nf
    exact pow_dvd_pow_of_dvd hxm_assoc.symm.dvd 2
  -- Descent to `R[Y]` via `IsIntegrallyClosed.eq_map_mul_C_of_dvd hmon (g := xm) (hg : xm ∣ s.map φ)`: it yields `x' : R[Y]` with `x'.map φ * C (xm.leadingCoeff) = xm`.
  obtain ⟨x', hx'map⟩ :
      ∃ x' : Polynomial (Polynomial ℝ),
        x'.map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))) = xm := by
    have := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing (Polynomial ℝ)) hmon hxm_dvd
    aesop
  have hx'mon : x'.Monic := by
    convert hxm_monic using 1
    rw [← hx'map, Polynomial.Monic.def, Polynomial.Monic.def,
      Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
    · aesop
    · intro h
      simp_all [Polynomial.Monic.def]
  -- By `Monic.dvd_iff_fraction_map_dvd_fraction_map` (`R` integrally closed, `x'` and `s` monic) we get `x' * x' ∣ s`.
  have hx'_sq_dvd : x' * x' ∣ s := by
    rw [← Polynomial.map_dvd_map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)))]
    · aesop
    · exact IsFractionRing.injective _ _
    · exact hx'mon.mul hx'mon
  have := hs x' ?_
  · convert hxm_assoc.symm.isUnit
    simp [← hx'map]
    refine Or.inl <| Polynomial.isUnit_iff_degree_eq_zero.mpr ?_
    rw [Polynomial.degree_map_eq_of_injective <| IsFractionRing.injective _ _]
    exact Polynomial.degree_eq_zero_of_isUnit this
  · exact hx'_sq_dvd

/-
**Bezout with cleared denominators for a squarefree polynomial over `ℝ[x]`.**

If `s` is squarefree (and monic) in `ℝ[x][Y]`, then over the fraction field `ℝ(x)` it is
separable, so `1 = U·s + V·s'` for some `U, V ∈ ℝ(x)[Y]`.  Clearing a common denominator
`w0 ∈ ℝ[x]` (nonzero) gives `A·s + B·s' = C w0` over `ℝ[x][Y]`.
-/
set_option maxHeartbeats 1000000 in
lemma exists_bezout_of_squarefree {s : Polynomial (Polynomial ℝ)}
    (hs : Squarefree s) (hmon : s.Monic) :
    ∃ (A B : Polynomial (Polynomial ℝ)) (w0 : Polynomial ℝ),
      w0 ≠ 0 ∧ A * s + B * Polynomial.derivative s = C w0 := by
  obtain ⟨U, V, h_bezout⟩ :
      ∃ U V : Polynomial (FractionRing (Polynomial ℝ)),
        U * (s.map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)))) +
          V * (Polynomial.derivative (s.map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))))) = 1 :=
    PerfectField.separable_iff_squarefree.mpr (squarefree_map_frac hs hmon)
  -- Clear denominators by multiplying both sides of the equation by a common denominator.
  obtain ⟨w0, hw0ne, A, B, hAB⟩ :
      ∃ w0 : Polynomial ℝ, w0 ≠ 0 ∧ ∃ A B : Polynomial (Polynomial ℝ),
        A * s + B * (derivative s) = Polynomial.C w0 := by
    -- Let `w0` be a common denominator of `U` and `V`.
    obtain ⟨w0, hw0⟩ :
        ∃ w0 : Polynomial ℝ, w0 ≠ 0 ∧ ∃ A B : Polynomial (Polynomial ℝ),
          Polynomial.map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))) A =
              U * Polynomial.C (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)) w0) ∧
          Polynomial.map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))) B =
              V * Polynomial.C (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)) w0) := by
      have h_clear_denom : ∀ p : Polynomial (FractionRing (Polynomial ℝ)),
          ∃ w0 : Polynomial ℝ, w0 ≠ 0 ∧ ∃ A : Polynomial (Polynomial ℝ),
            Polynomial.map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))) A =
              p * Polynomial.C (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)) w0) := by
        intro p
        induction' p using Polynomial.induction_on' with p q ihp ihq n a
        · obtain ⟨w0, hw0, A, hA⟩ := ihp
          obtain ⟨w1, hw1, B, hB⟩ := ihq
          use w0 * w1
          simp_all
          use A * Polynomial.C w1 + B * Polynomial.C w0
          simp [*, add_mul, mul_comm, mul_left_comm]
        · obtain ⟨w0, hw0⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial ℝ)) a
          refine ⟨w0.2, ?_, ?_⟩
          · simp_all
          · simp_all [← Polynomial.C_mul_X_pow_eq_monomial]
            use Polynomial.C w0.1 * Polynomial.X ^ n
            simp [← hw0, mul_assoc]
      obtain ⟨w0, hw0, A, hA⟩ := h_clear_denom U
      obtain ⟨w1, hw1, B, hB⟩ := h_clear_denom V
      use w0 * w1
      simp_all
      refine ⟨⟨A * Polynomial.C w1, ?_⟩, B * Polynomial.C w0, ?_⟩
      · simp [hA, mul_assoc]
      · simp [hB, mul_comm, mul_left_comm]
    obtain ⟨A, B, hA, hB⟩ := hw0.right
    have h_eq :
        Polynomial.map (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))) (A * s + B * (derivative s)) =
          Polynomial.C (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)) w0) := by
      simp_all [mul_comm, mul_left_comm]
      linear_combination h_bezout * C (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)) w0)
    refine ⟨w0, hw0.1, A, B, ?_⟩
    apply Polynomial.map_injective (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)))
      (IsFractionRing.injective _ _)
    aesop
  exact ⟨A, B, w0, hw0ne, hAB⟩

/-
The bivariate evaluation of a two-variable real polynomial is real-analytic.
-/
lemma contDiff_bivar_eval (g : Polynomial (Polynomial ℝ)) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (g.map (evalRingHom p.1)).eval p.2) := by
  induction' g using Polynomial.induction_on' with p q hp hq
  · simpa [Polynomial.eval_map] using hp.add hq
  · rename_i k a
    induction' a using Polynomial.induction_on' with a b ha hb
    · simpa [Polynomial.map_add, Polynomial.eval_add] using ha.add hb
    · simp
      fun_prop

/-
**Reduction to a smooth separable family with the same real roots (real version).**

For `F : ℝ[x][Y]` monic in `Y` of `Y`-degree `≥ 2`, there is a real-analytic family `R x`
of monic real polynomials of fixed degree `d ≥ 1` which, on a tail `[T₀, ∞)`, is separable
and has exactly the same real roots as the specialization `F.map (evalRingHom x)`.

`R x := (radical F).map (evalRingHom x)`.
-/
theorem exists_smooth_separable_reduction_real
    (F : Polynomial (Polynomial ℝ)) (hFmon : F.Monic) (hFdeg : 2 ≤ F.natDegree) :
    ∃ (d : ℕ) (R : ℝ → Polynomial ℝ) (T₀ : ℝ), 1 ≤ T₀ ∧ 1 ≤ d ∧
      (∀ x, (R x).Monic) ∧ (∀ x, (R x).natDegree = d) ∧
      ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (R p.1).eval p.2) ∧
      (∀ x : ℝ, T₀ ≤ x → (R x).Separable) ∧
      (∀ x : ℝ, T₀ ≤ x → ∀ y : ℝ,
        (R x).eval y = 0 ↔ (F.map (evalRingHom x)).eval y = 0) := by
  obtain ⟨s, hmon_s, hdvd_s, _, ⟨m, hm⟩, A, B, w0, hw0_ne_zero, h_bezout⟩ :
      ∃ s : Polynomial (Polynomial ℝ), s.Monic ∧ s ∣ F ∧ Squarefree s ∧
        (∃ m : ℕ, 1 ≤ m ∧ F ∣ s ^ m) ∧
        (∃ A B : Polynomial (Polynomial ℝ), ∃ w0 : Polynomial ℝ,
          w0 ≠ 0 ∧ A * s + B * Polynomial.derivative s = C w0) :=
    ⟨radical F, radical_monic hFmon, radical_dvd_self,
      squarefree_radical, dvd_radical_pow (by aesop),
      exists_bezout_of_squarefree squarefree_radical (radical_monic hFmon)⟩
  use s.natDegree, fun x ↦ s.map (evalRingHom x)
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ x ≥ T₀, w0.eval x ≠ 0 := by
    refine ⟨∑ x ∈ w0.roots.toFinset, |x| + 1, ?_, ?_⟩
    · linarith [show 0 ≤ ∑ x ∈ w0.roots.toFinset, |x| by
        exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _]
    · intro x hx hx'
      cases abs_cases x <;>
        linarith [Finset.single_le_sum (fun x _ ↦ abs_nonneg x)
          (show x ∈ w0.roots.toFinset from by aesop)]
  refine ⟨T₀, hT₀.1, ?_, ?_, ?_, contDiff_bivar_eval s, ?_, ?_⟩
  · have := Polynomial.natDegree_le_of_dvd hm.2
    simp_all [Polynomial.natDegree_pow]
    apply Nat.pos_of_ne_zero
    intro h
    have := this (by aesop)
    nlinarith
  · exact fun x ↦ hmon_s.map _
  · intro x
    apply Polynomial.natDegree_map_of_leadingCoeff_ne_zero
    aesop
  · intro x hx
    have := hT₀.2 x hx
    simp_all [Polynomial.Separable]
    replace h_bezout := congr_arg (Polynomial.map (evalRingHom x)) h_bezout
    simp_all [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    refine ⟨Polynomial.C (eval x w0) ⁻¹ * map (evalRingHom x) A,
      Polynomial.C (eval x w0) ⁻¹ * map (evalRingHom x) B, Polynomial.funext fun y ↦ ?_⟩
    have key : (eval x w0)⁻¹ * (eval y (map (evalRingHom x) A) * eval y (map (evalRingHom x) s)) +
        (eval x w0)⁻¹ * (eval y (map (evalRingHom x) B) *
          eval y (map (evalRingHom x) (derivative s))) = 1 := by
      have := congr_arg (Polynomial.eval y) h_bezout
      norm_num at *
      cases lt_or_gt_of_ne (hT₀.2 x hx) <;> nlinarith [mul_inv_cancel₀ (hT₀.2 x hx)]
    simpa [hT₀.2 x hx, mul_assoc, mul_left_comm, mul_add, add_mul, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X] using key
  · intro x hx y
    constructor <;> intro hy <;> simp_all [Polynomial.eval_map]
    · obtain ⟨k, hk⟩ := hdvd_s
      replace hk := congr_arg (Polynomial.eval₂ (evalRingHom x) y) hk
      aesop
    · obtain ⟨k, hk⟩ := hm.2
      replace hk := congr_arg (Polynomial.eval₂ (evalRingHom x) y) hk
      simp_all [Polynomial.eval₂_pow, Polynomial.eval₂_mul]

end SmoothSeparableReduction