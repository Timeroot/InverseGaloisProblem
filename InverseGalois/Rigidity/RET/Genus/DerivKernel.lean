/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.LineDerivation

/-!
# The functions killed by differentiation

Differentiating a rational function of one variable gives zero exactly for the constants: writing
the function in lowest terms, the denominator divides its own derivative, which forces the
derivative of the denominator to vanish on degree grounds, and then the same for the numerator.

The same is true on a cover of the line.  A function on the cover satisfies a monic equation of
least degree over the rational functions of the line; differentiating that equation kills the
leading term and leaves an equation of smaller degree, whose coefficients are the derivatives of
the original ones.  Minimality forces those to vanish, so the original equation already has
constant coefficients, and over an algebraically closed field of constants that makes the function
itself constant.

## Main results

* `Rigidity.RET.exists_algebraMap_of_ratFuncDeriv_eq_zero` — a rational function with vanishing
  derivative is a constant.
* `Rigidity.RET.mem_one_of_lineDeriv_eq_zero` — a function on a cover of the line with vanishing
  derivative is a constant.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-! ## Constants among the rational functions -/

section RatFuncKernel

variable {k : Type*} [Field k] [CharZero k]

/-- **A rational function with vanishing derivative is a constant.** -/
theorem exists_algebraMap_of_ratFuncDeriv_eq_zero {c : RatFunc k} (h : ratFuncDeriv k c = 0) :
    ∃ a : k, c = algebraMap k (RatFunc k) a := by
  have hq0 : c.denom ≠ 0 := RatFunc.denom_ne_zero c
  have hcq : c * algebraMap _ (RatFunc k) c.denom = algebraMap _ _ c.num := by
    nth_rewrite 1 [← RatFunc.num_div_denom c]
    exact div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hq0)
  have hd := congrArg (ratFuncDeriv k) hcq
  rw [Derivation.leibniz, h, smul_zero, add_zero, ratFuncDeriv_algebraMap,
    ratFuncDeriv_algebraMap] at hd
  have hmul : c.num * derivative c.denom = c.denom * derivative c.num := by
    apply RatFunc.algebraMap_injective k
    rw [map_mul, map_mul, ← hcq, ← hd, smul_eq_mul]
    ring
  have hdvd : c.denom ∣ derivative c.denom := by
    have hcop : IsCoprime c.denom c.num := (RatFunc.isCoprime_num_denom c).symm
    exact hcop.dvd_of_dvd_mul_left ⟨derivative c.num, hmul⟩
  have hdq : derivative c.denom = 0 := by
    by_contra hne
    exact absurd (Polynomial.degree_le_of_dvd hdvd hne)
      (not_le.2 (Polynomial.degree_derivative_lt hq0))
  have hq1 : c.denom = 1 :=
    (RatFunc.monic_denom c).natDegree_eq_zero.1
      (Polynomial.natDegree_eq_zero_of_derivative_eq_zero hdq)
  have hdp : derivative c.num = 0 := by
    have := hmul
    rw [hdq, hq1, mul_zero, one_mul] at this
    exact this.symm
  refine ⟨c.num.coeff 0, ?_⟩
  have hnum : c.num = C (c.num.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero hdp
  have : c = algebraMap (Polynomial k) (RatFunc k) c.num := by
    conv_lhs => rw [← RatFunc.num_div_denom c]
    rw [hq1, map_one, div_one]
  rw [this, hnum, IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]
  simp

end RatFuncKernel

/-! ## Constants among the functions on a cover -/

section CoverKernel

variable (k F : Type*) [Field k] [CharZero k] [IsAlgClosed k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

attribute [local instance] Algebra.FormallyEtale.of_isSeparable

variable {k F}

omit [CharZero k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] in
/-- An element algebraic over an algebraically closed field of constants is a constant. -/
theorem mem_one_of_isAlgebraic {y : F} (hy : IsAlgebraic k y) : y ∈ (1 : Submodule k F) := by
  have hint : IsIntegral k y := hy.isIntegral
  have hmon : (minpoly k y).Monic := minpoly.monic hint
  have hdeg1 : (minpoly k y).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
  have hform : minpoly k y = X + C ((minpoly k y).coeff 0) := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_eq_one hdeg1]
    rw [hmon.leadingCoeff, map_one, one_mul]
  have haev : Polynomial.aeval y (minpoly k y) = 0 := minpoly.aeval k y
  rw [hform] at haev
  simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C] at haev
  rw [Submodule.mem_one]
  refine ⟨-((minpoly k y).coeff 0), ?_⟩
  rw [map_neg]
  linear_combination -haev

omit [CharZero k] in
/-- **A function whose minimal equation over the line has constant coefficients is a constant.** -/
theorem mem_one_of_coeff_minpoly_mem_range {y : F}
    (h : ∀ j : ℕ, ∃ a : k, (minpoly (RatFunc k) y).coeff j = algebraMap k (RatFunc k) a) :
    y ∈ (1 : Submodule k F) := by
  classical
  have hint : IsIntegral (RatFunc k) y := Algebra.IsIntegral.isIntegral y
  set P := minpoly (RatFunc k) y with hP
  have hPm : P.Monic := minpoly.monic hint
  have hPa : Polynomial.aeval y P = 0 := minpoly.aeval (RatFunc k) y
  set n := P.natDegree with hn
  choose a ha using h
  set P' : Polynomial k := ∑ j ∈ Finset.range (n + 1), C (a j) * X ^ j with hP'
  have hP'a : Polynomial.aeval y P' = 0 := by
    rw [hP', map_sum]
    rw [Polynomial.aeval_eq_sum_range, ← hn] at hPa
    rw [← hPa]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Algebra.smul_def, ha i,
      ← IsScalarTower.algebraMap_apply k (RatFunc k) F]
  have hP'n : P'.coeff n = a n := by
    rw [hP']
    simp [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have han : a n ≠ 0 := by
    intro hz
    have := ha n
    rw [hz, map_zero, hn, hPm.coeff_natDegree] at this
    exact one_ne_zero this
  have hP'0 : P' ≠ 0 := fun hz => han (by rw [← hP'n, hz, Polynomial.coeff_zero])
  exact mem_one_of_isAlgebraic ⟨P', hP'0, hP'a⟩

/-- **A function on a cover of the line with vanishing derivative is a constant.** -/
theorem mem_one_of_lineDeriv_eq_zero {y : F} (h : lineDeriv k F y = 0) :
    y ∈ (1 : Submodule k F) := by
  classical
  have hint : IsIntegral (RatFunc k) y := Algebra.IsIntegral.isIntegral y
  set P := minpoly (RatFunc k) y with hP
  have hPm : P.Monic := minpoly.monic hint
  have hPa : Polynomial.aeval y P = 0 := minpoly.aeval (RatFunc k) y
  set n := P.natDegree with hn
  have hn0 : 0 < n := minpoly.natDegree_pos hint
  set Q : Polynomial (RatFunc k) :=
    ∑ j ∈ Finset.range n, C (ratFuncDeriv k (P.coeff j)) * X ^ j with hQ
  -- differentiating the minimal equation
  have hterm : ∀ i : ℕ, lineDeriv k F ((P.coeff i) • y ^ i)
      = y ^ i * algebraMap (RatFunc k) F (ratFuncDeriv k (P.coeff i)) := by
    intro i
    rw [Algebra.smul_def, Derivation.leibniz, Derivation.leibniz_pow, h]
    simp only [smul_eq_mul, mul_zero, smul_zero, zero_add, lineDeriv_algebraMap]
  have h0 : ∑ i ∈ Finset.range (n + 1),
      y ^ i * algebraMap (RatFunc k) F (ratFuncDeriv k (P.coeff i)) = 0 := by
    have := congrArg (lineDeriv k F) hPa
    rw [Polynomial.aeval_eq_sum_range, map_sum, map_zero] at this
    simpa only [hterm] using this
  have hQa : Polynomial.aeval y Q = 0 := by
    rw [hQ, map_sum]
    rw [Finset.sum_range_succ] at h0
    have hlast : P.coeff n = 1 := hPm.coeff_natDegree
    rw [hlast, Derivation.map_one_eq_zero, map_zero, mul_zero, add_zero] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, mul_comm]
  -- the derivative of the minimal equation is smaller, hence zero
  have hQdeg : Q.degree < (n : ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
    intro j hj
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le j _)
      (by exact_mod_cast Finset.mem_range.1 hj)
  have hQ0 : Q = 0 := by
    by_contra hne
    have hle := minpoly.degree_le_of_ne_zero (RatFunc k) y hne hQa
    rw [← hP, Polynomial.degree_eq_natDegree hPm.ne_zero, ← hn] at hle
    exact absurd (hle.trans_lt hQdeg) (lt_irrefl _)
  -- so the minimal equation has constant coefficients
  have hcoeff : ∀ j : ℕ, ratFuncDeriv k (P.coeff j) = 0 := by
    intro j
    rcases lt_trichotomy j n with hj | hj | hj
    · have hQj : Q.coeff j = ratFuncDeriv k (P.coeff j) := by
        rw [hQ]
        simp [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hj]
      rw [← hQj, hQ0, Polynomial.coeff_zero]
    · rw [hj, hn, hPm.coeff_natDegree, Derivation.map_one_eq_zero]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj, map_zero]
  -- and therefore the element is algebraic over the constants
  exact mem_one_of_coeff_minpoly_mem_range fun j =>
    exists_algebraMap_of_ratFuncDeriv_eq_zero (hcoeff j)

end CoverKernel

end Rigidity.RET
