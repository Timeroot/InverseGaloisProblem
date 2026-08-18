/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Weighted degrees of two-variable polynomials, and the size of a monic factor

Give the monomial `X ^ j * Y ^ i` of a two-variable polynomial the weight `j + D * i`, for a fixed
`D`.  The largest weight occurring in a polynomial is additive on products, because it is the
degree in `X` of the polynomial obtained by the substitution `Y ↦ X ^ D * Y`, read with the two
variables exchanged.

The consequence used downstream: if a monic (in `Y`) polynomial of degree `n` has all its weights
at most `D * n` — that is, the coefficient of `Y ^ i` has degree at most `D * (n - i)` in `X` —
then the same bound holds, with its own degree in place of `n`, for every monic factor.  Both
factors of a factorization spend the whole weight budget on their leading terms, so neither has
room for a coefficient of unexpectedly large degree.  This is the boundedness which makes the
factorizations of a two-variable polynomial into monic factors of prescribed degrees a *finite*
system of polynomial equations in the coefficients.

## Main results

* `Rigidity.RET.Transfer.wdeg_mul` — the largest weight is additive on products.
* `Rigidity.RET.Transfer.weight_le_of_monic_mul` — a monic factor of a polynomial of weight
  `D * n` has weight `D * (its own degree)`.
* `Rigidity.RET.Transfer.natDegree_coeff_le_of_monic_mul` — the same, stated for the degrees of
  the coefficients.
-/

open scoped Polynomial.Bivariate

open Polynomial

namespace Rigidity.RET.Transfer

variable {R : Type*}

section Semiring

variable [CommSemiring R]

/-- **Exchanging the two variables exchanges the two indices of a coefficient.** -/
theorem coeff_coeff_swap (p : R[X][Y]) (i j : ℕ) :
    ((Bivariate.swap p).coeff j).coeff i = (p.coeff i).coeff j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, coeff_add, coeff_add, hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add b c hb hc =>
      rw [show (monomial n) (b + c) = monomial n b + monomial n c from map_add _ _ _,
        map_add, coeff_add, coeff_add, coeff_add, coeff_add, hb, hc]
    | monomial m r =>
      rw [Bivariate.swap_monomial_monomial, coeff_monomial, coeff_monomial]
      by_cases h₁ : m = j <;> by_cases h₂ : n = i <;>
        simp [h₁, h₂, coeff_monomial]

/-- The substitution `Y ↦ X ^ D * Y`, which turns the weight `j + D * i` of a monomial into its
degree in `X`. -/
noncomputable def scale (D : ℕ) (p : R[X][Y]) : R[X][Y] := p.comp (C (X ^ D) * X)

@[simp]
theorem coeff_scale (D : ℕ) (p : R[X][Y]) (i : ℕ) :
    (scale D p).coeff i = p.coeff i * X ^ (D * i) := by
  rw [scale, comp_C_mul_X_coeff, ← pow_mul, mul_comm D i]

theorem scale_mul (D : ℕ) (p q : R[X][Y]) : scale D (p * q) = scale D p * scale D q :=
  mul_comp p q _

/-- **The largest weight `j + D * i` of a monomial `X ^ j * Y ^ i` occurring in `p`.** -/
noncomputable def wdeg (D : ℕ) (p : R[X][Y]) : ℕ := (Bivariate.swap (scale D p)).natDegree

theorem coeff_coeff_scale_swap (D : ℕ) (p : R[X][Y]) (i j : ℕ) :
    ((Bivariate.swap (scale D p)).coeff j).coeff i =
      if D * i ≤ j then (p.coeff i).coeff (j - D * i) else 0 := by
  rw [coeff_coeff_swap, coeff_scale, coeff_mul_X_pow']

/-- **Every monomial occurring in `p` has weight at most `wdeg D p`.** -/
theorem le_wdeg (D : ℕ) {p : R[X][Y]} {i j : ℕ} (h : (p.coeff i).coeff j ≠ 0) :
    j + D * i ≤ wdeg D p := by
  refine le_natDegree_of_ne_zero fun hz => h ?_
  have h2 : ((Bivariate.swap (scale D p)).coeff (j + D * i)).coeff i = 0 := by
    rw [hz, coeff_zero]
  rw [coeff_coeff_scale_swap, if_pos (Nat.le_add_left _ _)] at h2
  simpa using h2

/-- **A bound on the weights of the monomials of `p` bounds `wdeg D p`.** -/
theorem wdeg_le (D : ℕ) {p : R[X][Y]} {w : ℕ}
    (h : ∀ i j, (p.coeff i).coeff j ≠ 0 → j + D * i ≤ w) : wdeg D p ≤ w := by
  refine natDegree_le_iff_coeff_eq_zero.2 fun j hj => ?_
  ext i
  rw [coeff_coeff_scale_swap, coeff_zero]
  split_ifs with hij
  · by_contra hne
    have hle := h i (j - D * i) hne
    rw [Nat.sub_add_cancel hij] at hle
    omega
  · rfl

/-- The weight of the leading term of a monic polynomial. -/
theorem le_wdeg_of_monic (D : ℕ) [Nontrivial R] {p : R[X][Y]} (hp : p.Monic) :
    D * p.natDegree ≤ wdeg D p := by
  have h : (p.coeff p.natDegree).coeff 0 ≠ 0 := by
    rw [coeff_natDegree, hp.leadingCoeff]
    simp
  simpa using le_wdeg D h

end Semiring

section Domain

variable [CommRing R] [IsDomain R]

theorem scale_ne_zero (D : ℕ) {p : R[X][Y]} (hp : p ≠ 0) : scale D p ≠ 0 := by
  rw [scale, Ne, comp_C_mul_X_eq_zero_iff]
  · exact hp
  · exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ X_ne_zero)

theorem swap_scale_ne_zero (D : ℕ) {p : R[X][Y]} (hp : p ≠ 0) :
    Bivariate.swap (scale D p) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (Bivariate.swap (R := R)).injective]
  exact scale_ne_zero D hp

/-- **The largest weight is additive on products.** -/
theorem wdeg_mul (D : ℕ) {p q : R[X][Y]} (hp : p ≠ 0) (hq : q ≠ 0) :
    wdeg D (p * q) = wdeg D p + wdeg D q := by
  rw [wdeg, scale_mul, map_mul,
    natDegree_mul (swap_scale_ne_zero D hp) (swap_scale_ne_zero D hq)]
  rfl

/-- **A monic factor of a polynomial of weight `D * n` has weight `D * (its own degree)`.**

The two factors of a monic polynomial of degree `n = m + k` have weights at least `D * m` and
`D * k` — the weights of their leading terms — and those weights add up to at most `D * n`, so
each of them is exactly what its leading term forces. -/
theorem weight_le_of_monic_mul (D : ℕ) {g h : R[X][Y]} (hg : g.Monic) (hh : h.Monic)
    (hgh : ∀ i j, ((g * h).coeff i).coeff j ≠ 0 →
      j + D * i ≤ D * (g.natDegree + h.natDegree)) :
    ∀ i j, (g.coeff i).coeff j ≠ 0 → j + D * i ≤ D * g.natDegree := by
  have hbudget : wdeg D g + wdeg D h ≤ D * g.natDegree + D * h.natDegree := by
    rw [← wdeg_mul D hg.ne_zero hh.ne_zero, ← Nat.mul_add]
    exact wdeg_le D hgh
  have hkey : wdeg D g ≤ D * g.natDegree := by
    have := le_wdeg_of_monic (R := R) D hh
    omega
  exact fun i j hij => le_trans (le_wdeg D hij) hkey

/-- **The degrees of the coefficients of a monic factor are bounded**, in the form used to bound
the size of the unknowns describing a factorization. -/
theorem natDegree_coeff_le_of_monic_mul (D : ℕ) {g h : R[X][Y]} (hg : g.Monic) (hh : h.Monic)
    (hgh : ∀ i, (g * h).coeff i ≠ 0 →
      ((g * h).coeff i).natDegree + D * i ≤ D * (g.natDegree + h.natDegree))
    (i : ℕ) (hi : g.coeff i ≠ 0) :
    (g.coeff i).natDegree + D * i ≤ D * g.natDegree := by
  refine weight_le_of_monic_mul D hg hh (fun a b hab => ?_) i (g.coeff i).natDegree ?_
  · have hne : (g * h).coeff a ≠ 0 := fun hz => hab (by rw [hz, coeff_zero])
    exact le_trans (Nat.add_le_add_right (le_natDegree_of_ne_zero hab) _) (hgh a hne)
  · rw [coeff_natDegree, Ne, leadingCoeff_eq_zero]
    exact hi

end Domain

end Rigidity.RET.Transfer
