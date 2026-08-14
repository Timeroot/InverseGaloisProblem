/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.LineOrd
import InverseGalois.Rigidity.RET.RatFuncSubst

/-!
# The order of a rational function at the point at infinity

The points of the affine line do not exhaust the line: the projective line has one more point, and
a rational function has an order there too.  That point is reached by the inversion `u ↦ u⁻¹`,
which exchanges it with the origin, so the order at infinity is the order at the origin of the
inverted function.

Computing it is the reverse-polynomial identity: `p(u⁻¹) · u^{deg p}` is the polynomial with the
coefficients of `p` in the opposite order, whose constant term is the leading coefficient of `p`
and so is nonzero at the origin.  Hence a polynomial has a pole of order exactly its degree at
infinity, and a rational function has order `-intDegree` there.

Together with the affine count this gives the first theorem of divisor theory: on the projective
line the orders of a nonzero rational function, taken over all points including infinity, sum to
zero.

## Main definitions

* `Rigidity.RET.ordInfty` — the order of a rational function at the point at infinity.

## Main results

* `Rigidity.RET.ordInfty_polynomial` — a polynomial has order `-natDegree` at infinity.
* `Rigidity.RET.ordInfty_eq_neg_intDegree` — a rational function has order `-intDegree` there.
* `Rigidity.RET.finsum_ord_add_ordInfty` — the degree of the divisor of a rational function on the
  projective line is zero.
-/

open IsDedekindDomain Polynomial

noncomputable section


namespace Rigidity.RET

/-! ## Reversing the coefficients of a polynomial -/

/-- **Reflecting twice is the identity.**  Reflection permutes the coefficients by the involution
`revAt N` of the naturals, so it is an involution itself, whatever the bound `N`. -/
theorem reflect_reflect {R : Type*} [Semiring R] (N : ℕ) (p : R[X]) :
    reflect N (reflect N p) = p := by
  ext i
  rw [coeff_reflect, coeff_reflect, revAt_invol]

variable {F : Type*} [Field F]

/-- The parameter of the field of rational functions evaluates a polynomial to itself. -/
theorem aeval_X_eq_algebraMap (p : F[X]) :
    Polynomial.aeval (RatFunc.X : RatFunc F) p = algebraMap F[X] (RatFunc F) p := by
  have h : (Polynomial.aeval (RatFunc.X : RatFunc F) : F[X] →ₐ[F] RatFunc F)
      = IsScalarTower.toAlgHom F F[X] (RatFunc F) := by
    refine Polynomial.algHom_ext ?_
    simp [RatFunc.algebraMap_X]
  exact congrArg (fun φ => φ p) h

/-- **Substituting `u⁻¹` into a polynomial and clearing the pole reverses its coefficients.** -/
theorem aeval_inv_X_mul_pow (p : F[X]) :
    Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹ p * RatFunc.X ^ p.natDegree
      = algebraMap F[X] (RatFunc F) p.reverse := by
  letI : Invertible (RatFunc.X : RatFunc F) := invertibleOfNonzero RatFunc.X_ne_zero
  have h := Polynomial.eval₂_reflect_mul_pow (algebraMap F (RatFunc F))
    (RatFunc.X : RatFunc F) p.natDegree (Polynomial.reflect p.natDegree p)
    (natDegree_reflect_le.trans_eq (max_self _))
  rw [reflect_reflect, invOf_eq_inv] at h
  calc Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹ p * RatFunc.X ^ p.natDegree
      = Polynomial.eval₂ (algebraMap F (RatFunc F)) (RatFunc.X : RatFunc F)⁻¹ p
          * RatFunc.X ^ p.natDegree := by rw [Polynomial.aeval_def]
    _ = Polynomial.eval₂ (algebraMap F (RatFunc F)) (RatFunc.X : RatFunc F)
          (Polynomial.reflect p.natDegree p) := h
    _ = Polynomial.aeval (RatFunc.X : RatFunc F) p.reverse := by rw [Polynomial.aeval_def]; rfl
    _ = algebraMap F[X] (RatFunc F) p.reverse := aeval_X_eq_algebraMap _

/-! ## The order at infinity -/

/-- **The order of a rational function at the point at infinity**: the order at the origin of the
function obtained by inverting the parameter. -/
def ordInfty (g : RatFunc F) : ℤ := ord (RatFunc F) (pointPlace (0 : F)) (ratFuncInv g)

theorem ratFuncInv_ne_zero {g : RatFunc F} (hg : g ≠ 0) : ratFuncInv g ≠ 0 := by
  simpa using hg

@[simp]
theorem ordInfty_zero : ordInfty (0 : RatFunc F) = 0 := by
  rw [ordInfty, map_zero, ord_zero]

@[simp]
theorem ordInfty_one : ordInfty (1 : RatFunc F) = 0 := by
  rw [ordInfty, map_one, ord_one]

/-- **The order at infinity is additive on products.** -/
theorem ordInfty_mul {x y : RatFunc F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordInfty (x * y) = ordInfty x + ordInfty y := by
  rw [ordInfty, ordInfty, ordInfty, map_mul,
    ord_mul _ (ratFuncInv_ne_zero hx) (ratFuncInv_ne_zero hy)]

@[simp]
theorem ordInfty_inv (x : RatFunc F) : ordInfty x⁻¹ = -ordInfty x := by
  rw [ordInfty, ordInfty, map_inv₀, ord_inv]

theorem ordInfty_div {x y : RatFunc F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordInfty (x / y) = ordInfty x - ordInfty y := by
  rw [div_eq_mul_inv, ordInfty_mul hx (inv_ne_zero hy), ordInfty_inv, sub_eq_add_neg]

/-- The parameter has a simple zero at the origin. -/
@[simp]
theorem ord_zero_X : ord (RatFunc F) (pointPlace (0 : F)) RatFunc.X = 1 := by
  have h := ord_X_sub_C_self (0 : F)
  rwa [map_zero, sub_zero, RatFunc.algebraMap_X] at h

/-- **A polynomial has a pole at infinity of order its degree.** -/
theorem ordInfty_polynomial {p : F[X]} (hp : p ≠ 0) :
    ordInfty (algebraMap F[X] (RatFunc F) p) = -(p.natDegree : ℤ) := by
  have hrev : p.reverse ≠ 0 := fun h => hp (reverse_eq_zero.mp h)
  have hkey := aeval_inv_X_mul_pow p
  have hXpow : (RatFunc.X : RatFunc F) ^ p.natDegree ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  have haeval : Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹ p ≠ 0 := by
    intro h
    rw [h, zero_mul] at hkey
    exact algebraMap_ne_zero hrev hkey.symm
  -- the order at the origin of the reversed polynomial is zero: its constant term is the
  -- leading coefficient of `p`
  have hroot : ¬ p.reverse.IsRoot 0 := by
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hrhs : ord (RatFunc F) (pointPlace (0 : F)) (algebraMap F[X] (RatFunc F) p.reverse) = 0 := by
    rw [ord_polynomial 0 hrev, Polynomial.rootMultiplicity_eq_zero hroot]
    simp
  have hord := congrArg (ord (RatFunc F) (pointPlace (0 : F))) hkey
  rw [ord_mul _ haeval hXpow, ord_pow _ RatFunc.X_ne_zero, ord_zero_X, hrhs] at hord
  rw [ordInfty, ratFuncInv_algebraMap]
  omega

/-- **A rational function has order `-intDegree` at infinity.** -/
theorem ordInfty_eq_neg_intDegree {g : RatFunc F} (hg : g ≠ 0) :
    ordInfty g = -g.intDegree := by
  have hnum : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hgeq : g = algebraMap F[X] (RatFunc F) g.num / algebraMap F[X] (RatFunc F) g.denom := by
    simp [RatFunc.num_div_denom g]
  conv_lhs => rw [hgeq]
  rw [ordInfty_div (algebraMap_ne_zero hnum) (algebraMap_ne_zero hden),
    ordInfty_polynomial hnum, ordInfty_polynomial hden, RatFunc.intDegree]
  ring

/-! ## The degree of a principal divisor on the projective line -/

/-- **The divisor of a rational function on the projective line has degree zero**: the orders of a
nonzero rational function at the points of the line, together with its order at infinity, sum to
zero. -/
theorem finsum_ord_add_ordInfty [IsAlgClosed F] {g : RatFunc F} (hg : g ≠ 0) :
    (∑ᶠ t : F, ord (RatFunc F) (pointPlace t) g) + ordInfty g = 0 := by
  rw [finsum_ord_ratFunc hg, ordInfty_eq_neg_intDegree hg, add_neg_cancel]

end Rigidity.RET
