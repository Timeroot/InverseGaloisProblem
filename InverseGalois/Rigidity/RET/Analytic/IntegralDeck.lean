/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.ScaledComp
import InverseGalois.Rigidity.RET.Analytic.RationalDeck

/-!
# Root formulas with polynomial coefficients

A group of automorphisms of the function field of a family of equations is a group of formulas
`w ↦ N_g(z, w) / d(z)`: a polynomial numerator with polynomial coefficients, over one common
denominator taken from the coefficient ring.  The group law, the fact that the formulas permute
the roots, and the fact that different group elements move a root to different places, are all
divisibility statements between polynomials in two variables — statements which therefore hold at
every value of the parameter at once.

`IntegralDeck` bundles that data.  Away from the zeros of the denominator, and of the finitely
many other polynomials the separation statements produce, the formulas are continuous and give a
group of deck transformations of the root cover: an `Rigidity.RET.Analytic.RationalDeck`.

## Main definitions

* `Rigidity.RET.Analytic.IntegralDeck` — a group of root formulas with polynomial coefficients.
* `Rigidity.RET.Analytic.IntegralDeck.act` — the formula, evaluated.

## Main results

* `Rigidity.RET.Analytic.IntegralDeck.toRationalDeck` — such a group of formulas is a group of deck
  transformations of the root cover.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ} {G : Type} [Group G]

/-- **A group of root formulas with polynomial coefficients.**

The numerators `num g` and the single denominator `den` describe the formula
`w ↦ num g (z, w) / den z`.  The three divisibilities say, in order, that the formula carries
roots of the family to roots of the family, that the formula of the identity is the identity, and
that composing two formulas gives the formula of the product.  The last field separates two
different group elements by a Bézout identity whose right-hand side does not vanish outside `S`. -/
structure IntegralDeck (P : Polynomial (Polynomial ℂ)) (S : Finset ℂ) (G : Type) [Group G] where
  /-- the numerator of the formula of a group element. -/
  num : G → Polynomial (Polynomial ℂ)
  /-- the common denominator of all the formulas. -/
  den : Polynomial ℂ
  /-- the denominator does not vanish outside the exceptional set. -/
  den_ne : ∀ z ∉ (S : Set ℂ), den.eval z ≠ 0
  /-- the formulas carry roots of the family to roots of the family. -/
  dvd_root : ∀ g : G, P ∣ scaledComp P (num g) den
  /-- the formula of the identity is the identity. -/
  dvd_one : P ∣ num 1 - C den * X
  /-- composing two formulas gives the formula of the product. -/
  dvd_mul : ∀ g h : G,
    P ∣ scaledComp (num g) (num h) den - C (den ^ (num g).natDegree) * num (g * h)
  /-- different group elements move a root to different places. -/
  sep : ∀ g h : G, g ≠ h → ∃ (A B : Polynomial (Polynomial ℂ)) (c : Polynomial ℂ),
    (∀ z ∉ (S : Set ℂ), c.eval z ≠ 0) ∧ A * P + B * (num g - num h) = C c

namespace IntegralDeck

variable (D : IntegralDeck P S G)

/-- **The formula of a group element, evaluated.** -/
def act (g : G) (z w : ℂ) : ℂ := (spec (D.num g) z).eval w / D.den.eval z

theorem eval₂_eq_spec_eval (N : Polynomial (Polynomial ℂ)) (z w : ℂ) :
    eval₂ (Polynomial.evalRingHom z) w N = (spec N z).eval w :=
  (Polynomial.eval_map _ _).symm

theorem act_eq (g : G) (z w : ℂ) :
    D.act g z w = (D.den.eval z)⁻¹ * eval₂ (Polynomial.evalRingHom z) w (D.num g) := by
  rw [act, eval₂_eq_spec_eval, div_eq_inv_mul]

theorem inv_mul_den (z : ℂ) (hz : z ∉ (S : Set ℂ)) :
    (Polynomial.evalRingHom z) D.den * (D.den.eval z)⁻¹ = 1 :=
  mul_inv_cancel₀ (D.den_ne z hz)

/-! ### The formulas act on the roots -/

theorem isRoot_act (g : G) {z w : ℂ} (hz : z ∉ (S : Set ℂ)) (hw : (spec P z).IsRoot w) :
    (spec P z).IsRoot (D.act g z w) := by
  have h := isRoot_of_dvd_scaledComp (Polynomial.evalRingHom z) (D.dvd_root g)
    (D.inv_mul_den z hz) (D.den_ne z hz) hw
  rwa [← D.act_eq g z w] at h

theorem act_one' {z w : ℂ} (hz : z ∉ (S : Set ℂ)) (hw : (spec P z).IsRoot w) :
    D.act 1 z w = w := by
  have h := eval₂_eq_of_dvd_sub (Polynomial.evalRingHom z) D.dvd_one hw
  rw [eval₂_mul, eval₂_C, eval₂_X] at h
  rw [D.act_eq, h, show (Polynomial.evalRingHom z) D.den = D.den.eval z from rfl, ← mul_assoc,
    inv_mul_cancel₀ (D.den_ne z hz), one_mul]

theorem act_mul' (g h : G) {z w : ℂ} (hz : z ∉ (S : Set ℂ)) (hw : (spec P z).IsRoot w) :
    D.act (g * h) z w = D.act g z (D.act h z w) := by
  have hd : (Polynomial.evalRingHom z) D.den ≠ 0 := D.den_ne z hz
  have heq := eval₂_eq_of_dvd_sub (Polynomial.evalRingHom z) (D.dvd_mul g h) hw
  rw [eval₂_scaledComp_of_inv (Polynomial.evalRingHom z) w (D.den.eval z)⁻¹ _ _
      (D.inv_mul_den z hz), eval₂_mul, eval₂_C, map_pow] at heq
  have hcancel := mul_left_cancel₀ (pow_ne_zero (D.num g).natDegree hd) heq
  rw [D.act_eq (g * h) z w, D.act_eq g z (D.act h z w), ← hcancel, D.act_eq h z w]

/-! ### The formulas are pairwise different on the roots -/

theorem act_ne (g h : G) (hgh : g ≠ h) {z w : ℂ} (hz : z ∉ (S : Set ℂ))
    (hw : (spec P z).IsRoot w) : D.act g z w ≠ D.act h z w := by
  obtain ⟨A, B, c, hc, hbez⟩ := D.sep g h hgh
  have hval := congrArg (eval₂ (Polynomial.evalRingHom z) w) hbez
  rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_sub, eval₂_C,
    show eval₂ (Polynomial.evalRingHom z) w P = 0 from (eval₂_eq_spec_eval P z w).trans hw,
    mul_zero, zero_add] at hval
  intro hEq
  have hnum : eval₂ (Polynomial.evalRingHom z) w (D.num g)
      = eval₂ (Polynomial.evalRingHom z) w (D.num h) := by
    have := hEq
    rw [D.act_eq, D.act_eq] at this
    exact mul_left_cancel₀ (inv_ne_zero (D.den_ne z hz)) this
  rw [hnum, sub_self, mul_zero] at hval
  exact hc z hz hval.symm

/-! ### Continuity -/

theorem continuousOn_act (g : G) :
    ContinuousOn (fun q : ℂ × ℂ => D.act g q.1 q.2) {q : ℂ × ℂ | q.1 ∉ (S : Set ℂ)} := by
  have hnum : Continuous fun q : ℂ × ℂ => (spec (D.num g) q.1).eval q.2 :=
    continuous_biEval (D.num g)
  have hden : Continuous fun q : ℂ × ℂ => D.den.eval q.1 :=
    D.den.continuous_aeval.comp continuous_fst
  exact hnum.continuousOn.div hden.continuousOn fun q hq => D.den_ne q.1 hq

/-! ### The resulting group of deck transformations -/

/-- **A group of root formulas is a group of deck transformations of the root cover.** -/
def toRationalDeck : RationalDeck P S G where
  act := D.act
  continuousOn := D.continuousOn_act
  isRoot := D.isRoot_act
  act_one := D.act_one'
  act_mul := D.act_mul'
  injOn := fun {_ _} hz hw g h hgh => by
    by_contra hne
    exact D.act_ne g h hne hz hw hgh

end IntegralDeck

end Rigidity.RET.Analytic

end
