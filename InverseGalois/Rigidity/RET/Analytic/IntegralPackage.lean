/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverRational

/-!
# Integrality over the polynomials of the base, as a statement about a ring homomorphism

The functions on the total space of a covering form a commutative ring, and the polynomials of the
base coordinate map into it: a polynomial `p` becomes the function `y ↦ p (f y)`.  The equation
produced by the growth estimates says exactly that a holomorphic function of moderate growth,
multiplied by the leading coefficient of its equation, is *integral* for that ring homomorphism —
it satisfies a monic polynomial equation with coefficients in the image.

Packaging the equation this way replaces the family of coefficients by a single polynomial and
puts the conclusion in the language the algebraic side of the theory speaks, with no auxiliary
algebra instance on the ring of functions.

## Main definitions

* `Rigidity.RET.baseEvalHom` — the ring homomorphism from the polynomials of the base coordinate
  to the functions on the total space.

## Main results

* `Rigidity.RET.eval₂_baseEvalHom_apply` — evaluating a polynomial equation at a point of the total
  space is the same as evaluating it in the base coordinate at that point.
* `Rigidity.RET.exists_monic_eval₂_of_growth` — the equation of a function of moderate growth, as a
  single monic polynomial of degree the order of the deck group.
* `Rigidity.RET.isIntegralElem_of_growth` — that function, times the leading coefficient of its
  equation, is integral for `baseEvalHom`.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

section Hom

variable {Y : Type*}

/-- **The polynomials of the base coordinate, read as functions on the total space.** -/
def baseEvalHom (f : Y → ℂ) : ℂ[X] →+* (Y → ℂ) where
  toFun p := fun y => p.eval (f y)
  map_one' := by funext y; simp
  map_mul' p q := by funext y; simp
  map_zero' := by funext y; simp
  map_add' p q := by funext y; simp

@[simp]
theorem baseEvalHom_apply (f : Y → ℂ) (p : ℂ[X]) (y : Y) : baseEvalHom f p y = p.eval (f y) :=
  rfl

/-- **Evaluating at a point of the total space commutes with evaluating a polynomial equation**:
the value at `y` of an equation read in the ring of functions is the equation read in the base
coordinate at `f y`. -/
theorem eval₂_baseEvalHom_apply (f : Y → ℂ) (x : Y → ℂ) (P : ℂ[X][X]) (y : Y) :
    Polynomial.eval₂ (baseEvalHom f) x P y = P.eval₂ (evalRingHom (f y)) (x y) := by
  have hcomp : (Pi.evalRingHom (fun _ : Y => ℂ) y).comp (baseEvalHom f) = evalRingHom (f y) :=
    RingHom.ext fun p => rfl
  have := Polynomial.hom_eval₂ P (baseEvalHom f) (Pi.evalRingHom (fun _ : Y => ℂ) y) x
  rw [hcomp] at this
  exact this

end Hom

section Integral

variable {Y : Type*} [TopologicalSpace Y] {f g : Y → ℂ}
variable {H : Type*} [Group H] [Fintype H] [MulAction H Y] [ContinuousConstSMul H Y]

/-- **The equation of a function of moderate growth, as a single monic polynomial.**

The coefficients are polynomials in the base coordinate, the degree is the order of the deck group,
and the equation is satisfied at every point of the total space by the function multiplied by the
leading coefficient of its equation. -/
theorem exists_monic_eval₂_of_growth (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (S : Finset ℂ) (hrange : Set.range f = (↑S)ᶜ)
    (hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖g y‖ * ‖f y - s‖ ^ N ≤ C)
    {A R₀ : ℝ} (hA : 0 ≤ A) {m : ℕ} (hinf : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖g y‖ ≤ A * ‖f y‖ ^ m) :
    ∃ (P : ℂ[X][X]) (d : ℂ[X]), P.Monic ∧ P.natDegree = Fintype.card H ∧ d.Monic ∧
      ∀ y : Y, P.eval₂ (evalRingHom (f y)) (d.eval (f y) * g y) = 0 := by
  obtain ⟨b, d, hd, heq⟩ :=
    exists_integral_of_growth hf hover htrans hg S hrange hpunct hA hinf
  set n := Fintype.card H with hn
  set r : ℂ[X][X] := ∑ k ∈ Finset.range n, C (b k) * X ^ k with hr
  have hdeg : r.degree < (X ^ n : ℂ[X][X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)).2 fun k hk => ?_
    have hk' : k < n := Finset.mem_range.1 hk
    refine lt_of_le_of_lt ?_ (show (k : WithBot ℕ) < (n : WithBot ℕ) by exact_mod_cast hk')
    refine le_trans (degree_mul_le _ _) ?_
    calc (C (b k) : ℂ[X][X]).degree + (X ^ k : ℂ[X][X]).degree
        ≤ 0 + (k : WithBot ℕ) := add_le_add degree_C_le (degree_X_pow k).le
      _ = (k : WithBot ℕ) := zero_add _
  have hmonic : (X ^ n + r : ℂ[X][X]).Monic := (monic_X_pow n).add_of_left hdeg
  have hnatdeg : (X ^ n + r : ℂ[X][X]).natDegree = n := by
    have := degree_add_eq_left_of_degree_lt hdeg
    rw [natDegree, this, degree_X_pow]
    rfl
  refine ⟨X ^ n + r, d, hmonic, hnatdeg, hd, fun y => ?_⟩
  rw [hr]
  simp only [eval₂_add, eval₂_X_pow, eval₂_finset_sum, eval₂_mul, eval₂_C, coe_evalRingHom]
  exact heq y

/-- **A holomorphic function of moderate growth, times the leading coefficient of its equation, is
integral over the polynomials of the base coordinate.** -/
theorem isIntegralElem_of_growth (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (S : Finset ℂ) (hrange : Set.range f = (↑S)ᶜ)
    (hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖g y‖ * ‖f y - s‖ ^ N ≤ C)
    {A R₀ : ℝ} (hA : 0 ≤ A) {m : ℕ} (hinf : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖g y‖ ≤ A * ‖f y‖ ^ m) :
    ∃ d : ℂ[X], d.Monic ∧
      (baseEvalHom f).IsIntegralElem (fun y => d.eval (f y) * g y) := by
  obtain ⟨P, d, hP, -, hd, heq⟩ :=
    exists_monic_eval₂_of_growth (H := H) hf hover htrans hg S hrange hpunct hA hinf
  refine ⟨d, hd, P, hP, ?_⟩
  funext y
  rw [eval₂_baseEvalHom_apply]
  exact heq y

end Integral

end Rigidity.RET

end
