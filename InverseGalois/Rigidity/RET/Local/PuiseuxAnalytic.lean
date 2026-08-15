/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Pullback
import InverseGalois.Rigidity.RET.Local.PowerSeriesPlace
import InverseGalois.Rigidity.RET.Local.TaylorSeries

/-!
# A holomorphic branch of a family gives a formal root in the Kummer coordinate

Substituting the Kummer coordinate `X = s + uᵉ` into a family of equations and asking for a root is
a question that can be posed in two worlds: in the world of holomorphic functions of `u` near the
origin, and in the world of formal power series in `u`.  Taking Taylor series carries the first
answer to the second, because it is a ring homomorphism: a holomorphic function that solves the
equation near the origin has a Taylor series that solves it formally.

The proof is entirely formal once the Taylor homomorphism is available.  Substituting the Kummer
coordinate is a homomorphism of the coefficient ring into the germs, its composite with the Taylor
homomorphism is the Kummer substitution into power series, and evaluating a germ at a point is a
homomorphism whose composite with it is evaluation of the coefficient at `s + uᵉ`.  Chasing a
polynomial through those two squares turns the analytic identity into the formal one.

## Main definitions

* `Rigidity.RET.kummerSubstC` — the Kummer substitution with complex coefficients.
* `Rigidity.RET.kummerGerm` — the Kummer substitution valued in germs of smooth functions.

## Main results

* `Rigidity.RET.taylorHom_comp_kummerGerm` — the Taylor series of the Kummer coordinate.
* `Rigidity.RET.eval₂_kummerSubstC_eq_zero` — the Taylor series of a holomorphic root of the family
  in the Kummer coordinate is a formal root.
* `Rigidity.RET.kummerSubst_eq_kummerSubstC` — the Kummer substitution of a subfield of the complex
  numbers is the complex one, applied to the extended coefficients.
-/

open Polynomial Filter Topology GeomAKLB

noncomputable section

namespace Rigidity.RET

/-! ### The Kummer substitution with complex coefficients -/

/-- The **Kummer substitution** `X ↦ s + uᵉ`, from polynomials in the parameter to formal power
series in the local coordinate. -/
def kummerSubstC (s : ℂ) (e : ℕ) : Polynomial ℂ →+* PowerSeries ℂ :=
  Polynomial.coeToPowerSeries.ringHom.comp (Analytic.substHom s e)

@[simp] theorem kummerSubstC_C (s : ℂ) (e : ℕ) (a : ℂ) :
    kummerSubstC s e (C a) = PowerSeries.C a := by
  simp [kummerSubstC]

@[simp] theorem kummerSubstC_X (s : ℂ) (e : ℕ) :
    kummerSubstC s e X = PowerSeries.C s + PowerSeries.X ^ e := by
  simp [kummerSubstC]

/-! ### The Kummer substitution valued in germs -/

/-- Constants, as a ring homomorphism into the smooth germs. -/
def constGermHom (x : ℂ) : ℂ →+* smoothAt x where
  toFun c := constGerm x c
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[simp] theorem constGermHom_apply (x c : ℂ) : constGermHom x c = constGerm x c := rfl

@[simp] theorem coe_constGermHom (x c : ℂ) :
    ((constGermHom x c : smoothAt x) : ℂ → ℂ) = fun _ => c := rfl

/-- The Kummer coordinate `u ↦ s + uᵉ`, as a smooth germ at the origin. -/
def kummerGermFun (s : ℂ) (e : ℕ) : smoothAt (0 : ℂ) := constGerm 0 s + idGerm 0 ^ e

@[simp] theorem coe_kummerGermFun (s : ℂ) (e : ℕ) (u : ℂ) :
    ((kummerGermFun s e : smoothAt (0 : ℂ)) : ℂ → ℂ) u = s + u ^ e := rfl

/-- The **Kummer substitution valued in germs**: a polynomial in the parameter becomes a
holomorphic function of the local coordinate. -/
def kummerGerm (s : ℂ) (e : ℕ) : Polynomial ℂ →+* smoothAt (0 : ℂ) :=
  Polynomial.eval₂RingHom (constGermHom 0) (kummerGermFun s e)

/-- Evaluating a germ at a point of the plane is a ring homomorphism. -/
def evalGermHom (x u : ℂ) : smoothAt x →+* ℂ :=
  (Pi.evalRingHom (fun _ : ℂ => ℂ) u).comp (smoothAt x).subtype

@[simp] theorem evalGermHom_apply (x u : ℂ) (f : smoothAt x) :
    evalGermHom x u f = (f : ℂ → ℂ) u := rfl

/-- **Evaluating the Kummer coordinate at a point of the plane is evaluation of the parameter at
`s + uᵉ`.** -/
theorem evalGermHom_comp_kummerGerm (s : ℂ) (e : ℕ) (u : ℂ) :
    (evalGermHom 0 u).comp (kummerGerm s e) = evalRingHom (s + u ^ e) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_ <;> simp [kummerGerm]

/-- **The Taylor series of the Kummer coordinate is the Kummer substitution.** -/
theorem taylorHom_comp_kummerGerm (s : ℂ) (e : ℕ) :
    (taylorHom 0).comp (kummerGerm s e) = kummerSubstC s e := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [kummerGerm]
  · simp [kummerGerm, kummerGermFun]

/-! ### From a holomorphic root to a formal root -/

/-- The value at a point of the plane of the substituted family. -/
theorem coe_eval₂_kummerGerm (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ)
    (g : smoothAt (0 : ℂ)) (u : ℂ) :
    ((Polynomial.eval₂ (kummerGerm s e) g P : smoothAt (0 : ℂ)) : ℂ → ℂ) u
      = (Analytic.spec P (s + u ^ e)).eval ((g : ℂ → ℂ) u) := by
  have h := Polynomial.hom_eval₂ P (kummerGerm s e) (evalGermHom 0 u) g
  rw [evalGermHom_comp_kummerGerm] at h
  rw [show ((Polynomial.eval₂ (kummerGerm s e) g P : smoothAt (0 : ℂ)) : ℂ → ℂ) u
      = evalGermHom 0 u (Polynomial.eval₂ (kummerGerm s e) g P) from rfl, h,
    Polynomial.eval₂_eq_eval_map]
  rfl

/-- **A holomorphic root of the family in the Kummer coordinate has a formal root as its Taylor
series.** -/
theorem eval₂_kummerSubstC_eq_zero (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ)
    (g : smoothAt (0 : ℂ))
    (h : ∀ᶠ u in 𝓝 (0 : ℂ), (Analytic.spec P (s + u ^ e)).eval ((g : ℂ → ℂ) u) = 0) :
    Polynomial.eval₂ (kummerSubstC s e) (taylorHom 0 g) P = 0 := by
  have hcomp := Polynomial.hom_eval₂ P (kummerGerm s e) (taylorHom 0) g
  rw [taylorHom_comp_kummerGerm] at hcomp
  rw [← hcomp]
  refine taylorHom_eq_zero_of_eventuallyEq _ ?_
  filter_upwards [h] with u hu
  rw [coe_eval₂_kummerGerm]
  exact hu

/-! ### Comparison with the Kummer substitution of the constant field -/

section Descent

variable [Algebra k ℂ]

/-- **The Kummer substitution of the constant field is the complex one**, applied to the
coefficients extended to the complex numbers. -/
theorem kummerSubst_eq_kummerSubstC (s : k) (e : ℕ) :
    kummerSubst ℂ s e
      = (kummerSubstC (algebraMap k ℂ s) e).comp (Polynomial.mapRingHom (algebraMap k ℂ)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_ <;> simp

end Descent

end Rigidity.RET

end
