/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Analytic.GermField

/-!
# The Kummer substitution into the field of meromorphic germs

Fix a point `s : ℂ` and an exponent `d ≠ 0`.  Substituting the Kummer parameter `T = s + u ^ d`
into a rational function of `T` produces a meromorphic function of `u` near `u = 0`, hence a
meromorphic germ at `0`.  This file builds that substitution as a `ℂ`-algebra map
`RatFunc ℂ →ₐ[ℂ] MeroGerm 0`, and records the two order computations that make it useful: the
uniformizer `T - s` pulls back to a germ of order exactly `d`, while a polynomial not vanishing at
`s` pulls back to a germ of order zero.  Together they give injectivity, which is what allows the
substitution to be extended from polynomials to rational functions.

## Main definitions

* `Rigidity.RET.Analytic.kummerFun` — the Kummer parameter `u ↦ s + u ^ d`.
* `Rigidity.RET.Analytic.kummerHom`, `Rigidity.RET.Analytic.kummerAlgHom` — the substitution on
  polynomials.
* `Rigidity.RET.Analytic.kummerRatHom` — the substitution on rational functions.

## Main results

* `Rigidity.RET.Analytic.ord_kummerHom_X_sub_C` — the uniformizer pulls back to order `d`.
* `Rigidity.RET.Analytic.kummerHom_injective`, `Rigidity.RET.Analytic.kummerRatHom_injective` —
  the substitution is injective.
-/

open Filter Topology Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

open MeroGerm

/-- The Kummer parameter at `s` of exponent `d`: the function `u ↦ s + u ^ d`. -/
def kummerFun (s : ℂ) (d : ℕ) : ℂ → ℂ := fun u => s + u ^ d

theorem analyticAt_kummerFun (s : ℂ) (d : ℕ) : AnalyticAt ℂ (kummerFun s d) 0 :=
  analyticAt_const.add (analyticAt_id.pow d)

theorem analyticAt_kummerComp (s : ℂ) (d : ℕ) (p : Polynomial ℂ) :
    AnalyticAt ℂ ((aeval (R := ℂ) (kummerFun s d) p : ℂ → ℂ)) 0 := by
  have h : ((aeval (R := ℂ) (kummerFun s d) p : ℂ → ℂ))
      = fun u => aeval (kummerFun s d u) p := by
    funext u
    exact (aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : ℂ => ℂ) u) (kummerFun s d) p).symm
  rw [h]
  exact (analyticAt_kummerFun s d).aeval_polynomial p

/-- Substituting the Kummer parameter `s + u ^ d` into a polynomial. -/
def kummerHom (s : ℂ) (d : ℕ) : Polynomial ℂ →+* MeroGerm (0 : ℂ) :=
  RingHom.codRestrict
    ((Filter.Germ.coeRingHom (𝓝[≠] (0 : ℂ))).comp
      (aeval (R := ℂ) (A := ℂ → ℂ) (kummerFun s d)).toRingHom)
    (meroGerms 0)
    (fun p => ⟨_, (analyticAt_kummerComp s d p).meromorphicAt, rfl⟩)

theorem kummerHom_apply (s : ℂ) (d : ℕ) (p : Polynomial ℂ) :
    kummerHom s d p = of (analyticAt_kummerComp s d p).meromorphicAt := rfl

theorem kummerHom_eval (s : ℂ) (d : ℕ) (p : Polynomial ℂ) (u : ℂ) :
    (aeval (R := ℂ) (kummerFun s d) p : ℂ → ℂ) u = aeval (s + u ^ d) p :=
  (aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : ℂ => ℂ) u) (kummerFun s d) p).symm

/-- The Kummer parameter meets the branch point to order exactly `d`. -/
theorem ord_kummerHom_X_sub_C (s : ℂ) (d : ℕ) :
    ord (kummerHom s d (X - C s)) = ((d : ℤ) : WithTop ℤ) := by
  rw [kummerHom_apply]
  refine ord_eq_of_eventually_smul _ (g := fun _ => (1 : ℂ)) analyticAt_const one_ne_zero ?_
  filter_upwards with u
  rw [kummerHom_eval]
  simp [zpow_natCast]

/-- A polynomial not vanishing at the branch point pulls back to a germ of order zero. -/
theorem ord_kummerHom_of_eval_ne_zero {s : ℂ} {d : ℕ} (hd : d ≠ 0) {p : Polynomial ℂ}
    (hp : p.eval s ≠ 0) : ord (kummerHom s d p) = 0 := by
  rw [kummerHom_apply]
  refine ord_eq_zero_of_analyticAt (analyticAt_kummerComp s d p) ?_
  rw [kummerHom_eval]
  simpa [zero_pow hd] using hp

theorem kummerHom_X_sub_C_ne_zero (s : ℂ) (d : ℕ) : kummerHom s d (X - C s) ≠ 0 := by
  intro h
  have hord := ord_kummerHom_X_sub_C s d
  rw [h, ord_zero] at hord
  exact WithTop.top_ne_coe hord

theorem kummerHom_ne_zero_of_eval_ne_zero {s : ℂ} {d : ℕ} (hd : d ≠ 0) {p : Polynomial ℂ}
    (hp : p.eval s ≠ 0) : kummerHom s d p ≠ 0 := by
  intro h
  have hord := ord_kummerHom_of_eval_ne_zero hd hp
  rw [h, ord_zero] at hord
  simp at hord

/-- **The Kummer substitution is injective**: a nonzero polynomial does not pull back to the zero
germ.  Splitting off the largest power of `X - C s` writes the image as a product of two nonzero
germs, one of order `d` times the multiplicity, the other of order zero. -/
theorem kummerHom_injective (s : ℂ) {d : ℕ} (hd : d ≠ 0) :
    Function.Injective (kummerHom s d) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro p hp0
  by_contra hp
  set m := p.rootMultiplicity s with hm
  set q := p /ₘ (X - C s) ^ m with hq
  have hpq : (X - C s) ^ m * q = p := pow_mul_divByMonic_rootMultiplicity_eq p s
  have hqs : q.eval s ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero s hp
  have h1 : kummerHom s d ((X - C s) ^ m) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (kummerHom_X_sub_C_ne_zero s d)
  have h2 : kummerHom s d q ≠ 0 := kummerHom_ne_zero_of_eval_ne_zero hd hqs
  refine (mul_ne_zero h1 h2) ?_
  rw [← map_mul, hpq, hp0]

theorem kummerHom_C (s : ℂ) (d : ℕ) (a : ℂ) : kummerHom s d (C a) = constHom 0 a := by
  rw [kummerHom_apply, constHom_apply]
  refine of_congr _ _ ?_
  filter_upwards with u
  rw [kummerHom_eval]
  simp

/-- The Kummer substitution as a `ℂ`-algebra map. -/
def kummerAlgHom (s : ℂ) (d : ℕ) : Polynomial ℂ →ₐ[ℂ] MeroGerm (0 : ℂ) :=
  { kummerHom s d with
    commutes' := fun a => by
      rw [algebraMap_eq]
      exact kummerHom_C s d a }

@[simp] theorem kummerAlgHom_apply (s : ℂ) (d : ℕ) (p : Polynomial ℂ) :
    kummerAlgHom s d p = kummerHom s d p := rfl

theorem kummerAlgHom_injective (s : ℂ) {d : ℕ} (hd : d ≠ 0) :
    Function.Injective (kummerAlgHom s d) := kummerHom_injective s hd

/-- The Kummer substitution, extended to the field of rational functions: a rational function of
`T` becomes the germ at `0` of the meromorphic function obtained by substituting `T = s + u ^ d`. -/
def kummerRatHom (s : ℂ) {d : ℕ} (hd : d ≠ 0) : RatFunc ℂ →ₐ[ℂ] MeroGerm (0 : ℂ) :=
  RatFunc.liftAlgHom (kummerAlgHom s d)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (kummerAlgHom_injective s hd))

@[simp] theorem kummerRatHom_algebraMap (s : ℂ) {d : ℕ} (hd : d ≠ 0) (p : Polynomial ℂ) :
    kummerRatHom s hd (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = kummerHom s d p := by
  simpa using RatFunc.liftAlgHom_apply_div' (S := ℂ) (kummerAlgHom s d)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (kummerAlgHom_injective s hd)) p 1

theorem kummerRatHom_injective (s : ℂ) {d : ℕ} (hd : d ≠ 0) :
    Function.Injective (kummerRatHom s hd) :=
  RatFunc.liftAlgHom_injective _ (kummerAlgHom_injective s hd) _

/-- The image of the uniformizer `T - s` has order exactly `d`. -/
theorem ord_kummerRatHom_X_sub_C (s : ℂ) {d : ℕ} (hd : d ≠ 0) :
    ord (kummerRatHom s hd (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - C s)))
      = ((d : ℤ) : WithTop ℤ) := by
  rw [kummerRatHom_algebraMap, ord_kummerHom_X_sub_C]

end Rigidity.RET.Analytic

end
