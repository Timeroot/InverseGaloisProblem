/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.GermKummer
import InverseGalois.Rigidity.RET.RatFuncSubst

/-!
# The substitution at infinity into the field of meromorphic germs

The Kummer substitution `T = s + u ^ d` reads a rational function of `T` as a meromorphic germ at
`u = 0`, and so describes the line near the point `s`.  The point at infinity is described the same
way by the substitution `T = u ^ (-d)`: as `u` runs over a small punctured disc at the origin, `T`
runs over the exterior of a large disc, wrapping `d` times.

Formally the two substitutions differ only by the inversion `T ↦ T⁻¹` of the field of rational
functions, and that is how the substitution at infinity is built here: as the Kummer substitution
at `0` precomposed with the inversion.  In particular it is injective for free, and the order of a
germ measures the order of vanishing at infinity, with the sign reversed.

## Main definitions

* `Rigidity.RET.Analytic.invFun` — the parameter at infinity `u ↦ (u ^ d)⁻¹`.
* `Rigidity.RET.Analytic.invGerm` — its germ at the origin.
* `Rigidity.RET.Analytic.invAlgHom`, `Rigidity.RET.Analytic.invRatHom` — the substitution on
  polynomials and on rational functions.

## Main results

* `Rigidity.RET.Analytic.ord_invGerm` — the parameter at infinity has a pole of order exactly `d`.
* `Rigidity.RET.Analytic.invRatHom_injective` — the substitution is injective.
-/

open Filter Topology Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

open MeroGerm

/-! ### Inverting a germ -/

namespace MeroGerm

variable {x : ℂ}

/-- The inverse of the germ of a meromorphic function is the germ of the pointwise inverse. -/
theorem of_inv {f : ℂ → ℂ} (hf : MeromorphicAt f x) : (of hf)⁻¹ = of hf.inv := by
  by_cases h0 : of hf = 0
  · have hz : ∀ᶠ z in 𝓝[≠] x, f z = 0 := (of_eq_zero_iff hf).1 h0
    rw [h0, inv_zero]
    refine ((of_eq_zero_iff hf.inv).2 ?_).symm
    filter_upwards [hz] with z hz
    simp [Pi.inv_apply, hz]
  · refine inv_eq_of_mul_eq_one_right ?_
    have hne : ¬ (f =ᶠ[𝓝[≠] x] 0) := fun h => h0 ((of_eq_zero_iff hf).2 h)
    have hev : ∀ᶠ z in 𝓝[≠] x, f z ≠ 0 :=
      (hf.eventually_eq_zero_or_eventually_ne_zero).resolve_left hne
    refine Subtype.ext ?_
    show ((f : PunctGerm x) * ((f⁻¹ : ℂ → ℂ) : PunctGerm x)) = 1
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [hev] with z hz
    simp [mul_inv_cancel₀ hz]

end MeroGerm

/-! ### The parameter at infinity -/

/-- The parameter at infinity of exponent `d`: the function `u ↦ (u ^ d)⁻¹`. -/
def invFun (d : ℕ) : ℂ → ℂ := fun u => (u ^ d)⁻¹

theorem analyticAt_powFun (d : ℕ) : AnalyticAt ℂ (fun u : ℂ => u ^ d) 0 :=
  analyticAt_id.pow d

theorem meromorphicAt_invFun (d : ℕ) : MeromorphicAt (invFun d) 0 :=
  (analyticAt_powFun d).meromorphicAt.inv

/-- The germ at the origin of the parameter at infinity. -/
def invGerm (d : ℕ) : MeroGerm (0 : ℂ) := of (meromorphicAt_invFun d)

theorem invGerm_eq_inv (d : ℕ) : invGerm d = (of (analyticAt_powFun d).meromorphicAt)⁻¹ :=
  (MeroGerm.of_inv _).symm

theorem ord_powGerm (d : ℕ) :
    ord (of (analyticAt_powFun d).meromorphicAt) = ((d : ℤ) : WithTop ℤ) := by
  refine ord_eq_of_eventually_smul _ (g := fun _ => (1 : ℂ)) analyticAt_const one_ne_zero ?_
  filter_upwards with u
  simp [zpow_natCast]

/-- **The parameter at infinity has a pole of order exactly `d` at the origin.** -/
theorem ord_invGerm (d : ℕ) : ord (invGerm d) = ((-d : ℤ) : WithTop ℤ) := by
  rw [invGerm_eq_inv, ord_inv, ord_powGerm]
  rfl

/-! ### The substitution on polynomials -/

/-- Substituting the parameter at infinity `(u ^ d)⁻¹` into a polynomial. -/
def invAlgHom (d : ℕ) : Polynomial ℂ →ₐ[ℂ] MeroGerm (0 : ℂ) := aeval (invGerm d)

@[simp] theorem invAlgHom_X (d : ℕ) : invAlgHom d X = invGerm d := by
  simp [invAlgHom]

@[simp] theorem invAlgHom_C (d : ℕ) (a : ℂ) : invAlgHom d (C a) = constHom 0 a := by
  rw [invAlgHom, aeval_C, algebraMap_eq]

/-- The substitution at infinity computed pointwise: the underlying germ of the image of a
polynomial is the germ of the pointwise substitution. -/
theorem subtype_comp_invAlgHom (d : ℕ) :
    ((meroGerms (0 : ℂ)).subtype).comp (invAlgHom d).toRingHom
      = (Filter.Germ.coeRingHom (𝓝[≠] (0 : ℂ))).comp
          (aeval (R := ℂ) (A := ℂ → ℂ) (invFun d)).toRingHom := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · show ((invAlgHom d) (C a)).1 = ((aeval (R := ℂ) (A := ℂ → ℂ) (invFun d) (C a) : ℂ → ℂ) :
      PunctGerm (0 : ℂ))
    rw [invAlgHom_C, aeval_C]
    rfl
  · show ((invAlgHom d) X).1 = ((aeval (R := ℂ) (A := ℂ → ℂ) (invFun d) X : ℂ → ℂ) :
      PunctGerm (0 : ℂ))
    rw [invAlgHom_X, aeval_X]
    rfl

/-! ### The substitution on rational functions -/

/-- **The substitution at infinity**, on rational functions: the Kummer substitution at the origin
precomposed with the inversion of the parameter. -/
def invRatHom {d : ℕ} (hd : d ≠ 0) : RatFunc ℂ →ₐ[ℂ] MeroGerm (0 : ℂ) :=
  (kummerRatHom 0 hd).comp (ratFuncInv : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ).toAlgHom

theorem invRatHom_injective {d : ℕ} (hd : d ≠ 0) : Function.Injective (invRatHom hd) :=
  (kummerRatHom_injective 0 hd).comp (ratFuncInv : RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ).injective

theorem invRatHom_X {d : ℕ} (hd : d ≠ 0) : invRatHom hd (RatFunc.X : RatFunc ℂ) = invGerm d := by
  rw [invRatHom, AlgHom.comp_apply, AlgEquiv.coe_algHom, ratFuncInv_X, map_inv₀,
    show (RatFunc.X : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) X from
      (RatFunc.algebraMap_X).symm,
    kummerRatHom_algebraMap, kummerHom_apply, invGerm_eq_inv]
  refine congrArg (·⁻¹) (of_congr _ _ ?_)
  filter_upwards with u
  rw [kummerHom_eval]
  simp

/-- The substitution at infinity restricted to polynomials is the polynomial substitution. -/
theorem invRatHom_algebraMap {d : ℕ} (hd : d ≠ 0) (p : Polynomial ℂ) :
    invRatHom hd (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = invAlgHom d p := by
  have h : (invRatHom hd).comp (IsScalarTower.toAlgHom ℂ (Polynomial ℂ) (RatFunc ℂ))
      = invAlgHom d := by
    refine Polynomial.algHom_ext ?_
    show invRatHom hd (algebraMap (Polynomial ℂ) (RatFunc ℂ) X) = invAlgHom d X
    rw [RatFunc.algebraMap_X, invRatHom_X, invAlgHom_X]
  exact congrArg (fun f : Polynomial ℂ →ₐ[ℂ] MeroGerm (0 : ℂ) => f p) h

end Rigidity.RET.Analytic

end
