/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Translate

/-!
# Scaling the parameter of the line

Alongside the translations, the other coordinate changes of the affine line which preserve the
integral model `ℚ̄[X]` are the scalings `T ↦ cT` by a non-zero constant.  Together the two generate
the affine group of the line, and a cover read in an affine coordinate is the same cover with its
branch points moved by the corresponding affine map.

A scaling behaves better at the point at infinity than a translation does: it commutes with the
inversion of the parameter up to replacing `c` by `c⁻¹`, so unramifiedness at infinity can be
transported by the general machinery for semilinear isomorphisms rather than by a computation with
valuations.  What the general machinery needs is a slightly wider notion of twisting a semilinear
isomorphism, in which the two covers are read in *different* coordinates; that is
`Rigidity.RET.LineCover.SemiIso.twist₂`.

## Main definitions

* `Rigidity.RET.scalePoly` — the substitution `p ↦ p(cX)` of the integral model.
* `Rigidity.RET.scaleSubst` — the scaling `T ↦ cT` of `ℚ̄(T)`.
* `Rigidity.RET.LineCover.SemiIso.twist₂` — reading the two covers of a semilinear isomorphism in
  two coordinates related by the semilinearity.

## Main results

* `Rigidity.RET.map_placeP_scale` — a scaling moves the point `t` of the line to `c⁻¹ t`.
* `Rigidity.RET.scaleSubst_invSubst_comm` — a scaling commutes with the inversion of the parameter
  after inverting the scalar.
* `Rigidity.RET.LineCover.IsUnramifiedAtInfinity.semiIso₂` — unramifiedness at infinity travels
  along a semilinear isomorphism whose coordinate change normalizes the inversion.
* `Rigidity.RET.LineCover.IsUnramifiedOutside.twist_scale`,
  `Rigidity.RET.LineCover.IsUnramifiedAtInfinity.twist_scale` — unramifiedness travels to the
  scaled cover, with the branch locus scaled along.
-/

open Polynomial

noncomputable section


namespace Rigidity.RET

open GeomAKLB

/-! ## The scaling of the parameter -/

variable {c : k}

/-- The substitution `p ↦ p(aX)` composed with `p ↦ p(bX)` is the identity when `b * a = 1`. -/
private theorem aeval_scale_comp {a b : k} (hab : b * a = 1) :
    (aeval (C a * X : k[X])).comp (aeval (C b * X : k[X])) = AlgHom.id k k[X] := by
  refine Polynomial.algHom_ext ?_
  show (aeval (C a * X : k[X])) ((aeval (C b * X : k[X])) X) = X
  rw [aeval_X, map_mul, aeval_X, Polynomial.aeval_C, ← Polynomial.C_eq_algebraMap, ← mul_assoc,
    ← Polynomial.C_mul, hab, map_one, one_mul]

/-- The substitution `p ↦ p(cX)` of the integral model of the line, as an equivalence of
`ℚ̄`-algebras. -/
def scaleAlgEquiv (hc : c ≠ 0) : k[X] ≃ₐ[k] k[X] :=
  AlgEquiv.ofAlgHom (aeval (C c * X)) (aeval (C c⁻¹ * X))
    (aeval_scale_comp (inv_mul_cancel₀ hc)) (aeval_scale_comp (mul_inv_cancel₀ hc))

/-- **The substitution `p ↦ p(cX)` of the integral model of the line.** -/
abbrev scalePoly (hc : c ≠ 0) : k[X] ≃+* k[X] := (scaleAlgEquiv hc).toRingEquiv

@[simp] theorem scalePoly_X (hc : c ≠ 0) : scalePoly hc X = C c * X := aeval_X _

theorem scalePoly_C (hc : c ≠ 0) (a : k) : scalePoly hc (C a) = C a := by
  show (aeval (C c * X : k[X])) (C a) = C a
  rw [Polynomial.aeval_C, ← Polynomial.C_eq_algebraMap]

/-- **The scaling `T ↦ cT` of `ℚ̄(T)`.**  It moves the point `t` of the line to `c⁻¹ t`. -/
def scaleSubst (hc : c ≠ 0) : RatFunc k ≃+* RatFunc k :=
  IsFractionRing.ringEquivOfRingEquiv (A := k[X]) (B := k[X])
    (K := RatFunc k) (L := RatFunc k) (scalePoly hc)

/-- The scaling preserves the integral model, acting on it by the substitution. -/
theorem scaleSubst_polyPreserving (hc : c ≠ 0) :
    PolyPreserving (scaleSubst hc) (scalePoly hc) := fun p =>
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (scalePoly hc) p

/-- The substitution carries the coordinate at `t` to the coordinate at `c⁻¹ t`, up to the unit
`c`. -/
theorem scalePoly_X_sub_C (hc : c ≠ 0) (t : k) :
    scalePoly hc (X - C t) = C c * (X - C (c⁻¹ * t)) := by
  rw [map_sub, scalePoly_X, scalePoly_C, mul_sub, ← Polynomial.C_mul, mul_inv_cancel_left₀ hc]

/-- **A scaling moves the point `t` of the line to `c⁻¹ t`.** -/
theorem map_placeP_scale (hc : c ≠ 0) (t : k) :
    Ideal.map (scalePoly hc) (placeP t) = placeP (c⁻¹ * t) := by
  have hunit : IsUnit (C c : k[X]) := (Polynomial.isUnit_C).mpr (isUnit_iff_ne_zero.mpr hc)
  rw [placeP, placeP, Ideal.map_span, Set.image_singleton, scalePoly_X_sub_C,
    Ideal.span_singleton_mul_left_unit hunit]

/-- The inverse scaling moves the point `t` of the line to `c t`. -/
theorem map_placeP_scale_symm (hc : c ≠ 0) (t : k) :
    Ideal.map (scalePoly hc).symm (placeP t) = placeP (c * t) := by
  refine map_placeP_symm ?_
  rw [map_placeP_scale, inv_mul_cancel_left₀ hc]

/-! ## The scaling on the field of rational functions -/

/-- The scaling multiplies the parameter by `c`. -/
theorem scaleSubst_X (hc : c ≠ 0) :
    scaleSubst hc (RatFunc.X : RatFunc k) = algebraMap k (RatFunc k) c * RatFunc.X := by
  have h := scaleSubst_polyPreserving hc (X : k[X])
  rw [scalePoly_X] at h
  simpa [RatFunc.algebraMap_X, RatFunc.algebraMap_C] using h

/-- The scaling fixes the constants. -/
theorem scaleSubst_const (hc : c ≠ 0) (a : k) :
    scaleSubst hc (algebraMap k (RatFunc k) a) = algebraMap k (RatFunc k) a := by
  have h := scaleSubst_polyPreserving hc (C a)
  rw [scalePoly_C] at h
  simpa [RatFunc.algebraMap_C] using h

/-- **Scaling by `a` and then by `b` is the identity when `a * b = 1`.** -/
theorem scaleSubst_scaleSubst {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b = 1)
    (f : RatFunc k) : scaleSubst ha (scaleSubst hb f) = f := by
  have key : (scaleSubst ha : RatFunc k →+* RatFunc k).comp
      (scaleSubst hb : RatFunc k →+* RatFunc k) = RingHom.id (RatFunc k) := by
    refine ratFunc_ringHom_ext ?_ ?_
    · intro x
      show scaleSubst ha (scaleSubst hb (algebraMap k (RatFunc k) x)) = _
      rw [scaleSubst_const, scaleSubst_const]
      rfl
    · show scaleSubst ha (scaleSubst hb (RatFunc.X : RatFunc k)) = _
      rw [scaleSubst_X, map_mul, scaleSubst_X, scaleSubst_const, ← mul_assoc,
        ← map_mul, mul_comm b a, hab, map_one, one_mul]
      rfl
  exact congrArg (fun φ => φ f) key

/-- The inverse of a scaling is the scaling by the inverse. -/
theorem scaleSubst_symm_apply (hc : c ≠ 0) (f : RatFunc k) :
    (scaleSubst hc).symm f = scaleSubst (inv_ne_zero hc) f := by
  refine (scaleSubst hc).injective ?_
  rw [RingEquiv.apply_symm_apply,
    scaleSubst_scaleSubst hc (inv_ne_zero hc) (mul_inv_cancel₀ hc)]

/-- **A scaling commutes with the inversion of the parameter after inverting the scalar**: reading
the reciprocal coordinate of a scaled line is reading the reciprocally scaled reciprocal
coordinate.  In particular the scaling does not move the point at infinity. -/
theorem scaleSubst_invSubst_comm (hc : c ≠ 0) (f : RatFunc k) :
    scaleSubst (inv_ne_zero hc) (invSubst.toRingEquiv f)
      = invSubst.toRingEquiv (scaleSubst hc f) := by
  have key : (scaleSubst (inv_ne_zero hc) : RatFunc k →+* RatFunc k).comp
        (invSubst.toRingEquiv : RatFunc k →+* RatFunc k)
      = (invSubst.toRingEquiv : RatFunc k →+* RatFunc k).comp
        (scaleSubst hc : RatFunc k →+* RatFunc k) := by
    refine ratFunc_ringHom_ext ?_ ?_
    · intro a
      show scaleSubst (inv_ne_zero hc) (invSubst (algebraMap k (RatFunc k) a))
        = invSubst (scaleSubst hc (algebraMap k (RatFunc k) a))
      rw [invSubst.commutes, scaleSubst_const, scaleSubst_const, invSubst.commutes]
    · show scaleSubst (inv_ne_zero hc) (invSubst (RatFunc.X : RatFunc k))
        = invSubst (scaleSubst hc RatFunc.X)
      rw [invSubst_X, map_inv₀, scaleSubst_X, scaleSubst_X, map_mul, invSubst_X,
        invSubst.commutes, mul_inv, map_inv₀, inv_inv]
  exact congrArg (fun φ => φ f) key

/-! ## Twisting a semilinear isomorphism into two different coordinates -/

namespace LineCover

namespace SemiIso

variable {L L' : LineCover} {φ : RatFunc k ≃+* RatFunc k}

/-- **A semilinear isomorphism twists into two coordinates**: reading the source in the coordinate
`φ₀` and the target in the coordinate `φ₁` leaves the map semilinear, over the coordinate change
`ρ` which the two are related by. -/
def twist₂ (e : SemiIso L L' φ) (φ₀ φ₁ ρ : RatFunc k ≃+* RatFunc k)
    (hcomm : ∀ f, φ (φ₀ f) = φ₁ (ρ f)) : SemiIso (L.twist φ₀) (L'.twist φ₁) ρ where
  toRingEquiv := (e.toRingEquiv : (L.twist φ₀).M ≃+* (L'.twist φ₁).M)
  map_smul f x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    show e.toRingEquiv (algebraMap (RatFunc k) L.M (φ₀ f)) = algebraMap (RatFunc k) L'.M (φ₁ (ρ f))
    rw [e.map_algebraMap, hcomm]

end SemiIso

/-- **Unramifiedness at the point at infinity travels along a semilinear isomorphism** whose
coordinate change normalizes the inversion of the parameter: the conjugate coordinate change `ρ`
preserves the integral model and fixes the point `0`, which the inversion exchanges with
infinity. -/
theorem IsUnramifiedAtInfinity.semiIso₂ {L L' : LineCover} {φ ρ : RatFunc k ≃+* RatFunc k}
    {χ : k[X] ≃+* k[X]} (e : SemiIso L L' φ) (hρ : PolyPreserving ρ χ)
    (hcomm : ∀ f, φ (invSubst.toRingEquiv f) = invSubst.toRingEquiv (ρ f))
    (hfix : Ideal.map χ (placeP (0 : k)) = placeP 0)
    (hL : L.IsUnramifiedAtInfinity) : L'.IsUnramifiedAtInfinity := by
  intro τ hτ
  set e' := e.twist₂ invSubst.toRingEquiv invSubst.toRingEquiv ρ hcomm with he'
  have h1 : (L.twist invSubst.toRingEquiv).IsInertiaAt 0 (e'.symm.conj τ) :=
    IsInertiaAt.semiIso e'.symm hρ.symm (map_placeP_symm hfix) hτ
  have h2 := hL _ h1
  have h3 := congrArg e'.conj h2
  rw [SemiIso.conj_conj_symm] at h3
  rw [h3]
  exact e'.deckEquiv.map_one

/-! ## The scaled cover -/

/-- **Unramifiedness travels to the scaled cover**, with the branch locus scaled along. -/
theorem IsUnramifiedOutside.twist_scale {L : LineCover} {S : Set k} (hc : c ≠ 0)
    (hL : L.IsUnramifiedOutside S) :
    (L.twist (scaleSubst hc)).IsUnramifiedOutside ((fun s => c⁻¹ * s) ⁻¹' S) := by
  refine IsUnramifiedOutside.semiIso' (L.twistSemiIso (scaleSubst hc)).symm
    (scaleSubst_polyPreserving hc).symm (move := Equiv.mulLeft₀ c hc) ?_ ?_ hL
  · intro t
    exact map_placeP_scale_symm hc t
  · intro t ht
    simpa using ht

/-- **Unramifiedness at the point at infinity survives a scaling of the parameter.** -/
theorem IsUnramifiedAtInfinity.twist_scale {L : LineCover} (hc : c ≠ 0)
    (hL : L.IsUnramifiedAtInfinity) : (L.twist (scaleSubst hc)).IsUnramifiedAtInfinity := by
  refine IsUnramifiedAtInfinity.semiIso₂ (L.twistSemiIso (scaleSubst hc)).symm
    (scaleSubst_polyPreserving hc) ?_ ?_ hL
  · intro f
    show (scaleSubst hc).symm (invSubst.toRingEquiv f) = invSubst.toRingEquiv (scaleSubst hc f)
    rw [scaleSubst_symm_apply]
    exact scaleSubst_invSubst_comm hc f
  · rw [map_placeP_scale, mul_zero]

end LineCover

end Rigidity.RET
