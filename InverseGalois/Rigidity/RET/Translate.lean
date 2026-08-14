/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Semilinear

/-!
# Translating the parameter of the line

The points of the affine line are all alike: a translation `T ↦ T + a` of the parameter is an
automorphism of the base which carries the integral model `ℚ̄[X]` to itself and moves the point `t`
of the line to `t - a`.  Reading a cover in the translated coordinate therefore moves its branch
points by the translation and changes nothing else, and in particular a cover branched over a
single point of the affine line becomes, in a suitable coordinate, one branched over the origin.

The translation is realized by the substitution `p ↦ p(X + a)` on the integral model, extended to
the field of rational functions; the twist of a cover by it is the same cover read in the new
coordinate, and the general transport machinery for semilinear isomorphisms then moves
unramifiedness across.

## Main definitions

* `Rigidity.RET.translatePoly` — the substitution `p ↦ p(X + a)` of the integral model.
* `Rigidity.RET.translateSubst` — the translation `T ↦ T + a` of `ℚ̄(T)`.
* `Rigidity.RET.LineCover.twistSemiIso` — a cover is semilinearly isomorphic to itself read in a
  new coordinate.

## Main results

* `Rigidity.RET.map_placeP_translate` — a translation moves the point `t` of the line to `t - a`.
* `Rigidity.RET.LineCover.IsUnramifiedOutside.twist_translate` — unramifiedness travels to the
  translated cover, with the branch locus moved.
* `Rigidity.RET.LineCover.IsUnramifiedOutside.twist_translate_singleton` — a cover branched over a
  single point of the affine line is, in a suitable coordinate, branched over the origin.
-/

open Polynomial

noncomputable section


namespace Rigidity.RET

open GeomAKLB

/-! ## The translation of the parameter -/

/-- **The substitution `p ↦ p(X + a)` of the integral model of the line.** -/
abbrev translatePoly (a : k) : Polynomial k ≃+* Polynomial k :=
  (Polynomial.algEquivAevalXAddC a).toRingEquiv

/-- **The translation `T ↦ T + a` of `ℚ̄(T)`.**  It moves the point `t` of the line to `t - a`. -/
def translateSubst (a : k) : RatFunc k ≃+* RatFunc k :=
  IsFractionRing.ringEquivOfRingEquiv (A := Polynomial k) (B := Polynomial k)
    (K := RatFunc k) (L := RatFunc k) (translatePoly a)

/-- The translation preserves the integral model, acting on it by the substitution. -/
theorem translateSubst_polyPreserving (a : k) :
    PolyPreserving (translateSubst a) (translatePoly a) := fun p =>
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (translatePoly a) p

/-- The substitution carries the coordinate at `t` to the coordinate at `t - a`. -/
theorem translatePoly_X_sub_C (a t : k) :
    translatePoly a (X - C t) = X - C (t - a) := by
  have hdef : translatePoly a (X - C t) = Polynomial.aeval (X + C a : Polynomial k) (X - C t) :=
    rfl
  rw [hdef, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, ← Polynomial.C_eq_algebraMap,
    Polynomial.C_sub]
  ring

/-- **A translation moves the point `t` of the line to `t - a`.** -/
theorem map_placeP_translate (a t : k) :
    Ideal.map (translatePoly a) (placeP t) = placeP (t - a) := by
  rw [placeP, placeP, Ideal.map_span, Set.image_singleton, translatePoly_X_sub_C]

/-- The inverse translation moves the point `t` of the line to `t + a`. -/
theorem map_placeP_translate_symm (a t : k) :
    Ideal.map (translatePoly a).symm (placeP t) = placeP (t + a) := by
  refine map_placeP_symm ?_
  rw [map_placeP_translate, add_sub_cancel_right]

/-! ## A cover read in a new coordinate -/

namespace LineCover

/-- **A cover is semilinearly isomorphic to itself read in a new coordinate**: the twist is the
same field, with the base acting through the coordinate change. -/
def twistSemiIso (L : LineCover) (φ : RatFunc k ≃+* RatFunc k) : SemiIso (L.twist φ) L φ where
  toRingEquiv := RingEquiv.refl L.M
  map_smul f x := Twist.toBase_smul (φ := φ) (M := L.M) f x

/-- **Unramifiedness travels to the translated cover**, with the branch locus moved along. -/
theorem IsUnramifiedOutside.twist_translate {L : LineCover} {S : Set k} (a : k)
    (hL : L.IsUnramifiedOutside S) :
    (L.twist (translateSubst a)).IsUnramifiedOutside ((· - a) ⁻¹' S) := by
  refine IsUnramifiedOutside.semiIso' (L.twistSemiIso (translateSubst a)).symm
    (translateSubst_polyPreserving a).symm (move := Equiv.addRight a) ?_ ?_ hL
  · intro t
    exact map_placeP_translate_symm a t
  · intro t ht
    simpa [sub_eq_add_neg] using ht

/-- **A cover branched over a single point of the affine line is, in a suitable coordinate,
branched over the origin.** -/
theorem IsUnramifiedOutside.twist_translate_singleton {L : LineCover} (t₀ : k)
    (hL : L.IsUnramifiedOutside {t₀}) :
    (L.twist (translateSubst (-t₀))).IsUnramifiedOutside {(0 : k)} := by
  have hset : ((· - (-t₀)) ⁻¹' {t₀} : Set k) = {(0 : k)} := by
    ext t
    show t - (-t₀) = t₀ ↔ t = 0
    rw [sub_neg_eq_add]
    constructor
    · intro h
      exact add_right_cancel (h.trans (zero_add t₀).symm)
    · rintro rfl
      exact zero_add t₀
  exact hset ▸ IsUnramifiedOutside.twist_translate (-t₀) hL

end LineCover

end Rigidity.RET
