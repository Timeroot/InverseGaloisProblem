/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Translate
import InverseGalois.Rigidity.RET.NoUnbranchedCover

/-!
# The sphere with one puncture is simply connected

The affine line is simply connected, and every point of the sphere is like every other: a cover of
the line unramified away from a single point — one point of the affine line, or the point at
infinity — is trivial.

Moving the missing point to the point at infinity takes two coordinate changes.  A translation
`T ↦ T + a` moves it to the origin; it carries the integral model of the line to itself, so
unramifiedness over the affine line travels with it, but it does not commute with the inversion,
so its effect at the point at infinity has to be read off the places themselves: the inverse
coordinate `T⁻¹` and the translated inverse coordinate `(T + a)⁻¹` differ by the unit
`1 - a (T + a)⁻¹`, so a place at which one of them vanishes is a place at which the other vanishes
too.  The inversion `T ↦ T⁻¹` then exchanges the origin with the point at infinity, and the
remaining points of the affine line with each other, by the same kind of computation: the
coordinate and the inverse coordinate are reciprocal, so `T - t⁻¹` and `T⁻¹ - t` vanish together.

## Main results

* `Rigidity.RET.LineCover.isInertiaAt_of_inertial` — a place of a cover at which a coordinate of
  the line vanishes, carrying an inertial symmetry, is a place over the corresponding point.
* `Rigidity.RET.LineCover.IsUnramifiedAtInfinity.twist_translate` — unramifiedness at the point at
  infinity survives a translation of the parameter.
* `Rigidity.RET.LineCover.isUnramifiedOutside_twist_inv` — unramifiedness travels to the cover read
  in the inverted coordinate, with the branch locus carried along by the reciprocal.
* `Rigidity.RET.LineCover.isUnramifiedOutside_empty_twist_inv` — a cover unramified away from the
  origin and at infinity is unramified over the whole affine line of the inverted coordinate.
* `Rigidity.RET.LineCover.subsingleton_deck_of_unramifiedOutside_singleton` — a cover unramified
  away from one point of the affine line and at infinity is trivial.
-/

open Polynomial IsDedekindDomain

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

/-! ## Two computations with a place -/

/-- **The place of a sum is the place of the dominant summand.** -/
theorem valuation_add_eq_of_lt {F : Type*} [Field F] (A : ValuationSubring F) {x y : F}
    (h : A.valuation y < A.valuation x) : A.valuation (x + y) = A.valuation x :=
  Valuation.map_add_eq_of_lt_left _ h

/-- **A non-zero function regular at a place whose inverse is regular there too is a unit
there.** -/
theorem valuation_eq_one_of_le {F : Type*} [Field F] (A : ValuationSubring F) {x : F} (hx : x ≠ 0)
    (h : A.valuation x ≤ 1) (h' : A.valuation x⁻¹ ≤ 1) : A.valuation x = 1 := by
  refine le_antisymm h ?_
  have hmul : A.valuation x * A.valuation x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  calc (1 : A.ValueGroup) = A.valuation x * A.valuation x⁻¹ := hmul.symm
    _ ≤ A.valuation x * 1 := mul_le_mul_right h' _
    _ = A.valuation x := mul_one _

/-! ## The translated parameter -/

/-- The translation moves the parameter to `T + a`. -/
theorem translateSubst_X (a : k) :
    translateSubst a (RatFunc.X : RatFunc k) = RatFunc.X + algebraMap k (RatFunc k) a := by
  have h := translateSubst_polyPreserving a (X : Polynomial k)
  rw [RatFunc.algebraMap_X] at h
  rw [h]
  show algebraMap (Polynomial k) (RatFunc k) (Polynomial.aeval (X + C a : Polynomial k) X) = _
  rw [Polynomial.aeval_X, map_add, RatFunc.algebraMap_X, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- The translation fixes the constants. -/
theorem translateSubst_const (a c : k) :
    translateSubst a (algebraMap k (RatFunc k) c) = algebraMap k (RatFunc k) c := by
  have h := translateSubst_polyPreserving a (C c : Polynomial k)
  rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply] at h
  rw [h]
  show algebraMap (Polynomial k) (RatFunc k) (Polynomial.aeval (X + C a : Polynomial k) (C c)) = _
  rw [Polynomial.aeval_C, ← Polynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- The translated parameter is not the zero function. -/
theorem X_add_const_ne_zero (a : k) :
    (RatFunc.X : RatFunc k) + algebraMap k (RatFunc k) a ≠ 0 := by
  intro h
  have hp : algebraMap (Polynomial k) (RatFunc k) (X + C a : Polynomial k) = 0 := by
    rw [map_add, RatFunc.algebraMap_X, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply]
    exact h
  have h0 : (X + C a : Polynomial k) = 0 :=
    IsFractionRing.injective (Polynomial k) (RatFunc k) (by rw [hp, map_zero])
  have hdeg := congrArg Polynomial.natDegree h0
  rw [Polynomial.natDegree_X_add_C, Polynomial.natDegree_zero] at hdeg
  exact one_ne_zero hdeg

/-- **The inverse coordinate is the translated inverse coordinate times a unit.** -/
theorem inv_X_mul_eq (a : k) :
    (RatFunc.X : RatFunc k)⁻¹
      * (1 - algebraMap k (RatFunc k) a * (RatFunc.X + algebraMap k (RatFunc k) a)⁻¹)
      = (RatFunc.X + algebraMap k (RatFunc k) a)⁻¹ := by
  have hX : (RatFunc.X : RatFunc k) ≠ 0 := RatFunc.X_ne_zero
  have hXa : (RatFunc.X : RatFunc k) + algebraMap k (RatFunc k) a ≠ 0 := X_add_const_ne_zero a
  field_simp
  ring

namespace LineCover

attribute [local instance] LineCover.instAlgebraConst LineCover.instTowerConstRatFunc
  LineCover.instTowerConstPoly

/-! ## Reading polynomials at a place of a cover -/

/-- A polynomial in the coordinate is regular at every place of the integral model. -/
theorem algebraMap_poly_mem_placeSubring (N : LineCover) (v : HeightOneSpectrum (Bring N.M))
    (p : Polynomial k) : algebraMap (Polynomial k) N.M p ∈ placeSubring N.M v := by
  rw [IsScalarTower.algebraMap_apply (Polynomial k) (Bring N.M) N.M]
  exact algebraMap_mem_placeSubring N.M v _

/-- A polynomial in the coordinate lying in a prime of the integral model vanishes at its
place. -/
theorem valuation_algebraMap_poly_lt_one (N : LineCover) (v : HeightOneSpectrum (Bring N.M))
    {p : Polynomial k} (hp : algebraMap (Polynomial k) (Bring N.M) p ∈ v.asIdeal) :
    (placeSubring N.M v).valuation (algebraMap (Polynomial k) N.M p) < 1 := by
  rw [IsScalarTower.algebraMap_apply (Polynomial k) (Bring N.M) N.M]
  exact (valuation_lt_one_iff_mem (F := N.M) v _).2 hp

/-! ## A place at which a coordinate vanishes lies over the corresponding point -/

/-- **A place of a cover at which a coordinate of the line vanishes, and at which a deck
transformation is inertial, is a place over the corresponding point of the line.**  Such a place
contains the whole first chart, hence is the place of a prime of the integral model, and that
prime contains the coordinate. -/
theorem isInertiaAt_of_inertial (L : LineCover) (t : k) (A : ValuationSubring L.M) (hA : A ≠ ⊤)
    (hc : ∀ c : k, algebraMap (Polynomial k) L.M (C c) ∈ A)
    (hXt : A.valuation (algebraMap (Polynomial k) L.M (X - C t)) < 1)
    (σ : L.deck) (h : ∀ x ∈ A, A.valuation (σ x - x) < 1) : L.IsInertiaAt t σ := by
  have hXtA : algebraMap (Polynomial k) L.M (X - C t) ∈ A :=
    A.mem_of_valuation_le_one _ (le_of_lt hXt)
  have hXA : algebraMap (Polynomial k) L.M X ∈ A := by
    have hsum : algebraMap (Polynomial k) L.M (X - C t) + algebraMap (Polynomial k) L.M (C t) ∈ A :=
      add_mem hXtA (hc t)
    rwa [map_sub, sub_add_cancel] at hsum
  have hpoly : ∀ p : Polynomial k, algebraMap (Polynomial k) L.M p ∈ A :=
    algebraMap_polynomial_mem_of_C A hc hXA
  have hB : ∀ b : Bring L.M, algebraMap (Bring L.M) L.M b ∈ A := fun b =>
    mem_of_isIntegral_algebraMap (R := Polynomial k) hpoly b.2
  set v := underPlace A hB hA with hv
  have hpl : placeSubring L.M v = A := placeSubring_underPlace A hB hA
  have hcomm : ∀ (τ : L.deck) (b : Bring L.M),
      algebraMap (Bring L.M) L.M (τ • b) = τ • algebraMap (Bring L.M) L.M b :=
    fun τ b => coe_smul_geom L.M τ b
  have hmem : algebraMap (Polynomial k) (Bring L.M) (X - C t) ∈ v.asIdeal := by
    rw [← valuation_lt_one_iff_mem (F := L.M) v, hpl, ← IsScalarTower.algebraMap_apply]
    exact hXt
  refine ⟨v.asIdeal, v.isPrime.isMaximal v.ne_bot, ⟨?_⟩, ?_⟩
  · have hle : placeP t ≤ (v.asIdeal).under (Polynomial k) := by
      rw [placeP, Ideal.span_le, Set.singleton_subset_iff]
      exact hmem
    have hne : (v.asIdeal).under (Polynomial k) ≠ ⊤ := by
      haveI : (v.asIdeal).IsPrime := v.isPrime
      haveI : (Ideal.comap (algebraMap (Polynomial k) (Bring L.M)) v.asIdeal).IsPrime :=
        Ideal.comap_isPrime _ _
      exact Ideal.IsPrime.ne_top this
    exact (placeP_max t).eq_of_le hne hle
  · refine mem_inertia_of_isInertialAtPlace hcomm ?_
    rw [hpl]
    intro x hx
    exact h x hx

/-! ## Unramifiedness at infinity survives a translation -/

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Unramifiedness at the point at infinity survives a translation of the parameter.**  A place
at which the translated inverse coordinate vanishes is a place at which the inverse coordinate
vanishes: the two differ by a unit of the place. -/
theorem IsUnramifiedAtInfinity.twist_translate {L : LineCover} (a : k)
    (hL : L.IsUnramifiedAtInfinity) :
    (L.twist (translateSubst a)).IsUnramifiedAtInfinity := by
  intro σ' hσ'
  -- the underlying symmetry of the cover
  set σ : L.deck := Twist.unaut (Twist.unaut σ') with hσdef
  have hσeq : ∀ x : L.M, σ' x = σ x := fun _ => rfl
  have hcomm : ∀ (ρ : ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).deck)
      (b : Bring ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M),
      algebraMap (Bring ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M)
          ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M (ρ • b)
        = ρ • algebraMap (Bring ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M)
          ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M b :=
    fun ρ b => coe_smul_geom _ ρ b
  obtain ⟨Q, hQmax, hQover, hQin⟩ := hσ'
  rcases eq_or_ne Q ⊥ with rfl | hQbot
  · -- the symmetry fixes the whole model, hence the whole field
    refine eq_one_of_fixes_model
      (B := Bring ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M) fun b => ?_
    have hb : σ' • b = b := by
      have hmem : σ' • b - b ∈ (⊥ : Ideal (Bring _)) := hQin b
      rw [Ideal.mem_bot, sub_eq_zero] at hmem
      exact hmem
    have h2 := hcomm σ' b
    rw [hb] at h2
    exact h2.symm
  · set v : HeightOneSpectrum
        (Bring ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M) :=
      ⟨Q, hQmax.isPrime, hQbot⟩ with hvdef
    set A : ValuationSubring L.M :=
      placeSubring ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M v with hAdef
    -- the coordinate of the doubly twisted cover is the translated inverse coordinate
    have hcoord : algebraMap (Polynomial k)
        ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M X
        = algebraMap (RatFunc k) L.M ((RatFunc.X + algebraMap k (RatFunc k) a)⁻¹) := by
      show algebraMap (RatFunc k) L.M (translateSubst a (invSubst.toRingEquiv
        (algebraMap (Polynomial k) (RatFunc k) X))) = _
      rw [RatFunc.algebraMap_X]
      show algebraMap (RatFunc k) L.M
        (translateSubst a (invSubst (RatFunc.X : RatFunc k))) = _
      rw [invSubst_X, map_inv₀, translateSubst_X]
    have hconstk : ∀ c : k, algebraMap k L.M c ∈ A := by
      intro c
      have hmem : algebraMap (Polynomial k)
          ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M (C c) ∈ A := by
        rw [hAdef]
        exact algebraMap_poly_mem_placeSubring _ v _
      have hcc : algebraMap (Polynomial k)
          ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M (C c)
          = algebraMap k L.M c := by
        show algebraMap (RatFunc k) L.M (translateSubst a (invSubst.toRingEquiv
          (algebraMap (Polynomial k) (RatFunc k) (C c)))) = _
        rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
        show algebraMap (RatFunc k) L.M
          (translateSubst a (invSubst (algebraMap k (RatFunc k) c))) = _
        rw [invSubst.commutes, translateSubst_const, ← IsScalarTower.algebraMap_apply]
      rwa [hcc] at hmem
    -- the translated inverse coordinate vanishes at the place
    have hXQ : algebraMap (Polynomial k)
        (Bring ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M) X ∈ v.asIdeal := by
      have hle : (X : Polynomial k) ∈ placeP (0 : k) := by
        have hself := Ideal.mem_span_singleton_self (X - C (0 : k) : Polynomial k)
        simpa [placeP] using hself
      have hunder : placeP (0 : k) = Q.under (Polynomial k) := hQover.over
      rw [hunder] at hle
      exact hle
    have hXval : A.valuation (algebraMap (RatFunc k) L.M
        ((RatFunc.X + algebraMap k (RatFunc k) a)⁻¹)) < 1 := by
      rw [← hcoord, hAdef]
      exact valuation_algebraMap_poly_lt_one _ v hXQ
    -- so does the inverse coordinate: the two differ by a unit
    have hinvval : A.valuation (algebraMap (RatFunc k) L.M (RatFunc.X : RatFunc k)⁻¹) < 1 := by
      set y : L.M := algebraMap (RatFunc k) L.M
        ((RatFunc.X + algebraMap k (RatFunc k) a)⁻¹) with hy
      set z : L.M := algebraMap (RatFunc k) L.M (RatFunc.X : RatFunc k)⁻¹ with hz
      set c : L.M := algebraMap k L.M a with hcdef
      have hprod : z * (1 - c * y) = y := by
        have hmap := congrArg (algebraMap (RatFunc k) L.M) (inv_X_mul_eq a)
        rw [map_mul, map_sub, map_one, map_mul,
          ← IsScalarTower.algebraMap_apply k (RatFunc k) L.M] at hmap
        rw [hz, hy, hcdef]
        exact hmap
      have hcy : A.valuation (c * y) < 1 := by
        rw [map_mul]
        calc A.valuation c * A.valuation y ≤ 1 * A.valuation y :=
              mul_le_mul_left (A.valuation_le_one ⟨c, hconstk a⟩) _
          _ = A.valuation y := one_mul _
          _ < 1 := hXval
      have hunit : A.valuation (1 - c * y) = 1 := by
        have hlt : A.valuation (-(c * y)) < A.valuation 1 := by
          rw [map_one, Valuation.map_neg]
          exact hcy
        have heq := valuation_add_eq_of_lt A hlt
        rw [map_one] at heq
        rw [sub_eq_add_neg]
        exact heq
      have hval := congrArg A.valuation hprod
      rw [map_mul, hunit, mul_one] at hval
      rw [hz, hval]
      exact hXval
    -- the symmetry is inertial at the place
    have hin : ∀ x ∈ A, A.valuation (σ x - x) < 1 := by
      intro x hx
      have hI := isInertialAtPlace_of_mem_inertia
        (F := ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M)
        (B := Bring ((L.twist (translateSubst a)).twist invSubst.toRingEquiv).M) hcomm
        (v := v) (σ := σ') hQin x hx
      simpa [hσeq] using hI
    have hAtop : A ≠ ⊤ := placeSubring_ne_top _ v
    have hfinal := isInertiaAt_zero_twist L A hAtop hconstk hinvval σ hin
    have h1 := hL _ hfinal
    have h2 : σ = 1 := eq_one_of_twistAut_eq_one h1
    refine AlgEquiv.ext fun x => ?_
    rw [hσeq x]
    exact congrArg (fun e : L.deck => e x) h2

/-! ## Inverting the coordinate -/

/-- **Unramifiedness away from the origin travels to the cover read in the inverted coordinate**,
with the branch locus carried along by the reciprocal.  A point `t ≠ 0` of the new affine line
comes from the point `t⁻¹ ≠ 0` of the old one: the coordinate and the inverse coordinate are
reciprocal, so `T - t⁻¹` and `T⁻¹ - t` vanish at the same places.  Nothing is claimed at the
origin, which is where the point at infinity of the old coordinate has gone. -/
theorem isUnramifiedOutside_twist_inv_ne_zero (L : LineCover) {S : Set k}
    (h₁ : L.IsUnramifiedOutside S) :
    (L.twist invSubst.toRingEquiv).IsUnramifiedOutside ({0} ∪ {t : k | t ≠ 0 ∧ t⁻¹ ∈ S}) := by
  intro t ht σ' hσ'
  have ht0 : t ≠ 0 := fun h => ht (Or.inl h)
  set σ : L.deck := Twist.unaut σ' with hσdef
  have hσeq : ∀ x : L.M, σ' x = σ x := fun _ => rfl
  have hcomm : ∀ (ρ : (L.twist invSubst.toRingEquiv).deck)
      (b : Bring (L.twist invSubst.toRingEquiv).M),
      algebraMap (Bring (L.twist invSubst.toRingEquiv).M) (L.twist invSubst.toRingEquiv).M (ρ • b)
        = ρ • algebraMap (Bring (L.twist invSubst.toRingEquiv).M)
            (L.twist invSubst.toRingEquiv).M b :=
    fun ρ b => coe_smul_geom _ ρ b
  obtain ⟨Q, hQmax, hQover, hQin⟩ := hσ'
  rcases eq_or_ne Q ⊥ with rfl | hQbot
  · refine eq_one_of_fixes_model (B := Bring (L.twist invSubst.toRingEquiv).M) fun b => ?_
    have hb : σ' • b = b := by
      have hmem : σ' • b - b ∈ (⊥ : Ideal (Bring _)) := hQin b
      rw [Ideal.mem_bot, sub_eq_zero] at hmem
      exact hmem
    have h2 := hcomm σ' b
    rw [hb] at h2
    exact h2.symm
  · set v : HeightOneSpectrum (Bring (L.twist invSubst.toRingEquiv).M) :=
      ⟨Q, hQmax.isPrime, hQbot⟩ with hvdef
    set A : ValuationSubring L.M := placeSubring (L.twist invSubst.toRingEquiv).M v with hAdef
    -- the constants are regular at the place
    have hconstk : ∀ c : k, algebraMap k L.M c ∈ A := by
      intro c
      have hmem : algebraMap (Polynomial k) (L.twist invSubst.toRingEquiv).M (C c) ∈ A := by
        rw [hAdef]
        exact algebraMap_poly_mem_placeSubring _ v _
      rwa [twist_algebraMap_C L c] at hmem
    have hconst : ∀ c : k, algebraMap (Polynomial k) L.M (C c) ∈ A := by
      intro c
      have hcc : algebraMap (Polynomial k) L.M (C c) = algebraMap k L.M c := by
        rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
      rw [hcc]
      exact hconstk c
    -- the inverse coordinate takes the value `t` at the place
    have hXQ : algebraMap (Polynomial k) (Bring (L.twist invSubst.toRingEquiv).M) (X - C t)
        ∈ v.asIdeal := by
      have hle : (X - C t : Polynomial k) ∈ placeP t := Ideal.mem_span_singleton_self _
      have hunder : placeP t = Q.under (Polynomial k) := hQover.over
      rw [hunder] at hle
      exact hle
    set w : L.M := algebraMap (RatFunc k) L.M (RatFunc.X : RatFunc k)⁻¹ with hwdef
    set x : L.M := algebraMap (RatFunc k) L.M (RatFunc.X : RatFunc k) with hxdef
    set c : L.M := algebraMap k L.M t with hcdef
    have hc0 : c ≠ 0 := by
      rw [hcdef]
      intro hh
      exact ht0 ((algebraMap k L.M).injective (by rw [hh, map_zero]))
    have hxw : x * w = 1 := by
      rw [hxdef, hwdef, ← map_mul, mul_inv_cancel₀ (RatFunc.X_ne_zero (K := k)), map_one]
    have hNc : algebraMap (Polynomial k) (L.twist invSubst.toRingEquiv).M (X - C t) = w - c := by
      rw [map_sub, twist_algebraMap_X, twist_algebraMap_C]
    have hwc : A.valuation (w - c) < 1 := by
      rw [← hNc, hAdef]
      exact valuation_algebraMap_poly_lt_one _ v hXQ
    -- the constant `t` is a unit at the place, hence so is the inverse coordinate
    have hcval : A.valuation c = 1 := by
      refine valuation_eq_one_of_le A hc0 (A.valuation_le_one ⟨c, hconstk t⟩) ?_
      have hinv : c⁻¹ = algebraMap k L.M t⁻¹ := by rw [hcdef, map_inv₀]
      rw [hinv]
      exact A.valuation_le_one ⟨_, hconstk t⁻¹⟩
    have hwval : A.valuation w = 1 := by
      have hlt : A.valuation (w - c) < A.valuation c := by rw [hcval]; exact hwc
      have heq := valuation_add_eq_of_lt A hlt
      have hcw : c + (w - c) = w := by ring
      rw [hcw, hcval] at heq
      exact heq
    -- so the coordinate takes the value `t⁻¹` at the place
    have hgoal : A.valuation (algebraMap (Polynomial k) L.M (X - C t⁻¹)) < 1 := by
      have hxc : algebraMap (Polynomial k) L.M (X - C t⁻¹) = x - c⁻¹ := by
        rw [map_sub, hxdef, hcdef, ← map_inv₀, Polynomial.C_eq_algebraMap,
          ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Polynomial k)
            (RatFunc k) L.M, RatFunc.algebraMap_X]
      rw [hxc]
      have hid : (x - c⁻¹) * (w * c) = c - w := by
        have hexp : (x - c⁻¹) * (w * c) = (x * w) * c - (c⁻¹ * c) * w := by ring
        rw [hexp, hxw, one_mul, inv_mul_cancel₀ hc0, one_mul]
      have hval := congrArg A.valuation hid
      rw [map_mul, map_mul, hwval, hcval, mul_one, mul_one] at hval
      rw [hval, A.valuation.map_sub_swap]
      exact hwc
    -- the symmetry is inertial at the place
    have hin : ∀ y ∈ A, A.valuation (σ y - y) < 1 := by
      intro y hy
      have hI := isInertialAtPlace_of_mem_inertia
        (F := (L.twist invSubst.toRingEquiv).M)
        (B := Bring (L.twist invSubst.toRingEquiv).M) hcomm (v := v) (σ := σ') hQin y hy
      simpa [hσeq] using hI
    have hAtop : A ≠ ⊤ := placeSubring_ne_top _ v
    have hI := isInertiaAt_of_inertial L t⁻¹ A hAtop hconst hgoal σ hin
    have h1 : σ = 1 := h₁ t⁻¹ (fun hmem => ht (Or.inr ⟨ht0, hmem⟩)) σ hI
    refine AlgEquiv.ext fun y => ?_
    rw [hσeq y]
    exact congrArg (fun e : L.deck => e y) h1

/-- **Unramifiedness travels to the cover read in the inverted coordinate**, with the branch locus
carried along by the reciprocal.  The point at infinity becomes the origin, which the second
hypothesis covers. -/
theorem isUnramifiedOutside_twist_inv (L : LineCover) {S : Set k}
    (h₁ : L.IsUnramifiedOutside S) (h₂ : L.IsUnramifiedAtInfinity) :
    (L.twist invSubst.toRingEquiv).IsUnramifiedOutside {t : k | t ≠ 0 ∧ t⁻¹ ∈ S} := by
  intro t ht σ hσ
  rcases eq_or_ne t 0 with rfl | ht0
  · exact h₂ σ hσ
  refine isUnramifiedOutside_twist_inv_ne_zero L h₁ t ?_ σ hσ
  rintro (h | h)
  · exact ht0 h
  · exact ht h

/-- **A cover unramified away from the origin and at the point at infinity is unramified over the
whole affine line of the inverted coordinate.**  Inverting the coordinate sends the origin to the
point at infinity, so nothing is left to branch over. -/
theorem isUnramifiedOutside_empty_twist_inv (L : LineCover)
    (h₁ : L.IsUnramifiedOutside {(0 : k)}) (h₂ : L.IsUnramifiedAtInfinity) :
    (L.twist invSubst.toRingEquiv).IsUnramifiedOutside ∅ := by
  intro t _ σ hσ
  refine isUnramifiedOutside_twist_inv L h₁ h₂ t ?_ σ hσ
  rintro ⟨ht0, ht⟩
  exact ht0 (inv_eq_zero.mp ht)

/-! ## The sphere with one puncture is simply connected -/

/-- **A cover of the line unramified away from the origin and the point at infinity is trivial.**
Inverting the coordinate turns it into a cover unramified over the whole affine line. -/
theorem subsingleton_deck_of_unramifiedOutside_zero (L : LineCover)
    (h₁ : L.IsUnramifiedOutside {(0 : k)}) (h₂ : L.IsUnramifiedAtInfinity) :
    Subsingleton L.deck := by
  haveI hsub : Subsingleton (L.twist invSubst.toRingEquiv).deck :=
    subsingleton_deck_of_unramifiedOutside_empty _ (isUnramifiedOutside_empty_twist_inv L h₁ h₂)
  refine ⟨fun σ ρ => ?_⟩
  have h := hsub.elim (L.twistAut invSubst.toRingEquiv σ) (L.twistAut invSubst.toRingEquiv ρ)
  refine AlgEquiv.ext fun x => ?_
  exact congrArg (fun e : (L.twist invSubst.toRingEquiv).deck => e x) h

/-- **A cover of the line unramified away from one point of the affine line and the point at
infinity is trivial.**  Translating the point to the origin reduces this to the case of the
origin: the sphere with one puncture is simply connected. -/
theorem subsingleton_deck_of_unramifiedOutside_singleton (L : LineCover) (t₀ : k)
    (h₁ : L.IsUnramifiedOutside {t₀}) (h₂ : L.IsUnramifiedAtInfinity) : Subsingleton L.deck := by
  have h₁' : (L.twist (translateSubst (-t₀))).IsUnramifiedOutside {(0 : k)} :=
    IsUnramifiedOutside.twist_translate_singleton t₀ h₁
  have h₂' : (L.twist (translateSubst (-t₀))).IsUnramifiedAtInfinity :=
    IsUnramifiedAtInfinity.twist_translate (-t₀) h₂
  haveI hsub : Subsingleton (L.twist (translateSubst (-t₀))).deck :=
    subsingleton_deck_of_unramifiedOutside_zero _ h₁' h₂'
  refine ⟨fun σ ρ => ?_⟩
  have h := hsub.elim (L.twistAut (translateSubst (-t₀)) σ)
    (L.twistAut (translateSubst (-t₀)) ρ)
  refine AlgEquiv.ext fun x => ?_
  exact congrArg (fun e : (L.twist (translateSubst (-t₀))).deck => e x) h

/-- **A cover of the line unramified away from a single point carries the one-term system of
distinguished branch cycles.**

This is the completeness half of the correspondence between covers and generating product-one
tuples, in rank one: the sphere group of the once-punctured sphere is trivial, so the deck group,
generated by the single branch cycle, is trivial too. -/
theorem exists_branchCycleGenSystem_singleton (L : LineCover) (t : Fin 1 → k)
    (h₁ : L.IsUnramifiedOutside (Set.range t)) (h₂ : L.IsUnramifiedAtInfinity) :
    ∃ g : Fin 1 → L.deck, L.IsBranchCycleGenSystem t g := by
  have hrange : Set.range t = {t 0} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [Subsingleton.elim i 0]
      rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  rw [hrange] at h₁
  haveI : Subsingleton L.deck := subsingleton_deck_of_unramifiedOutside_singleton L (t 0) h₁ h₂
  refine ⟨fun _ => 1, ⟨fun i => ?_, ?_, ?_⟩⟩
  · obtain ⟨Q, hQmax, hQover⟩ := exists_Q_over_placeP L.M (t i)
    refine ⟨Q, hQmax, hQover, ?_⟩
    refine Subgroup.ext fun x => ?_
    rw [Subsingleton.elim x 1]
    simp
  · refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    rw [Subsingleton.elim x 1]
    exact one_mem _
  · simp

end LineCover

end Rigidity.RET
