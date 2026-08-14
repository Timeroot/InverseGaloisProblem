/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.UnbranchedCover
import InverseGalois.Rigidity.RET.Genus.ChartCompare
import InverseGalois.Rigidity.RET.Genus.AffineUnbranched
import InverseGalois.Rigidity.RET.Genus.LogTame
import InverseGalois.Rigidity.RET.Genus.LogTameProof
import InverseGalois.Rigidity.RET.Twist
import InverseGalois.Rigidity.RET.InertiaGen

/-!
# A cover of the line unramified everywhere is trivial

The ramification of a cover of the line is recorded, in the development, in two different
languages.  Over the affine line it is recorded point by point, by the inertia at a place of the
integral model lying over the point; at the far end of the line it is recorded on the inversion
twist, where the far end has become the point `0`.  The comparison of dimensions that shows an
unbranched cover to be trivial, on the other hand, wants the ramification of both charts recorded
on the two integral models of one and the same field.

Translating between the two is what this file does, and the translation rests on the fact that
inertia is a property of the place: a place of the second model is a place of the field, and the
same place is visible either in the first model — when the coordinate is regular there — or on the
inversion twist, whose coordinate is the inverse coordinate, which vanishes there in the remaining
case.  The two hypotheses therefore between them cover every place of the second model.

## Main results

* `Rigidity.RET.LineCover.isInertiaAt_zero_of_inertial` — a place at which the coordinate vanishes,
  carrying an inertial symmetry, lies over the point `0`.
* `Rigidity.RET.LineCover.isUnramifiedOnInftyChart_of` — a cover unramified over the affine line
  and at the far end has no non-trivial inertia at any place of the second model.
* `Rigidity.RET.LineCover.subsingleton_deck_of_unramified` — such a cover has trivial deck group.
* `Rigidity.RET.LineCover.exists_branchCycleGenSystem_empty` — such a cover carries the empty
  system of distinguished branch cycles.
* `Rigidity.RET.LineCover.isLogTameAtInfinity_of_unramifiedOutside_empty` — a cover unramified over
  the affine line is logarithmically tame at the far end.
* `Rigidity.RET.LineCover.subsingleton_deck_of_unramifiedOutside_empty` — a cover unramified over
  the affine line has trivial deck group: the affine line is simply connected.
-/

open Polynomial IsDedekindDomain

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

/-! ## A symmetry trivial on an integral model is trivial -/

/-- **A symmetry fixing every element of a chart is the identity**: every function is a ratio of
two functions of the chart. -/
theorem eq_one_of_fixes_model {F : Type*} [Field F] {K : Type*} [Field K] [Algebra K F]
    {B : Type*} [CommRing B] [Algebra B F] [IsFractionRing B F] {σ : F ≃ₐ[K] F}
    (h : ∀ b : B, σ (algebraMap B F b) = algebraMap B F b) : σ = 1 := by
  refine AlgEquiv.ext fun x => ?_
  show σ x = x
  obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj (M := nonZeroDivisors B) x
  have hb0 : algebraMap B F (b : B) ≠ 0 := (IsLocalization.map_units F b).ne_zero
  refine mul_right_cancel₀ hb0 ?_
  conv_lhs => rw [← h (b : B)]
  rw [← map_mul, hx, h a]

namespace LineCover

/-! ## A place at which the coordinate vanishes lies over the origin -/

/-- **A place of a cover at which the coordinate vanishes, and at which a deck transformation is
inertial, is a place over the point `0`.**  Such a place contains the whole first chart, hence is
the place of a prime of the integral model, and that prime contains the coordinate. -/
theorem isInertiaAt_zero_of_inertial (L : LineCover) (A : ValuationSubring L.M) (hA : A ≠ ⊤)
    (hc : ∀ c : k, algebraMap (Polynomial k) L.M (C c) ∈ A)
    (hX : A.valuation (algebraMap (Polynomial k) L.M X) < 1)
    (σ : L.deck) (h : ∀ x ∈ A, A.valuation (σ x - x) < 1) : L.IsInertiaAt 0 σ := by
  have hXA : algebraMap (Polynomial k) L.M X ∈ A := A.mem_of_valuation_le_one _ (le_of_lt hX)
  have hpoly : ∀ p : Polynomial k, algebraMap (Polynomial k) L.M p ∈ A :=
    algebraMap_polynomial_mem_of_C A hc hXA
  have hB : ∀ b : Bring L.M, algebraMap (Bring L.M) L.M b ∈ A := fun b =>
    mem_of_isIntegral_algebraMap (R := Polynomial k) hpoly b.2
  set v := underPlace A hB hA with hv
  have hpl : placeSubring L.M v = A := placeSubring_underPlace A hB hA
  have hcomm : ∀ (τ : L.deck) (b : Bring L.M),
      algebraMap (Bring L.M) L.M (τ • b) = τ • algebraMap (Bring L.M) L.M b :=
    fun τ b => coe_smul_geom L.M τ b
  have hmem : algebraMap (Polynomial k) (Bring L.M) X ∈ v.asIdeal := by
    rw [← valuation_lt_one_iff_mem (F := L.M) v, hpl, ← IsScalarTower.algebraMap_apply]
    exact hX
  refine ⟨v.asIdeal, v.isPrime.isMaximal v.ne_bot, ⟨?_⟩, ?_⟩
  · have hle : placeP 0 ≤ (v.asIdeal).under (Polynomial k) := by
      rw [placeP, Ideal.span_le, Set.singleton_subset_iff, map_zero, sub_zero]
      exact hmem
    have hne : (v.asIdeal).under (Polynomial k) ≠ ⊤ := by
      haveI : (v.asIdeal).IsPrime := v.isPrime
      haveI : (Ideal.comap (algebraMap (Polynomial k) (Bring L.M)) v.asIdeal).IsPrime :=
        Ideal.comap_isPrime _ _
      exact Ideal.IsPrime.ne_top this
    exact (placeP_max 0).eq_of_le hne hle
  · refine mem_inertia_of_isInertialAtPlace hcomm ?_
    rw [hpl]
    intro x hx
    exact h x hx

/-! ## The two charts between them see every place -/

section Charts

attribute [local instance] LineCover.instAlgebraConst LineCover.instTowerConstRatFunc
  LineCover.instTowerConstPoly

variable (L : LineCover)

/-- The inverse coordinate is a function regular at the far end. -/
theorem inv_X_mem_inftyChart : (RatFunc.X : RatFunc k)⁻¹ ∈ inftyChart k :=
  Algebra.self_mem_adjoin_singleton _ _

/-- The inverse coordinate, as a function on the cover integral over the far chart. -/
def invCoord : ↥(integralClosure ↥(inftyChart k) L.M) :=
  ⟨algebraMap ↥(inftyChart k) L.M ⟨_, inv_X_mem_inftyChart⟩, isIntegral_algebraMap⟩

theorem coe_invCoord : algebraMap ↥(integralClosure ↥(inftyChart k) L.M) L.M (invCoord L)
    = algebraMap (RatFunc k) L.M (RatFunc.X : RatFunc k)⁻¹ := by
  show algebraMap ↥(inftyChart k) L.M ⟨_, inv_X_mem_inftyChart⟩ = _
  rw [IsScalarTower.algebraMap_apply ↥(inftyChart k) (RatFunc k) L.M]
  rfl

/-! ## The coordinate of the inversion twist is the inverse coordinate -/

/-- Scalars of the twisted cover are scalars of the cover, moved by the coordinate change. -/
theorem twist_algebraMap_poly (φ : RatFunc k ≃+* RatFunc k) (p : Polynomial k) :
    algebraMap (Polynomial k) (L.twist φ).M p
      = algebraMap (RatFunc k) L.M (φ (algebraMap (Polynomial k) (RatFunc k) p)) := rfl

/-- The coordinate of the inversion twist is the inverse coordinate of the cover. -/
theorem twist_algebraMap_X :
    algebraMap (Polynomial k) (L.twist invSubst.toRingEquiv).M X
      = algebraMap (RatFunc k) L.M (RatFunc.X : RatFunc k)⁻¹ := by
  rw [twist_algebraMap_poly, RatFunc.algebraMap_X]
  show algebraMap (RatFunc k) L.M (invSubst (RatFunc.X : RatFunc k)) = _
  rw [invSubst_X]

/-- The constants of the inversion twist are the constants of the cover. -/
theorem twist_algebraMap_C (c : k) :
    algebraMap (Polynomial k) (L.twist invSubst.toRingEquiv).M (C c) = algebraMap k L.M c := by
  rw [twist_algebraMap_poly, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]
  show algebraMap (RatFunc k) L.M (invSubst (algebraMap k (RatFunc k) c)) = _
  rw [invSubst.commutes]
  rfl

/-- A deck transformation of a cover, read as one of a twist of the cover: linearity over the base
for one action of the base is linearity for the other. -/
def twistAut (φ : RatFunc k ≃+* RatFunc k) (σ : L.deck) : (L.twist φ).deck where
  toFun := σ
  invFun := σ.symm
  left_inv := σ.left_inv
  right_inv := σ.right_inv
  map_mul' := σ.map_mul
  map_add' := σ.map_add
  commutes' := fun f => σ.commutes (φ f)

variable {L}

/-- A deck transformation trivial on a twist of the cover is trivial. -/
theorem eq_one_of_twistAut_eq_one {φ : RatFunc k ≃+* RatFunc k} {σ : L.deck}
    (h : L.twistAut φ σ = 1) : σ = 1 := by
  refine AlgEquiv.ext fun x => ?_
  show σ x = x
  exact congrArg (fun e : (L.twist φ).deck => e x) h

variable (L)

/-- **A place of the cover at which the inverse coordinate vanishes, carrying an inertial
symmetry, is a place over the far end of the line**, read on the inversion twist, whose coordinate
is the inverse coordinate. -/
theorem isInertiaAt_zero_twist (A : ValuationSubring L.M) (hA : A ≠ ⊤)
    (hc : ∀ c : k, algebraMap k L.M c ∈ A)
    (hX : A.valuation (algebraMap (RatFunc k) L.M (RatFunc.X : RatFunc k)⁻¹) < 1)
    (σ : L.deck) (h : ∀ x ∈ A, A.valuation (σ x - x) < 1) :
    (L.twist invSubst.toRingEquiv).IsInertiaAt 0 (L.twistAut invSubst.toRingEquiv σ) :=
  isInertiaAt_zero_of_inertial (L.twist invSubst.toRingEquiv) A hA
    (fun c => by rw [twist_algebraMap_C]; exact hc c)
    (by rw [twist_algebraMap_X]; exact hX) (L.twistAut invSubst.toRingEquiv σ)
    (fun x hx => h x hx)

end Charts

/-! ## Every place of the second model is seen by one of the two hypotheses -/

section Assembly

attribute [local instance] LineCover.instAlgebraConst LineCover.instTowerConstRatFunc
  LineCover.instTowerConstPoly

/-- **A cover of the line unramified over the affine line and at the far end has no non-trivial
inertia at any place of the integral model over the second chart.**  At a place where the
coordinate is regular the place is one of the first model; at the remaining place the inverse
coordinate vanishes, and the place is the far end read on the inversion twist. -/
theorem isUnramifiedOnInftyChart_of (L : LineCover) (h₁ : L.IsUnramifiedOutside ∅)
    (h₂ : L.IsUnramifiedAtInfinity) : L.IsUnramifiedOnInftyChart := by
  have hcomm₂ : ∀ (τ : L.deck) (b : ↥(integralClosure ↥(inftyChart k) L.M)),
      algebraMap ↥(integralClosure ↥(inftyChart k) L.M) L.M (τ • b)
        = τ • algebraMap ↥(integralClosure ↥(inftyChart k) L.M) L.M b :=
    fun τ b => algebraMap_smul_integralClosure ↥(inftyChart k) τ b
  intro Q hQ σ hσ
  rcases eq_or_ne Q ⊥ with rfl | hQbot
  · -- the symmetry fixes the whole model, hence the whole field
    refine eq_one_of_fixes_model (B := ↥(integralClosure ↥(inftyChart k) L.M)) fun b => ?_
    have hb : σ • b = b := by
      have hmem : σ • b - b ∈ (⊥ : Ideal ↥(integralClosure ↥(inftyChart k) L.M)) := hσ b
      rw [Ideal.mem_bot, sub_eq_zero] at hmem
      exact hmem
    have h2 := hcomm₂ σ b
    rw [hb] at h2
    exact h2.symm
  · set v₂ : HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) L.M) :=
      ⟨Q, hQ.isPrime, hQbot⟩ with hv₂
    set A := placeSubring L.M v₂ with hAdef
    have hin : ∀ x ∈ A, A.valuation (σ x - x) < 1 :=
      isInertialAtPlace_of_mem_inertia hcomm₂ hσ
    by_cases hy : invCoord L ∈ Q
    · -- the inverse coordinate vanishes: the place is the far end
      have hX : A.valuation (algebraMap (RatFunc k) L.M (RatFunc.X : RatFunc k)⁻¹) < 1 := by
        rw [← coe_invCoord L]
        exact (valuation_lt_one_iff_mem (F := L.M) v₂ (invCoord L)).mpr hy
      have hinf := isInertiaAt_zero_twist L A (placeSubring_ne_top L.M v₂)
        (algebraMap_const_mem_placeSubring v₂) hX σ hin
      exact eq_one_of_twistAut_eq_one (h₂ _ hinf)
    · -- the coordinate is regular: the place is one of the first model
      have hXreg : algebraMap (RatFunc k) L.M RatFunc.X ∈ A :=
        mem_placeSubring_of_notMem v₂ (coe_invCoord L) hy
      exact inertia_eq_one_of_chartOne
        (fun P hP τ hτ => inertia_eq_one_of_isUnramifiedOutside_empty h₁ P hP τ hτ) v₂ hXreg σ hσ

/-- **A cover of the line unramified over the affine line and at the far end is trivial.**  The
projective line is simply connected. -/
theorem subsingleton_deck_of_unramified (L : LineCover) (h₁ : L.IsUnramifiedOutside ∅)
    (h₂ : L.IsUnramifiedAtInfinity) : Subsingleton L.deck :=
  L.subsingleton_deck_of_unbranched h₁ (isUnramifiedOnInftyChart_of L h₁ h₂)

/-! ## Only the far end is left, and only through the logarithmic derivation -/

/-- A cover of the line is **logarithmically tame at the far end** when the logarithmic derivation
of the line at the far end — the derivation `x · d/dx`, which vanishes to first order there —
preserves the functions on the cover regular at the far end. -/
def IsLogTameAtInfinity (L : LineCover) : Prop :=
  ∀ y ∈ inftyIntegers k L.M, coord k L.M * lineDeriv k L.M y ∈ inftyIntegers k L.M

/-- **A cover is logarithmically tame at the far end as soon as it is so at every place there.**
Regularity at the far end is read place by place. -/
theorem isLogTameAtInfinity_of_ord_nonneg (L : LineCover)
    (h : ∀ (v : IsDedekindDomain.HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) L.M))
      (y : L.M), 0 ≤ ord L.M v y → 0 ≤ ord L.M v (coord k L.M * lineDeriv k L.M y)) :
    L.IsLogTameAtInfinity :=
  fun _ hy => logDeriv_mem_inftyIntegers_of_ord_nonneg h hy

/-- **A cover of the line unramified over the affine line is logarithmically tame at the far
end.**  The inverse coordinate is a coordinate at every place of the far chart: at the place over
the far end it vanishes to the order of ramification there, and at the remaining places it differs
from its value by a function generating the prime below, which the absence of inertia makes a
coordinate. -/
theorem isLogTameAtInfinity_of_unramifiedOutside_empty (L : LineCover)
    (h₁ : L.IsUnramifiedOutside ∅) : L.IsLogTameAtInfinity :=
  isLogTameAtInfinity_of_ord_nonneg L
    (ord_nonneg_lineLogDeriv
      (fun Q hQ σ hσ => inertia_eq_one_of_isUnramifiedOutside_empty h₁ Q hQ σ hσ))

/-- **A cover of the line unramified over the affine line is trivial.**  The affine line is simply
connected. -/
theorem subsingleton_deck_of_unramifiedOutside_empty (L : LineCover)
    (h₁ : L.IsUnramifiedOutside ∅) : Subsingleton L.deck :=
  subsingleton_autGroup_of_inertia_trivial_affine
    (fun Q hQ σ hσ => inertia_eq_one_of_isUnramifiedOutside_empty h₁ Q hQ σ hσ)
    (isLogTameAtInfinity_of_unramifiedOutside_empty L h₁)

/-- **A cover of the line unramified away from no points at all carries the empty system of
distinguished branch cycles.**

This is the completeness half of the correspondence between covers and generating product-one
tuples, in the case of an empty branch locus: the sphere group of the unpunctured sphere is
trivial, so the deck group, generated by the empty tuple, is trivial too. -/
theorem exists_branchCycleGenSystem_empty (L : LineCover) (t : Fin 0 → k)
    (h₁ : L.IsUnramifiedOutside (Set.range t)) (h₂ : L.IsUnramifiedAtInfinity) :
    ∃ g : Fin 0 → L.deck, L.IsBranchCycleGenSystem t g := by
  haveI : Subsingleton L.deck :=
    subsingleton_deck_of_unramified L (by rwa [Set.range_eq_empty t] at h₁) h₂
  refine ⟨Fin.elim0, ⟨fun i => i.elim0, ?_, ?_⟩⟩
  · refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    rw [Subsingleton.elim x 1]
    exact one_mem _
  · simp

end Assembly

end LineCover

end Rigidity.RET
