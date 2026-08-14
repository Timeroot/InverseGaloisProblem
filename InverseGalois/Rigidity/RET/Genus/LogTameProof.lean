/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdLog
import InverseGalois.Rigidity.RET.Genus.ResidueField
import InverseGalois.Rigidity.RET.Genus.OrdRamification
import InverseGalois.Rigidity.RET.Genus.LogTame

/-!
# The logarithmic derivation of the line preserves the functions regular at the far end

A cover of the line unramified over the affine line is differentiated by the logarithmic derivation
`x · d/dx` without creating poles at the far end.  The statement is local: at every place of the
model of the cover over the second chart the derivation must preserve the functions regular there,
and the derivation is logarithmic along the inverse coordinate, which it sends to its own negative.

Two kinds of place occur, told apart by the value of the inverse coordinate.  At a place where that
value is zero — a place over the far end — what vanishes is the inverse coordinate itself, and its
derivative, being its negative, vanishes to the very same order, one better than is needed; the
ramification there is arbitrary, since a logarithmic derivation is tame at a branch point in
characteristic zero however deep the branching.  At a place where the value is not zero, what
vanishes is the difference of the inverse coordinate with that value, while the derivative of that
difference is again the negative of the inverse coordinate, a unit; the bound then holds precisely
when the difference vanishes to first order, that is, when the place is unramified — and it is,
being a place over the affine line, where the cover is unramified by hypothesis.

## Main definitions

* `Rigidity.RET.lineLogDeriv` — the logarithmic derivation `x · d/dx` of the line, on a cover.
* `Rigidity.RET.inftyCoord` — the inverse coordinate, as a function of the far chart.
* `Rigidity.RET.inftyUnif` — the inverse coordinate, as a function of the model over that chart.

## Main results

* `Rigidity.RET.lineLogDeriv_inv_coord` — the logarithmic derivation sends the inverse coordinate
  to its own negative.
* `Rigidity.RET.ord_sub_const_eq_one_of_unramified` — away from the far end the difference of the
  inverse coordinate with its value at a place vanishes there to first order.
* `Rigidity.RET.ord_nonneg_lineLogDeriv` — a cover unramified over the affine line has, at every
  place over the second chart, a logarithmic derivation preserving the functions regular there.
-/

open Polynomial IsDedekindDomain

noncomputable section


namespace Rigidity.RET

/-! ## The logarithmic derivation of the line -/

section LogDeriv

variable (k F : Type*) [Field k] [CharZero k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [Algebra.IsAlgebraic (RatFunc k) F]

attribute [local instance] Algebra.FormallyEtale.of_isSeparable

/-- **The logarithmic derivation of the line**, `x · d/dx`: differentiation along the coordinate,
scaled by the coordinate itself. -/
def lineLogDeriv : Derivation k F F := coord k F • lineDeriv k F

variable {k F}

theorem lineLogDeriv_apply (y : F) : lineLogDeriv k F y = coord k F * lineDeriv k F y := rfl

/-- **The logarithmic derivation sends the inverse coordinate to its own negative.** -/
theorem lineLogDeriv_inv_coord : lineLogDeriv k F (coord k F)⁻¹ = -(coord k F)⁻¹ := by
  have hx : coord k F ≠ 0 := coord_ne_zero k F
  rw [lineLogDeriv_apply, Derivation.leibniz_inv, lineDeriv_coord, smul_eq_mul, mul_one]
  field_simp

omit [CharZero k] [Algebra.IsAlgebraic (RatFunc k) F] in
/-- **The inverse coordinate is transcendental over the constants**, the coordinate being so. -/
theorem transcendental_inv_coord_cover : Transcendental k (coord k F)⁻¹ := fun h =>
  transcendental_coord k F (IsAlgebraic.inv_iff.mp h)

end LogDeriv

/-! ## The inverse coordinate as a function of the far chart -/

section Chart

variable (k : Type*) [Field k]

/-- The far chart is an algebra of finite type over the constants, being a polynomial ring in the
inverse coordinate. -/
instance instFiniteTypeInftyChart : Algebra.FiniteType k ↥(inftyChart k) :=
  Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType k k[X]) (inftyChartEquiv k)

/-- **The inverse coordinate, as a function of the far chart.** -/
def inftyCoord : ↥(inftyChart k) :=
  ⟨(RatFunc.X : RatFunc k)⁻¹, Algebra.self_mem_adjoin_singleton _ _⟩

theorem coe_inftyCoord : (inftyCoord k : RatFunc k) = (RatFunc.X : RatFunc k)⁻¹ := rfl

/-- The far chart is the polynomial ring in the inverse coordinate, generator for generator. -/
theorem inftyChartEquiv_X : inftyChartEquiv k X = inftyCoord k :=
  Subtype.ext (by simp [inftyChartEquiv, inftyCoord])

end Chart

/-! ## The model of a cover over the far chart -/

section Model

variable (k F : Type*) [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F]

omit [Algebra k F] [IsScalarTower k (RatFunc k) F] in
theorem algebraMap_inftyCoord :
    algebraMap ↥(inftyChart k) F (inftyCoord k) = (coord k F)⁻¹ := by
  rw [IsScalarTower.algebraMap_apply ↥(inftyChart k) (RatFunc k) F, coord, ← map_inv₀]
  rfl

/-- **The inverse coordinate, as a function of the model over the far chart.** -/
def inftyUnif : ↥(integralClosure ↥(inftyChart k) F) :=
  algebraMap ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F) (inftyCoord k)

set_option synthInstance.maxHeartbeats 400000 in
omit [Algebra k F] [IsScalarTower k (RatFunc k) F] in
/-- **The inverse coordinate, read on the model over the far chart, is the inverse coordinate.** -/
theorem algebraMap_inftyUnif :
    algebraMap ↥(integralClosure ↥(inftyChart k) F) F (inftyUnif k F) = (coord k F)⁻¹ := by
  rw [inftyUnif, ← IsScalarTower.algebraMap_apply ↥(inftyChart k)
    ↥(integralClosure ↥(inftyChart k) F) F, algebraMap_inftyCoord]

variable {k F}

set_option synthInstance.maxHeartbeats 400000 in
theorem algebraMap_inftyCoord_sub (c : k) :
    algebraMap ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F)
        (inftyCoord k - algebraMap k ↥(inftyChart k) c)
      = inftyUnif k F - algebraMap k ↥(integralClosure ↥(inftyChart k) F) c := by
  rw [map_sub, inftyUnif, ← IsScalarTower.algebraMap_apply k ↥(inftyChart k)
    ↥(integralClosure ↥(inftyChart k) F)]

set_option synthInstance.maxHeartbeats 400000 in
theorem algebraMap_inftyCoord_sub_field (c : k) :
    algebraMap ↥(integralClosure ↥(inftyChart k) F) F
        (algebraMap ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F)
          (inftyCoord k - algebraMap k ↥(inftyChart k) c))
      = (coord k F)⁻¹ - algebraMap k F c := by
  rw [algebraMap_inftyCoord_sub, map_sub, algebraMap_inftyUnif,
    ← IsScalarTower.algebraMap_apply k ↥(integralClosure ↥(inftyChart k) F) F]

end Model

/-! ## Finiteness of the model over the far chart -/

section ModelFinite

variable (k F : Type*) [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [IsGalois (RatFunc k) F]

open scoped Rigidity.RET

set_option synthInstance.maxHeartbeats 400000 in
/-- The model of the cover over the far chart is finite over that chart. -/
instance instFiniteInftyModel :
    Module.Finite ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F) :=
  IsIntegralClosure.finite ↥(inftyChart k) (RatFunc k) F _

set_option synthInstance.maxHeartbeats 400000 in
/-- The model of the cover over the far chart is of finite type over the constants. -/
instance instFiniteTypeInftyModel :
    Algebra.FiniteType k ↥(integralClosure ↥(inftyChart k) F) :=
  Algebra.FiniteType.trans (S := ↥(inftyChart k)) inferInstance inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- The Galois group of the cover is the Galois group of its model over the far chart. -/
instance instIsGaloisGroupInftyModel :
    IsGaloisGroup (F ≃ₐ[RatFunc k] F) ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F) :=
  IsGaloisGroup.of_isFractionRing (F ≃ₐ[RatFunc k] F) ↥(inftyChart k)
    ↥(integralClosure ↥(inftyChart k) F) (RatFunc k) F

end ModelFinite

/-! ## The place-by-place statement -/

section Tame

variable {k F : Type*} [Field k] [CharZero k] [IsAlgClosed k] [Field F] [Algebra k F]
  [Algebra k[X] F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  [IsGalois (RatFunc k) F]

attribute [local instance] Algebra.FormallyEtale.of_isSeparable

open scoped Rigidity.RET

omit [IsAlgClosed k] [Algebra k[X] F] [IsScalarTower k k[X] F] [IsScalarTower k[X] (RatFunc k) F]
  in
/-- **The functions of the far chart are differentiated to functions regular at the far end.**
They are polynomials in the inverse coordinate, which the logarithmic derivation does not leave. -/
theorem ordAtLeast_zero_lineLogDeriv_algebraMap
    (v : HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) F)) (a : ↥(inftyChart k)) :
    OrdAtLeast F v 0 (lineLogDeriv k F (algebraMap ↥(inftyChart k) F a)) := by
  have hsub : Algebra.adjoin k {(coord k F)⁻¹} ≤ inftyIntegers k F :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 inv_coord_mem_inftyIntegers)
  have ht : lineLogDeriv k F (coord k F)⁻¹ ∈ Algebra.adjoin k {(coord k F)⁻¹} := by
    rw [lineLogDeriv_inv_coord]
    exact neg_mem (Algebra.self_mem_adjoin_singleton _ _)
  have hmem := deriv_mem_adjoin ht (algebraMap_inftyChart_mem_adjoin a)
  exact ordAtLeast_zero_iff.2 (mem_inftyIntegers_iff_ord_nonneg.1 (hsub hmem) v)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
omit [IsAlgClosed k] in
/-- **Away from the far end the difference of the inverse coordinate with its value at a place
vanishes there to first order.**  The place is one of the model over the affine line, where the
cover is unramified, so the prime it lies over — generated by that very difference — is not
squeezed into the square of the place. -/
theorem ord_sub_const_eq_one_of_unramified
    (h₁ : ∀ Q : Ideal ↥(integralClosure k[X] F), Q.IsMaximal →
      ∀ σ : F ≃ₐ[RatFunc k] F, σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) Q → σ = 1)
    (v : HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) F)) {c : k} (hc0 : c ≠ 0)
    (hc : algebraMap ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F)
      (inftyCoord k - algebraMap k ↥(inftyChart k) c) ∈ v.asIdeal) :
    ord F v ((coord k F)⁻¹ - algebraMap k F c) = 1 := by
  classical
  haveI hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hbF := algebraMap_inftyCoord_sub_field (k := k) (F := F) c
  -- the difference is a nonzero function of the model
  have hgne : (coord k F)⁻¹ - algebraMap k F c ≠ 0 := by
    rw [sub_ne_zero]
    intro hcon
    exact transcendental_inv_coord_cover (k := k) (F := F) (hcon ▸ isAlgebraic_algebraMap c)
  have hb0 : algebraMap ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F)
      (inftyCoord k - algebraMap k ↥(inftyChart k) c) ≠ 0 := by
    intro h
    rw [h, map_zero] at hbF
    exact hgne hbF.symm
  -- the value being nonzero, the inverse coordinate does not vanish at the place
  have hvu : inftyUnif k F ∉ v.asIdeal := by
    intro hmem
    rw [algebraMap_inftyCoord_sub] at hc
    have hcmem : algebraMap k ↥(integralClosure ↥(inftyChart k) F) c ∈ v.asIdeal := by
      have h := Ideal.sub_mem _ hmem hc
      simpa using h
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hcmem
      ((algebraMap k ↥(integralClosure ↥(inftyChart k) F)).isUnit_map
        (isUnit_iff_ne_zero.2 hc0)))
  -- so the coordinate is regular there, and the place is one of the model over the affine line
  have hX : algebraMap (RatFunc k) F RatFunc.X ∈ placeSubring F v := by
    refine mem_placeSubring_of_notMem v (y := inftyUnif k F) ?_ hvu
    rw [algebraMap_inftyUnif, coord, map_inv₀]
  have hinertia : ∀ σ : F ≃ₐ[RatFunc k] F,
      σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) v.asIdeal → σ = 1 :=
    inertia_eq_one_of_chartOne h₁ v hX
  -- the prime below is generated by the difference, an irreducible of the far chart
  haveI hamax : (Ideal.span {inftyCoord k - algebraMap k ↥(inftyChart k) c}).IsMaximal := by
    have hmax : (Ideal.span {(X - C c : k[X])}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C c)
    have hmapped := hmax.map_bijective (inftyChartEquiv k) (inftyChartEquiv k).bijective
    have hae : inftyChartEquiv k (X - C c) = inftyCoord k - algebraMap k ↥(inftyChart k) c := by
      rw [map_sub, C_eq_algebraMap, AlgEquiv.commutes, inftyChartEquiv_X]
    rwa [Ideal.map_span, Set.image_singleton, hae] at hmapped
  have hspan : Ideal.span {inftyCoord k - algebraMap k ↥(inftyChart k) c}
      = v.asIdeal.under ↥(inftyChart k) := by
    refine hamax.eq_of_le (Ideal.IsPrime.under ↥(inftyChart k) v.asIdeal).ne_top ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hc
  haveI : (v.asIdeal.under ↥(inftyChart k)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
  haveI := residue_isSeparable_of_charZero k (A := ↥(inftyChart k))
    (v.asIdeal.under ↥(inftyChart k)) v.asIdeal
  have h := ord_eq_one_of_inertia_trivial (A := ↥(inftyChart k))
    (G := F ≃ₐ[RatFunc k] F) (K := F) v hinertia hspan hb0
  rwa [hbF] at h

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **A cover of the line unramified over the affine line is differentiated by the logarithmic
derivation without creating poles at any place over the far chart.** -/
theorem ord_nonneg_lineLogDeriv
    (h₁ : ∀ Q : Ideal ↥(integralClosure k[X] F), Q.IsMaximal →
      ∀ σ : F ≃ₐ[RatFunc k] F, σ ∈ Ideal.inertia (F ≃ₐ[RatFunc k] F) Q → σ = 1)
    (v : HeightOneSpectrum ↥(integralClosure ↥(inftyChart k) F)) (y : F) (hy : 0 ≤ ord F v y) :
    0 ≤ ord F v (coord k F * lineDeriv k F y) := by
  classical
  haveI hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hunn : 0 ≤ ord F v ((coord k F)⁻¹) :=
    algebraMap_inftyUnif k F ▸ ord_nonneg v (inftyUnif k F)
  -- the value of the inverse coordinate at the place
  obtain ⟨c, hc⟩ := exists_const_sub_mem (k := k) v.asIdeal (inftyUnif k F)
  rw [← algebraMap_inftyCoord_sub] at hc
  have hbF := algebraMap_inftyCoord_sub_field (k := k) (F := F) c
  obtain ⟨g, hg⟩ : ∃ z : F, z = (coord k F)⁻¹ - algebraMap k F c := ⟨_, rfl⟩
  have hgne : g ≠ 0 := by
    rw [hg, sub_ne_zero]
    intro hcon
    exact transcendental_inv_coord_cover (k := k) (F := F) (hcon ▸ isAlgebraic_algebraMap c)
  have hb0 : algebraMap ↥(inftyChart k) ↥(integralClosure ↥(inftyChart k) F)
      (inftyCoord k - algebraMap k ↥(inftyChart k) c) ≠ 0 := by
    intro h
    rw [h, map_zero] at hbF
    exact hgne (hg.trans hbF.symm)
  have hgpos : 0 < ord F v g := by
    have h := (mem_iff_ord_pos (K := F) v hb0).1 hc
    rwa [hbF, ← hg] at h
  obtain ⟨e, hge⟩ : ∃ e : ℕ, ord F v g = (e : ℤ) :=
    ⟨(ord F v g).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  -- the derivative of the difference is the negative of the inverse coordinate
  have hδg : lineLogDeriv k F g = -(coord k F)⁻¹ := by
    rw [hg, map_sub, Derivation.map_algebraMap, sub_zero, lineLogDeriv_inv_coord]
  -- and its order is one better than the order of the difference
  have hkey : (e : ℤ) - 1 ≤ ord F v ((coord k F)⁻¹) := by
    rcases eq_or_ne c 0 with rfl | hc0
    · have hgu : g = (coord k F)⁻¹ := by rw [hg, map_zero, sub_zero]
      rw [← hgu, hge]
      omega
    · have hord1 : ord F v g = 1 := by
        rw [hg]
        exact ord_sub_const_eq_one_of_unramified h₁ v hc0 hc
      have he1 : e = 1 := by omega
      rw [he1]
      simpa using hunn
  -- the master descent
  have hmain : ∀ z : F, OrdAtLeast F v 0 z → OrdAtLeast F v 0 (lineLogDeriv k F z) := by
    refine ordAtLeast_zero_deriv_of_logarithmic (A := ↥(inftyChart k)) (lineLogDeriv k F)
      (fun b => ordAtLeast_zero_lineLogDeriv_algebraMap v b)
      (fun b => exists_const_sub_mem v.asIdeal b) hgne hge ?_ ?_
    · exact Nat.cast_ne_zero.mpr (by omega)
    · rw [hδg]
      exact (ordAtLeast_of_ord_le hkey).neg
  have hz := hmain y (ordAtLeast_zero_iff.2 hy)
  rw [lineLogDeriv_apply] at hz
  exact ordAtLeast_zero_iff.1 hz

end Tame

end Rigidity.RET
