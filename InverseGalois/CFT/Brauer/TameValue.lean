/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicGenerator
import InverseGalois.CFT.Brauer.SymbolCyclicAlgebra
import InverseGalois.CFT.Brauer.TameEvaluation

/-!
# The value of the tame norm residue symbol

The tame norm residue symbol of a uniformiser against a unit of the valuation ring is trivial
exactly when the unit is a power; what is computed here is its actual value.

The level of a unit of the valuation ring which is not a power of prime order is the radical
extension by that unit, and the reduction of the minimal polynomial of the chosen root stays
irreducible, so every absolute value of the level is already an absolute value of the base: the
level is unramified.  The power symbol of a uniformiser against the unit is therefore the inverse
of the class of a cyclic algebra over an unramified extension, whose invariant is the value of the
uniformiser divided by the degree — provided the invariant is taken with respect to the generator
matching the Kummer character.  Rescaling that generator to the Frobenius automorphism multiplies
the invariant by the discrete logarithm of the Frobenius automorphism, which is exactly the value
of the Kummer character of the unit at any automorphism inducing the Frobenius automorphism.

So the symbol is the class, modulo the integers, of the opposite of the Kummer character of the
unit at a Frobenius automorphism, divided by the exponent.

## Main results

* `InverseGalois.CFT.exists_divisionNorm_eq_of_radical_unit`: every absolute value of a radical
  extension of prime degree by a unit is the absolute value of a scalar.
* `InverseGalois.CFT.exists_divisionNorm_eq_kummerLevel`: **the level of a unit of the valuation
  ring which is not a power is unramified.**
* `InverseGalois.CFT.localKummerSymbol_eq_inv_localInvariant`: the power symbol of two units is
  the inverse of the normalised invariant of a cyclic algebra over the level of the second.
* `InverseGalois.CFT.localKummerSymbol_uniformiser_eq_kummerChar`,
  `InverseGalois.CFT.localSymbol_uniformiser_eq_kummerChar`: **the value of the tame norm residue
  symbol of a uniformiser against a unit of the valuation ring** is the opposite of the Kummer
  character of that unit at a Frobenius automorphism, divided by the exponent.

## Tags

norm residue symbol, Hilbert symbol, tame symbol, local field, uniformiser, unramified extension,
Frobenius, Kummer theory, class field theory
-/

namespace InverseGalois.CFT

open Module Polynomial

open scoped Valued WithZero

/-! ### A radical extension by a unit has no new absolute values -/

section Radical

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [Field L] [Algebra K L] [FiniteDimensional K L] {p e : ℕ}

/-- **Every absolute value of a radical extension by a unit is the absolute value of a scalar**,
the reduction of the minimal polynomial of the generator staying irreducible when the residue
characteristic does not divide the degree. -/
theorem exists_divisionNorm_eq_of_radical_unit (pb : PowerBasis K L) {n : ℕ}
    (hn : IsRadicalExponent n K) (hnk : IsRadicalExponent n 𝓀[K]) (hn0 : n ≠ 0) (hpn : ¬ p ∣ n)
    {c : K} (hc : Valued.v c = 1)
    (hmin : minpoly K pb.gen = X ^ n - C c) (hres : HasResidueChar K p e) (z : L) (hz : z ≠ 0) :
    ∃ d : K, d ≠ 0 ∧ divisionNorm K L z = ‖d‖ := by
  have hcmem : c ∈ 𝒪[K] := le_of_eq hc
  set c₀ : ↥(𝒪[K]) := ⟨c, hcmem⟩ with hc₀
  have hcval : Valued.v ((c₀ : ↥(𝒪[K])) : K) = 1 := hc
  have hF : (X ^ n - C c₀).Monic := monic_X_pow_sub_C _ hn0
  have hFmin : (X ^ n - C c₀).map (Subring.subtype 𝒪[K]) = minpoly K pb.gen := by
    rw [hmin, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hnp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ∀ y : K, y ^ ℓ ≠ c := by
    refine (hn c).1 ?_
    rw [← hmin]
    exact minpoly.irreducible (IsIntegral.of_finite K pb.gen)
  have hirr : Irreducible ((X ^ n - C c₀).map (IsLocalRing.residue ↥(𝒪[K]))) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact irreducible_X_pow_sub_C_residue hres hnk hpn hcval hnp
  obtain ⟨d, hd0, hd⟩ := exists_norm_eq_spectralNorm pb hF hFmin hirr z hz
  exact ⟨d, hd0, by rw [divisionNorm_eq_spectralNorm, hd]⟩

end Radical

/-! ### The degree of the level of a unit which is not a power -/

section Degree

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] {n : ℕ} [NeZero n]
  {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-- **The level of a unit which is not a power of any prime order dividing the exponent has degree
the exponent**: the degree divides the exponent, and the unit is the power, with the complementary
exponent, of a scalar. -/
theorem card_gal_kummerLevel_eq_of_not_isPow {b : Kˣ}
    (hnp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ¬ ∃ c : Kˣ, c ^ ℓ = b) :
    Nat.card Gal(↥(kummerLevel h b)/K) = n := by
  obtain ⟨d, hd⟩ := card_gal_kummerLevel_dvd h b
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (by rw [hd, Nat.mul_zero])
  have hdvd : d ∣ n := ⟨Nat.card Gal(↥(kummerLevel h b)/K), hd.trans (Nat.mul_comm _ _)⟩
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_pow_card h b
  have hbn : algebraMap K ↥(kummerLevel h b) (b : K) = kummerLevelGen h b ^ n := by
    refine (algebraMap ↥(kummerLevel h b) Ω).injective ?_
    rw [map_pow, ← IsScalarTower.algebraMap_apply]
    exact (congrArg Units.val (h.root_pow b)).symm
  have hcd : c ^ d = (b : K) := by
    refine (algebraMap K ↥(kummerLevel h b)).injective ?_
    rw [map_pow, hc, ← pow_mul, ← hd, hbn]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact b.ne_zero (by rw [← hcd, zero_pow hd0])
  have hu : Units.mk0 c hc0 ^ d = b := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hcd
  have hd1 : d = 1 := by
    by_contra hne
    obtain ⟨ℓ, hl, hld⟩ := Nat.exists_prime_and_dvd hne
    refine hnp ℓ hl (hld.trans hdvd) ⟨Units.mk0 c hc0 ^ (d / ℓ), ?_⟩
    rw [← pow_mul, Nat.div_mul_cancel hld, hu]
  rw [hd1, Nat.mul_one] at hd
  exact hd.symm

end Degree

/-! ### The level of a unit of the valuation ring is unramified -/

section Level

variable {K Ω : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [Field Ω] [Algebra K Ω] [IsGalois K Ω] {n : ℕ} [NeZero n] {ζ : K}
  {hζ : IsPrimitiveRoot ζ n} {p e : ℕ}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-- **The level of a unit of the valuation ring of full degree is unramified**: it is the radical
extension by that unit, so every absolute value of it is the absolute value of a scalar. -/
theorem exists_divisionNorm_eq_kummerLevel (hpn : ¬ p ∣ n)
    (hres : HasResidueChar K p e) {b : Kˣ} (hb : Valued.v (b : K) = 1)
    (hdn : Nat.card Gal(↥(kummerLevel h b)/K) = n) (z : ↥(kummerLevel h b)) (hz : z ≠ 0) :
    ∃ d : K, d ≠ 0 ∧ divisionNorm K ↥(kummerLevel h b) z = ‖d‖ := by
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_pow_card h b
  have hbn : algebraMap K ↥(kummerLevel h b) (b : K) = kummerLevelGen h b ^ n := by
    refine (algebraMap ↥(kummerLevel h b) Ω).injective ?_
    rw [map_pow, ← IsScalarTower.algebraMap_apply]
    exact (congrArg Units.val (h.root_pow b)).symm
  have hcb : c = (b : K) := by
    refine (algebraMap K ↥(kummerLevel h b)).injective ?_
    rw [hc, hbn, hdn]
  have hmin : minpoly K (kummerLevelPowerBasis h b).gen = X ^ n - C (b : K) := by
    rw [kummerLevelPowerBasis_gen, minpoly_kummerLevelGen h b hc, hcb, hdn]
  exact exists_divisionNorm_eq_of_radical_unit (kummerLevelPowerBasis h b)
    (isRadicalExponent_of_isPrimitiveRoot (NeZero.ne n) hζ)
    (isRadicalExponent_residueField (NeZero.ne n) hζ) (NeZero.ne n) hpn hb hmin hres z hz

end Level

/-! ### The invariant of a uniformiser -/

section Uniformiser

/-- The invariant of the reciprocal of a number, raised to a power, is the invariant of the
opposite of that power. -/
theorem inv_ofAdd_intQModZ_pow (d s : ℕ) :
    ((Multiplicative.ofAdd (intQModZ d 1)) ^ s)⁻¹
      = Multiplicative.ofAdd (intQModZ d (-(s : ℤ))) := by
  have hz : -((s : ℕ) • (1 : ℤ)) = -(s : ℤ) := by rw [nsmul_eq_mul, mul_one]
  rw [← ofAdd_nsmul, ← ofAdd_neg, ← map_nsmul, ← map_neg, hz]

/-- The class of an integer divided by a number is the class of its residue. -/
theorem intQModZ_eq_zmodQModZ (n : ℕ) [NeZero n] (k : ℤ) :
    intQModZ n k = zmodQModZ n (k : ZMod n) :=
  (intQModZ_apply n k).trans (zmodQModZ_intCast n k).symm

end Uniformiser

/-! ### The value of the symbol -/

section Value

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ} {n : ℕ} [NeZero n] {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData K (AlgebraicClosure K) (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-- **The norm residue symbol of two units is the inverse of the normalised invariant of a cyclic
algebra over the level of the second**, as soon as the level is unramified and its Galois group is
generated by an automorphism whose discrete logarithm carries like the Kummer character. -/
theorem localKummerSymbol_eq_inv_localInvariant (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) {b : Kˣ}
    (hur : ∀ z : ↥(kummerLevel h b), z ≠ 0 →
      ∃ d : K, d ≠ 0 ∧ divisionNorm K ↥(kummerLevel h b) z = ‖d‖)
    {σ₀ : Gal(↥(kummerLevel h b)/K)}
    (hσ₀ : ∀ x : Gal(↥(kummerLevel h b)/K), x ∈ Subgroup.zpowers σ₀)
    (hcarry : ∀ g g' : Gal(AlgebraicClosure K/K),
      (dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)).val
          + (dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g')).val
            < Nat.card Gal(↥(kummerLevel h b)/K) ↔
        (kummerChar h b g).val + (kummerChar h b g').val < n)
    (a : Kˣ) :
    localKummerSymbol hres hm h (mulZMod n) a b
      = (localInvariant K ↥(kummerLevel h b) hur hm
          ⟨cyclicBrauerHom hσ₀ a, cyclicBrauerHom_mem_relative hσ₀ a⟩)⁻¹ := by
  have hbr : smoothBrauer (kummerSymbolUnits h (mulZMod n) a b) = (cyclicBrauerHom hσ₀ a)⁻¹ :=
    smoothBrauerHom_kummerSymbolUnits h (kummerLevel h b) hσ₀ a b hcarry
  have hinv : localInvariantHom K hm (cyclicBrauerHom hσ₀ a)
      = localInvariant K ↥(kummerLevel h b) hur hm
          ⟨cyclicBrauerHom hσ₀ a, cyclicBrauerHom_mem_relative hσ₀ a⟩ :=
    localInvariantHom_apply_of_unramified hm hur
      ⟨cyclicBrauerHom hσ₀ a, cyclicBrauerHom_mem_relative hσ₀ a⟩
  rw [localKummerSymbol_apply, smoothLocalInvariantEquiv_apply, hbr, map_inv, hinv]

/-- **The norm residue symbol of a uniformiser against a unit of the valuation ring** is the
opposite of the discrete logarithm of the Frobenius automorphism of the level, divided by the
degree of the level. -/
theorem localKummerSymbol_uniformiser_eq (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    {b : Kˣ}
    (hur : ∀ z : ↥(kummerLevel h b), z ≠ 0 →
      ∃ d : K, d ≠ 0 ∧ divisionNorm K ↥(kummerLevel h b) z = ‖d‖)
    {σ₀ : Gal(↥(kummerLevel h b)/K)}
    (hσ₀ : ∀ x : Gal(↥(kummerLevel h b)/K), x ∈ Subgroup.zpowers σ₀)
    (hcarry : ∀ g g' : Gal(AlgebraicClosure K/K),
      (dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)).val
          + (dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g')).val
            < Nat.card Gal(↥(kummerLevel h b)/K) ↔
        (kummerChar h b g).val + (kummerChar h b g').val < n)
    {π : Kˣ} (hπ : unitValDiv hm (Additive.ofMul π) = 1) {s : ℕ}
    (hs : divisionFrobenius K ↥(kummerLevel h b) hur = σ₀ ^ s) :
    localKummerSymbol hres hm h (mulZMod n) π b
      = Multiplicative.ofAdd (intQModZ (finrank K ↥(kummerLevel h b)) (-(s : ℤ))) := by
  rw [localKummerSymbol_eq_inv_localInvariant h hres hm hur hσ₀ hcarry π,
    localInvariant_cyclicBrauerHom_pow hur hm hσ₀ hs π, baseInvariant_apply, unitInvariant_apply,
    hπ, ← intQModZ_apply]
  exact inv_ofAdd_intQModZ_pow _ _

omit [CompleteSpace K] in
/-- **Some automorphism of an algebraic closure induces the Frobenius automorphism of the level of
a unit**, restriction to a normal intermediate field being onto. -/
theorem exists_isDivisionFrobenius_restrictNormalHom {b : Kˣ}
    (hur : ∀ z : ↥(kummerLevel h b), z ≠ 0 →
      ∃ d : K, d ≠ 0 ∧ divisionNorm K ↥(kummerLevel h b) z = ‖d‖) :
    ∃ g : Gal(AlgebraicClosure K/K),
      IsDivisionFrobenius (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g) := by
  refine ⟨levelPreimage h b (divisionFrobenius K ↥(kummerLevel h b) hur), ?_⟩
  rw [restrictNormalHom_levelPreimage]
  exact isDivisionFrobenius_divisionFrobenius K ↥(kummerLevel h b) hur

/-- **The value of the tame norm residue symbol of a uniformiser against a unit of the valuation
ring which is not a power**: it is the class, modulo the integers, of the opposite of the Kummer
character of the unit at any automorphism inducing the Frobenius automorphism of the level of the
unit, divided by the exponent. -/
theorem localKummerSymbol_uniformiser_eq_kummerChar (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = 1) {b : Kˣ} (hb : Valued.v (b : K) = 1)
    (hnp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ¬ ∃ c : Kˣ, c ^ ℓ = b) {g : Gal(AlgebraicClosure K/K)}
    (hg : IsDivisionFrobenius (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)) :
    localKummerSymbol hres hm h (mulZMod n) π b
      = Multiplicative.ofAdd (zmodQModZ n (-kummerChar h b g)) := by
  have hdn : Nat.card Gal(↥(kummerLevel h b)/K) = n :=
    card_gal_kummerLevel_eq_of_not_isPow h hnp
  have hur : ∀ z : ↥(kummerLevel h b), z ≠ 0 →
      ∃ d : K, d ≠ 0 ∧ divisionNorm K ↥(kummerLevel h b) z = ‖d‖ :=
    exists_divisionNorm_eq_kummerLevel h hpn hres hb hdn
  obtain ⟨σ₀, t, hgen, htpos, hmt, hval⟩ := exists_generator_kummerLevel_index h b
  have ht1 : t = 1 := by
    rw [hdn] at hmt
    have hmt' : n * t = n * 1 := by rw [hmt, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne n)) hmt'
  have hchar : (kummerChar h b g).val
      = (dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)).val := by
    rw [hval g, ht1, one_mul]
  have hfrob : AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g
      = divisionFrobenius K ↥(kummerLevel h b) hur :=
    eq_divisionFrobenius K ↥(kummerLevel h b) hur hg
  have hs : divisionFrobenius K ↥(kummerLevel h b) hur = σ₀ ^ (kummerChar h b g).val := by
    rw [hchar, pow_val_dlog hgen, hfrob]
  have hfr : finrank K ↥(kummerLevel h b) = n :=
    (IsGalois.card_aut_eq_finrank K ↥(kummerLevel h b)).symm.trans hdn
  have hcast : ((-((kummerChar h b g).val : ℤ) : ℤ) : ZMod n) = -kummerChar h b g := by
    rw [Int.cast_neg, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  rw [localKummerSymbol_uniformiser_eq h hres hm hur hgen
      (carry_iff_of_index h htpos hmt hval) hπ hs, hfr, intQModZ_eq_zmodQModZ, hcast]

end Value

/-! ### The value for the symbol attached to a primitive root of unity -/

section Root

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ} {n : ℕ} [NeZero n] {ζ : K}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-- **The value of the tame norm residue symbol of a uniformiser against a unit of the valuation
ring which is not a power**: it is the class, modulo the integers, of the opposite of the Kummer
character of the unit at any automorphism inducing the Frobenius automorphism of the level of the
unit, divided by the exponent. -/
theorem localSymbol_uniformiser_eq_kummerChar (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hpn : ¬ p ∣ n)
    {π : Kˣ} (hπ : unitValDiv hm (Additive.ofMul π) = 1) {b : Kˣ} (hb : Valued.v (b : K) = 1)
    (hnp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ¬ ∃ c : Kˣ, c ^ ℓ = b) {g : Gal(AlgebraicClosure K/K)}
    (hg : IsDivisionFrobenius (AlgEquiv.restrictNormalHom
      ↥(kummerLevel (isKummerData_zmod (Ω := AlgebraicClosure K) hζ exists_units_pow_eq) b) g)) :
    localSymbol hres hm hζ π b
      = Multiplicative.ofAdd (zmodQModZ n
          (-kummerChar (isKummerData_zmod (Ω := AlgebraicClosure K) hζ exists_units_pow_eq) b g)) :=
  localKummerSymbol_uniformiser_eq_kummerChar
    (isKummerData_zmod (Ω := AlgebraicClosure K) hζ exists_units_pow_eq) hres hm hpn hπ hb hnp hg

end Root

end InverseGalois.CFT
