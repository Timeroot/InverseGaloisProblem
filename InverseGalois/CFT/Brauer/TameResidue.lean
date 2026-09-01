/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.FrobeniusBaseChange
import InverseGalois.CFT.Brauer.TameValue
import InverseGalois.CFT.Local.PrimeResidue
import InverseGalois.CFT.Local.RootOfUnityValued

/-!
# The tame norm residue symbol is the power residue symbol

The value of the tame norm residue symbol of a uniformiser against a unit of the valuation ring is
the Kummer character of that unit at a Frobenius automorphism of its level.  That character is
identified here with the classical power residue exponent, which removes both the Frobenius
automorphism and the Kummer character from the statement.

The chosen root of the unit has absolute value one, its power of exponent the exponent being the
unit itself.  A Frobenius automorphism moves every integer to within distance one of its power by
the number of residues of the base, and it multiplies the chosen root by the root of unity that the
Kummer character names, so cancelling the chosen root leaves that root of unity within distance one
of the power of the chosen root by one less than the number of residues.  The exponent divides one
less than the number of residues, because the base already contains a primitive root of unity of
that exponent; so the surviving power of the chosen root is a power of the unit itself, and no
trace of the level is left.

Two roots of unity of order prime to the residue characteristic at distance less than one are
equal, so the congruence determines the Kummer character.  The symbol of a uniformiser against a
unit is therefore the class, modulo the integers, of the opposite of the power residue exponent,
divided by the exponent.

## Main results

* `InverseGalois.CFT.divisionNorm_sub_pow_card_sub_one_lt_one`: **an eigenvector of a Frobenius
  automorphism of absolute value one has its eigenvalue congruent to its power by one less than the
  number of residues of the base.**
* `InverseGalois.CFT.algebraMap_eq_kummerLevelGen_pow`: the chosen root of a unit, read in the
  level of the unit, has that unit as its power of exponent the exponent.
* `InverseGalois.CFT.restrictNormalHom_kummerLevelGen`: an automorphism multiplies the chosen root
  of a unit, read in the level of the unit, by the root of unity the Kummer character names.
* `InverseGalois.CFT.valued_pow_kummerChar_sub_pow_lt_one`: **the Kummer character of a unit at a
  Frobenius automorphism is the power residue exponent of that unit.**
* `InverseGalois.CFT.kummerChar_eq_of_valued_pow_sub_pow_lt_one`: the power residue congruence
  determines the Kummer character.
* `InverseGalois.CFT.localSymbol_uniformiser_eq_powerResidue`: **the tame norm residue symbol of a
  uniformiser against a unit of the valuation ring is the class, modulo the integers, of the
  opposite of the power residue exponent of the unit, divided by the exponent.**

## Tags

norm residue symbol, power residue symbol, tame symbol, local field, Frobenius, residue field,
Kummer theory, class field theory
-/

universe u

namespace InverseGalois.CFT

open scoped Valued WithZero

/-! ### An eigenvector of a Frobenius automorphism -/

section Frobenius

variable {K L : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]

omit [IsUltrametricDist K] [ProperSpace K] [FiniteDimensional K L] in
/-- An element a nontrivial power of which has absolute value one has absolute value one. -/
theorem divisionNorm_eq_one_of_pow_eq_one {x : L} {N : ℕ} (hN : N ≠ 0)
    (hx : divisionNorm K L x ^ N = 1) : divisionNorm K L x = 1 := by
  rcases lt_trichotomy (divisionNorm K L x) 1 with hlt | heq | hgt
  · exact absurd hx (ne_of_lt (pow_lt_one₀ (divisionNorm_nonneg x) hlt hN))
  · exact heq
  · exact absurd hx (ne_of_gt (one_lt_pow₀ hgt hN))

/-- **The eigenvalue of a Frobenius automorphism at an eigenvector of absolute value one is
congruent to the power of that eigenvector by one less than the number of residues of the base.**
The Frobenius automorphism moves the eigenvector to within distance one of its power by the number
of residues, and the eigenvector may then be cancelled from the difference. -/
theorem divisionNorm_sub_pow_card_sub_one_lt_one {σ : L ≃ₐ[K] L} (hσ : IsDivisionFrobenius σ)
    {x c : L} (hx : divisionNorm K L x = 1) (hσx : σ x = c * x) :
    divisionNorm K L (c - x ^ (Nat.card (DivisionResidue K K) - 1)) < 1 := by
  have hQ : 1 < Nat.card (DivisionResidue K K) := Finite.one_lt_card
  have hmem : x ∈ divisionIntegers K L := mem_divisionIntegers.2 hx.le
  have hfrob : divisionNorm K L (σ x - x ^ Nat.card (DivisionResidue K K)) < 1 :=
    (isDivisionFrobenius_iff σ).1 hσ ⟨x, hmem⟩
  have hfac : σ x - x ^ Nat.card (DivisionResidue K K)
      = (c - x ^ (Nat.card (DivisionResidue K K) - 1)) * x := by
    rw [hσx, sub_mul, ← pow_succ, Nat.sub_add_cancel hQ.le]
  rwa [hfac, divisionNorm_mul, hx, mul_one] at hfrob

end Frobenius

/-! ### The chosen root of a unit inside its level -/

section Kummer

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {n : ℕ} [NeZero n]
  {ζ : k} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData k Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

omit [IsGalois k Ω] in
/-- **The power of exponent the exponent of the chosen root of a unit, read inside the level of
that unit, is the unit itself.** -/
theorem algebraMap_eq_kummerLevelGen_pow (b : kˣ) :
    algebraMap k ↥(kummerLevel h b) (b : k) = kummerLevelGen h b ^ n := by
  refine (algebraMap ↥(kummerLevel h b) Ω).injective ?_
  rw [map_pow, ← IsScalarTower.algebraMap_apply]
  exact (congrArg Units.val (h.root_pow b)).symm

/-- **An automorphism multiplies the chosen root of a unit, read inside the level of that unit, by
the root of unity which the Kummer character of the unit names.** -/
theorem restrictNormalHom_kummerLevelGen (b : kˣ) (g : Gal(Ω/k)) :
    AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g (kummerLevelGen h b)
      = algebraMap k ↥(kummerLevel h b) (ζ ^ (kummerChar h b g).val) * kummerLevelGen h b := by
  have hs := congrArg Units.val (smul_root_eq_kummerRootUnit_pow h b g)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, kummerRootUnit, Units.coe_map,
    MonoidHom.coe_coe] at hs
  refine SetLike.coe_eq_coe.mp ?_
  rw [AlgEquiv.restrictNormalHom_apply, MulMemClass.coe_mul,
    IntermediateField.coe_algebraMap_apply, map_pow, coe_kummerLevelGen]
  exact (show g ((h.root b : Ωˣ) : Ω) = ((g • h.root b : Ωˣ) : Ω) from rfl).trans hs

end Kummer

/-! ### An exponent prime to the residue characteristic -/

section NatCast

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] {p e n : ℕ}

/-- An integer prime to the residue characteristic has absolute value one. -/
theorem norm_natCast_of_not_dvd (hres : HasResidueChar K p e) (hpn : ¬ p ∣ n) :
    ‖((n : ℕ) : K)‖ = 1 :=
  (norm_eq_one_iff_valued _).2
    (valued_natCast_eq_one_of_not_dvd hres.prime (valued_residueChar_lt_one hres) hpn)

end NatCast

/-! ### The Kummer character is the power residue exponent -/

section Residue

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {p e : ℕ} {n : ℕ} [NeZero n] {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData K (AlgebraicClosure K) (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

omit [CompleteSpace K] in
/-- **The Kummer character of a unit of the valuation ring at a Frobenius automorphism of the level
of that unit is the power residue exponent of the unit**: the corresponding power of the root of
unity is congruent, modulo the maximal ideal, to the power of the unit by the quotient of one less
than the number of residues by the exponent. -/
theorem valued_pow_kummerChar_sub_pow_lt_one (hres : HasResidueChar K p e) (hpn : ¬ p ∣ n)
    {b : Kˣ} (hb : Valued.v (b : K) = 1) {g : Gal(AlgebraicClosure K/K)}
    (hg : IsDivisionFrobenius (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)) :
    Valued.v (ζ ^ (kummerChar h b g).val
      - (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1 := by
  have hbn : ‖(b : K)‖ = 1 := (norm_eq_one_iff_valued _).2 hb
  have hgen : divisionNorm K ↥(kummerLevel h b) (kummerLevelGen h b) = 1 := by
    refine divisionNorm_eq_one_of_pow_eq_one (NeZero.ne n) ?_
    rw [← divisionNorm_pow, ← algebraMap_eq_kummerLevelGen_pow h b, divisionNorm_algebraMap, hbn]
  have hkey := divisionNorm_sub_pow_card_sub_one_lt_one hg hgen
    (restrictNormalHom_kummerLevelGen h b g)
  have hdvd : n ∣ Nat.card (DivisionResidue K K) - 1 :=
    dvd_card_divisionResidue_sub_one_of_isPrimitiveRoot (K := K) (L := K) hζ
      (norm_natCast_of_not_dvd hres hpn)
  have hsplit : kummerLevelGen h b ^ (Nat.card (DivisionResidue K K) - 1)
      = algebraMap K ↥(kummerLevel h b)
        ((b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) := by
    rw [map_pow, algebraMap_eq_kummerLevelGen_pow h b, ← pow_mul, Nat.mul_div_cancel' hdvd]
  rw [hsplit, ← map_sub, divisionNorm_algebraMap] at hkey
  exact Valued.toNormedField.norm_lt_one_iff.1 hkey

omit [CompleteSpace K] in
/-- **The power residue congruence determines the Kummer character of a unit at a Frobenius
automorphism**: two roots of unity of order prime to the residue characteristic at distance less
than one are equal. -/
theorem kummerChar_eq_of_valued_pow_sub_pow_lt_one (hres : HasResidueChar K p e) (hpn : ¬ p ∣ n)
    {b : Kˣ} (hb : Valued.v (b : K) = 1) {g : Gal(AlgebraicClosure K/K)}
    (hg : IsDivisionFrobenius (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)) {j : ℕ}
    (hj : Valued.v (ζ ^ j - (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) :
    kummerChar h b g = (j : ZMod n) := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have hnv : Valued.v ((n : ℕ) : K) = 1 :=
    valued_natCast_eq_one_of_not_dvd hres.prime (valued_residueChar_lt_one hres) hpn
  have hmain := valued_pow_kummerChar_sub_pow_lt_one h hres hpn hb hg
  have hdiff : Valued.v (ζ ^ (kummerChar h b g).val - ζ ^ j) < 1 := by
    have hsub : ζ ^ (kummerChar h b g).val - ζ ^ j
        = (ζ ^ (kummerChar h b g).val
            - (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n))
          - (ζ ^ j - (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) := by ring
    rw [hsub]
    exact lt_of_le_of_lt (Valued.v.map_sub _ _) (max_lt hmain hj)
  have hpz : ∀ i : ℕ, (ζ ^ i) ^ n = 1 := fun i => by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have heq := eq_of_valued_sub_lt_one hn0 hnv (hpz _) (hpz j) hdiff
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨n, Nat.pos_of_ne_zero hn0, hζ.pow_eq_one⟩
  have hmod : (kummerChar h b g).val ≡ j [MOD orderOf ζ] := hfin.pow_eq_pow_iff_modEq.1 heq
  rw [← hζ.eq_orderOf] at hmod
  have hcast : (((kummerChar h b g).val : ℕ) : ZMod n) = ((j : ℕ) : ZMod n) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  rwa [ZMod.natCast_val, ZMod.cast_id] at hcast

end Residue

/-! ### The tame symbol as a power residue symbol -/

section Root

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ} {n : ℕ} [NeZero n] {ζ : K}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-- **The tame norm residue symbol of a uniformiser against a unit of the valuation ring which is
not a power is the power residue symbol of that unit**: it is the class, modulo the integers, of
the opposite of an exponent whose power of the chosen root of unity is congruent to the power of
the unit by the quotient of one less than the number of residues by the exponent, divided by the
exponent. -/
theorem localSymbol_uniformiser_eq_powerResidue (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hpn : ¬ p ∣ n)
    {π : Kˣ} (hπ : unitValDiv hm (Additive.ofMul π) = 1) {b : Kˣ} (hb : Valued.v (b : K) = 1)
    (hnp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ¬ ∃ c : Kˣ, c ^ ℓ = b) {j : ℕ}
    (hj : Valued.v (ζ ^ j - (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) :
    localSymbol hres hm hζ π b = Multiplicative.ofAdd (zmodQModZ n (-(j : ZMod n))) := by
  obtain ⟨g, hg⟩ :=
    exists_isDivisionFrobenius_restrictNormalHom
      (isKummerData_zmod (Ω := AlgebraicClosure K) hζ exists_units_pow_eq)
      (exists_divisionNorm_eq_kummerLevel _ hpn hres hb
        (card_gal_kummerLevel_eq_of_not_isPow _ hnp))
  rw [localSymbol_uniformiser_eq_kummerChar hres hm hζ hpn hπ hb hnp hg,
    kummerChar_eq_of_valued_pow_sub_pow_lt_one _ hres hpn hb hg hj]

end Root

end InverseGalois.CFT
