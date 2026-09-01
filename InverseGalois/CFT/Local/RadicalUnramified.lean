/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.CyclicNormIndex
import InverseGalois.CFT.Local.GaussNorm
import InverseGalois.CFT.Local.UnitRootPower
import InverseGalois.CFT.Local.UnramifiedNormValue

/-!
# A radical extension by a unit is unramified

Over a complete field with a rank one valuation, adjoining a root of prime order `ℓ` of a unit
gives an unramified extension as soon as the residue characteristic does not divide `ℓ`.

The reason is that the reduction of the minimal polynomial stays irreducible.  A unit which is an
`ℓ`-th power modulo the maximal ideal is already an `ℓ`-th power, because a unit congruent to one is
a power with any exponent prime to the residue characteristic; so a unit which is not an `ℓ`-th
power in the field is not one in the residue field either, and for a prime exponent that is exactly
the irreducibility of the difference of the `ℓ`-th power of the variable and the reduction.  The
Gauss norm of that power basis is then an absolute value, hence the spectral norm, and all its
values are values of the base field.

Consequently a unit of the valuation ring of the base field is a norm from such an extension: the
norm subgroup of a cyclic extension of a local field has index the degree, and the invariant of an
unramified extension reads the value of a unit, which is trivial.

## Main results

* `InverseGalois.CFT.exists_pow_eq_of_residue_pow_eq`: **a unit which is a power modulo the maximal
  ideal is a power**, for an exponent prime to the residue characteristic.
* `InverseGalois.CFT.IsRadicalExponent`: the exponents, among them the prime ones and the odd ones,
  for which a radical polynomial is irreducible exactly when its constant term is not a power of
  prime order dividing the exponent.
* `InverseGalois.CFT.irreducible_X_pow_sub_C_residue`: **the reduction of the minimal polynomial of
  a root of such an order of a unit stays irreducible.**
* `InverseGalois.CFT.exists_valued_of_radical_unit`: **a radical extension of prime degree by a unit
  is an unramified extension of local fields.**
* `InverseGalois.CFT.mem_normSubgroup_of_radical_unit`: **every unit of the valuation ring of the
  base field is a norm from such an extension.**

## Tags

unramified extension, radical extension, Kummer extension, local field, residue field, norm,
class field theory
-/

namespace InverseGalois.CFT

open Module Polynomial

open scoped Valued WithZero

/-! ### Exponents of an irreducible radical polynomial -/

section Exponent

/-- **An exponent for which the difference of that power of the variable and a constant is
irreducible exactly when the constant is not a power of prime order dividing the exponent.**  Both
a prime exponent and an odd exponent have this property. -/
def IsRadicalExponent (n : ℕ) : Prop :=
  ∀ (F : Type) [Field F] (a : F),
    Irreducible ((X : F[X]) ^ n - C a) ↔ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ∀ b : F, b ^ ℓ ≠ a

/-- A prime exponent is an exponent of an irreducible radical polynomial, the only prime dividing
it being itself. -/
theorem isRadicalExponent_of_prime {n : ℕ} (hn : n.Prime) : IsRadicalExponent n := by
  intro F _ a
  rw [X_pow_sub_C_irreducible_iff_of_prime hn]
  exact ⟨fun hb ℓ hℓ hℓn => by rwa [(Nat.prime_dvd_prime_iff_eq hℓ hn).1 hℓn],
    fun hb => hb n hn dvd_rfl⟩

/-- An odd exponent is an exponent of an irreducible radical polynomial. -/
theorem isRadicalExponent_of_odd {n : ℕ} (hn : Odd n) : IsRadicalExponent n := by
  intro F _ a
  exact X_pow_sub_C_irreducible_iff_forall_prime_of_odd hn

end Exponent

/-! ### Units and the residue field -/

section Residue

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] {p e : ℕ}

/-- An integer of the valuation is a unit exactly when it survives the reduction to the residue
field. -/
theorem valued_eq_one_iff_residue_ne_zero (y : ↥(𝒪[K])) :
    Valued.v (y : K) = 1 ↔ IsLocalRing.residue ↥(𝒪[K]) y ≠ 0 := by
  rw [← norm_eq_one_iff_valued, norm_eq_one_iff_residue_ne_zero]

/-- The maximal ideal of the valuation ring is the elements of value smaller than one. -/
theorem mem_maximalIdeal_iff_valued_lt_one (y : ↥(𝒪[K])) :
    y ∈ IsLocalRing.maximalIdeal ↥(𝒪[K]) ↔ Valued.v (y : K) < 1 := by
  rw [← IsLocalRing.residue_eq_zero_iff, ← not_ne_iff, ← valued_eq_one_iff_residue_ne_zero]
  exact ⟨fun h => lt_of_le_of_ne y.2 h, fun h => h.ne⟩

variable [CompleteSpace K]

/-- **A unit which is a power modulo the maximal ideal is a power**, for an exponent prime to the
residue characteristic: the quotient of the unit by the power of a lift is congruent to one, and a
unit congruent to one is a power with any exponent prime to the residue characteristic. -/
theorem exists_pow_eq_of_residue_pow_eq (hres : HasResidueChar K p e) {d : ℕ} (hd : d ≠ 0)
    (hpd : ¬ p ∣ d) {c : ↥(𝒪[K])} (hc : Valued.v (c : K) = 1) {y : 𝓀[K]}
    (hy : y ^ d = IsLocalRing.residue ↥(𝒪[K]) c) : ∃ z : K, z ^ d = (c : K) := by
  obtain ⟨y₀, rfl⟩ := IsLocalRing.residue_surjective y
  have hcne : IsLocalRing.residue ↥(𝒪[K]) c ≠ 0 := (valued_eq_one_iff_residue_ne_zero c).1 hc
  have hyne : IsLocalRing.residue ↥(𝒪[K]) y₀ ≠ 0 := fun h0 =>
    hcne (by rw [← hy, h0, zero_pow hd])
  have hy₀ : Valued.v (y₀ : K) = 1 := (valued_eq_one_iff_residue_ne_zero y₀).2 hyne
  have hmem : y₀ ^ d - c ∈ IsLocalRing.maximalIdeal ↥(𝒪[K]) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hy, sub_self]
  have hcoe : (((y₀ ^ d - c : ↥(𝒪[K])) : K)) = (y₀ : K) ^ d - (c : K) := by
    push_cast
    ring
  have hlt : Valued.v ((c : K) - (y₀ : K) ^ d) < 1 := by
    have hmm := (mem_maximalIdeal_iff_valued_lt_one _).1 hmem
    rw [hcoe] at hmm
    rwa [show (c : K) - (y₀ : K) ^ d = -((y₀ : K) ^ d - (c : K)) from by ring, Valuation.map_neg]
  have hc0 : (c : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at hc; exact zero_ne_one hc
  have hy0 : (y₀ : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at hy₀; exact zero_ne_one hy₀
  obtain ⟨z, hz⟩ := exists_pow_eq_of_valued_sub_lt_one hres hd hpd
    (ζ := Units.mk0 (c : K) hc0) (b := Units.mk0 (y₀ : K) hy0) hc hlt
  exact ⟨(z : K), congrArg Units.val hz⟩

/-- **The reduction of the difference of a power of the variable and a unit stays irreducible**,
when the exponent is prime to the residue characteristic and the unit is not a power of any prime
order dividing the exponent in the base field. -/
theorem irreducible_X_pow_sub_C_residue (hres : HasResidueChar K p e) {n : ℕ}
    (hn : IsRadicalExponent n) (hpn : ¬ p ∣ n) {c : ↥(𝒪[K])} (hc : Valued.v (c : K) = 1)
    (hnp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ∀ z : K, z ^ ℓ ≠ (c : K)) :
    Irreducible (X ^ n - C (IsLocalRing.residue ↥(𝒪[K]) c)) := by
  refine (hn 𝓀[K] _).2 fun ℓ hl hln y hy => ?_
  obtain ⟨z, hz⟩ := exists_pow_eq_of_residue_pow_eq hres hl.ne_zero
    (fun hd => hpn (hd.trans hln)) hc hy
  exact hnp ℓ hl hln z hz

end Residue

/-! ### The extension is unramified -/

section Radical

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [Field L] [Algebra K L] [FiniteDimensional K L] {p e : ℕ}

/-- **A radical extension of prime degree by a unit is an unramified extension of local
fields**, as soon as the residue characteristic does not divide the degree. -/
theorem exists_valued_of_radical_unit (pb : PowerBasis K L) {ℓ : ℕ} (hl : ℓ.Prime)
    (hpl : ¬ p ∣ ℓ) {c : K} (hc : Valued.v c = 1) (hmin : minpoly K pb.gen = X ^ ℓ - C c)
    (hres : HasResidueChar K p e) :
    ∃ (_ : Valued L ℤᵐ⁰) (_ : CompleteSpace L) (m : ℤ) (e' : ℕ),
      (∀ y : L, Valued.v y = Valued.v (Algebra.norm K y)) ∧
      (∀ (σ : L ≃ₐ[K] L) (x : L), Valued.v (σ x) = Valued.v x) ∧
        HasResidueChar L p e' ∧ (∀ k : ℤ, Finite (gradedAdd L k)) ∧
          IsUnramifiedValued K L ∧ IsUnitValGen L m := by
  have hcmem : c ∈ 𝒪[K] := le_of_eq hc
  set c₀ : ↥(𝒪[K]) := ⟨c, hcmem⟩ with hc₀
  have hcval : Valued.v ((c₀ : ↥(𝒪[K])) : K) = 1 := hc
  have hF : (X ^ ℓ - C c₀).Monic := monic_X_pow_sub_C _ hl.ne_zero
  have hFmin : (X ^ ℓ - C c₀).map (Subring.subtype 𝒪[K]) = minpoly K pb.gen := by
    rw [hmin, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hnp : ∀ k : ℕ, k.Prime → k ∣ ℓ → ∀ z : K, z ^ k ≠ c := by
    refine (isRadicalExponent_of_prime hl K c).1 ?_
    rw [← hmin]
    exact minpoly.irreducible (IsIntegral.of_finite K pb.gen)
  have hirr : Irreducible ((X ^ ℓ - C c₀).map (IsLocalRing.residue ↥(𝒪[K]))) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact irreducible_X_pow_sub_C_residue hres (isRadicalExponent_of_prime hl) hpl hcval hnp
  exact exists_valued_of_residue_irreducible pb hF hFmin hirr hres

/-- **Every unit of the valuation ring of the base field is a norm from a radical extension of
prime degree by a unit.**  The extension is unramified, and the norm subgroup of a cyclic extension
of a local field has index the degree, so the invariant of a unit of the valuation ring, which is
its value, is trivial. -/
theorem mem_normSubgroup_of_radical_unit [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (pb : PowerBasis K L) {ℓ : ℕ} (hl : ℓ.Prime) (hpl : ¬ p ∣ ℓ) {c : K} (hc : Valued.v c = 1)
    (hmin : minpoly K pb.gen = X ^ ℓ - C c) (hres : HasResidueChar K p e) {a : Kˣ}
    (ha : Valued.v (a : K) = 1) : a ∈ normSubgroup K L := by
  obtain ⟨instV, instC, m, e', hvL, hv, hres', hgr, hur, hm⟩ :=
    exists_valued_of_radical_unit pb hl hpl hc hmin hres
  letI := instV
  haveI := instC
  refine mem_normSubgroup_of_unitVal_eq_zero hv hur hm
    (index_normSubgroup_eq_finrank_local K L hres) ?_
  have hval : Valued.v ((unitsAlgebraMap K L a : Lˣ) : L) = 1 := by
    rw [coe_unitsAlgebraMap, hvL, Algebra.norm_algebraMap, map_pow, ha, one_pow]
  rw [unitVal_apply, hval, WithZero.log_one]

end Radical

end InverseGalois.CFT
