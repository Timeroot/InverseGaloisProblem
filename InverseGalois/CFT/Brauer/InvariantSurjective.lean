/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.InvariantInjective

/-!
# The invariant map of a local field is an isomorphism

A local field has unramified extensions of every degree: adjoining the roots of unity of order one
less than a power of the number of residues never ramifies, and the roots of unity survive in the
residue field, which is therefore at least as large as that power.  Since the normalised invariant
attains the reciprocal of the degree on an unramified extension, its image contains every rational
whose denominator divides that degree, and every rational modulo the integers is of that shape.

Together with the injectivity of the invariant this identifies the Brauer group of a local field
with the rationals modulo the integers.  It is the group-theoretic heart of local class field
theory: the Brauer group of a local field is `ℚ/ℤ`, canonically.

## Main results

* `InverseGalois.CFT.dvd_of_pow_sub_one_dvd_pow_sub_one`: one less than a power divides one less
  than another power exactly when the exponents divide.
* `InverseGalois.CFT.dvd_card_divisionResidue_sub_one_of_isPrimitiveRoot`: **a root of unity of
  invertible order in an extension of a local field has the same order in the residue field.**
* `InverseGalois.CFT.exists_unramified_dvd_finrank`: **a local field has an unramified extension of
  degree divisible by any prescribed number.**
* `InverseGalois.CFT.localInvariantHom_surjective`: **every rational modulo the integers is the
  invariant of a Brauer class over a local field.**
* `InverseGalois.CFT.localInvariantEquiv`: **the Brauer group of a local field is the rationals
  modulo the integers.**

## Tags

Brauer group, local field, unramified extension, invariant map, class field theory
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

universe u

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

/-! ### Divisibility between the exponents -/

/-- **One less than a power divides one less than another power only if the exponents divide.**
The remainder of the exponents leaves a smaller nonnegative multiple, which must vanish. -/
theorem dvd_of_pow_sub_one_dvd_pow_sub_one {q a b : ℕ} (hq : 2 ≤ q)
    (h : q ^ a - 1 ∣ q ^ b - 1) : a ∣ b := by
  have hq0 : 0 < q := by omega
  have hone : ∀ c : ℕ, 1 ≤ q ^ c := fun c => Nat.one_le_pow c q hq0
  have hZ : ((q : ℤ)) ^ a - 1 ∣ ((q : ℤ)) ^ b - 1 := by
    have hcast : ∀ c : ℕ, ((q ^ c - 1 : ℕ) : ℤ) = ((q : ℤ)) ^ c - 1 := fun c => by
      push_cast [Nat.cast_sub (hone c)]
      ring
    rw [← hcast a, ← hcast b]
    exact Int.natCast_dvd_natCast.2 h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hb : ((q : ℤ)) ^ b - 1 = 0 := by
      have h1 : ((q : ℤ)) ^ 0 - 1 = 0 := by norm_num
      rw [h1] at hZ
      exact (zero_dvd_iff.1 hZ)
    have hb1 : q ^ b = 1 := by
      have : ((q ^ b : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    rcases Nat.eq_zero_or_pos b with rfl | hbpos
    · exact dvd_rfl
    · have : q ≤ q ^ b := Nat.le_self_pow hbpos.ne' q
      omega
  · have hsplit : b = a * (b / a) + b % a := (Nat.div_add_mod b a).symm
    have hlt : b % a < a := Nat.mod_lt _ ha
    have hdvdmul : ((q : ℤ)) ^ a - 1 ∣ ((q : ℤ)) ^ (a * (b / a)) - 1 := by
      have hd := sub_dvd_pow_sub_pow (((q : ℤ)) ^ a) 1 (b / a)
      rwa [one_pow, ← pow_mul] at hd
    have hid : ((q : ℤ)) ^ b - 1
        = ((q : ℤ)) ^ (b % a) * (((q : ℤ)) ^ (a * (b / a)) - 1) + (((q : ℤ)) ^ (b % a) - 1) := by
      conv_lhs => rw [hsplit]
      rw [pow_add]
      ring
    have hrem : ((q : ℤ)) ^ a - 1 ∣ ((q : ℤ)) ^ (b % a) - 1 := by
      have := (Dvd.dvd.sub (hid ▸ hZ) (hdvdmul.mul_left (((q : ℤ)) ^ (b % a))))
      simpa using this
    have hnn : (0 : ℤ) ≤ ((q : ℤ)) ^ (b % a) - 1 := by
      have h1 := hone (b % a)
      have h2 : ((1 : ℕ) : ℤ) ≤ ((q ^ (b % a) : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    have hsmall : ((q : ℤ)) ^ (b % a) - 1 < ((q : ℤ)) ^ a - 1 := by
      have hlt' : q ^ (b % a) < q ^ a := Nat.pow_lt_pow_right (by omega) hlt
      have h2 : ((q ^ (b % a) : ℕ) : ℤ) < ((q ^ a : ℕ) : ℤ) := by exact_mod_cast hlt'
      push_cast at h2
      linarith
    have hzero : ((q : ℤ)) ^ (b % a) - 1 = 0 := by
      rcases hnn.lt_or_eq with hpos | heq
      · exact absurd hsmall (not_lt.2 (Int.le_of_dvd hpos hrem))
      · exact heq.symm
    have hmod : b % a = 0 := by
      by_contra hne
      have : q ≤ q ^ (b % a) := Nat.le_self_pow hne q
      have hc : ((q : ℤ)) ≤ ((q : ℤ)) ^ (b % a) := by exact_mod_cast this
      have hq' : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
      linarith
    exact Nat.dvd_of_mod_eq_zero hmod

/-! ### Roots of unity survive in the residue field -/

section Residue

variable {K L : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **A root of unity of invertible order in an extension of a local field has the same order in
the residue field.**  Its residue is a nonzero element of a finite field, so it is killed by one
less than the number of residues, and a root of unity of invertible order which is a residue of one
is one. -/
theorem dvd_card_divisionResidue_sub_one_of_isPrimitiveRoot {ζ : L} {M : ℕ}
    (hζ : IsPrimitiveRoot ζ M) (hM : ‖((M : ℕ) : K)‖ = 1) :
    M ∣ Nat.card (DivisionResidue K L) - 1 := by
  classical
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, norm_zero] at hM
    exact zero_ne_one hM
  have hML : divisionNorm K L ((M : ℕ) : L) = 1 := by
    rw [show (((M : ℕ)) : L) = algebraMap K L ((M : ℕ) : K) by rw [map_natCast],
      divisionNorm_algebraMap]
    exact hM
  have hpow : ζ ^ M = 1 := hζ.pow_eq_one
  have h1 : divisionNorm K L ζ = 1 := by
    have hp : divisionNorm K L ζ ^ M = 1 := by rw [← divisionNorm_pow, hpow, divisionNorm_one]
    have hnn := divisionNorm_nonneg (K := K) (D := L) ζ
    rcases lt_trichotomy (divisionNorm K L ζ) 1 with h | h | h
    · exact absurd hp (ne_of_lt (pow_lt_one₀ hnn h hM0))
    · exact h
    · exact absurd hp (ne_of_gt (one_lt_pow₀ h hM0))
  have hζO : ζ ∈ divisionIntegers K L := mem_divisionIntegers.2 h1.le
  letI : Field (DivisionResidue K L) := (Finite.isField_of_domain (DivisionResidue K L)).toField
  haveI : Fintype (DivisionResidue K L) := Fintype.ofFinite _
  set N : ℕ := Nat.card (DivisionResidue K L) - 1 with hN
  have hz0 : ((⟨ζ, hζO⟩ : divisionIntegers K L) : DivisionResidue K L) ≠ 0 := by
    rw [Ne, divisionResidue_eq_zero_iff]
    simp only [h1]
    exact lt_irrefl 1
  have hcard : Fintype.card (DivisionResidue K L) - 1 = N := by
    rw [hN, Nat.card_eq_fintype_card]
  have hres : ((⟨ζ, hζO⟩ : divisionIntegers K L) : DivisionResidue K L) ^ N = 1 := by
    rw [← hcard]
    exact FiniteField.pow_card_sub_one_eq_one _ hz0
  have hpowres : (((⟨ζ, hζO⟩ : divisionIntegers K L) ^ N : divisionIntegers K L) :
      DivisionResidue K L) = ((1 : divisionIntegers K L) : DivisionResidue K L) := by
    rw [RingCon.coe_pow, RingCon.coe_one]
    exact hres
  have hlt : divisionNorm K L (ζ ^ N - 1) < 1 := by
    have := divisionResidue_eq_iff.1 hpowres
    simpa using this
  have hkill : (ζ ^ N) ^ M = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
  exact hζ.dvd_of_pow_eq_one N
    (eq_one_of_pow_eq_one_of_divisionNorm_sub_lt_one hkill hML hlt)

variable (K) in
/-- One less than a power of the number of residues of a local field is invertible there. -/
theorem norm_natCast_pow_card_divisionResidue_sub_one {n : ℕ} (hn : n ≠ 0) :
    ‖((Nat.card (DivisionResidue K K) ^ n - 1 : ℕ) : K)‖ = 1 := by
  have hcard : 1 < Nat.card (DivisionResidue K K) := Finite.one_lt_card
  have hpowcard : 1 < Nat.card (DivisionResidue K K) ^ n :=
    lt_of_lt_of_le hcard (Nat.le_self_pow hn _)
  have hQ : divisionNorm K K ((Nat.card (DivisionResidue K K) : ℕ) : K) < 1 :=
    divisionNorm_natCard_divisionResidue_lt_one K K
  rw [show (((Nat.card (DivisionResidue K K) : ℕ)) : K)
      = algebraMap K K ((Nat.card (DivisionResidue K K) : ℕ) : K) by rw [map_natCast],
    divisionNorm_algebraMap] at hQ
  have hQn : ‖((Nat.card (DivisionResidue K K) ^ n : ℕ) : K)‖ < 1 := by
    rw [Nat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hQ hn
  have hne : ‖((Nat.card (DivisionResidue K K) ^ n : ℕ) : K)‖ ≠ ‖(-1 : K)‖ := by
    rw [norm_neg, norm_one]
    exact hQn.ne
  have hcast : ((Nat.card (DivisionResidue K K) ^ n - 1 : ℕ) : K)
      = ((Nat.card (DivisionResidue K K) ^ n : ℕ) : K) + (-1 : K) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_one,
    max_eq_right hQn.le]

end Residue

/-! ### Unramified extensions of every degree -/

section Existence

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]

omit [CompleteSpace K] in
variable (K) in
/-- **A local field has an unramified extension of degree divisible by any prescribed number.**
Adjoining the roots of unity of order one less than the corresponding power of the number of
residues is unramified, and those roots of unity persist in the residue field, so the residue field
is at least as large as that power. -/
theorem exists_unramified_dvd_finrank {n : ℕ} (hn : n ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      (∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖) ∧ n ∣ finrank K L := by
  classical
  have hQ2 : 2 ≤ Nat.card (DivisionResidue K K) := Finite.one_lt_card
  have hQpow : 2 ≤ Nat.card (DivisionResidue K K) ^ n :=
    le_trans hQ2 (Nat.le_self_pow hn _)
  set M : ℕ := Nat.card (DivisionResidue K K) ^ n - 1 with hMdef
  have hM0 : M ≠ 0 := by omega
  have hMnorm : ‖((M : ℕ) : K)‖ = 1 := norm_natCast_pow_card_divisionResidue_sub_one K hn
  haveI : NeZero M := ⟨hM0⟩
  haveI : NeZero ((M : ℕ) : K) := ⟨fun h => by
    rw [h, norm_zero] at hMnorm
    exact zero_ne_one hMnorm⟩
  haveI : FiniteDimensional K (CyclotomicField M K) :=
    IsCyclotomicExtension.finiteDimensional (S := ({M} : Set ℕ)) (K := K) (CyclotomicField M K)
  have hur : ∀ z : CyclotomicField M K, z ≠ 0 →
      ∃ c : K, c ≠ 0 ∧ divisionNorm K (CyclotomicField M K) z = ‖c‖ :=
    unramified_of_isCyclotomicExtension K (CyclotomicField M K) hMnorm
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := ({M} : Set ℕ)) K
    (CyclotomicField M K) rfl hM0
  have hdvd : M ∣ Nat.card (DivisionResidue K (CyclotomicField M K)) - 1 :=
    dvd_card_divisionResidue_sub_one_of_isPrimitiveRoot hζ hMnorm
  rw [card_divisionResidue_of_unramified K (CyclotomicField M K) hur, hMdef] at hdvd
  exact ⟨CyclotomicField M K, inferInstance, inferInstance, inferInstance, hur,
    dvd_of_pow_sub_one_dvd_pow_sub_one hQ2 hdvd⟩

end Existence

/-! ### The invariant map is onto -/

section Surjective

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K] {m : ℤ}
  {p e : ℕ}

variable (K) in
/-- **Every rational modulo the integers is the invariant of a Brauer class over a local field.**
The class is a power of the one whose invariant is the reciprocal of the degree of an unramified
extension whose degree the denominator divides. -/
theorem localInvariantHom_surjective (hm : IsUnitValGen K m) :
    Function.Surjective (localInvariantHom K hm) := by
  intro y
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ))
    (Multiplicative.toAdd y)
  rw [QuotientAddGroup.mk'_apply] at hr
  obtain ⟨L, hLfield, hLalg, hLfin, hur, hdvd⟩ :=
    exists_unramified_dvd_finrank K (n := r.den) r.den_nz
  letI : Field L := hLfield
  letI : Algebra K L := hLalg
  haveI : FiniteDimensional K L := hLfin
  haveI : IsGalois K L := isGalois_of_unramified K L hur
  obtain ⟨t, ht⟩ := hdvd
  have hd0 : finrank K L ≠ 0 := Module.finrank_pos.ne'
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at ht
    exact hd0 ht
  obtain ⟨w, hw⟩ := exists_localInvariant_eq hur hm
  refine ⟨(w : BrauerGroup K) ^ (r.num * (t : ℤ)), ?_⟩
  rw [map_zpow, localInvariantHom_apply_of_unramified hm hur w, hw, ← ofAdd_zsmul,
    ← QuotientAddGroup.mk'_apply, ← map_zsmul]
  have htq : ((t : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 ht0
  have hval : (r.num * (t : ℤ)) • (1 / (finrank K L : ℚ)) = r := by
    rw [zsmul_eq_mul, ht]
    push_cast
    rw [mul_one_div, mul_comm (r.num : ℚ) (t : ℚ), mul_comm (r.den : ℚ) (t : ℚ),
      mul_div_mul_left _ _ htq]
    exact Rat.num_div_den r
  rw [hval, QuotientAddGroup.mk'_apply, hr]
  rfl

variable (K) in
/-- **The Brauer group of a local field is the rationals modulo the integers.**  A class is
determined by its invariant, and every rational modulo the integers occurs. -/
noncomputable def localInvariantEquiv (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) :
    BrauerGroup.{0, 0} K ≃* Multiplicative QModZ :=
  MulEquiv.ofBijective (localInvariantHom K hm)
    ⟨localInvariantHom_injective K hres hm, localInvariantHom_surjective K hm⟩

@[simp]
theorem localInvariantEquiv_apply (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (x : BrauerGroup.{0, 0} K) :
    localInvariantEquiv K hres hm x = localInvariantHom K hm x := rfl

end Surjective

end InverseGalois.CFT
