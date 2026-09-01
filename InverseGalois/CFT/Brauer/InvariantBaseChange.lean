/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.AdicUnramified
import InverseGalois.CFT.Brauer.InertiaSubfield
import InverseGalois.CFT.Brauer.InvariantBaseUnramified
import InverseGalois.CFT.Brauer.InvariantRamified
import InverseGalois.CFT.Brauer.RamificationIdentity

/-!
# Functoriality of the invariant map of a local field

Let `M / K` be an arbitrary finite extension of nonarchimedean local fields whose absolute value
extends that of `K`.  The invariant of a Brauer class of `K`, computed over `M`, is `[M : K]` times
the invariant computed over `K`:

`inv_M (res_M x) = [M : K] · inv_K x`.

The proof factors the extension through its maximal unramified subextension `S`.  Over the
unramified part the two invariants differ by the degree `[S : K]`, and over the totally ramified
part they differ by the ratio of the two normalised valuations, which the fundamental identity
identifies with the degree `[M : S]` because the residue field does not grow there.

## Main results

* `InverseGalois.CFT.unitVal_of_isNormUniformizer`: the valuation of a uniformizer generates the
  value group.
* `InverseGalois.CFT.exists_unitValDiv_ratio`: the normalised valuation of the extension restricts
  to a multiple of the normalised valuation of the base field.
* `InverseGalois.CFT.localInvariantHom_baseChange`: **the invariant of a Brauer class is multiplied
  by the degree under base change to a finite extension of local fields.**

## Tags

Brauer group, local field, invariant map, base change, ramification, class field theory
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

attribute [local instance] residueBaseField residueBaseAlgebra

/-! ### Reading the valuation off the absolute value -/

section Norm

variable {A : Type} [Field A] [Valued A ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation A ℤᵐ⁰)] {m : ℤ}

/-- An element has absolute value one exactly when it has valuation one. -/
theorem norm_eq_one_iff_valued_eq_one {x : A} : ‖x‖ = 1 ↔ (Valued.v x : ℤᵐ⁰) = 1 := by
  rw [le_antisymm_iff, le_antisymm_iff, Valued.toNormedField.norm_le_one_iff,
    Valued.toNormedField.one_le_norm_iff]

/-- A unit has valuation zero exactly when it has absolute value one. -/
theorem unitVal_eq_zero_iff (u : Aˣ) : unitVal (Additive.ofMul u) = 0 ↔ ‖(u : A)‖ = 1 := by
  rw [norm_eq_one_iff_valued_eq_one]
  exact ⟨fun h => mem_ker_unitVal.1 (AddMonoidHom.mem_ker.2 h),
    fun h => AddMonoidHom.mem_ker.1 (mem_ker_unitVal.2 h)⟩

/-- A unit has negative valuation exactly when it has absolute value less than one. -/
theorem unitVal_lt_zero_iff (u : Aˣ) : unitVal (Additive.ofMul u) < 0 ↔ ‖(u : A)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, valued_eq_exp_unitVal u, ← WithZero.exp_zero,
    WithZero.exp_lt_exp]

/-- A unit has positive valuation exactly when it has absolute value greater than one. -/
theorem zero_lt_unitVal_iff (u : Aˣ) : 0 < unitVal (Additive.ofMul u) ↔ 1 < ‖(u : A)‖ := by
  rw [Valued.toNormedField.one_lt_norm_iff, valued_eq_exp_unitVal u, ← WithZero.exp_zero,
    WithZero.exp_lt_exp]

omit [Valued A ℤᵐ⁰] [Valuation.RankOne (Valued.v : Valuation A ℤᵐ⁰)] in
/-- An additive homomorphism out of the units, evaluated on a unit divided by a power of another
unit. -/
theorem addHom_ofMul_mul_zpow (φ : Additive Aˣ →+ ℤ) (a b : Aˣ) (k : ℤ) :
    φ (Additive.ofMul (a * b ^ (-k))) = φ (Additive.ofMul a) - k * φ (Additive.ofMul b) := by
  rw [ofMul_mul, ofMul_zpow, map_add, map_zsmul]
  simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_id]
  ring

/-- **The valuation of a uniformizer is the generator of the value group**, up to sign: it is
negative, it is a multiple of the generator, and no unit valuation lies strictly between it and
zero. -/
theorem unitVal_of_isNormUniformizer (hm : IsUnitValGen A m) {π : A}
    (hπ : IsNormUniformizer π) :
    unitVal (Additive.ofMul (Units.mk0 π hπ.ne_zero)) = -|m| := by
  have hmpos : 0 < |m| := abs_pos.2 hm.ne_zero
  have hvπ : (Valued.v ((Units.mk0 π hπ.ne_zero : Aˣ) : A) : ℤᵐ⁰)
      = WithZero.exp (unitVal (Additive.ofMul (Units.mk0 π hπ.ne_zero))) :=
    valued_eq_exp_unitVal _
  -- the valuation of a uniformizer is negative
  have hneg : unitVal (Additive.ofMul (Units.mk0 π hπ.ne_zero)) < 0 := by
    have h1 : (Valued.v ((Units.mk0 π hπ.ne_zero : Aˣ) : A) : ℤᵐ⁰) < 1 :=
      Valued.toNormedField.norm_lt_one_iff.1 hπ.norm_lt_one
    rw [hvπ, ← WithZero.exp_zero] at h1
    exact WithZero.exp_lt_exp.1 h1
  -- a unit realising minus the absolute value of the generator
  obtain ⟨y, hy⟩ : ∃ y : Additive Aˣ, unitVal y = -|m| := by
    obtain ⟨z, hz⟩ := hm.exists_eq
    rcases abs_choice m with h | h
    · exact ⟨-z, by rw [map_neg, hz, h]⟩
    · exact ⟨z, by rw [hz, h, neg_neg]⟩
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := hm.dvd (Additive.ofMul (Units.mk0 π hπ.ne_zero))
    have habs : |m| ≤ |unitVal (Additive.ofMul (Units.mk0 π hπ.ne_zero))| :=
      Int.le_of_dvd (abs_pos.2 hneg.ne) ((abs_dvd _ _).2 ((dvd_abs _ _).2 ⟨k, hk⟩))
    rw [abs_of_neg hneg] at habs
    omega
  · have hyv : (Valued.v ((Additive.toMul y : Aˣ) : A) : ℤᵐ⁰) = WithZero.exp (-|m|) := by
      rw [valued_eq_exp_unitVal]
      exact congrArg WithZero.exp hy
    have hylt : ‖((Additive.toMul y : Aˣ) : A)‖ < 1 := by
      refine Valued.toNormedField.norm_lt_one_iff.2 ?_
      rw [hyv, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.2 (by omega)
    have hle : (Valued.v ((Additive.toMul y : Aˣ) : A) : ℤᵐ⁰)
        ≤ Valued.v ((Units.mk0 π hπ.ne_zero : Aˣ) : A) :=
      Valued.toNormedField.norm_le_iff.1 (hπ.le_norm _ hylt)
    rw [hyv, hvπ] at hle
    exact WithZero.exp_le_exp.1 hle

end Norm

/-! ### A uniformizer of an extension which is a field -/

section Division

variable {K L : Type} [NormedField K] [NormedField L] [Algebra K L]

/-- A uniformizer of an extension which is again a field is a uniformizer for its absolute
value. -/
theorem isNormUniformizer_of_isDivisionUniformizer (hnl : ∀ y : L, ‖y‖ = divisionNorm K L y)
    {ϖ : L} (hϖ : IsDivisionUniformizer K L ϖ) : IsNormUniformizer ϖ where
  ne_zero := hϖ.ne_zero
  norm_lt_one := by rw [hnl]; exact hϖ.norm_lt_one
  le_norm c hc := by
    rw [hnl] at hc ⊢
    rw [hnl]
    exact hϖ.le_norm c hc

end Division

/-! ### The ratio of the two normalised valuations -/

section Ratio

variable {K M : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)]
variable [Field M] [Valued M ℤᵐ⁰] [Valuation.RankOne (Valued.v : Valuation M ℤᵐ⁰)]
variable [Algebra K M] {mK mM : ℤ}

/-- **The normalised valuation of an extension restricts to a multiple of the normalised valuation
of the base field.**  The absolute values agree, so a unit of absolute value one downstairs has
absolute value one upstairs, and the two normalised valuations therefore differ by the factor by
which the generator of the value group grows.  That factor is not negative as soon as the two
generators are chosen with the same sign. -/
theorem exists_unitValDiv_ratio (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (hmK : IsUnitValGen K mK) (hmM : IsUnitValGen M mM) (hsign : 0 < mK * mM) :
    ∃ r : ℕ, ∀ a : Kˣ,
      unitValDiv hmM (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a))
        = (r : ℤ) * unitValDiv hmK (Additive.ofMul a) := by
  have hnf : ∀ a : Kˣ,
      ‖(((Units.map (algebraMap K M).toMonoidHom a : Mˣ)) : M)‖ = ‖((a : K))‖ := by
    intro a
    rw [Units.coe_map]
    exact hnorm _
  have hmapz : ∀ (a b : Kˣ) (k : ℤ),
      Units.map (algebraMap K M).toMonoidHom (a * b ^ (-k))
        = Units.map (algebraMap K M).toMonoidHom a
          * (Units.map (algebraMap K M).toMonoidHom b) ^ (-k) := by
    intro a b k
    rw [map_mul, map_zpow]
  -- a unit of the base field whose normalised valuation is one
  obtain ⟨a₀, ha₀⟩ : ∃ a : Kˣ, unitValDiv hmK (Additive.ofMul a) = 1 := by
    obtain ⟨y, hy⟩ := unitValDiv_surjective hmK 1
    exact ⟨Additive.toMul y, hy⟩
  obtain ⟨r₀, hr₀⟩ : ∃ z : ℤ,
      unitValDiv hmM (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a₀)) = z := ⟨_, rfl⟩
  -- the two normalised valuations are proportional
  have hkey : ∀ a : Kˣ,
      unitValDiv hmM (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a))
        = r₀ * unitValDiv hmK (Additive.ofMul a) := by
    intro a
    obtain ⟨k, hk⟩ : ∃ k : ℤ, unitValDiv hmK (Additive.ofMul a) = k := ⟨_, rfl⟩
    have hzero : unitValDiv hmK (Additive.ofMul (a * a₀ ^ (-k))) = 0 := by
      rw [addHom_ofMul_mul_zpow, hk, ha₀]
      ring
    have hK1 : unitVal (Additive.ofMul (a * a₀ ^ (-k))) = 0 := by
      rw [unitVal_eq_mul_unitValDiv hmK, hzero, mul_zero]
    have hM1 : unitVal (Additive.ofMul
        (Units.map (algebraMap K M).toMonoidHom (a * a₀ ^ (-k)))) = 0 := by
      rw [unitVal_eq_zero_iff, hnf]
      exact (unitVal_eq_zero_iff _).1 hK1
    have hM2 : unitValDiv hmM (Additive.ofMul
        (Units.map (algebraMap K M).toMonoidHom (a * a₀ ^ (-k)))) = 0 := by
      rw [unitValDiv_apply, hM1, Int.zero_ediv]
    rw [hmapz, addHom_ofMul_mul_zpow, hr₀] at hM2
    rw [hk]
    linear_combination hM2
  -- the ratio is not negative
  have hnn : 0 ≤ r₀ := by
    have hK : unitVal (Additive.ofMul a₀) = mK := by
      rw [unitVal_eq_mul_unitValDiv hmK, ha₀, mul_one]
    have hM : unitVal (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a₀)) = mM * r₀ := by
      rw [unitVal_eq_mul_unitValDiv hmM, hr₀]
    rcases lt_trichotomy mK 0 with h | h | h
    · have hMneg : mM < 0 := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_nonneg (neg_nonneg.2 h.le) hc]
      have h1 : ‖((a₀ : K))‖ < 1 := by
        rw [← unitVal_lt_zero_iff, hK]
        exact h
      have h2 : unitVal (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a₀)) < 0 := by
        rw [unitVal_lt_zero_iff, hnf]
        exact h1
      rw [hM] at h2
      nlinarith
    · exact absurd h hmK.ne_zero
    · have hMpos : 0 < mM := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_nonneg h.le (neg_nonneg.2 hc)]
      have h1 : 1 < ‖((a₀ : K))‖ := by
        rw [← zero_lt_unitVal_iff, hK]
        exact h
      have h2 : 0 < unitVal (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a₀)) := by
        rw [zero_lt_unitVal_iff, hnf]
        exact h1
      rw [hM] at h2
      nlinarith
  refine ⟨r₀.toNat, fun a => ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  exact hkey a

end Ratio

/-! ### The invariant map under an arbitrary base change -/

section BaseChange

variable {K M : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
variable [Field M] [Valued M ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation M ℤᵐ⁰)] [CompleteSpace M] [ProperSpace M]
variable [Algebra K M] [FiniteDimensional K M] {mK mM : ℤ}

/-- **The invariant of a Brauer class is multiplied by the degree under base change to a finite
extension of local fields.**  The extension is factored through its maximal unramified
subextension; the unramified part multiplies the invariant by its degree, the remaining part
multiplies it by the ratio of the two normalised valuations, and the fundamental identity says that
this ratio is the degree of the remaining part because the residue field does not grow there. -/
theorem localInvariantHom_baseChange_of_ratio (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (hmK : IsUnitValGen K mK) (hmM : IsUnitValGen M mM) {r : ℕ}
    (hval : ∀ a : Kˣ,
      unitValDiv hmM (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a))
        = (r : ℤ) * unitValDiv hmK (Additive.ofMul a))
    (x : BrauerGroup.{0, 0} K) :
    localInvariantHom M hmM (BrauerGroup.baseChangeHom M x)
      = localInvariantHom K hmK x ^ finrank K M := by
  obtain ⟨S, fS, aKS, aSM, tKSM, dKS, dSM, vS, rkS, cS, pS, hnormKS, hnormSM, hvSM, hurS, hcard⟩ :=
    exists_maximalUnramified_subextension K M hnorm
  -- a unit of the base field whose normalised valuation is one
  obtain ⟨a₀, ha₀⟩ : ∃ a : Kˣ, unitValDiv hmK (Additive.ofMul a) = 1 := by
    obtain ⟨y, hy⟩ := unitValDiv_surjective hmK 1
    exact ⟨Additive.toMul y, hy⟩
  -- the ratio of the two normalised valuations is not zero
  have hr0 : r ≠ 0 := by
    intro h0
    have h1 : unitVal (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a₀)) = 0 := by
      rw [unitVal_eq_mul_unitValDiv hmM, hval a₀, h0]
      simp
    rw [unitVal_eq_zero_iff, Units.coe_map] at h1
    have h2 : ‖((a₀ : K))‖ = 1 := by rw [← hnorm]; exact h1
    have h3 : unitVal (Additive.ofMul a₀) = 0 := (unitVal_eq_zero_iff a₀).2 h2
    rw [unitValDiv_apply, h3, Int.zero_ediv] at ha₀
    exact one_ne_zero ha₀.symm
  have hSne : (mM * (r : ℤ)) ≠ 0 := mul_ne_zero hmM.ne_zero (Int.natCast_ne_zero.2 hr0)
  -- the valuation of the intermediate field is the restriction of the valuation upstairs
  have hunitS : ∀ b : Sˣ, unitVal (Additive.ofMul (Units.map (algebraMap S M).toMonoidHom b))
      = unitVal (Additive.ofMul b) := by
    intro b
    rw [unitVal_apply, unitVal_apply, Units.coe_map]
    exact congrArg WithZero.log (hvSM (b : S))
  have hmap : ∀ a : Kˣ, Units.map (algebraMap S M).toMonoidHom
      (Units.map (algebraMap K S).toMonoidHom a) = Units.map (algebraMap K M).toMonoidHom a := by
    intro a
    refine Units.ext ?_
    show algebraMap S M (algebraMap K S (a : K)) = algebraMap K M (a : K)
    rw [← IsScalarTower.algebraMap_apply]
  have hunitKS : ∀ a : Kˣ, unitVal (Additive.ofMul (Units.map (algebraMap K S).toMonoidHom a))
      = mM * (r : ℤ) * unitValDiv hmK (Additive.ofMul a) := by
    intro a
    rw [← hunitS, hmap, unitVal_eq_mul_unitValDiv hmM, hval a, ← mul_assoc]
  -- the value group of the intermediate field
  have hmS : IsUnitValGen S (mM * (r : ℤ)) := by
    refine ⟨hSne, ?_, ?_⟩
    · intro b
      obtain ⟨c, hc0, hcn⟩ := hurS ((Additive.toMul b : Sˣ) : S) (Additive.toMul b).ne_zero
      have h1 : ‖(((Additive.toMul b : Sˣ) : S))‖ = ‖algebraMap K S c‖ := by
        rw [norm_eq_divisionNorm hnormKS, hcn, hnormKS]
      have hb : unitVal b = WithZero.log (Valued.v (((Additive.toMul b : Sˣ) : S))) :=
        unitVal_apply (Additive.toMul b)
      have h2 : unitVal b
          = unitVal (Additive.ofMul (Units.map (algebraMap K S).toMonoidHom
              (Units.mk0 c hc0))) := by
        rw [hb, unitVal_apply, Units.coe_map]
        exact congrArg WithZero.log (valued_eq_of_norm_eq h1)
      rw [h2, hunitKS]
      exact ⟨_, rfl⟩
    · exact ⟨Additive.ofMul (Units.map (algebraMap K S).toMonoidHom a₀), by
        rw [hunitKS, ha₀, mul_one]⟩
  have hvalKS : ∀ a : Kˣ,
      unitValDiv hmS (Additive.ofMul (Units.map (algebraMap K S).toMonoidHom a))
        = unitValDiv hmK (Additive.ofMul a) := by
    intro a
    rw [unitValDiv_apply, hunitKS, Int.mul_ediv_cancel_left _ hSne]
  have hvalSM : ∀ b : Sˣ,
      unitValDiv hmM (Additive.ofMul (Units.map (algebraMap S M).toMonoidHom b))
        = (r : ℤ) * unitValDiv hmS (Additive.ofMul b) := by
    intro b
    obtain ⟨k, hk⟩ := hmS.dvd (Additive.ofMul b)
    rw [unitValDiv_apply, unitValDiv_apply, hunitS, hk, Int.mul_ediv_cancel_left _ hSne, mul_assoc,
      Int.mul_ediv_cancel_left _ hmM.ne_zero]
  -- the ratio of the two normalised valuations is the degree of the ramified part
  have hre : r = finrank S M := by
    obtain ⟨π, hπ⟩ := exists_isNormUniformizer S
    obtain ⟨ϖ, hϖ⟩ := exists_isDivisionUniformizer_of_field (K := S) (L := M) hπ
    obtain ⟨e, he, hee⟩ := IsDivisionUniformizer.exists_pow_eq_norm S M hϖ hπ
    have hfund := ramification_mul_finrank_divisionResidue S M hπ hϖ he hee
    have hd1 : finrank (DivisionResidue S S) (DivisionResidue S M) = 1 := by
      have hpow : Nat.card (DivisionResidue S M)
          = Nat.card (DivisionResidue S S)
            ^ finrank (DivisionResidue S S) (DivisionResidue S M) := Module.natCard_eq_pow_finrank
      have h2 : 2 ≤ Nat.card (DivisionResidue S S) := Finite.one_lt_card
      rw [hcard] at hpow
      have h3 : Nat.card (DivisionResidue S S) ^ 1
          = Nat.card (DivisionResidue S S)
            ^ finrank (DivisionResidue S S) (DivisionResidue S M) := by
        rw [pow_one]
        exact hpow
      exact (Nat.pow_right_injective h2 h3).symm
    rw [hd1, mul_one] at hfund
    have hϖ' : IsNormUniformizer ϖ :=
      isNormUniformizer_of_isDivisionUniformizer (norm_eq_divisionNorm hnormSM) hϖ
    have hnormpow : ‖ϖ ^ e‖ = ‖algebraMap S M π‖ := by
      rw [norm_pow, norm_eq_divisionNorm hnormSM ϖ, hee, hnormSM]
    have hstep : (e : ℤ) * unitVal (Additive.ofMul (Units.mk0 ϖ hϖ'.ne_zero))
        = unitVal (Additive.ofMul (Units.mk0 π hπ.ne_zero)) := by
      have h1 : unitVal (Additive.ofMul ((Units.mk0 ϖ hϖ'.ne_zero) ^ e))
          = unitVal (Additive.ofMul (Units.map (algebraMap S M).toMonoidHom
              (Units.mk0 π hπ.ne_zero))) := by
        rw [unitVal_apply, unitVal_apply, Units.val_pow_eq_pow_val, Units.coe_map]
        exact congrArg WithZero.log (valued_eq_of_norm_eq hnormpow)
      rw [ofMul_pow, map_nsmul, nsmul_eq_mul, hunitS] at h1
      exact h1
    rw [unitVal_of_isNormUniformizer hmM hϖ', unitVal_of_isNormUniformizer hmS hπ,
      abs_mul, Nat.abs_cast] at hstep
    have hmMpos : 0 < |mM| := abs_pos.2 hmM.ne_zero
    have h4 : |mM| * (e : ℤ) = |mM| * (r : ℤ) := by linear_combination -hstep
    have h5 : (e : ℤ) = (r : ℤ) := mul_left_cancel₀ hmMpos.ne' h4
    rw [← hfund, ← Nat.cast_inj (R := ℤ), h5]
  have hrank : finrank K S * r = finrank K M := by
    rw [hre]
    exact Module.finrank_mul_finrank K S M
  -- the two halves of the factorisation
  have hD := localInvariantHom_baseChange_of_unramified (K := K) (M := S) hnormKS hurS hmK hmS
    hvalKS x
  have hres : Nat.card (DivisionResidue M M) = Nat.card (DivisionResidue S S) := by
    rw [natCard_divisionResidue_self (K := S) (M := M) hnormSM, hcard]
  have hC := localInvariantHom_baseChange_of_residue_eq (K := S) (M := M) hnormSM hres hmS hmM
    hvalSM (BrauerGroup.baseChangeHom S x)
  have htrans : BrauerGroup.baseChangeHom M (BrauerGroup.baseChangeHom S x)
      = BrauerGroup.baseChangeHom M x := by
    rw [← MonoidHom.comp_apply, BrauerGroup.baseChangeHom_comp K S M]
  rw [htrans] at hC
  rw [hC, hD, ← pow_mul, hrank]

/-- **The invariant of a Brauer class is multiplied by the degree under base change to a finite
extension of local fields.**  The two normalised valuations are proportional, and once the two
generators of the value groups are chosen with the same sign the factor is a natural number, so the
factorisation through the maximal unramified subextension applies. -/
theorem localInvariantHom_baseChange (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (hmK : IsUnitValGen K mK) (hmM : IsUnitValGen M mM) (hsign : 0 < mK * mM)
    (x : BrauerGroup.{0, 0} K) :
    localInvariantHom M hmM (BrauerGroup.baseChangeHom M x)
      = localInvariantHom K hmK x ^ finrank K M := by
  obtain ⟨r, hr⟩ := exists_unitValDiv_ratio hnorm hmK hmM hsign
  exact localInvariantHom_baseChange_of_ratio hnorm hmK hmM hr x

end BaseChange

end InverseGalois.CFT
