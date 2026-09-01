/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicNorm
import InverseGalois.CFT.Brauer.LocalInvariant

/-!
# Changing the generator of a cyclic Galois group

The cyclic algebra `(L / K, σ₀, a)` depends on the choice of a generator `σ₀` of the Galois group,
and so does the invariant of its Brauer class.  Replacing the generator by a power rescales the
invariant, and the rescaling is visible already at the level of the explicit two-cocycle.

The two-cocycle attached to a generator `g` of a cyclic group of order `n` records the carry of the
addition of discrete logarithms.  Passing from `g` to `g ^ t` multiplies every discrete logarithm
by the inverse of `t` modulo `n`, and the difference between the carry of the rescaled logarithms
and the rescaled carry of the original ones is the coboundary of the integer measuring how far the
rescaled logarithm is from a genuine multiple.  So the cocycle of `g ^ t` with coefficient `a ^ t`
is cohomologous to the cocycle of `g` with coefficient `a`, and the Brauer classes agree.

## Main definitions

* `InverseGalois.CFT.dlogShift`: the integer measuring the discrepancy between the discrete
  logarithm to the base a generator and the discrete logarithm to the base a power of it.

## Main results

* `InverseGalois.CFT.isMulCoboundary₂_cyclicCocycle_pow_div`: **the cocycle of a power of a
  generator, with the coefficient raised to that power, is cohomologous to the original cocycle.**
* `InverseGalois.CFT.cyclicBrauerHom_pow_generator`: **the cyclic algebra of a power of a generator
  with the scalar raised to that power has the Brauer class of the original cyclic algebra.**
* `InverseGalois.CFT.brauerInvariant_pow_generator`: **replacing the generator by its `t`-th power
  raises the invariant to the `t`-th power.**
* `InverseGalois.CFT.brauerInvariant_eq_localInvariant_pow`: **the invariant taken with respect to
  a power of the Frobenius automorphism is the corresponding power of the normalised invariant.**

## Tags

Brauer group, cyclic algebra, generator, discrete logarithm, invariant map, class field theory
-/

namespace InverseGalois.CFT

open Module

open groupCohomology

open scoped Valued WithZero

/-! ### The carry of an addition in the integers modulo `n` -/

/-- The value of a sum in the integers modulo `n` is the sum of the values, less the modulus when
the sum of the values reaches it. -/
theorem intCast_val_add {n : ℕ} [NeZero n] (u w : ZMod n) :
    (((u + w).val : ℕ) : ℤ)
      = ((u.val : ℕ) : ℤ) + ((w.val : ℕ) : ℤ)
        - (n : ℤ) * (if u.val + w.val < n then 0 else 1) := by
  rcases Nat.lt_or_ge (u.val + w.val) n with h | h
  · rw [ZMod.val_add_of_lt h, if_pos h]
    push_cast
    ring
  · rw [ZMod.val_add_of_le h, if_neg (Nat.not_lt.mpr h), Nat.cast_sub h]
    push_cast
    ring

/-! ### The two-cocycle of a power of a generator -/

section Cocycle

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M] {g : G}

/-- The discrete logarithm to the base a generator is the discrete logarithm to the base a power of
it, scaled by that power. -/
theorem dlog_eq_mul_dlog_pow (hg : ∀ x : G, x ∈ Subgroup.zpowers g) {t : ℕ}
    (ht : ∀ x : G, x ∈ Subgroup.zpowers (g ^ t)) (σ : G) :
    dlog g σ = (t : ZMod (Nat.card G)) * dlog (g ^ t) σ := by
  letI := neZero_card G
  conv_lhs => rw [← pow_val_dlog ht σ, ← pow_mul]
  rw [dlog_pow hg, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id]

variable (g) in
/-- **The discrepancy between the two discrete logarithms**: the amount, divided by the order of the
group, by which the discrete logarithm to the base `g ^ t`, scaled by `t`, exceeds the discrete
logarithm to the base `g`. -/
noncomputable def dlogShift (t : ℕ) (σ : G) : ℤ :=
  ((t : ℤ) * (((dlog (g ^ t) σ).val : ℕ) : ℤ) - (((dlog g σ).val : ℕ) : ℤ)) / (Nat.card G : ℤ)

/-- The defining property of the discrepancy: it really is the quotient by the order of the
group. -/
theorem card_mul_dlogShift (hg : ∀ x : G, x ∈ Subgroup.zpowers g) {t : ℕ}
    (ht : ∀ x : G, x ∈ Subgroup.zpowers (g ^ t)) (σ : G) :
    (Nat.card G : ℤ) * dlogShift g t σ
      = (t : ℤ) * (((dlog (g ^ t) σ).val : ℕ) : ℤ) - (((dlog g σ).val : ℕ) : ℤ) := by
  letI := neZero_card G
  refine Int.mul_ediv_cancel' ?_
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id,
    dlog_eq_mul_dlog_pow hg ht σ, sub_self]

/-- **The cocycle of a power of a generator, with the coefficient raised to that power, is
cohomologous to the cocycle of the generator.** -/
theorem isMulCoboundary₂_cyclicCocycle_pow_div (hg : ∀ x : G, x ∈ Subgroup.zpowers g) {t : ℕ}
    (ht : ∀ x : G, x ∈ Subgroup.zpowers (g ^ t)) {a : M} (ha : ∀ σ : G, σ • a = a) :
    IsMulCoboundary₂ fun p : G × G =>
      cyclicCocycle (g ^ t) (a ^ t) p / cyclicCocycle g a p := by
  letI := neZero_card G
  have hcard : ((Nat.card G : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne _)
  have hsm : ∀ (σ : G) (k : ℤ), σ • (a ^ k) = a ^ k := fun σ k => by
    rw [← MulDistribMulAction.toMonoidHom_apply, map_zpow,
      MulDistribMulAction.toMonoidHom_apply, ha]
  refine ⟨fun σ => a ^ dlogShift g t σ, fun σ τ => ?_⟩
  have hexp : dlogShift g t τ - dlogShift g t (σ * τ) + dlogShift g t σ
      = (t : ℤ) * (if (dlog (g ^ t) σ).val + (dlog (g ^ t) τ).val < Nat.card G then 0 else 1)
        - (if (dlog g σ).val + (dlog g τ).val < Nat.card G then 0 else 1) := by
    refine mul_left_cancel₀ hcard ?_
    have hX := intCast_val_add (dlog g σ) (dlog g τ)
    have hY := intCast_val_add (dlog (g ^ t) σ) (dlog (g ^ t) τ)
    rw [← dlog_mul hg] at hX
    rw [← dlog_mul ht] at hY
    have hbσ := card_mul_dlogShift hg ht σ
    have hbτ := card_mul_dlogShift hg ht τ
    have hbστ := card_mul_dlogShift hg ht (σ * τ)
    linear_combination hbτ - hbστ + hbσ - (t : ℤ) * hY + hX
  have hz₁ : cyclicCocycle g a (σ, τ)
      = a ^ (if (dlog g σ).val + (dlog g τ).val < Nat.card G then (0 : ℤ) else 1) := by
    rw [cyclicCocycle_apply]
    split_ifs
    · rw [zpow_zero]
    · rw [zpow_one]
  have hz₂ : cyclicCocycle (g ^ t) (a ^ t) (σ, τ)
      = a ^ ((t : ℤ)
          * (if (dlog (g ^ t) σ).val + (dlog (g ^ t) τ).val < Nat.card G then (0 : ℤ) else 1)) := by
    rw [cyclicCocycle_apply]
    split_ifs
    · rw [mul_zero, zpow_zero]
    · rw [mul_one, zpow_natCast]
  show σ • (a ^ dlogShift g t τ) / a ^ dlogShift g t (σ * τ) * a ^ dlogShift g t σ
    = cyclicCocycle (g ^ t) (a ^ t) (σ, τ) / cyclicCocycle g a (σ, τ)
  rw [hsm, hz₁, hz₂]
  simp only [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
  exact congrArg (fun k : ℤ => a ^ k) (by linarith [hexp])

end Cocycle

/-! ### The Brauer class of a cyclic algebra -/

section Galois

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {σ₀ : Gal(L/K)}

omit [IsGalois K L] in
/-- The cyclic algebra cocycle of a power of a generator, with the scalar raised to that power, is
cohomologous to the cyclic algebra cocycle of the generator. -/
theorem isMulCoboundary₂_cyclicUnitCocycle_pow_div
    (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) {t : ℕ}
    (ht : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers (σ₀ ^ t)) (a : Kˣ) :
    IsMulCoboundary₂ fun p : Gal(L/K) × Gal(L/K) =>
      cyclicUnitCocycle (σ₀ ^ t) (a ^ t) p / cyclicUnitCocycle σ₀ a p := by
  have h := isMulCoboundary₂_cyclicCocycle_pow_div hσ₀ ht
    (a := Units.map (algebraMap K L).toMonoidHom a) (smul_unitsMap_algebraMap a)
  simpa only [cyclicUnitCocycle, map_pow] using h

/-- **The cyclic algebra of a power of a generator, with the scalar raised to that power, has the
Brauer class of the original cyclic algebra.** -/
theorem cyclicBrauerHom_pow_generator (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) {t : ℕ}
    (ht : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers (σ₀ ^ t)) (a : Kˣ) :
    cyclicBrauerHom ht (a ^ t) = cyclicBrauerHom hσ₀ a := by
  rw [cyclicBrauerHom_apply, cyclicBrauerHom_apply]
  exact (CrossedProduct.mk_csa_eq_mk_csa_iff _ _).mpr
    (isMulCoboundary₂_cyclicUnitCocycle_pow_div hσ₀ ht a)

end Galois

/-! ### The invariant -/

section Invariant

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] {σ₀ : Gal(L/K)} {m : ℤ}

/-- **Replacing the generator by its `t`-th power raises the invariant to the `t`-th power.** -/
theorem brauerInvariant_pow_generator (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) {t : ℕ}
    (ht : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers (σ₀ ^ t)) (hur : HasUnramifiedNormValues K L)
    (hm : IsUnitValGen K m) (y : ↥(BrauerGroup.relative K L)) :
    brauerInvariant ht hur hm y = brauerInvariant hσ₀ hur hm y ^ t := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨a, rfl⟩ := exists_cyclicBrauerHom_eq hσ₀ y hy
  have hsub : (⟨cyclicBrauerHom hσ₀ a, hy⟩ : ↥(BrauerGroup.relative K L))
      = ⟨cyclicBrauerHom ht (a ^ t), cyclicBrauerHom_mem_relative ht (a ^ t)⟩ :=
    Subtype.ext (cyclicBrauerHom_pow_generator hσ₀ ht a).symm
  have hL := congrArg (brauerInvariant ht hur hm) hsub
  rw [brauerInvariant_apply_cyclicBrauerHom ht hur hm (a ^ t)] at hL
  rw [hL, brauerInvariant_apply_cyclicBrauerHom hσ₀ hur hm a, map_pow]

end Invariant

/-! ### The invariant against a power of the Frobenius automorphism -/

section Frobenius

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K] {m : ℤ}
variable [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {σ₀ : Gal(L/K)}

/-- **The invariant taken with respect to a power of the Frobenius automorphism is the
corresponding power of the normalised invariant.** -/
theorem brauerInvariant_eq_localInvariant_pow
    (hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖) (hm : IsUnitValGen K m)
    (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) {t : ℕ}
    (hσ : σ₀ = divisionFrobenius K L hur ^ t) (y : ↥(BrauerGroup.relative K L)) :
    brauerInvariant hσ₀ (hasUnramifiedNormValues_of_divisionNorm hur) hm y
      = localInvariant K L hur hm y ^ t := by
  have ht : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers (divisionFrobenius K L hur ^ t) := by
    rw [← hσ]
    exact hσ₀
  refine (brauerInvariant_congr_apply hσ hσ₀ ht _ hm y).trans ?_
  exact brauerInvariant_pow_generator (forall_mem_zpowers_divisionFrobenius K L hur) ht
    (hasUnramifiedNormValues_of_divisionNorm hur) hm y

end Frobenius

end InverseGalois.CFT
