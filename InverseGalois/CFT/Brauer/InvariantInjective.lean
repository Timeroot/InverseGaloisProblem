/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.InvariantMap
import InverseGalois.CFT.Brauer.LocalBrauerOrder

/-!
# The invariant determines the Brauer class

The relative Brauer group of an unramified extension of a local field has the order of the degree,
and the normalised invariant attains the reciprocal of the degree, which is an element of order the
degree in the rationals modulo the integers.  A homomorphism out of a finite group whose image
contains an element of the order of the group is injective, so **the normalised invariant is
injective on the relative Brauer group of an unramified extension.**

Every Brauer class over a local field is split by some finite unramified extension, so the same
argument applies to the whole Brauer group: **a Brauer class over a local field is determined by
its invariant.**

## Main results

* `InverseGalois.CFT.addOrderOf_mk_one_div`: the reciprocal of `n` has order `n` in the rationals
  modulo the integers.
* `InverseGalois.CFT.localInvariant_injective`: **the normalised invariant is injective on the
  relative Brauer group of an unramified extension of a local field.**
* `InverseGalois.CFT.localInvariantHom_injective`: **a Brauer class over a local field is
  determined by its invariant.**

## Tags

Brauer group, local field, unramified extension, invariant map, class field theory
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

/-! ### The order of the reciprocal of `n` -/

/-- **The reciprocal of `n` has order `n` in the rationals modulo the integers**, because the
integers modulo `n` embed into the rationals modulo the integers by sending the class of `k` to
`k / n`. -/
theorem addOrderOf_mk_one_div (n : ℕ) [NeZero n] :
    addOrderOf (QuotientAddGroup.mk (1 / (n : ℚ)) : QModZ) = n := by
  have h : (QuotientAddGroup.mk (1 / (n : ℚ)) : QModZ) = zmodQModZ n ((1 : ℤ) : ZMod n) := by
    rw [zmodQModZ_intCast]
    norm_num
  rw [h, addOrderOf_injective (zmodQModZ n) (zmodQModZ_injective n), Int.cast_one,
    ZMod.addOrderOf_one]

/-! ### A counting criterion for injectivity -/

/-- A homomorphism out of a finite group whose image has order divisible by the order of the group
is injective, because the index of its kernel is both a divisor and a multiple of the order of the
group. -/
theorem injective_of_natCard_dvd_natCard_range {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (h : Nat.card G ∣ Nat.card ↥f.range) : Function.Injective f := by
  have hG : 0 < Nat.card G := Nat.card_pos
  have hidx : f.ker.index = Nat.card ↥f.range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hmul : Nat.card ↥f.ker * f.ker.index = Nat.card G := Subgroup.card_mul_index f.ker
  have hdvd₁ : f.ker.index ∣ Nat.card G := ⟨Nat.card ↥f.ker, by rw [← hmul, Nat.mul_comm]⟩
  have hdvd₂ : Nat.card G ∣ f.ker.index := hidx ▸ h
  have hidx' : f.ker.index = Nat.card G := Nat.dvd_antisymm hdvd₁ hdvd₂
  rw [hidx'] at hmul
  have hker : Nat.card ↥f.ker = 1 :=
    Nat.eq_of_mul_eq_mul_left hG (by rw [Nat.mul_comm, hmul, Nat.mul_one])
  exact (MonoidHom.ker_eq_bot_iff f).1 (Subgroup.eq_bot_of_card_eq _ hker)

/-! ### The invariant of an unramified extension is injective -/

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K] {m : ℤ}
  {p e : ℕ}

section Extension

variable [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **The normalised invariant is injective on the relative Brauer group of an unramified extension
of a local field.**  The relative Brauer group has the order of the degree, and the invariant
attains the reciprocal of the degree, an element of order the degree. -/
theorem localInvariant_injective (hres : HasResidueChar K p e)
    (hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖) (hm : IsUnitValGen K m) :
    Function.Injective (localInvariant K L hur hm) := by
  haveI : IsCyclic (L ≃ₐ[K] L) :=
    ⟨⟨divisionFrobenius K L hur, forall_mem_zpowers_divisionFrobenius K L hur⟩⟩
  haveI : NeZero (finrank K L) := ⟨Module.finrank_pos.ne'⟩
  have hval : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖ := by
    intro z hz
    obtain ⟨c, hc, hcz⟩ := hur z hz
    exact ⟨c, hc, by rw [← divisionNorm_eq_spectralNorm, hcz]⟩
  have hcard : Nat.card ↥(BrauerGroup.relative K L) = finrank K L :=
    card_relative_eq_finrank_of_spectralNorm hres hval
  haveI : Finite ↥(BrauerGroup.relative K L) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
  obtain ⟨y, hy⟩ := exists_localInvariant_eq hur hm
  have hord : orderOf (localInvariant K L hur hm y) = finrank K L := by
    rw [hy]
    exact addOrderOf_mk_one_div (finrank K L)
  refine injective_of_natCard_dvd_natCard_range _ ?_
  rw [hcard, ← hord]
  exact Subgroup.orderOf_dvd_natCard _ ⟨y, rfl⟩

end Extension

/-! ### The invariant determines the Brauer class -/

variable (K) in
/-- **A Brauer class over a local field is determined by its invariant.**  The class is split by a
finite unramified extension, on whose relative Brauer group the invariant is injective. -/
theorem localInvariantHom_injective (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) :
    Function.Injective (localInvariantHom K hm) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, localInvariantHom_apply] at hx
  obtain ⟨F, hF⟩ := exists_unramifiedSubfield_mem_relative K x
  rw [localInvariantMap_eq hm F x hF] at hx
  have h1 : F.invariant hm ⟨x, hF⟩ = F.invariant hm 1 := by rw [hx, map_one]
  have h2 : (⟨x, hF⟩ : ↥(BrauerGroup.relative K ↥F.carrier)) = 1 :=
    localInvariant_injective hres F.unramified hm h1
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)

end InverseGalois.CFT
