/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.H2Surjective
import InverseGalois.CFT.Brauer.InvariantSurjective
import InverseGalois.CFT.Brauer.LocalBrauerOrder

/-!
# The relative Brauer group of a local field is bounded by the degree

The cohomology of a finite group in positive degrees is killed by the order of the group, so the
relative Brauer group of a finite Galois extension consists of classes whose order divides the
degree.  Over a local field the Brauer group is the rationals modulo the integers, and the elements
of that group killed by a number are exactly as many as the number.  So the relative Brauer group
of a finite Galois extension of a local field has at most as many elements as the degree, with no
hypothesis whatsoever on the extension.

For an unramified extension the two counts agree, and the relative Brauer group is therefore
*exactly* the subgroup of classes killed by the degree: over a local field a class killed by `n` is
split by the unramified extension of degree `n`.

## Main definitions

* `InverseGalois.CFT.nsmulTorsionQModZ`: the rationals modulo the integers killed by a number.
* `InverseGalois.CFT.brauerTorsion`: the classes of a Brauer group killed by a number.

## Main results

* `InverseGalois.CFT.natCard_nsmulTorsionQModZ`: **the elements of the rationals modulo the
  integers killed by `n` are `n` in number.**
* `InverseGalois.CFT.natCard_brauerTorsion`: **the classes of the Brauer group of a local field
  killed by `n` are `n` in number.**
* `InverseGalois.CFT.card_relative_le_finrank_local`: **the relative Brauer group of a finite
  Galois extension of a local field has at most as many elements as the degree.**
* `InverseGalois.CFT.relative_eq_brauerTorsion_of_unramified`: **the relative Brauer group of an
  unramified extension of a local field is the subgroup of classes killed by the degree.**

## Tags

Brauer group, relative Brauer group, local field, invariant map, torsion, class field theory
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

/-! ### Powers in a multiplicative type tag -/

/-- A power of an element of a multiplicative type tag is trivial exactly when the corresponding
multiple in the underlying additive group vanishes. -/
theorem pow_eq_one_iff_nsmul_toAdd {A : Type*} [AddGroup A] (x : Multiplicative A) (n : ℕ) :
    x ^ n = 1 ↔ n • Multiplicative.toAdd x = 0 := Iff.rfl

/-! ### The torsion of the rationals modulo the integers -/

/-- The elements of the rationals modulo the integers killed by a given number. -/
def nsmulTorsionQModZ (n : ℕ) : AddSubgroup QModZ where
  carrier := {x | n • x = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [smul_add, hx, hy, add_zero]
  zero_mem' := by simp
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [smul_neg, hx, neg_zero]

theorem mem_nsmulTorsionQModZ {n : ℕ} {x : QModZ} :
    x ∈ nsmulTorsionQModZ n ↔ n • x = 0 := Iff.rfl

/-- **The elements of the rationals modulo the integers killed by `n` are exactly the multiples of
the reciprocal of `n`.** -/
theorem mem_nsmulTorsionQModZ_iff_exists (n : ℕ) [NeZero n] {x : QModZ} :
    x ∈ nsmulTorsionQModZ n ↔ ∃ k : ZMod n, zmodQModZ n k = x := by
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) x
    rw [QuotientAddGroup.mk'_apply] at hq
    subst hq
    rw [mem_nsmulTorsionQModZ] at hx
    have hmul : (QuotientAddGroup.mk ((n : ℚ) * q) : QModZ) = 0 := by
      have h1 : (QuotientAddGroup.mk (n • q) : QModZ)
          = n • (QuotientAddGroup.mk q : QModZ) := by
        rw [← QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk'_apply, map_nsmul]
      rw [nsmul_eq_mul] at h1
      rw [h1, hx]
    obtain ⟨j, hj⟩ := (QModZ.mk_eq_zero_iff _).1 hmul
    have hn : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    refine ⟨(j : ZMod n), ?_⟩
    rw [zmodQModZ_intCast, hj, mul_comm, mul_div_assoc, div_self hn, mul_one]
  · rintro ⟨k, rfl⟩
    rw [mem_nsmulTorsionQModZ, ← map_nsmul]
    have hk : n • k = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hk, map_zero]

/-- The reciprocals of `n` inside the rationals modulo the integers, as an equivalence with the
integers modulo `n`. -/
noncomputable def zmodEquivNsmulTorsionQModZ (n : ℕ) [NeZero n] :
    ZMod n ≃ ↥(nsmulTorsionQModZ n) :=
  Equiv.ofBijective (fun k => ⟨zmodQModZ n k, (mem_nsmulTorsionQModZ_iff_exists n).2 ⟨k, rfl⟩⟩)
    ⟨fun _ _ h => zmodQModZ_injective n (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨k, hk⟩ := (mem_nsmulTorsionQModZ_iff_exists n).1 hx
      exact ⟨k, Subtype.ext hk⟩⟩

instance finite_nsmulTorsionQModZ (n : ℕ) [NeZero n] : Finite ↥(nsmulTorsionQModZ n) :=
  Finite.of_equiv _ (zmodEquivNsmulTorsionQModZ n)

/-- **The elements of the rationals modulo the integers killed by `n` are `n` in number.** -/
theorem natCard_nsmulTorsionQModZ (n : ℕ) [NeZero n] :
    Nat.card ↥(nsmulTorsionQModZ n) = n := by
  rw [← Nat.card_congr (zmodEquivNsmulTorsionQModZ n), Nat.card_eq_fintype_card, ZMod.card]

/-! ### The torsion of a Brauer group -/

/-- The classes of the Brauer group killed by a given number. -/
def brauerTorsion (K : Type) [Field K] (n : ℕ) : Subgroup (BrauerGroup.{0, 0} K) where
  carrier := {x | x ^ n = 1}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [mul_pow, hx, hy, mul_one]
  one_mem' := one_pow n
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [inv_pow, hx, inv_one]

theorem mem_brauerTorsion {K : Type} [Field K] {n : ℕ} {x : BrauerGroup.{0, 0} K} :
    x ∈ brauerTorsion K n ↔ x ^ n = 1 := Iff.rfl

section Relative

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

variable (L) in
/-- The relative Brauer group of a finite Galois extension consists of classes killed by the
degree. -/
theorem relative_le_brauerTorsion :
    BrauerGroup.relative K L ≤ brauerTorsion K (finrank K L) :=
  fun x hx => pow_finrank_eq_one_of_mem_relative (L := L) x hx

end Relative

section Local

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K] {m : ℤ}
  {p e : ℕ}

variable (K) in
/-- The classes of the Brauer group of a local field killed by `n`, in bijection with the elements
of the rationals modulo the integers killed by `n`.  The invariant map is an isomorphism, and it
carries one condition to the other. -/
noncomputable def brauerTorsionEquiv (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (n : ℕ) : ↥(brauerTorsion K n) ≃ ↥(nsmulTorsionQModZ n) := by
  refine Equiv.ofBijective
    (fun y => ⟨Multiplicative.toAdd (localInvariantEquiv K hres hm (y : BrauerGroup K)), ?_⟩)
    ⟨?_, ?_⟩
  · rw [mem_nsmulTorsionQModZ, ← pow_eq_one_iff_nsmul_toAdd, ← map_pow,
      mem_brauerTorsion.1 (Subtype.prop _), map_one]
  · rintro ⟨y, hy⟩ ⟨z, hz⟩ h
    exact Subtype.ext ((localInvariantEquiv K hres hm).injective
      (congrArg Multiplicative.ofAdd (congrArg Subtype.val h)))
  · rintro ⟨x, hx⟩
    refine ⟨⟨(localInvariantEquiv K hres hm).symm (Multiplicative.ofAdd x), ?_⟩, ?_⟩
    · rw [mem_brauerTorsion, ← map_pow,
        (pow_eq_one_iff_nsmul_toAdd (Multiplicative.ofAdd x) n).2
          (mem_nsmulTorsionQModZ.1 hx), map_one]
    · exact Subtype.ext (by simp)

variable (K) in
/-- **The classes of the Brauer group of a local field killed by `n` are `n` in number.**  The
invariant map identifies the Brauer group with the rationals modulo the integers. -/
theorem natCard_brauerTorsion (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) (n : ℕ)
    [NeZero n] : Nat.card ↥(brauerTorsion K n) = n := by
  rw [Nat.card_congr (brauerTorsionEquiv K hres hm n), natCard_nsmulTorsionQModZ]

theorem finite_brauerTorsion (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) (n : ℕ)
    [NeZero n] : Finite ↥(brauerTorsion K n) :=
  Finite.of_equiv _ (brauerTorsionEquiv K hres hm n).symm

/-! ### The bound on a relative Brauer group -/

variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

variable (L) in
/-- The relative Brauer group of a finite Galois extension of a local field is finite. -/
theorem finite_relative_local (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) :
    Finite ↥(BrauerGroup.relative K L) := by
  haveI : NeZero (finrank K L) := ⟨Module.finrank_pos.ne'⟩
  haveI := finite_brauerTorsion hres hm (finrank K L)
  exact Finite.of_injective (Subgroup.inclusion (relative_le_brauerTorsion L))
    (Subgroup.inclusion_injective _)

variable (L) in
/-- **The relative Brauer group of a finite Galois extension of a local field has at most as many
elements as the degree.**  Its classes are killed by the degree, and the classes of the Brauer
group killed by the degree are exactly as many as the degree. -/
theorem card_relative_le_finrank_local (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) :
    Nat.card ↥(BrauerGroup.relative K L) ≤ finrank K L := by
  haveI : NeZero (finrank K L) := ⟨Module.finrank_pos.ne'⟩
  haveI := finite_brauerTorsion hres hm (finrank K L)
  rw [← natCard_brauerTorsion K hres hm (finrank K L)]
  exact Subgroup.card_le_of_le (relative_le_brauerTorsion L)

/-- **The relative Brauer group of an unramified extension of a local field is the subgroup of
classes killed by the degree.**  Both have the order of the degree, and one contains the other. -/
theorem relative_eq_brauerTorsion_of_unramified (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m)
    (hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖) :
    BrauerGroup.relative K L = brauerTorsion K (finrank K L) := by
  haveI : NeZero (finrank K L) := ⟨Module.finrank_pos.ne'⟩
  haveI := finite_brauerTorsion hres hm (finrank K L)
  haveI : IsCyclic (L ≃ₐ[K] L) :=
    ⟨⟨divisionFrobenius K L hur, forall_mem_zpowers_divisionFrobenius K L hur⟩⟩
  have hval : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖ := by
    intro z hz
    obtain ⟨c, hc, hcz⟩ := hur z hz
    exact ⟨c, hc, by rw [← divisionNorm_eq_spectralNorm, hcz]⟩
  have hcard : Nat.card ↥(BrauerGroup.relative K L) = finrank K L :=
    card_relative_eq_finrank_of_spectralNorm hres hval
  refine Subgroup.eq_of_le_of_card_ge (relative_le_brauerTorsion L) ?_
  rw [hcard, natCard_brauerTorsion K hres hm (finrank K L)]

end Local

end InverseGalois.CFT
