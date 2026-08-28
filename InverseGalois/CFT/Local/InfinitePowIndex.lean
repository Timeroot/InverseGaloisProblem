/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RealPlace
import InverseGalois.CFT.Local.ComplexHerbrand

/-!
# The index of the `n`-th powers in the units of the completion at an infinite place

The completion of a number field at an infinite place is the reals or the complexes.  Every complex
unit is an `n`-th power, while the `n`-th powers among the real units are the positive ones when `n`
is even and everything when `n` is odd; correspondingly the `n`-th roots of unity number `n` in the
complexes and two or one in the reals.

Multiplying out, the archimedean local index obeys the same formula as the one at a finite place:
the index of the `n`-th powers in the units, times the normalised absolute value of `n`, is `n`
times the number of `n`-th roots of unity.

## Main results

* `InverseGalois.CFT.index_range_powMonoidHom_units_complex`: every complex unit is an `n`-th power.
* `InverseGalois.CFT.index_range_powMonoidHom_units_real`: **the index of the `n`-th powers in the
  real units** is two for `n` even and one for `n` odd.
* `InverseGalois.CFT.card_rootsOfUnity_real`: the number of real `n`-th roots of unity.
* `InverseGalois.CFT.index_range_powMonoidHom_units_infinitePlace`: **the local index formula at an
  infinite place**, the index of the `n`-th powers times `n` raised to the multiplicity of the place
  being `n` times the number of `n`-th roots of unity.

## Tags

infinite place, local index, roots of unity, real place, complex place
-/

namespace InverseGalois.CFT

open NumberField

/-! ### Transporting the index and the roots of unity along an isomorphism -/

section Transport

variable {A B : Type*} [Field A] [Field B]

/-- The index of the `n`-th powers in the units is invariant under an isomorphism of fields. -/
theorem index_range_powMonoidHom_units_congr (e : A ≃+* B) (n : ℕ) :
    (powMonoidHom n : Aˣ →* Aˣ).range.index = (powMonoidHom n : Bˣ →* Bˣ).range.index := by
  have hmap : Subgroup.map (Units.mapEquiv e.toMulEquiv : Aˣ →* Bˣ)
      (powMonoidHom n : Aˣ →* Aˣ).range = (powMonoidHom n : Bˣ →* Bˣ).range := by
    ext y
    simp only [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨Units.mapEquiv e.toMulEquiv a, by simp [powMonoidHom]⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := (Units.mapEquiv e.toMulEquiv).surjective b
      exact ⟨a ^ n, ⟨a, rfl⟩, by simp [powMonoidHom]⟩
  rw [← hmap, Subgroup.index_map_equiv _ (Units.mapEquiv e.toMulEquiv)]

/-- The number of `n`-th roots of unity is invariant under an isomorphism of fields. -/
theorem card_rootsOfUnity_congr (e : A ≃+* B) (n : ℕ) :
    Nat.card ↥(rootsOfUnity n A) = Nat.card ↥(rootsOfUnity n B) :=
  Nat.card_congr (MulEquiv.restrictRootsOfUnity e.toMulEquiv n).toEquiv

end Transport

/-! ### The complex units -/

/-- **Every complex unit is an `n`-th power.**  The complexes are algebraically closed. -/
theorem range_powMonoidHom_units_complex {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y : ℂ) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hz, zero_pow hn])
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [show ((powMonoidHom n (Units.mk0 z hz0) : ℂˣ) : ℂ)
    = z ^ n from rfl, hz])⟩

/-- **Every complex unit is an `n`-th power**, in the form of an index. -/
theorem index_range_powMonoidHom_units_complex {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range.index = 1 := by
  rw [range_powMonoidHom_units_complex hn, Subgroup.index_top]

/-- The number of complex `n`-th roots of unity is `n`. -/
theorem card_rootsOfUnity_complex {n : ℕ} (hn : n ≠ 0) :
    Nat.card ↥(rootsOfUnity n ℂ) = n := by
  haveI : NeZero n := ⟨hn⟩
  rw [Nat.card_eq_fintype_card, Complex.card_rootsOfUnity n]

/-! ### The real units -/

/-- Every positive real unit is the `n`-th power of a positive real unit. -/
theorem exists_pow_eq_of_pos {n : ℕ} (hn : n ≠ 0) {y : ℝˣ} (hy : 0 < (y : ℝ)) :
    ∃ u : ℝˣ, u ^ n = y := by
  have hr : (0 : ℝ) < (y : ℝ) ^ ((n : ℝ)⁻¹) := Real.rpow_pos_of_pos hy _
  refine ⟨Units.mk0 _ hr.ne', Units.ext ?_⟩
  rw [show ((Units.mk0 _ hr.ne' ^ n : ℝˣ) : ℝ) = ((y : ℝ) ^ ((n : ℝ)⁻¹)) ^ n from rfl]
  exact Real.rpow_inv_natCast_pow hy.le hn

/-- **The `n`-th powers among the real units are the positive ones when `n` is even.** -/
theorem range_powMonoidHom_units_real_of_even {n : ℕ} (hn : n ≠ 0) (hev : Even n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range = normSubgroup ℝ ℂ := by
  ext y
  rw [MonoidHom.mem_range, mem_normSubgroup_real_complex_iff]
  constructor
  · rintro ⟨x, rfl⟩
    rw [show ((powMonoidHom n x : ℝˣ) : ℝ) = (x : ℝ) ^ n from rfl]
    exact hev.pow_pos x.ne_zero
  · intro hy
    exact exists_pow_eq_of_pos hn hy

/-- **Every real unit is an `n`-th power when `n` is odd.** -/
theorem range_powMonoidHom_units_real_of_odd {n : ℕ} (hod : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  rcases lt_or_gt_of_ne y.ne_zero with hy | hy
  · obtain ⟨u, hu⟩ := exists_pow_eq_of_pos hod.pos.ne' (y := -y) (by simpa using hy)
    refine ⟨-u, ?_⟩
    rw [show (powMonoidHom n (-u) : ℝˣ) = (-u) ^ n from rfl, hod.neg_pow, hu, neg_neg]
  · exact ⟨_, (exists_pow_eq_of_pos hod.pos.ne' hy).choose_spec⟩

/-- **The index of the `n`-th powers in the real units** is two for `n` even and one for `n`
odd. -/
theorem index_range_powMonoidHom_units_real {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = if Even n then 2 else 1 := by
  rcases Nat.even_or_odd n with hev | hod
  · rw [if_pos hev, range_powMonoidHom_units_real_of_even hn hev,
      index_normSubgroup_real_complex]
  · rw [if_neg (Nat.not_even_iff_odd.mpr hod), range_powMonoidHom_units_real_of_odd hod,
      Subgroup.index_top]

/-- A real unit whose `n`-th power is one is plus or minus one. -/
theorem eq_one_or_neg_one_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) {u : ℝˣ} (hu : u ^ n = 1) :
    u = 1 ∨ u = -1 := by
  have h : (u : ℝ) ^ n = 1 := by
    rw [show ((u : ℝ)) ^ n = ((u ^ n : ℝˣ) : ℝ) from rfl, hu, Units.val_one]
  rcases (pow_eq_one_iff_of_ne_zero hn).mp h with h1 | ⟨h1, -⟩
  · exact Or.inl (Units.ext (by rw [h1, Units.val_one]))
  · exact Or.inr (Units.ext (by rw [h1]; norm_num))

/-- Minus one is not one, among the real units. -/
theorem neg_one_ne_one_real : (-1 : ℝˣ) ≠ 1 := fun h => by
  have := congrArg Units.val h
  norm_num at this

/-- The number of real `n`-th roots of unity is two for `n` even and one for `n` odd. -/
theorem card_rootsOfUnity_real {n : ℕ} (hn : n ≠ 0) :
    Nat.card ↥(rootsOfUnity n ℝ) = if Even n then 2 else 1 := by
  rcases Nat.even_or_odd n with hev | hod
  · rw [if_pos hev]
    have hsub : rootsOfUnity n ℝ = Subgroup.zpowers (-1 : ℝˣ) := by
      ext u
      rw [mem_rootsOfUnity]
      constructor
      · intro hu
        rcases eq_one_or_neg_one_of_pow_eq_one hn hu with rfl | rfl
        · exact one_mem _
        · exact Subgroup.mem_zpowers _
      · rintro ⟨m, rfl⟩
        rw [← zpow_natCast _ n, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hev.neg_one_pow,
          one_zpow]
    rw [hsub, Nat.card_zpowers,
      orderOf_eq_prime (p := 2) (by rw [neg_one_sq]) neg_one_ne_one_real]
  · rw [if_neg (Nat.not_even_iff_odd.mpr hod)]
    have hsub : rootsOfUnity n ℝ = ⊥ := by
      ext u
      rw [mem_rootsOfUnity, Subgroup.mem_bot]
      constructor
      · intro hu
        rcases eq_one_or_neg_one_of_pow_eq_one hod.pos.ne' hu with rfl | rfl
        · rfl
        · rw [hod.neg_pow, one_pow] at hu
          exact absurd hu neg_one_ne_one_real
      · rintro rfl
        exact one_pow n
    rw [hsub]
    simp

/-! ### The local index at an infinite place -/

section InfinitePlace

variable {K : Type*} [Field K] (w : InfinitePlace K)

set_option synthInstance.maxHeartbeats 400000 in
/-- **The local index formula at an infinite place.**  The index of the `n`-th powers in the units
of the completion, times `n` raised to the multiplicity of the place, is `n` times the number of
`n`-th roots of unity of the completion. -/
theorem index_range_powMonoidHom_units_infinitePlace {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index * n ^ w.mult
      = n * Nat.card ↥(rootsOfUnity n w.Completion) := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [index_range_powMonoidHom_units_congr (InfinitePlace.Completion.ringEquivRealOfIsReal hw) n,
      card_rootsOfUnity_congr (InfinitePlace.Completion.ringEquivRealOfIsReal hw) n,
      index_range_powMonoidHom_units_real hn, card_rootsOfUnity_real hn,
      InfinitePlace.mult, if_pos hw, pow_one, mul_comm]
  · rw [index_range_powMonoidHom_units_congr
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) n,
      card_rootsOfUnity_congr (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) n,
      index_range_powMonoidHom_units_complex hn, card_rootsOfUnity_complex hn,
      InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr hw), one_mul, sq]

end InfinitePlace

end InverseGalois.CFT
