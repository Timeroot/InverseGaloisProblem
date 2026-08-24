/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.TrivialLattice
import InverseGalois.CFT.Units.SUnitHerbrand
import InverseGalois.CFT.Units.UnitLattice

/-!
# The index of the `n`-th powers in the group of `S`-units

Forgetting the Galois action, the short exact sequence of the `S`-units still computes: the units
of the ring of integers, with trivial action, have Herbrand quotient `n` raised to the rank of the
unit lattice, the lattice of order vectors has Herbrand quotient `n` raised to the number of chosen
primes, and multiplying gives the quotient of the `S`-units themselves.

For a trivial action the two Tate groups are the quotient by the `n`-th powers and the `n`-torsion.
The `n`-torsion of the `S`-units is the group of `n`-th roots of unity, because a root of unity has
order zero at every prime; so if the field contains the `n`-th roots of unity that torsion has
exactly `n` elements.  Multiplying the Herbrand quotient by it, and using that the rank of the unit
lattice is one less than the number of infinite places, the index of the `n`-th powers in the group
of `S`-units is `n` raised to the number of places of `S`, counting both the infinite places and
the chosen finite primes.

## Main definitions

* `InverseGalois.CFT.sUnitsTrivialTateSES`: the short exact sequence of the `S`-units, with trivial
  actions.
* `InverseGalois.CFT.kerPowSUnitsEquiv`: the `n`-torsion of the `S`-units is the group of `n`-th
  roots of unity.

## Main results

* `InverseGalois.CFT.rootsOfUnity_le_sUnits`: a root of unity is an `S`-unit.
* `InverseGalois.CFT.herbrand_one_units`: the Herbrand quotient of the units of the ring of
  integers, with trivial action, is `n` raised to the rank of the unit lattice.
* `InverseGalois.CFT.herbrand_one_sUnits`: **the Herbrand quotient of the `S`-units with trivial
  action.**
* `InverseGalois.CFT.index_range_powMonoidHom_sUnits`: **the index of the `n`-th powers in the
  group of `S`-units**, for a field containing the `n`-th roots of unity, is `n` raised to the
  number of places of `S`.

## Tags

number field, S-unit, index, roots of unity, Herbrand quotient, unit lattice
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField NumberField.Units Rigidity.RET

/-! ### The roots of unity as `S`-units -/

section Roots

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {n : ℕ}

variable (K) in
/-- **A root of unity is an `X`-unit**: its order at any prime is killed by `n`, hence zero. -/
theorem rootsOfUnity_le_sUnits (hn : n ≠ 0) (X : Set (HeightOneSpectrum R)) :
    rootsOfUnity n K ≤ sUnits K X := by
  refine fun ζ hζ => mem_sUnits.mpr fun v _ => ?_
  have hzero : ((ζ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hpow : ((ζ : Kˣ) : K) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity n ζ).mp hζ, Units.val_one]
  have h : (n : ℤ) * ord K v ((ζ : Kˣ) : K) = 0 := by
    rw [← ord_pow v hzero, hpow, ord_one]
  exact (mul_eq_zero.mp h).resolve_left (Int.natCast_ne_zero.mpr hn)

variable (K n) in
/-- **The `n`-torsion of the `X`-units is the group of `n`-th roots of unity.** -/
def kerPowSUnitsEquiv (hn : n ≠ 0) (X : Set (HeightOneSpectrum R)) :
    ↥(powMonoidHom n : ↥(sUnits K X) →* ↥(sUnits K X)).ker ≃ ↥(rootsOfUnity n K) where
  toFun u := ⟨((u.1 : ↥(sUnits K X)) : Kˣ), by
    have h : (u.1 : ↥(sUnits K X)) ^ n = 1 := MonoidHom.mem_ker.mp u.2
    rw [mem_rootsOfUnity, ← Subgroup.coe_pow, h, OneMemClass.coe_one]⟩
  invFun ζ := ⟨⟨(ζ : Kˣ), rootsOfUnity_le_sUnits K hn X ζ.2⟩, by
    have h : ((ζ : Kˣ)) ^ n = 1 := (mem_rootsOfUnity n _).mp ζ.2
    refine MonoidHom.mem_ker.mpr (Subtype.ext ?_)
    rw [powMonoidHom_apply, Subgroup.coe_pow, h, OneMemClass.coe_one]⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (K n) in
/-- **The `n`-torsion of the `X`-units has `n` elements** when the field contains the `n`-th roots
of unity. -/
theorem card_ker_pow_sUnits [NeZero n] [HasEnoughRootsOfUnity K n]
    (X : Set (HeightOneSpectrum R)) :
    Nat.card ↥(powMonoidHom n : ↥(sUnits K X) →* ↥(sUnits K X)).ker = n := by
  rw [Nat.card_congr (kerPowSUnitsEquiv K n (NeZero.ne n) X),
    HasEnoughRootsOfUnity.natCard_rootsOfUnity K n]

end Roots

/-! ### The Herbrand quotient of a trivial action -/

section Trivial

variable {K : Type*} [Field K] [NumberField K] {Y : Type*} [Fintype Y]
  {ι : Y → HeightOneSpectrum (𝓞 K)} (n : ℕ)

variable (K) in
/-- The rank of the unit lattice is one less than the number of infinite places. -/
theorem rank_add_one : rank K + 1 = Fintype.card (InfinitePlace K) := by
  rw [rank]
  exact Nat.succ_pred_eq_of_pos Fintype.card_pos

variable (K) in
/-- **The Herbrand quotient of the units of the ring of integers with trivial action** is `n`
raised to the rank of the unit lattice, the torsion of the unit group being finite. -/
theorem herbrand_one_units (hn : n ≠ 0) :
    herbrand (1 : Additive (𝓞 K)ˣ ≃+ Additive (𝓞 K)ˣ) n = (n : ℚ) ^ rank K := by
  haveI : NeZero n := ⟨hn⟩
  have h : herbrand (1 : Additive (𝓞 K)ˣ ≃+ Additive (𝓞 K)ˣ) n
      = herbrand (1 : ↥(unitLatticeFull K) ≃+ ↥(unitLatticeFull K)) n :=
    herbrand_eq_of_finite_ker (g := fullLogSurj K) (fun _ => rfl) (one_pow n) (one_pow n)
      fullLogSurj_surjective
  rw [h, herbrand_one_of_basis n (basisUnitLatticeFull K) hn, Fintype.card_fin]

variable (ι) in
/-- **The short exact sequence of the `S`-units, with trivial actions**: the units of the ring of
integers, the `S`-units, and the lattice of order vectors. -/
noncomputable def sUnitsTrivialTateSES :
    TateSES n (Additive (𝓞 K)ˣ) (Additive ↥(sUnits K (Set.range ι))) ↥(sUnitsLattice K ι) where
  σA := 1
  σB := 1
  σC := 1
  hσA := one_pow n
  hσB := one_pow n
  hσC := one_pow n
  f := unitsToSUnits K (Set.range ι)
  g := (sUnitsVal K ι).rangeRestrict
  hf _ := rfl
  hg _ := rfl
  finj := unitsToSUnits_injective _
  gsurj := (sUnitsVal K ι).rangeRestrict_surjective
  range_eq_ker := by rw [ker_rangeRestrict_sUnitsVal, range_unitsToSUnits]

/-- **The Herbrand quotient of the `S`-units with trivial action** is `n` raised to the rank of the
unit lattice plus the number of chosen primes. -/
theorem herbrand_one_sUnits (hinj : Function.Injective ι) (hn : n ≠ 0) :
    herbrand (1 : Additive ↥(sUnits K (Set.range ι)) ≃+ Additive ↥(sUnits K (Set.range ι))) n
      = (n : ℚ) ^ (rank K + Fintype.card Y) := by
  haveI : NeZero n := ⟨hn⟩
  haveI : Module.Finite ℤ ↥(sUnitsLattice K ι) := module_finite_addSubgroup _
  haveI : Module.Finite ℤ ↥((sUnitsVal K ι).range) := module_finite_addSubgroup _
  haveI : Module.Finite ℤ (Additive ↥(sUnits K (Set.range ι))) :=
    module_finite_of_range_eq_ker (unitsToSUnits K (Set.range ι)) (sUnitsVal K ι)
      (range_unitsToSUnits ι)
  have hmul : herbrand (1 : Additive (𝓞 K)ˣ ≃+ Additive (𝓞 K)ˣ) n
      * herbrand (1 : ↥(sUnitsLattice K ι) ≃+ ↥(sUnitsLattice K ι)) n
      = herbrand (1 : Additive ↥(sUnits K (Set.range ι))
        ≃+ Additive ↥(sUnits K (Set.range ι))) n := (sUnitsTrivialTateSES ι n).herbrand_mul
  rw [← hmul, herbrand_one_units K n hn, herbrand_one_addSubgroup_of_nsmul_mem n
    (Nat.card_pos (α := ClassGroup (𝓞 K))).ne' (fun x => nsmul_mem_sUnitsLattice hinj x) hn,
    ← pow_add]

/-- **The index of the `n`-th powers in the group of `S`-units**, for a number field containing the
`n`-th roots of unity, is `n` raised to the number of places of `S`: the infinite places together
with the chosen finite primes. -/
theorem index_range_powMonoidHom_sUnits (hinj : Function.Injective ι) [NeZero n]
    [HasEnoughRootsOfUnity K n] :
    (powMonoidHom n : ↥(sUnits K (Set.range ι)) →* ↥(sUnits K (Set.range ι))).range.index
      = n ^ (Fintype.card (InfinitePlace K) + Fintype.card Y) := by
  have hn : n ≠ 0 := NeZero.ne n
  haveI : Module.Finite ℤ ↥(sUnitsLattice K ι) := module_finite_addSubgroup _
  haveI : Module.Finite ℤ ↥((sUnitsVal K ι).range) := module_finite_addSubgroup _
  haveI : Module.Finite ℤ (Additive ↥(sUnits K (Set.range ι))) :=
    module_finite_of_range_eq_ker (unitsToSUnits K (Set.range ι)) (sUnitsVal K ι)
      (range_unitsToSUnits ι)
  have hm1 : Nat.card (tateHm1 (1 : Additive ↥(sUnits K (Set.range ι))
      ≃+ Additive ↥(sUnits K (Set.range ι))) n) = n := by
    rw [card_tateHm1_one_additive, card_ker_pow_sUnits K n]
  have h0 : (Nat.card (tateH0 (1 : Additive ↥(sUnits K (Set.range ι))
      ≃+ Additive ↥(sUnits K (Set.range ι))) n) : ℚ)
      = (n : ℚ) ^ (rank K + Fintype.card Y) * n := by
    rw [← herbrand_one_sUnits n hinj hn, herbrand, hm1,
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]
  rw [← card_tateH0_one_additive]
  have hexp : rank K + Fintype.card Y + 1 = Fintype.card (InfinitePlace K) + Fintype.card Y := by
    rw [← rank_add_one K]
    ring
  refine Nat.cast_injective (R := ℚ) ?_
  rw [h0, ← hexp, Nat.cast_pow, pow_succ]

end Trivial

end InverseGalois.CFT
