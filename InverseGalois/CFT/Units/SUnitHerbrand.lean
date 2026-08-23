/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Commensurable
import InverseGalois.CFT.Tate.Restrict
import InverseGalois.CFT.Units.Herbrand
import InverseGalois.CFT.Units.SUnit

/-!
# The Herbrand quotient of the group of `S`-units

For a cyclic extension of number fields and a finite set of primes of the top field carried into
itself by the Galois group, the group of `S`-units sits in a short exact sequence: the units of the
ring of integers inject into it, and the vector of orders at the chosen primes identifies the
quotient with a lattice inside the free lattice on those primes.  The lattice has finite index
there, because a power of every prime is principal, so the two have the same Herbrand quotient; and
the free lattice on the primes is a permutation representation, whose Herbrand quotient is the
product over the orbits of the order of a decomposition group.

Multiplying the two computations gives the classical formula: the Herbrand quotient of the
`S`-units of a cyclic extension, times the degree, is the product of the orders of the
decomposition groups at the infinite places of the base field and at the orbits of the chosen
finite primes.

## Main definitions

* `InverseGalois.CFT.sUnitsLattice`: the lattice of order vectors of the `S`-units.
* `InverseGalois.CFT.sUnitsLatticeAut`: the action of a field automorphism on that lattice.
* `InverseGalois.CFT.sUnitsTateSES`: the short exact sequence of the `S`-units.

## Main results

* `InverseGalois.CFT.ord_of_span_eq_pow_self`: the order of a generator of a power of a prime.
* `InverseGalois.CFT.exists_span_eq_pow_card_classGroup`: **a power of every prime is principal.**
* `InverseGalois.CFT.nsmul_mem_sUnitsLattice`: the lattice of order vectors has finite index in the
  free lattice on the chosen primes.
* `InverseGalois.CFT.herbrand_sUnitsAut_mul`: **the Herbrand quotient of the `S`-units of a cyclic
  extension of number fields**, times the degree, is the product of the orders of the decomposition
  groups at the infinite places and at the orbits of the chosen finite primes.

## Tags

number field, S-unit, Herbrand quotient, class group, decomposition group
-/

namespace InverseGalois.CFT

open FractionalIdeal IsDedekindDomain MulAction NumberField Rigidity.RET

open scoped nonZeroDivisors

/-! ### The order of a generator of a power of a prime -/

section Ord

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {v w : HeightOneSpectrum R} {a : R} {m : ℕ}

/-- **The order of a generator of a power of a prime**, at that prime, is the exponent. -/
theorem ord_of_span_eq_pow_self (ha : Ideal.span {a} = v.asIdeal ^ m) :
    ord K v (algebraMap R K a) = m := by
  rw [ord_def, ← coeIdeal_span_singleton, ha, coeIdeal_pow]
  exact count_pow_self K v m

/-- **The order of a generator of a power of a prime**, at any other prime, is zero. -/
theorem ord_of_span_eq_pow_of_ne (ha : Ideal.span {a} = v.asIdeal ^ m) (hw : w ≠ v) :
    ord K w (algebraMap R K a) = 0 := by
  rw [ord_def, ← coeIdeal_span_singleton, ha, coeIdeal_pow, count_pow,
    count_maximal_coprime K w (Ne.symm hw), mul_zero]

variable (R) in
/-- **A power of every prime is principal**: the class of a prime is killed by the order of the
class group. -/
theorem exists_span_eq_pow_card_classGroup [Finite (ClassGroup R)] (v : HeightOneSpectrum R) :
    ∃ a : R, Ideal.span {a} = v.asIdeal ^ Nat.card (ClassGroup R) := by
  have hbot : v.asIdeal ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact v.ne_bot
  have hmem : v.asIdeal ∈ (Ideal R)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hbot
  have hpow : v.asIdeal ^ Nat.card (ClassGroup R) ∈ (Ideal R)⁰ := pow_mem hmem _
  have hone : ClassGroup.mk0 (⟨v.asIdeal ^ Nat.card (ClassGroup R), hpow⟩ : (Ideal R)⁰) = 1 := by
    have hcoe : (⟨v.asIdeal ^ Nat.card (ClassGroup R), hpow⟩ : (Ideal R)⁰)
        = (⟨v.asIdeal, hmem⟩ : (Ideal R)⁰) ^ Nat.card (ClassGroup R) := rfl
    rw [hcoe, map_pow, pow_card_eq_one']
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff hpow).mp hone
  exact ⟨a, ha.symm⟩

end Ord

/-! ### The lattice of order vectors -/

section Lattice

variable {K : Type*} [Field K] [NumberField K]
variable {Y : Type*} {ι : Y → HeightOneSpectrum (𝓞 K)}

variable (K ι) in
/-- **The lattice of order vectors of the `S`-units** inside the free lattice on the chosen
primes. -/
noncomputable def sUnitsLattice : AddSubgroup (Y → ℤ) := (sUnitsVal K ι).range

theorem mem_sUnitsLattice {x : Y → ℤ} :
    x ∈ sUnitsLattice K ι ↔ ∃ u, sUnitsVal K ι u = x := Iff.rfl

/-- The kernel of the corestriction of the order vector is the kernel of the order vector. -/
theorem ker_rangeRestrict_sUnitsVal :
    ((sUnitsVal K ι).rangeRestrict).ker = (sUnitsVal K ι).ker := by
  ext u
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, Subtype.ext_iff]
  rfl

/-- The order vector of a suitable `S`-unit is the exponent of the class number at one chosen prime
and zero at the others. -/
theorem single_mem_sUnitsLattice [DecidableEq Y] (hinj : Function.Injective ι) (y : Y) :
    (fun y' => if y' = y then (Nat.card (ClassGroup (𝓞 K)) : ℤ) else 0) ∈ sUnitsLattice K ι := by
  obtain ⟨a, ha⟩ := exists_span_eq_pow_card_classGroup (𝓞 K) (ι y)
  have hne : (ι y).asIdeal ^ Nat.card (ClassGroup (𝓞 K)) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    refine pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact (ι y).ne_bot
  have ha0 : a ≠ 0 := by
    intro h0
    refine hne ?_
    rw [← ha, h0]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hx0 : algebraMap (𝓞 K) K a ≠ 0 := by
    refine fun h => ha0 (FaithfulSMul.algebraMap_injective (𝓞 K) K ?_)
    rw [h, map_zero]
  have hmem : Units.mk0 (algebraMap (𝓞 K) K a) hx0 ∈ sUnits K (Set.range ι) := by
    intro w hw
    show ord K w (algebraMap (𝓞 K) K a) = 0
    exact ord_of_span_eq_pow_of_ne ha fun h => hw ⟨y, h.symm⟩
  refine ⟨Additive.ofMul ⟨Units.mk0 (algebraMap (𝓞 K) K a) hx0, hmem⟩, ?_⟩
  funext y'
  show ord K (ι y') (algebraMap (𝓞 K) K a)
    = if y' = y then (Nat.card (ClassGroup (𝓞 K)) : ℤ) else 0
  by_cases hy : y' = y
  · subst hy
    rw [if_pos rfl]
    exact ord_of_span_eq_pow_self ha
  · rw [if_neg hy]
    exact ord_of_span_eq_pow_of_ne ha fun h => hy (hinj h)

/-- **The lattice of order vectors has finite index in the free lattice on the chosen primes**: the
class number carries the one into the other. -/
theorem nsmul_mem_sUnitsLattice [Fintype Y] (hinj : Function.Injective ι) (x : Y → ℤ) :
    Nat.card (ClassGroup (𝓞 K)) • x ∈ sUnitsLattice K ι := by
  classical
  have hsum : Nat.card (ClassGroup (𝓞 K)) • x
      = ∑ y : Y, x y • fun y' => if y' = y then (Nat.card (ClassGroup (𝓞 K)) : ℤ) else 0 := by
    funext y'
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul]
    ring
  rw [hsum]
  exact AddSubgroup.sum_mem _ fun y _ =>
    AddSubgroup.zsmul_mem _ (single_mem_sUnitsLattice hinj y) _

end Lattice

/-! ### The short exact sequence of the `S`-units -/

section Galois

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]
variable {Y : Type*} [MulAction Gal(K/k) Y] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (σ : Gal(K/k)) (y : Y), ι (σ • y) = σ • ι y)

include hι

/-- The lattice of order vectors is stable under the Galois action. -/
theorem permLatticeAut_mem_sUnitsLattice (σ : Gal(K/k)) {x : Y → ℤ}
    (hx : x ∈ sUnitsLattice K ι) :
    permLatticeAut (toPerm σ : Equiv.Perm Y) x ∈ sUnitsLattice K ι := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨sUnitsAut hι σ⁻¹ u, ?_⟩
  rw [sUnitsVal_equivariant hι σ⁻¹ u, inv_inv]

variable (σ : Gal(K/k))

theorem mapsTo_sUnitsLattice : ∀ x ∈ sUnitsLattice K ι,
    permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y) x ∈ sUnitsLattice K ι :=
  fun _ hx => permLatticeAut_mem_sUnitsLattice hι σ⁻¹ hx

theorem mapsTo_symm_sUnitsLattice : ∀ x ∈ sUnitsLattice K ι,
    (permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y)).symm x ∈ sUnitsLattice K ι := by
  intro x hx
  have hsymm : (permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y)).symm x
      = permLatticeAut (toPerm σ : Equiv.Perm Y) x := by
    funext y
    show x (σ⁻¹⁻¹ • y) = x (σ • y)
    rw [inv_inv]
  rw [hsymm]
  exact permLatticeAut_mem_sUnitsLattice hι σ hx

/-- **The action of a field automorphism on the lattice of order vectors.** -/
noncomputable def sUnitsLatticeAut : ↥(sUnitsLattice K ι) ≃+ ↥(sUnitsLattice K ι) :=
  subgroupAut (permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y)) (sUnitsLattice K ι)
    (mapsTo_sUnitsLattice hι σ) (mapsTo_symm_sUnitsLattice hι σ)

@[simp]
theorem coe_sUnitsLatticeAut_apply (x : ↥(sUnitsLattice K ι)) :
    ((sUnitsLatticeAut hι σ x : ↥(sUnitsLattice K ι)) : Y → ℤ)
      = permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y) (x : Y → ℤ) := rfl

variable {n : ℕ}

/-- **The short exact sequence of the `S`-units**: the units of the ring of integers, the
`S`-units, and the lattice of order vectors. -/
noncomputable def sUnitsTateSES (hσ : σ ^ n = 1) (hperm : (toPerm σ⁻¹ : Equiv.Perm Y) ^ n = 1) :
    TateSES n (Additive (𝓞 K)ˣ) (Additive ↥(sUnits K (Set.range ι))) ↥(sUnitsLattice K ι) where
  σA := unitsAutHom σ
  σB := sUnitsAut hι σ
  σC := sUnitsLatticeAut hι σ
  hσA := unitsAutHom_pow_eq_one hσ
  hσB := sUnitsAut_pow_eq_one hι hσ
  hσC := subgroupAut_pow_eq_one _ _ (permLatticeAut_pow_eq_one hperm)
  f := unitsToSUnits K (Set.range ι)
  g := (sUnitsVal K ι).rangeRestrict
  hf _ := rfl
  hg _ := Subtype.ext (sUnitsVal_equivariant hι σ _)
  finj := unitsToSUnits_injective _
  gsurj := (sUnitsVal K ι).rangeRestrict_surjective
  range_eq_ker := by rw [ker_rangeRestrict_sUnitsVal, range_unitsToSUnits]

end Galois

/-! ### The Herbrand quotient -/

section Herbrand

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField k] [NumberField K]
  [IsGalois k K]
variable {Y : Type*} [Fintype Y] [MulAction Gal(K/k) Y] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (σ : Gal(K/k)) (y : Y), ι (σ • y) = σ • ι y)

include hι

omit [NumberField k] [IsGalois k K] in
/-- **The Herbrand quotient of the lattice of order vectors** is that of the free lattice on the
chosen primes, the two being commensurable. -/
theorem herbrand_sUnitsLatticeAut (hinj : Function.Injective ι) (σ : Gal(K/k)) {n : ℕ} [NeZero n]
    (hperm : (toPerm σ⁻¹ : Equiv.Perm Y) ^ n = 1) :
    herbrand (sUnitsLatticeAut hι σ) n
      = herbrand (permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y)) n := by
  have htop : ∀ x ∈ (⊤ : AddSubgroup (Y → ℤ)),
      permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y) x ∈ (⊤ : AddSubgroup (Y → ℤ)) :=
    fun _ _ => trivial
  have htop' : ∀ x ∈ (⊤ : AddSubgroup (Y → ℤ)),
      (permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y)).symm x ∈ (⊤ : AddSubgroup (Y → ℤ)) :=
    fun _ _ => trivial
  haveI : Module.Finite ℤ ↥(sUnitsLattice K ι) := module_finite_addSubgroup _
  haveI : Module.Finite ℤ ↥(⊤ : AddSubgroup (Y → ℤ)) := module_finite_addSubgroup _
  haveI : Module.Free ℤ ↥(sUnitsLattice K ι) := module_free_addSubgroup _
  haveI : Module.Free ℤ ↥(⊤ : AddSubgroup (Y → ℤ)) := module_free_addSubgroup _
  have hcard : Nat.card (ClassGroup (𝓞 K)) ≠ 0 := Nat.card_pos.ne'
  have hcomm : herbrand (sUnitsLatticeAut hι σ) n
      = herbrand (subgroupAut (permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y)) ⊤ htop htop') n :=
    herbrand_eq_of_commensurable (σV := permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y))
      (subgroupAut_pow_eq_one _ _ (permLatticeAut_pow_eq_one hperm))
      (subgroupAut_pow_eq_one _ _ (permLatticeAut_pow_eq_one hperm)) (fun _ => rfl) (fun _ => rfl)
      one_ne_zero hcard (fun _ _ => trivial) (fun x _ => nsmul_mem_sUnitsLattice hinj x)
  rw [hcomm, herbrand_topAut]

/-- **The Herbrand quotient of the `S`-units of a cyclic extension of number fields**, times the
degree, is the product of the orders of the decomposition groups at the infinite places of the base
field and at the orbits of the chosen finite primes. -/
theorem herbrand_sUnitsAut_mul (hinj : Function.Injective ι) {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ} [NeZero n]
    [Fintype (orbitRel.Quotient Gal(K/k) Y)] (hn : Nat.card Gal(K/k) = n) :
    herbrand (sUnitsAut hι σ) n * n
      = (∏ v : InfinitePlace k, (Nat.card (stabilizer Gal(K/k) (placeAbove k K v)) : ℚ))
        * ∏ o : orbitRel.Quotient Gal(K/k) Y, (Nat.card (stabilizer Gal(K/k) o.out) : ℚ) := by
  have hσ : σ ^ n = 1 := by rw [← hn]; exact pow_card_eq_one'
  have hperm : (toPerm σ⁻¹ : Equiv.Perm Y) ^ n = 1 := by
    show (MulAction.toPermHom Gal(K/k) Y σ⁻¹) ^ n = 1
    rw [← map_pow, inv_pow, hσ, inv_one, map_one]
  haveI : Module.Finite ℤ ↥(sUnitsLattice K ι) := module_finite_addSubgroup _
  haveI : Module.Finite ℤ ↥((sUnitsVal K ι).range) := module_finite_addSubgroup _
  haveI : Module.Finite ℤ (Additive ↥(sUnits K (Set.range ι))) :=
    module_finite_of_range_eq_ker (unitsToSUnits K (Set.range ι)) (sUnitsVal K ι)
      (range_unitsToSUnits ι)
  have hmul : herbrand (unitsAutHom σ) n * herbrand (sUnitsLatticeAut hι σ) n
      = herbrand (sUnitsAut hι σ) n := (sUnitsTateSES hι σ hσ hperm).herbrand_mul
  have horb : herbrand (permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y)) n
      = ∏ o : orbitRel.Quotient Gal(K/k) Y, (Nat.card (stabilizer Gal(K/k) o.out) : ℚ) := by
    refine herbrand_permLatticeAut_toPerm_orbits (σ := σ⁻¹) (fun g => ?_) hn
    rw [Subgroup.zpowers_inv]
    exact hgen g
  have hA := herbrand_unitsAutHom_mul (K := K) (k := k) hgen hn
  rw [← hmul, herbrand_sUnitsLatticeAut hι hinj σ hperm, horb, ← hA]
  ring

end Herbrand

end InverseGalois.CFT
