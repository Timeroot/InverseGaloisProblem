/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.GaloisAction
import InverseGalois.CFT.Units.Places
import InverseGalois.Rigidity.RET.Genus.OrdDomain

/-!
# The `S`-units of a number field

Fix a set `X` of height one primes of a Dedekind domain.  The `X`-units of its field of fractions
are the elements whose order vanishes at every prime outside `X`; they form a subgroup of the
multiplicative group of the field, containing the units of the domain and equal to them when `X` is
empty.  Recording the orders at the primes of `X` is a homomorphism of the `X`-units to the free
lattice on `X`, and its kernel is exactly the group of units of the domain: an element whose order
is nonnegative everywhere lies in the domain, and one whose order vanishes everywhere has an
inverse there as well.

For a Galois extension of number fields and a set of primes carried into itself by the Galois
group, all of this is equivariant: an automorphism moves the order at a prime to the order at the
moved prime, so the group of `X`-units is stable and the homomorphism to the lattice intertwines
the action on the units with the permutation action on the lattice.  The set of primes is
presented here by an equivariant injection from a finite set carrying the action, which is what
makes the permutation lattice on the target available with no further choices.

## Main definitions

* `InverseGalois.CFT.sUnits`: the group of `X`-units of the field of fractions.
* `InverseGalois.CFT.unitsToSUnits`: the units of the domain, as `X`-units.
* `InverseGalois.CFT.sUnitsVal`: the vector of orders of an `X`-unit at the primes of `X`.
* `InverseGalois.CFT.sUnitsMulEquiv`, `InverseGalois.CFT.sUnitsAut`: the action of the Galois group
  on the `X`-units, written multiplicatively and additively.

## Main results

* `InverseGalois.CFT.range_unitsToSUnits`: **the units of the domain are exactly the `X`-units of
  order zero at every prime of `X`.**
* `InverseGalois.CFT.sUnitsVal_equivariant`: **the order vector intertwines the Galois action with
  the permutation action on the lattice.**

## Tags

number field, S-unit, Dedekind domain, height one prime, Galois action
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

/-! ### The group of units outside a set of primes -/

section Basic

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The group of `X`-units**: the elements of the field of fractions whose order vanishes at
every height one prime outside `X`. -/
def sUnits (X : Set (HeightOneSpectrum R)) : Subgroup Kˣ where
  carrier := {u : Kˣ | ∀ v ∉ X, ord K v (u : K) = 0}
  mul_mem' {u w} hu hw v hv := by
    show ord K v ((u * w : Kˣ) : K) = 0
    rw [Units.val_mul, ord_mul v u.ne_zero w.ne_zero, hu v hv, hw v hv, add_zero]
  one_mem' v _ := by
    show ord K v ((1 : Kˣ) : K) = 0
    rw [Units.val_one, ord_one]
  inv_mem' {u} hu v hv := by
    show ord K v ((u⁻¹ : Kˣ) : K) = 0
    rw [Units.val_inv_eq_inv_val, ord_inv, hu v hv, neg_zero]

variable {K}

theorem mem_sUnits {X : Set (HeightOneSpectrum R)} {u : Kˣ} :
    u ∈ sUnits K X ↔ ∀ v ∉ X, ord K v (u : K) = 0 := Iff.rfl

/-! ### The units of the domain -/

/-- A unit of the domain is an `X`-unit, of order zero at every prime. -/
theorem unitsCoe_mem_sUnits (X : Set (HeightOneSpectrum R)) (u : Rˣ) :
    Units.map (algebraMap R K : R →* K) u ∈ sUnits K X :=
  fun v _ => intOrd_eq_zero_of_isUnit (K := K) (v := v) u.isUnit

variable (K) in
/-- **The units of the domain, as `X`-units.** -/
def unitsToSUnitsHom (X : Set (HeightOneSpectrum R)) : Rˣ →* ↥(sUnits K X) :=
  (Units.map (algebraMap R K : R →* K)).codRestrict (sUnits K X) (unitsCoe_mem_sUnits X)

@[simp]
theorem coe_unitsToSUnitsHom_apply (X : Set (HeightOneSpectrum R)) (u : Rˣ) :
    (((unitsToSUnitsHom K X u : ↥(sUnits K X)) : Kˣ) : K) = algebraMap R K (u : R) := rfl

theorem unitsToSUnitsHom_injective (X : Set (HeightOneSpectrum R)) :
    Function.Injective (unitsToSUnitsHom K X) := fun u w h => by
  refine Units.ext (IsFractionRing.injective R K ?_)
  have h2 := congrArg (fun z : ↥(sUnits K X) => ((z : Kˣ) : K)) h
  simpa only [coe_unitsToSUnitsHom_apply] using h2

variable (K) in
/-- **The units of the domain, as `X`-units**, written additively. -/
def unitsToSUnits (X : Set (HeightOneSpectrum R)) : Additive Rˣ →+ Additive ↥(sUnits K X) :=
  MonoidHom.toAdditive (unitsToSUnitsHom K X)

@[simp]
theorem toMul_unitsToSUnits_apply (X : Set (HeightOneSpectrum R)) (u : Additive Rˣ) :
    (unitsToSUnits K X u).toMul = unitsToSUnitsHom K X u.toMul := rfl

theorem unitsToSUnits_injective (X : Set (HeightOneSpectrum R)) :
    Function.Injective (unitsToSUnits K X) := fun _ _ h =>
  Additive.ofMul.injective (unitsToSUnitsHom_injective X (congrArg Additive.toMul h))

/-- **An `X`-unit of order zero at every prime is a unit of the domain.** -/
theorem exists_unitsToSUnitsHom_eq {X : Set (HeightOneSpectrum R)} {u : ↥(sUnits K X)}
    (hu : ∀ v : HeightOneSpectrum R, ord K v ((u : Kˣ) : K) = 0) :
    ∃ a : Rˣ, unitsToSUnitsHom K X a = u := by
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_ord_nonneg (R := R) (K := K)
    (x := ((u : Kˣ) : K)) fun v => (hu v).ge
  obtain ⟨b, hb⟩ := exists_algebraMap_eq_of_ord_nonneg (R := R) (K := K)
    (x := (((u : Kˣ)⁻¹ : Kˣ) : K)) fun v => by
      rw [Units.val_inv_eq_inv_val, ord_inv, hu v, neg_zero]
  have hab : a * b = 1 := by
    refine IsFractionRing.injective R K ?_
    rw [map_mul, ha, hb, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  refine ⟨⟨a, b, hab, hba⟩, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  simpa using ha

/-! ### The order vector -/

section Index

variable {Y : Type*} (ι : Y → HeightOneSpectrum R)

variable (K) in
/-- **The vector of orders of an `X`-unit at the primes of `X`**, the primes being listed by an
injection from an index set. -/
noncomputable def sUnitsVal : Additive ↥(sUnits K (Set.range ι)) →+ (Y → ℤ) where
  toFun u y := ord K (ι y) (((u.toMul : ↥(sUnits K (Set.range ι))) : Kˣ) : K)
  map_zero' := funext fun y => by
    show ord K (ι y) (((1 : ↥(sUnits K (Set.range ι))) : Kˣ) : K) = 0
    rw [OneMemClass.coe_one, Units.val_one, ord_one]
  map_add' u w := funext fun y => by
    show ord K (ι y) (((u.toMul * w.toMul : ↥(sUnits K (Set.range ι))) : Kˣ) : K) = _
    rw [Subgroup.coe_mul, Units.val_mul, ord_mul _ (Units.ne_zero _) (Units.ne_zero _)]
    rfl

@[simp]
theorem sUnitsVal_apply (u : Additive ↥(sUnits K (Set.range ι))) (y : Y) :
    sUnitsVal K ι u y = ord K (ι y) (((u.toMul : ↥(sUnits K (Set.range ι))) : Kˣ) : K) := rfl

/-- **The units of the domain are exactly the `X`-units of order zero at every prime of `X`.** -/
theorem range_unitsToSUnits :
    (unitsToSUnits K (Set.range ι)).range = (sUnitsVal K ι).ker := by
  ext u
  constructor
  · rintro ⟨a, rfl⟩
    refine funext fun y => ?_
    show ord K (ι y) (algebraMap R K ((a.toMul : Rˣ) : R)) = 0
    exact intOrd_eq_zero_of_isUnit (K := K) a.toMul.isUnit
  · intro hu
    have hzero : ∀ v : HeightOneSpectrum R,
        ord K v (((u.toMul : ↥(sUnits K (Set.range ι))) : Kˣ) : K) = 0 := by
      intro v
      by_cases hv : v ∈ Set.range ι
      · obtain ⟨y, rfl⟩ := hv
        exact congrFun (AddMonoidHom.mem_ker.mp hu) y
      · exact u.toMul.2 v hv
    obtain ⟨a, ha⟩ := exists_unitsToSUnitsHom_eq hzero
    exact ⟨Additive.ofMul a, Additive.toMul.injective ha⟩

end Index

end Basic

/-! ### The Galois action -/

section Galois

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]

/-- **The action of a field automorphism on the units of a number field.** -/
def galUnits (σ : Gal(K/k)) : Kˣ ≃* Kˣ := Units.mapEquiv σ.toRingEquiv.toMulEquiv

omit [NumberField K] in
@[simp]
theorem coe_galUnits_apply (σ : Gal(K/k)) (u : Kˣ) : ((galUnits σ u : Kˣ) : K) = σ (u : K) := rfl

variable {Y : Type*} [MulAction Gal(K/k) Y] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (σ : Gal(K/k)) (y : Y), ι (σ • y) = σ • ι y)

include hι

omit [NumberField K] in
/-- A set of primes listed equivariantly is carried into itself. -/
theorem smul_mem_range (σ : Gal(K/k)) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ Set.range ι) :
    σ • v ∈ Set.range ι := by
  obtain ⟨y, rfl⟩ := hv
  exact ⟨σ • y, hι σ y⟩

/-- The group of `X`-units is stable under the Galois action. -/
theorem galUnits_mem_sUnits (σ : Gal(K/k)) {u : Kˣ} (hu : u ∈ sUnits K (Set.range ι)) :
    galUnits σ u ∈ sUnits K (Set.range ι) := by
  intro v hv
  have hσv : σ⁻¹ • v ∉ Set.range ι := by
    refine fun h => hv ?_
    simpa using smul_mem_range hι σ h
  have h : ord K (σ • (σ⁻¹ • v)) (σ (u : K)) = ord K (σ⁻¹ • v) (u : K) :=
    ord_galSmul σ (σ⁻¹ • v) (u : K)
  rw [smul_inv_smul] at h
  rw [coe_galUnits_apply, h, hu _ hσv]

/-- **The action of a field automorphism on the `X`-units.** -/
def sUnitsMulEquiv (σ : Gal(K/k)) :
    ↥(sUnits K (Set.range ι)) ≃* ↥(sUnits K (Set.range ι)) where
  toFun u := ⟨galUnits σ u, galUnits_mem_sUnits hι σ u.2⟩
  invFun u := ⟨galUnits σ⁻¹ u, galUnits_mem_sUnits hι σ⁻¹ u.2⟩
  left_inv u := Subtype.ext (Units.ext (by simp))
  right_inv u := Subtype.ext (Units.ext (by simp))
  map_mul' u w := Subtype.ext (map_mul _ _ _)

@[simp]
theorem coe_sUnitsMulEquiv_apply (σ : Gal(K/k)) (u : ↥(sUnits K (Set.range ι))) :
    (((sUnitsMulEquiv hι σ u : ↥(sUnits K (Set.range ι))) : Kˣ) : K) = σ ((u : Kˣ) : K) := rfl

/-- **The action of the Galois group on the `X`-units**, written additively. -/
def sUnitsAut : Gal(K/k) →*
    (Additive ↥(sUnits K (Set.range ι)) ≃+ Additive ↥(sUnits K (Set.range ι))) where
  toFun σ := MulEquiv.toAdditive (sUnitsMulEquiv hι σ)
  map_one' := AddEquiv.ext fun _ => Additive.toMul.injective (Subtype.ext (Units.ext rfl))
  map_mul' _ _ := AddEquiv.ext fun _ => Additive.toMul.injective (Subtype.ext (Units.ext rfl))

@[simp]
theorem coe_sUnitsAut_apply (σ : Gal(K/k)) (u : Additive ↥(sUnits K (Set.range ι))) :
    ((((sUnitsAut hι σ u).toMul : ↥(sUnits K (Set.range ι))) : Kˣ) : K)
      = σ ((u.toMul : Kˣ) : K) := rfl

/-- **The action on the `X`-units inherits the order of the automorphism.** -/
theorem sUnitsAut_pow_eq_one {σ : Gal(K/k)} {n : ℕ} (hσ : σ ^ n = 1) :
    (sUnitsAut hι σ) ^ n = 1 := by rw [← map_pow, hσ, map_one]

/-- **The order vector intertwines the Galois action with the permutation action on the
lattice.** -/
theorem sUnitsVal_equivariant (σ : Gal(K/k)) (u : Additive ↥(sUnits K (Set.range ι))) :
    sUnitsVal K ι (sUnitsAut hι σ u)
      = permLatticeAut (toPerm σ⁻¹ : Equiv.Perm Y) (sUnitsVal K ι u) := by
  refine funext fun y => ?_
  rw [permLatticeAut_apply, sUnitsVal_apply, sUnitsVal_apply]
  show ord K (ι y) (σ ((u.toMul : Kˣ) : K)) = ord K (ι (σ⁻¹ • y)) _
  rw [hι σ⁻¹ y]
  have h := ord_galSmul σ (σ⁻¹ • ι y) ((u.toMul : Kˣ) : K)
  rw [smul_inv_smul] at h
  exact h

end Galois

end InverseGalois.CFT
