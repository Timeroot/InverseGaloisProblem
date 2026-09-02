/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TensorFunctor
import InverseGalois.CFT.Units.BaseTate
import InverseGalois.CFT.Units.IdeleClassSES
import InverseGalois.CFT.Units.IdeleClassTate

/-!
# The locally trivial classes of the units tensored with a lattice

The units of a Galois extension of number fields sit inside the ideles with the idele classes as
quotient, and tensoring that sequence with a representation flat over the integers leaves it exact.
The long exact sequence of complete cohomology then reads the kernel of the map from the units to
the ideles in one degree as the image of the connecting map coming out of the idele classes one
degree lower.  By Shapiro's lemma the cohomology of the ideles is the product of the cohomologies of
the completions over the decomposition groups, so that kernel is the group of everywhere locally
trivial classes: the Tate-Shafarevich group of the torus whose cocharacter lattice is the given
representation.

The idele class group is the module of a class formation, so the theorem of Tate and Nakayama
identifies its complete cohomology tensored with a flat representation in a degree with the complete
cohomology of the representation itself two degrees lower.  Composing the two statements computes
the locally trivial classes: **the everywhere locally trivial part of the complete cohomology of the
units tensored with a lattice, in degree `n + 3`, is exactly the image of the complete cohomology of
the lattice in degree `n`.**  Taking `n = -2` computes the locally trivial classes of the first
cohomology as a quotient of the complete cohomology of the lattice in degree `-2`, which for the
trivial lattice is the abelianisation of the Galois group; this is the finiteness that makes the
group accessible, since the complete cohomology of a finite group in a fixed degree is a finite
object while the cohomology of the units is not.

## Main definitions

* `InverseGalois.CFT.shaTorusMap`: the map from the complete cohomology of a lattice to the complete
  cohomology of the units tensored with it, three degrees higher.
* `InverseGalois.CFT.baseShaTorusMap`: the same map for the fundamental class of the extension, which
  every Galois extension of number fields has.

## Main results

* `InverseGalois.CFT.tateMap_shaTorusMap_eq_zero`: **the classes it produces are locally trivial.**
* `InverseGalois.CFT.exists_shaTorusMap_eq`: **every locally trivial class is produced by it.**
* `InverseGalois.CFT.range_shaTorusMap`: **the locally trivial classes of the units tensored with a
  lattice are exactly the image of the complete cohomology of the lattice three degrees lower.**
* `InverseGalois.CFT.range_baseShaTorusMap`: the same statement for an arbitrary Galois extension of
  number fields, with no hypothesis beyond flatness of the lattice.
* `InverseGalois.CFT.range_baseShaTorusMap_one`: **the everywhere locally trivial classes of the
  first cohomology are a quotient of the complete cohomology of the lattice in degree `-2`.**

## Tags

number field, idele class group, Tate cohomology, Tate-Nakayama, Tate-Shafarevich group, torus
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory Tate

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

variable (α : tateModule (ideleClassRep k K) 2)
  (hα : ∀ m : ℤ, m • α = 0 → (Nat.card Gal(K/k) : ℤ) ∣ m)
  (N : Rep ℤ Gal(K/k)) (hN : Module.Flat ℤ ↥N.V)

/-! ### The tensored sequence -/

omit [NumberField k] [IsGalois k K] in
include hN in
/-- **The sequence of the units, the ideles and the idele classes stays exact after tensoring with
a representation flat over the integers.** -/
theorem tensorSeq_ideleClassShortComplex_shortExact :
    (tensorSeq N (ideleClassShortComplex k K)).ShortExact :=
  haveI := hN
  tensorSeq_shortExact N (ideleClassShortComplex_shortExact k K)

/-! ### The map -/

/-- **The map from the complete cohomology of a lattice to the complete cohomology of the units
tensored with it, three degrees higher**: the theorem of Tate and Nakayama for the idele class
group, followed by the connecting map of the sequence of the idele classes. -/
def shaTorusMap (n : ℤ) :
    tateModule N n →ₗ[ℤ] tateModule (tensorObj (globalUnitsRep k K) N) (n + 1 + 1 + 1) :=
  (tateδ (tensorSeq_ideleClassShortComplex_shortExact N hN) (n + 1 + 1)).hom ∘ₗ
    (tateNakayamaIdeleClass α hα N hN n).toLinearMap

theorem shaTorusMap_apply (n : ℤ) (y : ↥(tateModule N n)) :
    shaTorusMap α hα N hN n y =
      tateδ (tensorSeq_ideleClassShortComplex_shortExact N hN) (n + 1 + 1)
        (tateNakayamaIdeleClass α hα N hN n y) :=
  rfl

/-! ### The locally trivial classes -/

/-- **The classes produced by the map die in the ideles.**  They are in the image of the connecting
map of the sequence of the idele classes, and the composite of the connecting map with the map
induced by the inclusion of the units into the ideles is zero. -/
theorem tateMap_shaTorusMap_eq_zero (n : ℤ) (y : ↥(tateModule N n)) :
    tateMap (tensorHomLeft N (globalUnitsToIdele k K)) (n + 1 + 1 + 1)
      (shaTorusMap α hα N hN n y) = 0 :=
  (tateExact_δ_map (tensorSeq_ideleClassShortComplex_shortExact N hN)
      (n + 1 + 1)).apply_apply_eq_zero (tateNakayamaIdeleClass α hα N hN n y)

/-- **Every class of the units tensored with a lattice which dies in the ideles comes from the
complete cohomology of the lattice three degrees lower.**  This is the exactness of the long exact
sequence of the tensored idele sequence at the units, read through the theorem of Tate and
Nakayama for the idele class group. -/
theorem exists_shaTorusMap_eq (n : ℤ)
    (x : ↥(tateModule (tensorObj (globalUnitsRep k K) N) (n + 1 + 1 + 1)))
    (hx : tateMap (tensorHomLeft N (globalUnitsToIdele k K)) (n + 1 + 1 + 1) x = 0) :
    ∃ y : ↥(tateModule N n), shaTorusMap α hα N hN n y = x := by
  obtain ⟨z, hz⟩ :=
    (tateExact_δ_map (tensorSeq_ideleClassShortComplex_shortExact N hN) (n + 1 + 1) x).1 hx
  refine ⟨(tateNakayamaIdeleClass α hα N hN n).symm z, ?_⟩
  rw [shaTorusMap_apply, LinearEquiv.apply_symm_apply, hz]

/-- **The locally trivial classes of the units tensored with a lattice are exactly the image of the
complete cohomology of the lattice three degrees lower.**  The kernel on the right is the group of
everywhere locally trivial classes, since the cohomology of the ideles is the product of the
cohomologies of the completions; so the group of everywhere locally trivial classes of a torus is a
quotient of the complete cohomology of its cocharacter lattice, and in particular finite. -/
theorem range_shaTorusMap (n : ℤ) :
    LinearMap.range (shaTorusMap α hα N hN n)
      = LinearMap.ker (tateMap (tensorHomLeft N (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  refine ⟨?_, exists_shaTorusMap_eq α hα N hN n x⟩
  rintro ⟨y, rfl⟩
  exact tateMap_shaTorusMap_eq_zero α hα N hN n y

/-! ### The unconditional form -/

/-- **The map from the complete cohomology of a lattice to the locally trivial classes of the units
tensored with it**, built from the fundamental class of the extension.  Every Galois extension of
number fields has one, so this needs no hypotheses beyond flatness of the lattice. -/
def baseShaTorusMap (n : ℤ) :
    tateModule N n →ₗ[ℤ] tateModule (tensorObj (globalUnitsRep k K) N) (n + 1 + 1 + 1) :=
  shaTorusMap (baseFundamentalClass k K) (zsmul_baseFundamentalClass_eq_zero_imp_dvd k K) N hN n

/-- **The locally trivial classes of the units of a Galois extension of number fields tensored with
a lattice are exactly the image of the complete cohomology of the lattice three degrees lower.**
The kernel on the right is the group of everywhere locally trivial classes, since the cohomology of
the ideles is the product of the cohomologies of the completions; so the group of everywhere locally
trivial classes of a torus is a quotient of the complete cohomology of its cocharacter lattice, and
in particular finite. -/
theorem range_baseShaTorusMap (n : ℤ) :
    LinearMap.range (baseShaTorusMap N hN n)
      = LinearMap.ker (tateMap (tensorHomLeft N (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom :=
  range_shaTorusMap _ _ N hN n

/-- **The everywhere locally trivial classes of the first cohomology of the units tensored with a
lattice form a quotient of the complete cohomology of the lattice in degree `-2`.**  For a finite
group that degree is a finite object, so the group of everywhere locally trivial classes of a torus
over a number field is finite. -/
theorem range_baseShaTorusMap_one :
    LinearMap.range (baseShaTorusMap N hN (-2))
      = LinearMap.ker (tateMap (tensorHomLeft N (globalUnitsToIdele k K)) 1).hom :=
  range_baseShaTorusMap N hN (-2)

end

end InverseGalois.CFT
