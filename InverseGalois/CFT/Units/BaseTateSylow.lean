/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.NakayamaNextNatural
import InverseGalois.CFT.TateCohomology.NakayamaSubgroupError
import InverseGalois.CFT.TateCohomology.TorsionErrorLong
import InverseGalois.CFT.Units.BaseTateCoeff

/-!
# The obstruction to the locally trivial classes, read on a Sylow subgroup

The everywhere locally trivial classes of the units of a Galois extension of number fields, tensored
with coefficients killed by a prime, are exactly what the complete cohomology of the coefficients
three degrees lower produces as soon as a spanning condition holds on a Sylow subgroup for that
prime: the classes of the idele classes tensored with the coefficients, read on the subgroup, have
to be spanned by those the comparison of Tate and Nakayama produces together with those coming from
the ideles.

The idele class group carries a fundamental class whose complete cohomology satisfies, on every
subgroup of the Galois group, the count that yields the classical hypotheses of Tate's theorem.  The
count therefore holds on the subgroups of a Sylow subgroup as well, so the four term exact sequence
measuring the failure of Tate and Nakayama at the prime exists over that Sylow subgroup, and its
comparison map is the comparison of the whole group read there.  What the comparison produces on the
subgroup is thus exactly what one linear map over the subgroup kills.

**The spanning condition on a Sylow subgroup is therefore a statement about the obstruction map of
that subgroup alone**: the obstruction takes, on the idele classes tensored with the coefficients,
no value that it does not already take on the ideles.  That is the local shape a duality theorem for
the everywhere locally trivial classes has to take, now placed over a field over which the extension
has degree a power of the prime.

The values the obstruction takes at all are themselves named by the long exact sequence it belongs
to: they are exactly what the map entering the comparison one degree higher kills.  So the spanning
condition can be read entirely inside the vectors of the idele classes killed by the prime, tensored
with the coefficients, as the equality of one image with one kernel there.

## Main definitions

* `InverseGalois.CFT.resBaseTateNakayamaPTorsionRight`: the obstruction of Tate and Nakayama for the
  idele class group with coefficients killed by a prime, read on a subgroup of the Galois group.
* `InverseGalois.CFT.resBaseTateNakayamaPTorsionLeft`: the map entering the comparison there.

## Main results

* `InverseGalois.CFT.ker_resBaseTateNakayamaPTorsionRight`: **the classes of the idele classes
  tensored with the coefficients on which the obstruction vanishes, read on a subgroup, are exactly
  the values of the comparison of Tate and Nakayama there.**
* `InverseGalois.CFT.range_resBaseTateNakayamaPTorsionRight`: **the values the obstruction takes on
  a subgroup are exactly what the map entering the comparison one degree higher kills.**
* `InverseGalois.CFT.range_shaTorusPTorsionMap_of_sylow_sup`,
  `InverseGalois.CFT.range_shaTorusPTorsionMap_of_sylow_map`,
  `InverseGalois.CFT.range_shaTorusPTorsionMap_of_sylow_ker`: **the everywhere locally trivial
  classes of the units tensored with coefficients killed by a prime are exactly the image of the
  complete cohomology of the coefficients three degrees lower**, as soon as the obstruction of the
  Sylow subgroup takes no value on the idele classes that it does not already take on the ideles.
* `InverseGalois.CFT.map_resBaseTateNakayamaPTorsionRight_eq_range_iff`,
  `InverseGalois.CFT.range_shaTorusPTorsionMap_of_sylow_next`: the same criterion, stated for the
  map the obstruction is built from rather than for the obstruction itself.
* `InverseGalois.CFT.range_shaTorusPTorsionMap_of_sylow_nakayama`: the same criterion, stated with
  no obstruction at all — the comparison of Tate and Nakayama over the Sylow subgroup, together with
  the classes coming from the ideles, spans.

## Tags

number field, idele class group, Tate-Nakayama, Sylow subgroup, Tate-Shafarevich group, duality
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory

namespace InverseGalois.CFT

noncomputable section

open Tate

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {p : ℕ} [Fact p.Prime] (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0)
  (S : Subgroup Gal(K/k))

/-! ### The obstruction on a subgroup -/

/-- **The obstruction of Tate and Nakayama for the idele class group with coefficients killed by a
prime, read on a subgroup of the Galois group**: the count that yields the classical hypotheses of
Tate's theorem holds on every subgroup, hence on every subgroup of the subgroup, so the four term
exact sequence measuring the failure of the comparison exists there. -/
def resBaseTateNakayamaPTorsionRight (n : ℤ) :
    ↥(tateModule (tensorObj (resObj S (ideleClassRep k K)) (resObj S W)) (n + 1 + 1)) →ₗ[ℤ]
      ↥(tateModule (tensorObj (nsmulTorsion (resObj S (ideleClassRep k K)) p) (resObj S W))
        (n + 1 + 1 + 1 + 1)) :=
  resTateNakayamaPTorsionErrorRight (ideleClassRep k K) (baseFundamentalClass k K)
    (fun T => isZero_tateModule_resObj_ideleClassRep_one T)
    (fun T => finite_tateModule_resObj_ideleClassRep_two T)
    (fun T => card_tateModule_resObj_ideleClassRep_two_le T)
    (zsmul_baseFundamentalClass_eq_zero_imp_dvd k K) S W hW n

/-- **The classes of the idele classes tensored with coefficients killed by a prime on which the
obstruction of Tate and Nakayama vanishes, read on a subgroup, are exactly the values of the
comparison of Tate and Nakayama there.** -/
theorem ker_resBaseTateNakayamaPTorsionRight (n : ℤ) :
    LinearMap.ker (resBaseTateNakayamaPTorsionRight k K W hW S n)
      = LinearMap.range
        (resTateNakayamaTwoMap S (ideleClassRep k K) (baseFundamentalClass k K) W n) :=
  ker_resTateNakayamaPTorsionErrorRight (ideleClassRep k K) (baseFundamentalClass k K)
    (fun T => isZero_tateModule_resObj_ideleClassRep_one T)
    (fun T => finite_tateModule_resObj_ideleClassRep_two T)
    (fun T => card_tateModule_resObj_ideleClassRep_two_le T)
    (zsmul_baseFundamentalClass_eq_zero_imp_dvd k K) S W hW n

/-- **The map entering the comparison of Tate and Nakayama for the idele class group with
coefficients killed by a prime, read on a subgroup of the Galois group**: the vectors of the idele
classes killed by the prime, tensored with the coefficients, three degrees above the lower of the
two degrees. -/
def resBaseTateNakayamaPTorsionLeft (n : ℤ) :
    ↥(tateModule (tensorObj (nsmulTorsion (resObj S (ideleClassRep k K)) p) (resObj S W))
        (n + 1 + 1 + 1)) →ₗ[ℤ] ↥(tateModule (resObj S W) n) :=
  resTateNakayamaPTorsionErrorLeft (ideleClassRep k K) (baseFundamentalClass k K)
    (fun T => isZero_tateModule_resObj_ideleClassRep_one T)
    (fun T => finite_tateModule_resObj_ideleClassRep_two T)
    (fun T => card_tateModule_resObj_ideleClassRep_two_le T)
    (zsmul_baseFundamentalClass_eq_zero_imp_dvd k K) S W hW n

/-- **The values the obstruction of Tate and Nakayama takes on a subgroup are exactly what the map
entering the comparison one degree higher kills**, both being read off the same term of the long
exact sequence of the extension attached to the fundamental class. -/
theorem range_resBaseTateNakayamaPTorsionRight (n : ℤ) :
    LinearMap.range (resBaseTateNakayamaPTorsionRight k K W hW S n)
      = LinearMap.ker (resBaseTateNakayamaPTorsionLeft k K W hW S (n + 1)) :=
  range_resTateNakayamaPTorsionErrorRight (ideleClassRep k K) (baseFundamentalClass k K)
    (fun T => isZero_tateModule_resObj_ideleClassRep_one T)
    (fun T => finite_tateModule_resObj_ideleClassRep_two T)
    (fun T => card_tateModule_resObj_ideleClassRep_two_le T)
    (zsmul_baseFundamentalClass_eq_zero_imp_dvd k K) S W hW n

/-- **The obstruction of Tate and Nakayama for the idele class group, read on a subgroup, takes on a
set of classes every value it takes at all exactly when the map it is built from does.**  The
identification of the target of the obstruction with the vectors of the idele classes killed by the
prime is an isomorphism, so it may be stripped off a spanning statement without loss. -/
theorem map_resBaseTateNakayamaPTorsionRight_eq_range_iff (n : ℤ)
    (V : Submodule ℤ ↥(tateModule (tensorObj (resObj S (ideleClassRep k K)) (resObj S W))
      (n + 1 + 1))) :
    Submodule.map (resBaseTateNakayamaPTorsionRight k K W hW S n) V
        = LinearMap.range (resBaseTateNakayamaPTorsionRight k K W hW S n)
      ↔ Submodule.map (tateNakayamaTwoNextMap (resObj S (ideleClassRep k K))
            (tateRes S (ideleClassRep k K) 2 (baseFundamentalClass k K)) (resObj S W) n) V
        = LinearMap.range (tateNakayamaTwoNextMap (resObj S (ideleClassRep k K))
            (tateRes S (ideleClassRep k K) 2 (baseFundamentalClass k K)) (resObj S W) n) :=
  map_resTateNakayamaPTorsionErrorRight_eq_range_iff (ideleClassRep k K)
    (baseFundamentalClass k K)
    (fun T => isZero_tateModule_resObj_ideleClassRep_one T)
    (fun T => finite_tateModule_resObj_ideleClassRep_two T)
    (fun T => card_tateModule_resObj_ideleClassRep_two_le T)
    (zsmul_baseFundamentalClass_eq_zero_imp_dvd k K) S W hW n V

/-! ### The criterion on a Sylow subgroup -/

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**, as
soon as the classes of the idele classes tensored with the coefficients are spanned, on a Sylow
subgroup for that prime, by those the obstruction of that subgroup kills together with those coming
from the ideles. -/
theorem range_shaTorusPTorsionMap_of_sylow_sup (P : Sylow p Gal(K/k)) (n : ℤ)
    (h : LinearMap.ker (resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n)
        ⊔ LinearMap.range (tateMap (resHom (P : Subgroup Gal(K/k))
          (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom = ⊤) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom := by
  refine range_shaTorusPTorsionMap_of_sylow k K W hW P n ?_
  rwa [← ker_resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n]

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**, as
soon as the obstruction of Tate and Nakayama over a Sylow subgroup for that prime takes no value on
the idele classes tensored with the coefficients that it does not already take on the ideles. -/
theorem range_shaTorusPTorsionMap_of_sylow_map (P : Sylow p Gal(K/k)) (n : ℤ)
    (h : Submodule.map (resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n)
          (LinearMap.range (tateMap (resHom (P : Subgroup Gal(K/k))
            (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom)
        = LinearMap.range
          (resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n)) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom := by
  refine range_shaTorusPTorsionMap_of_sylow_sup k K W hW P n ?_
  rw [sup_comm]
  exact (map_eq_range_iff_sup_ker_eq_top _ _).1 h

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**, as
soon as the obstruction of Tate and Nakayama over a Sylow subgroup for that prime takes, on the
ideles tensored with the coefficients, every value that the map entering the comparison one degree
higher kills. -/
theorem range_shaTorusPTorsionMap_of_sylow_ker (P : Sylow p Gal(K/k)) (n : ℤ)
    (h : Submodule.map (resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n)
          (LinearMap.range (tateMap (resHom (P : Subgroup Gal(K/k))
            (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom)
        = LinearMap.ker
          (resBaseTateNakayamaPTorsionLeft k K W hW (P : Subgroup Gal(K/k)) (n + 1))) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom := by
  refine range_shaTorusPTorsionMap_of_sylow_map k K W hW P n ?_
  rw [h, range_resBaseTateNakayamaPTorsionRight]

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**, as
soon as the map leaving the comparison of Tate and Nakayama over a Sylow subgroup for that prime
takes no value on the idele classes tensored with the coefficients that it does not already take on
the ideles.  This is the criterion in the form in which the map is natural in the representation, so
in the form in which its values can be compared with local ones. -/
theorem range_shaTorusPTorsionMap_of_sylow_next (P : Sylow p Gal(K/k)) (n : ℤ)
    (h : Submodule.map
          (tateNakayamaTwoNextMap (resObj (P : Subgroup Gal(K/k)) (ideleClassRep k K))
            (tateRes (P : Subgroup Gal(K/k)) (ideleClassRep k K) 2 (baseFundamentalClass k K))
            (resObj (P : Subgroup Gal(K/k)) W) n)
          (LinearMap.range (tateMap (resHom (P : Subgroup Gal(K/k))
            (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom)
        = LinearMap.range
          (tateNakayamaTwoNextMap (resObj (P : Subgroup Gal(K/k)) (ideleClassRep k K))
            (tateRes (P : Subgroup Gal(K/k)) (ideleClassRep k K) 2 (baseFundamentalClass k K))
            (resObj (P : Subgroup Gal(K/k)) W) n)) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom :=
  range_shaTorusPTorsionMap_of_sylow_map k K W hW P n
    ((map_resBaseTateNakayamaPTorsionRight_eq_range_iff k K W hW (P : Subgroup Gal(K/k)) n _).2 h)

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**, as
soon as the comparison of Tate and Nakayama over a Sylow subgroup for that prime, together with the
classes coming from the ideles, spans the classes of the idele classes tensored with the
coefficients.  This is the criterion in the form in which no obstruction appears at all: only the
comparison itself, and the ideles. -/
theorem range_shaTorusPTorsionMap_of_sylow_nakayama (P : Sylow p Gal(K/k)) (n : ℤ)
    (h : LinearMap.range (resTateNakayamaTwoMap (P : Subgroup Gal(K/k)) (ideleClassRep k K)
          (baseFundamentalClass k K) W n)
        ⊔ LinearMap.range (tateMap (resHom (P : Subgroup Gal(K/k))
          (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom = ⊤) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom := by
  refine range_shaTorusPTorsionMap_of_sylow_sup k K W hW P n ?_
  rwa [ker_resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n]

end

end InverseGalois.CFT
