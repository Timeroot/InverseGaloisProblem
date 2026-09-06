/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.NakayamaSubgroup
import InverseGalois.CFT.Units.DecompositionLocalization

/-!
# The comparison of Tate and Nakayama at a decomposition group is local

The comparison of Tate and Nakayama for the idele class group and the fundamental class of an
extension, read on the decomposition group at a finite place, is the comparison of that group for
the class of the idele classes restricted there.  The fundamental class localised at the place is a
class of the units of the completion whose ideles are exactly that restriction, so the comparison
read on the decomposition group is computed by the units of the completion: everything it produces
already comes from a single place.

In particular everything it produces comes from the ideles.  This is the local half of the
comparison of the global obstruction with the local ones: on a decomposition group the classes of
the idele classes that the comparison reaches are exactly classes of ideles, and no information
about the extension away from the place is involved.

Corestriction sends the local statement back up.  The comparison is a product with a fixed class,
and corestriction moves such a product past itself, so a class produced by the local comparison at a
place is carried, first to the idele classes and then by corestriction, to a class the global
comparison produces.  Whatever the places contribute is therefore already accounted for, and the
question of what the global comparison misses is a question about the places jointly, not about any
one of them.

## Main results

* `InverseGalois.CFT.tateMap_localizedFundamentalClass`: **the localised fundamental class is
  carried to the restriction of the fundamental class**, in the grading of complete cohomology.
* `InverseGalois.CFT.range_resTateNakayamaTwoMap_le_decompositionUnits`: **the comparison of Tate
  and Nakayama, read on a decomposition group, produces nothing that does not already come from the
  units of the completion there.**
* `InverseGalois.CFT.range_resTateNakayamaTwoMap_le_idele`: **the comparison of Tate and Nakayama,
  read on a decomposition group, produces nothing that does not already come from the ideles.**
* `InverseGalois.CFT.map_tateCor_range_tateNakayamaTwoMap_decompositionUnits_le`: **what the
  comparison of Tate and Nakayama of a decomposition group produces from the units of the completion
  there corestricts into what the comparison for the idele class group produces.**

## Tags

number field, idele class group, decomposition group, fundamental class, Tate-Nakayama,
localisation
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The localised fundamental class is carried to the restriction of the fundamental class to the
decomposition group**, read in the grading of complete cohomology. -/
theorem tateMap_localizedFundamentalClass :
    tateMap (decompositionPlaceIdeleClass k w) 2 (localizedFundamentalClass k w)
      = tateRes (stabilizer Gal(K/k) w) (ideleClassRep k K) 2 (baseFundamentalClass k K) :=
  map_localizedFundamentalClass k w

variable (k) in
/-- **The comparison of Tate and Nakayama for the idele class group and the fundamental class, read
on a decomposition group, produces nothing that does not already come from the units of the
completion there.** -/
theorem range_resTateNakayamaTwoMap_le_decompositionUnits (M : Rep ℤ Gal(K/k)) (n : ℤ) :
    LinearMap.range (resTateNakayamaTwoMap (stabilizer Gal(K/k) w) (ideleClassRep k K)
        (baseFundamentalClass k K) M n)
      ≤ LinearMap.range (tateMap (tensorHomLeft (resObj (stabilizer Gal(K/k) w) M)
          (decompositionPlaceIdeleClass k w)) (n + 1 + 1)).hom :=
  range_resTateNakayamaTwoMap_le _ _ M _ _ (tateMap_localizedFundamentalClass k w) n

variable (k) in
/-- **The comparison of Tate and Nakayama for the idele class group and the fundamental class, read
on a decomposition group, produces nothing that does not already come from the ideles.**  The units
of the completion at the place are a subrepresentation of the ideles for the decomposition group
there. -/
theorem range_resTateNakayamaTwoMap_le_idele (M : Rep ℤ Gal(K/k)) (n : ℤ) :
    LinearMap.range (resTateNakayamaTwoMap (stabilizer Gal(K/k) w) (ideleClassRep k K)
        (baseFundamentalClass k K) M n)
      ≤ LinearMap.range (tateMap (resHom (stabilizer Gal(K/k) w)
          (tensorHomLeft M (ideleToIdeleClass k K))) (n + 1 + 1)).hom := by
  refine le_trans (range_resTateNakayamaTwoMap_le_decompositionUnits k w M n) ?_
  have h : tensorHomLeft (resObj (stabilizer Gal(K/k) w) M) (decompositionPlaceIdeleClass k w)
      = tensorHomLeft (resObj (stabilizer Gal(K/k) w) M) (decompositionPlaceIdele k w)
        ≫ resHom (stabilizer Gal(K/k) w) (tensorHomLeft M (ideleToIdeleClass k K)) := by
    rw [decompositionPlaceIdeleClass, ← tensorHomLeft_comp, resHom_tensorHomLeft]
  rw [h, tateMap_comp, ModuleCat.hom_comp]
  exact LinearMap.range_comp_le_range _ _

variable (k) in
/-- **What the comparison of Tate and Nakayama of the decomposition group at a finite place produces
from the units of the completion there corestricts into what the comparison of Tate and Nakayama for
the idele class group and the fundamental class produces.**  Corestriction moves a product with a
fixed class past itself, and the localised fundamental class is carried to the restriction of the
fundamental class, so a purely local class never leaves the values of the global comparison. -/
theorem map_tateCor_range_tateNakayamaTwoMap_decompositionUnits_le (M : Rep ℤ Gal(K/k)) (n : ℤ) :
    Submodule.map (tateCor (stabilizer Gal(K/k) w) (tensorObj (ideleClassRep k K) M) (n + 1 + 1))
        (Submodule.map (tateMap (tensorHomLeft (resObj (stabilizer Gal(K/k) w) M)
            (decompositionPlaceIdeleClass k w)) (n + 1 + 1)).hom
          (LinearMap.range (tateNakayamaTwoMap (decompositionUnitsRep k w)
            (localizedFundamentalClass k w) (resObj (stabilizer Gal(K/k) w) M) n)))
      ≤ LinearMap.range (tateNakayamaTwoMap (ideleClassRep k K) (baseFundamentalClass k K) M n) :=
  map_tateCor_range_tateNakayamaTwoMap_le _ _ M _ _ (tateMap_localizedFundamentalClass k w) n

end

end InverseGalois.CFT
