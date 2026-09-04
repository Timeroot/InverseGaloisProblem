/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.NakayamaNextNatural
import InverseGalois.CFT.Units.DecompositionNakayama

/-!
# The obstruction of Tate and Nakayama at a decomposition group is local

The map leaving the comparison of Tate and Nakayama is natural in the representation, and the
fundamental class of an extension of number fields localises at a finite place to a class of the
units of the completion there.  Putting the two together computes that map on the classes of the
idele classes that come from a single place: **on the decomposition group at a finite place, the
values the map leaving the comparison takes on the classes coming from the units of the completion
are exactly the image of the values the purely local map takes there.**

Nothing about the extension away from the place enters.  This is the local half of the comparison of
the global obstruction with the local ones: the companion of
`InverseGalois.CFT.range_resTateNakayamaTwoMap_le_idele`, which says that the comparison itself
produces nothing on a decomposition group that does not already come from the ideles.

## Main results

* `InverseGalois.CFT.exists_map_range_tateNakayamaTwoNextMap_decomposition`: **the values the map
  leaving the comparison of Tate and Nakayama takes, on a decomposition group, on the classes coming
  from the units of the completion there are the image of the values the local map takes.**

## Tags

number field, idele class group, decomposition group, fundamental class, Tate-Nakayama,
localisation, obstruction
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The values the map leaving the comparison of Tate and Nakayama takes, on the decomposition
group at a finite place, on the classes of the idele classes coming from the units of the completion
there are exactly the image of the values the purely local map takes.**  The localised fundamental
class is carried to the restriction of the fundamental class, so the two maps are compared by a map
of the two extensions attached to those classes. -/
theorem exists_map_range_tateNakayamaTwoNextMap_decomposition (M : Rep ℤ Gal(K/k)) :
    ∃ ψ : cocycleTensorObj (shiftObj (decompositionUnitsRep k w))
          (tateTwoCocycle (decompositionUnitsRep k w) (localizedFundamentalClass k w))
          (resObj (stabilizer Gal(K/k) w) M)
        ⟶ cocycleTensorObj (shiftObj (resObj (stabilizer Gal(K/k) w) (ideleClassRep k K)))
          (tateTwoCocycle (resObj (stabilizer Gal(K/k) w) (ideleClassRep k K))
            (tateRes (stabilizer Gal(K/k) w) (ideleClassRep k K) 2 (baseFundamentalClass k K)))
          (resObj (stabilizer Gal(K/k) w) M),
      ∀ n : ℤ,
        Submodule.map
            (tateNakayamaTwoNextMap (resObj (stabilizer Gal(K/k) w) (ideleClassRep k K))
              (tateRes (stabilizer Gal(K/k) w) (ideleClassRep k K) 2 (baseFundamentalClass k K))
              (resObj (stabilizer Gal(K/k) w) M) n)
            (LinearMap.range (tateMap (tensorHomLeft (resObj (stabilizer Gal(K/k) w) M)
              (decompositionPlaceIdeleClass k w)) (n + 1 + 1)).hom)
          = Submodule.map (tateMap ψ (n + 1)).hom
            (LinearMap.range (tateNakayamaTwoNextMap (decompositionUnitsRep k w)
              (localizedFundamentalClass k w) (resObj (stabilizer Gal(K/k) w) M) n)) := by
  have h := exists_map_range_tateNakayamaTwoNextMap (decompositionPlaceIdeleClass k w)
    (localizedFundamentalClass k w) (resObj (stabilizer Gal(K/k) w) M)
  rw [tateMap_localizedFundamentalClass k w] at h
  exact h

end

end InverseGalois.CFT
