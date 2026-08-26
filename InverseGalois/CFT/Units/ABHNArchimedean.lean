/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TotallyReal
import InverseGalois.CFT.Units.ABHNTorsion

/-!
# The archimedean places impose nothing when none of them ramifies

The Albert-Brauer-Hasse-Noether theorem asks for a local trivialisation of a two-cocycle of the
units at every place of the extension, the archimedean ones included.  When no archimedean place
ramifies, those conditions are empty: the decomposition group of an unramified archimedean place is
trivial, and a two-cochain of the trivial group is the differential of the constant cochain given
by its only value.  No hypothesis of torsion on the cocycle is needed for this, in contrast with the
reduction that leans on the order of the decomposition group.

Two hypotheses deliver that unramifiedness.  A base field all of whose archimedean places are
complex is unramified at the archimedean places of any extension, since a ramified place is by
definition a complex place lying over a real one; and so is a totally real extension of any base,
for the same reason read from above.  Under either the theorem reads: a two-cocycle of the units
which is a coboundary at every finite place is a coboundary.

## Main results

* `InverseGalois.CFT.IsUnramifiedAtInfinitePlaces.of_isTotallyComplex`: an extension of a totally
  complex number field is unramified at the archimedean places.
* `InverseGalois.CFT.exists_sub_add_eq_infiniteUnits_of_isUnramified`: at an unramified archimedean
  place every two-cochain of the units is locally a coboundary.
* `InverseGalois.CFT.exists_sub_add_eq_globalUnits_of_forall_finite`: **over a base unramified at
  the archimedean places, a two-cocycle of the units which is a coboundary at every finite place is
  a coboundary.**
* `InverseGalois.CFT.exists_sub_add_eq_globalUnits_of_forall_finite_of_isTotallyReal`: **the same
  conclusion for a totally real extension**, with no condition on the base and none on the order of
  the cocycle.

## Tags

number field, idele, Brauer group, two-cocycle, coboundary, archimedean place, totally complex,
totally real, Albert-Brauer-Hasse-Noether
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

omit [NumberField k] [NumberField K] in
/-- **An extension of a totally complex number field is unramified at the archimedean places**, a
ramified archimedean place being a complex place lying over a real one. -/
theorem IsUnramifiedAtInfinitePlaces.of_isTotallyComplex [IsTotallyComplex k] :
    IsUnramifiedAtInfinitePlaces k K where
  isUnramified w := by
    by_contra h
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _))
      (InfinitePlace.not_isUnramified_iff.mp h).2

variable [IsGalois k K]

omit [NumberField k] [NumberField K] in
/-- **At an unramified archimedean place every two-cochain of the units is locally a coboundary**,
the decomposition group there being trivial. -/
theorem exists_sub_add_eq_infiniteUnits_of_isUnramified (w : InfinitePlace K)
    (hw : w.IsUnramified k) (a : Gal(K/k) → Gal(K/k) → Additive Kˣ) :
    ∃ c : ↥(stabilizer Gal(K/k) w) → Additive w.Completionˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) w),
        Additive.ofMul (infiniteUnitHom w (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  have hsub : Subsingleton ↥(stabilizer Gal(K/k) w) :=
    (Nat.card_eq_one_iff_unique.mp
      (InfinitePlace.isUnramified_iff_card_stabilizer_eq_one.mp hw)).1
  refine ⟨fun _ => Additive.ofMul (infiniteUnitHom w (a 1 1).toMul), fun s t => ?_⟩
  have hs : s = 1 := Subsingleton.elim _ _
  have ht : t = 1 := Subsingleton.elim _ _
  subst hs
  subst ht
  simp

/-- **Over a base unramified at the archimedean places, a two-cocycle of the units which is a
coboundary at every finite place is a coboundary.**  This is the form of the
Albert-Brauer-Hasse-Noether theorem in which no condition at all is imposed at infinity. -/
theorem exists_sub_add_eq_globalUnits_of_forall_finite [IsUnramifiedAtInfinitePlaces k K]
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (ha : ∀ x y z : Gal(K/k),
      globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/k) → Additive Kˣ,
      ∀ x y : Gal(K/k), a x y = globalUnitsAut x (b y) - b (x * y) + b x :=
  exists_sub_add_eq_globalUnits ha
    (fun w => exists_sub_add_eq_infiniteUnits_of_isUnramified w (w.isUnramified k) a) hfin

/-- **In a totally real extension, a two-cocycle of the units which is a coboundary at every finite
place is a coboundary.**  Total reality is the hypothesis that replaces oddness of the degree: an
archimedean place of a totally real field is real, hence unramified over anything, so the conditions
at infinity are empty whatever the order of the cocycle. -/
theorem exists_sub_add_eq_globalUnits_of_forall_finite_of_isTotallyReal [IsTotallyReal K]
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (ha : ∀ x y z : Gal(K/k),
      globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/k) → Additive Kˣ,
      ∀ x y : Gal(K/k), a x y = globalUnitsAut x (b y) - b (x * y) + b x :=
  haveI := IsUnramifiedAtInfinitePlaces.of_isTotallyReal k K
  exists_sub_add_eq_globalUnits_of_forall_finite ha hfin

end InverseGalois.CFT
