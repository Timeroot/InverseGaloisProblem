/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.HasseNoether
import InverseGalois.CFT.Units.ABHNUnitValues

/-!
# A Brauer class over a number field is split at all but finitely many finite places

A class of the Brauer group of a number field is the class of a crossed product of a finite Galois
extension of number fields, for a two-cocycle taking finitely many values.  Only finitely many
places of the extension ramify over the base, and each of the finitely many values of the cocycle
is a unit of the valuation ring outside a finite set of places, so outside a finite set the place
is unramified and the local component of the cocycle takes its values in the units of the valuation
ring.  There the second cohomology of the cyclic decomposition group vanishes, so the local
component is a coboundary and the completion splits the class.

Together with the Albert-Brauer-Hasse-Noether theorem this says that the map from the Brauer group
of a number field to the product of the Brauer groups of the completions is injective with image in
the restricted product: a class is determined by its local invariants, and almost all of them
vanish.

## Main results

* `InverseGalois.CFT.finite_setOf_not_mem_relative_adicCompletion`: **a Brauer class over a number
  field is split by the completion at all but finitely many finite places.**
* `InverseGalois.CFT.finite_setOf_baseChangeHom_adicCompletion_ne_one`: the same, phrased through
  the base change map on Brauer groups.
* `InverseGalois.CFT.finite_setOf_placeInvariant_ne_one`: **the invariant of a Brauer class over a
  number field vanishes at all but finitely many finite places.**

## Tags

Brauer group, number field, completion, crossed product, local invariant, unramified,
Albert-Brauer-Hasse-Noether, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open groupCohomology

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section PlaceInvariantFinite

variable {k : Type} [Field k] [NumberField k]

/-- **A Brauer class over a number field is split by the completion at all but finitely many finite
places.**  The class is that of a crossed product of a finite Galois extension of number fields;
outside the ramified places and the places where one of the finitely many values of the cocycle
fails to be a unit of the valuation ring, the local component of the cocycle is a two-cocycle of a
cyclic group with values in those units, hence a coboundary. -/
theorem finite_setOf_not_mem_relative_adicCompletion (x : BrauerGroup k) :
    {v : HeightOneSpectrum (𝓞 k) | x ∉ BrauerGroup.relative k (v.adicCompletion k)}.Finite := by
  classical
  obtain ⟨L, hfd, hgal, hx⟩ := exists_isGalois_mem_relative x
  haveI : FiniteDimensional k ↥L := hfd
  haveI : IsGalois k ↥L := hgal
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  obtain ⟨f, hf, rfl⟩ := exists_mk_csa_eq_of_mem_relative (L := ↥L) x hx
  have hga : ∀ (σ : Gal(↥L/k)) (u : Additive (↥L)ˣ),
      Additive.toMul (globalUnitsAut σ u) = σ • Additive.toMul u := fun _ _ => Units.ext rfl
  have ha : ∀ x y z : Gal(↥L/k),
      globalUnitsAut x (Additive.ofMul (f (y, z))) + Additive.ofMul (f (x, y * z))
        = Additive.ofMul (f (x * y, z)) + Additive.ofMul (f (x, y)) := by
    intro x y z
    refine Additive.toMul.injective ?_
    simp only [toMul_add, hga, toMul_ofMul]
    exact (hf x y z).symm
  have hBad : ({w : HeightOneSpectrum (𝓞 ↥L) | ¬Algebra.IsUnramifiedAt (𝓞 k) w.asIdeal} ∪
      ⋃ p : Gal(↥L/k) × Gal(↥L/k),
        {w : HeightOneSpectrum (𝓞 ↥L) |
          unitVal (Additive.ofMul (adicUnitHom w (f p))) ≠ 0}).Finite :=
    (finite_setOf_not_isUnramifiedAt k).union
      (Set.finite_iUnion fun p => finite_setOf_unitVal_adicUnitHom_ne_zero ↥L (f p))
  refine Set.Finite.subset (hBad.image (primeUnder (𝓞 k))) ?_
  rintro v hv
  obtain ⟨w, rfl⟩ := exists_primeUnder_eq (𝓞 k) (𝓞 ↥L) v
  refine ⟨w, ?_, rfl⟩
  by_contra hw
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists,
    not_not] at hw
  obtain ⟨hunr, hval⟩ := hw
  refine hv ((mem_relative_mk_csa_adicCompletion_iff_exists k w hf).mpr ?_)
  exact exists_sub_add_eq_adicUnits_of_unitVal
    (a := fun σ τ : Gal(↥L/k) => Additive.ofMul (f (σ, τ))) w hunr
    (fun s t => hval (s, t)) ha

/-- **A Brauer class over a number field has trivial image in the Brauer group of the completion at
all but finitely many finite places.** -/
theorem finite_setOf_baseChangeHom_adicCompletion_ne_one (x : BrauerGroup k) :
    {v : HeightOneSpectrum (𝓞 k) |
      BrauerGroup.baseChangeHom (v.adicCompletion k) x ≠ 1}.Finite := by
  refine (finite_setOf_not_mem_relative_adicCompletion x).subset fun v hv hmem => ?_
  rw [BrauerGroup.relative, MonoidHom.mem_ker] at hmem
  exact hv hmem

/-- **The invariant of a Brauer class over a number field vanishes at all but finitely many finite
places.** -/
theorem finite_setOf_placeInvariant_ne_one (x : BrauerGroup k) :
    {v : HeightOneSpectrum (𝓞 k) | placeInvariant k v x ≠ 1}.Finite :=
  (finite_setOf_not_mem_relative_adicCompletion x).subset fun _ hv hmem =>
    hv ((placeInvariant_eq_one_iff _ x).mpr hmem)

end PlaceInvariantFinite

end InverseGalois.CFT
