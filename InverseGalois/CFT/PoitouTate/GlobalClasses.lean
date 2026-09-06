/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceExponent
import InverseGalois.CFT.Local.AdicAction
import InverseGalois.CFT.PoitouTate.Prescribed

/-!
# The local classes of a global unit, and their behaviour under the Galois action

A unit of a number field has a class modulo `n`-th powers in the completion at every finite place,
and the two invariants of that class which the construction of algebraic numbers with prescribed
local behaviour uses are its valuation modulo `n` and the place it lives at.  The first is the
value of the unit at the place, read modulo `n`, so the class is unramified exactly when the
exponent divides that value; this is the dictionary between the ramification of a class and the
arithmetic of the unit.

A Galois automorphism of the number field carries the completion at a place isomorphically onto
the completion at the image of the place, and being an isometry it carries the `n`-th powers onto
the `n`-th powers and preserves the valuation.  So it identifies the classes at a place with the
classes at the image of the place, matches the class of a unit with the class of its image, and
carries the unramified classes onto the unramified classes.  Conditions on the local behaviour of
a unit therefore transport along the Galois group with no loss.

## Main definitions

* `InverseGalois.CFT.adicUnitsGalEquiv`: the units of a completion, moved by a Galois automorphism
  to the units of the completion at the image of the place.
* `InverseGalois.CFT.localClassesGalEquiv`: **the classes modulo `n`-th powers at a place,
  identified with the classes at the image of the place.**

## Main results

* `InverseGalois.CFT.unitValModQuot_localClassHom`: the valuation modulo `n` of the class of a unit
  of a number field is the value of that unit at the place.
* `InverseGalois.CFT.localClassHom_mem_localUnramified_iff`: **the class of a unit of a number
  field is unramified exactly when the exponent divides its value at the place.**
* `InverseGalois.CFT.placeValue_galSmul`: the value of a unit at a place is the value of its image
  under a Galois automorphism at the image of the place.
* `InverseGalois.CFT.localClassesGalEquiv_localClassHom`: the identification of the classes carries
  the class of a unit to the class of its image.
* `InverseGalois.CFT.unitValModQuot_localClassesGalEquiv`: the identification of the classes
  preserves the valuation modulo `n`.
* `InverseGalois.CFT.map_localUnramified_localClassesGalEquiv`: **the identification of the classes
  carries the unramified classes onto the unramified classes.**

## Tags

number field, adic completion, local class, unramified, Galois action, valuation
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped Pointwise

/-! ### The ramification of the class of a global unit -/

section Ramification

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/-- **The valuation modulo `n` of the class of a unit of a number field at a finite place is the
value of that unit at the place**, read modulo `n`. -/
theorem unitValModQuot_localClassHom (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (a : Kˣ) :
    unitValModQuot (isUnitValGen_one (valued_adicCompletion_surjective v)) n
        (localClassHom v n a)
      = Multiplicative.ofAdd ((placeValue v a : ℤ) : ZMod n) := rfl

/-- **The class of a unit of a number field at a finite place is unramified exactly when the
exponent divides the value of that unit at the place.** -/
theorem localClassHom_mem_localUnramified_iff [NeZero n] (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    localClassHom v n a ∈ localUnramified v n ↔ (n : ℤ) ∣ placeValue v a :=
  mk_mem_unramifiedClasses_iff _ _

end Ramification

/-! ### Powers under an isomorphism -/

section MapPow

/-- **An isomorphism of commutative groups carries the `n`-th powers onto the `n`-th powers.** -/
theorem map_range_powMonoidHom {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ) :
    Subgroup.map (e : G →* H) (powMonoidHom n : G →* G).range
      = (powMonoidHom n : H →* H).range := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (map_pow e x n).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨e.symm z ^ n, ⟨e.symm z, rfl⟩, by simp [powMonoidHom]⟩

end MapPow

/-! ### The Galois action on the local classes -/

section GaloisAction

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] {n : ℕ}

/-- The isomorphism of completions carries a scalar to the image of that scalar under the
automorphism. -/
theorem adicCompletionGalEquiv_algebraMap (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k)) (x : K) :
    adicCompletionGalEquiv v σ (algebraMap K (v.adicCompletion K) x)
      = algebraMap K ((σ • v).adicCompletion K) (σ x) :=
  adicCompletionGalEquiv_coe v σ x

/-- **The units of a completion, moved by a Galois automorphism** to the units of the completion at
the image of the place. -/
noncomputable def adicUnitsGalEquiv (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k)) :
    (v.adicCompletion K)ˣ ≃* ((σ • v).adicCompletion K)ˣ :=
  Units.mapEquiv (adicCompletionGalEquiv v σ).toMulEquiv

/-- The image of a unit of a number field in a completion is moved to the image of that unit under
the automorphism. -/
theorem adicUnitsGalEquiv_map_algebraMap (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k)) (a : Kˣ) :
    adicUnitsGalEquiv v σ (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
      = Units.map (algebraMap K ((σ • v).adicCompletion K)).toMonoidHom (galUnits σ a) := by
  ext
  exact adicCompletionGalEquiv_algebraMap v σ (a : K)

/-- Moving a unit of a completion by a Galois automorphism preserves its valuation. -/
theorem unitVal_adicUnitsGalEquiv (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k))
    (u : (v.adicCompletion K)ˣ) :
    unitVal (Additive.ofMul (adicUnitsGalEquiv v σ u)) = unitVal (Additive.ofMul u) := by
  show WithZero.log (Valued.v ((adicUnitsGalEquiv v σ u : ((σ • v).adicCompletion K))))
    = WithZero.log (Valued.v ((u : v.adicCompletion K)))
  rw [show ((adicUnitsGalEquiv v σ u : ((σ • v).adicCompletion K)))
    = adicCompletionGalEquiv v σ (u : v.adicCompletion K) from rfl,
    valued_adicCompletionGalEquiv]

/-- Moving a unit of a completion by a Galois automorphism preserves its valuation, divided by a
uniformiser. -/
theorem unitValDiv_adicUnitsGalEquiv (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k))
    (u : (v.adicCompletion K)ˣ) :
    unitValDiv (isUnitValGen_one (valued_adicCompletion_surjective (σ • v)))
        (Additive.ofMul (adicUnitsGalEquiv v σ u))
      = unitValDiv (isUnitValGen_one (valued_adicCompletion_surjective v)) (Additive.ofMul u) := by
  rw [unitValDiv_apply, unitValDiv_apply, unitVal_adicUnitsGalEquiv]

/-- **The value of a unit of a number field at a place is the value of its image under a Galois
automorphism at the image of the place.** -/
theorem placeValue_galSmul (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k)) (a : Kˣ) :
    placeValue (σ • v) (galUnits σ a) = placeValue v a := by
  rw [placeValue_def, placeValue_def, ← adicUnitsGalEquiv_map_algebraMap,
    unitValDiv_adicUnitsGalEquiv]

/-- **The classes modulo `n`-th powers at a place, identified with the classes at the image of the
place** under a Galois automorphism. -/
noncomputable def localClassesGalEquiv (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localClasses v n ≃* localClasses (σ • v) n :=
  QuotientGroup.congr _ _ (adicUnitsGalEquiv v σ) (map_range_powMonoidHom _ n)

/-- The identification of the classes is induced by the map of units. -/
theorem localClassesGalEquiv_mk (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (u : (v.adicCompletion K)ˣ) :
    localClassesGalEquiv σ v n (u : localClasses v n)
      = ((adicUnitsGalEquiv v σ u : ((σ • v).adicCompletion K)ˣ) : localClasses (σ • v) n) := rfl

/-- **The identification of the classes carries the class of a unit of the number field to the
class of the image of that unit.** -/
theorem localClassesGalEquiv_localClassHom (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a : Kˣ) :
    localClassesGalEquiv σ v n (localClassHom v n a) = localClassHom (σ • v) n (galUnits σ a) := by
  refine (QuotientGroup.congr_mk _ _ _ _ _).trans ?_
  congr 1
  ext
  exact adicCompletionGalEquiv_algebraMap v σ (a : K)

/-- **The identification of the classes preserves the valuation modulo `n`.** -/
theorem unitValModQuot_localClassesGalEquiv (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : localClasses v n) :
    unitValModQuot (isUnitValGen_one (valued_adicCompletion_surjective (σ • v))) n
        (localClassesGalEquiv σ v n x)
      = unitValModQuot (isUnitValGen_one (valued_adicCompletion_surjective v)) n x := by
  induction x using QuotientGroup.induction_on with
  | _ u =>
    rw [localClassesGalEquiv_mk, unitValModQuot_mk, unitValModQuot_mk, unitValMod_apply,
      unitValMod_apply, unitValDiv_adicUnitsGalEquiv]

/-- A class is unramified exactly when its image under the identification of the classes is. -/
theorem localClassesGalEquiv_mem_localUnramified_iff (σ : Gal(K/k))
    (v : HeightOneSpectrum (𝓞 K)) (x : localClasses v n) :
    localClassesGalEquiv σ v n x ∈ localUnramified (σ • v) n ↔ x ∈ localUnramified v n := by
  rw [localUnramified, localUnramified, unramifiedClasses, unramifiedClasses,
    MonoidHom.mem_ker, MonoidHom.mem_ker, unitValModQuot_localClassesGalEquiv]

/-- **The identification of the classes carries the unramified classes onto the unramified
classes.** -/
theorem map_localUnramified_localClassesGalEquiv (σ : Gal(K/k))
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup.map (localClassesGalEquiv σ v n).toMonoidHom (localUnramified v n)
      = localUnramified (σ • v) n := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (localClassesGalEquiv_mem_localUnramified_iff σ v x).2 hx
  · intro hy
    refine ⟨(localClassesGalEquiv σ v n).symm y, ?_, by simp⟩
    rw [← localClassesGalEquiv_mem_localUnramified_iff σ v, MulEquiv.apply_symm_apply]
    exact hy

end GaloisAction

end InverseGalois.CFT
