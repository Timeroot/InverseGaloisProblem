/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.GlobalClasses
import InverseGalois.CFT.Units.InvariantUniformizer

/-!
# A Galois equivariant line of local classes at every place at once

A prescription allowed to be ramified at a family of places is answered only when the classes
prescribed at a place lie on a single line, and the lines at the places of one orbit have to be
carried into one another by the identification of the classes at a place with the classes at its
image.  Spreading a line named at one place over its orbit asks the orbit to be free, because two
automorphisms carrying the named place to the same place would have to name the same line there.

There is no need to spread anything.  The family of local unit groups carries a Galois invariant
section whose value is a uniformiser at every place carrying one fixed by its decomposition group,
and all but finitely many places carry one; the classes of the values of that section are a line at
every place at once, equivariant on the nose and with no freeness asked of anything.  Its valuation
is one wherever the section is a uniformiser, so a unit of the number field whose class at such a
place is the line there is ramified there, which is the other half of what a prescription ramified
at a place needs.

## Main definitions

* `InverseGalois.CFT.uniformizerSection`: the Galois invariant family of local units.
* `InverseGalois.CFT.uniformizerLine`: **the line of local classes it cuts out at every place.**

## Main results

* `InverseGalois.CFT.localClassesGalEquiv_uniformizerLine`: **the line is Galois equivariant**, the
  line at the image of a place being the image of the line at the place.
* `InverseGalois.CFT.uniformizerLine_zpowers_smul`: the form the two-place construction asks the
  lines in.
* `InverseGalois.CFT.unitValModQuot_uniformizerLine`: at a place carrying a uniformiser fixed by its
  decomposition group the valuation of the line is one.
* `InverseGalois.CFT.not_dvd_placeValue_of_localClassHom_eq_uniformizerLine`: **a unit of the number
  field whose class at such a place is the line there is ramified there.**
* `InverseGalois.CFT.mem_fixedUniformizerPlaces_of_isUnramifiedAt`: an unramified place carries a
  uniformiser fixed by its decomposition group.

## Tags

number field, uniformiser, local class, Galois action, invariant section, ramified
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

noncomputable section

section UniformizerLine

variable (k K : Type) [Field k] [Field K] [Algebra k K] [NumberField K]

/-! ### The invariant section -/

/-- **A Galois invariant family of local units**, of valuation one at every place carrying a
uniformiser fixed by its decomposition group. -/
def uniformizerSection : ∀ v : HeightOneSpectrum (𝓞 K), Additive (v.adicCompletion K)ˣ :=
  (exists_familyAut_eq_self_unitVal_eq_one k K).choose

/-- The family is fixed by the action on the sections of the family of local unit groups. -/
theorem familyAut_uniformizerSection (σ : Gal(K/k)) :
    (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ (uniformizerSection k K)
      = uniformizerSection k K :=
  (exists_familyAut_eq_self_unitVal_eq_one k K).choose_spec.1 σ

variable {k K}

/-- At a place carrying a uniformiser fixed by its decomposition group the family is one. -/
theorem unitVal_uniformizerSection {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ fixedUniformizerPlaces k K) : unitVal (uniformizerSection k K v) = 1 :=
  (exists_familyAut_eq_self_unitVal_eq_one k K).choose_spec.2 v hv

/-- **The value of the family at the image of a place is the image of its value at the place.** -/
theorem uniformizerSection_smul (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) :
    Additive.toMul (uniformizerSection k K (σ • v))
      = adicUnitsGalEquiv v σ (Additive.toMul (uniformizerSection k K v)) := by
  have h := congrFun (familyAut_uniformizerSection k K σ) (σ • v)
  rw [FamilyAction.familyAut_apply_smul] at h
  exact congrArg Additive.toMul h.symm

/-- The valuation of the family at a place carrying a uniformiser fixed by its decomposition group,
divided by the chosen generator of the value group. -/
theorem unitValDiv_uniformizerSection {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ fixedUniformizerPlaces k K) :
    unitValDiv (isUnitValGen_one (valued_adicCompletion_surjective v))
      (uniformizerSection k K v) = 1 := by
  rw [unitValDiv_apply, unitVal_uniformizerSection hv]
  norm_num

/-! ### The line -/

variable (k) in
/-- **The line of local classes cut out by the invariant family of uniformisers**: at every place,
the class modulo `n`-th powers of the value of the family there. -/
def uniformizerLine (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : localClasses v n :=
  ((Additive.toMul (uniformizerSection k K v) : (v.adicCompletion K)ˣ) : localClasses v n)

/-- **The line is Galois equivariant**: the line at the image of a place is the image of the line at
the place, because the invariant family has that property already. -/
theorem localClassesGalEquiv_uniformizerLine (n : ℕ) (σ : Gal(K/k))
    (v : HeightOneSpectrum (𝓞 K)) :
    localClassesGalEquiv σ v n (uniformizerLine k n v) = uniformizerLine k n (σ • v) :=
  (localClassesGalEquiv_mk σ v n (Additive.toMul (uniformizerSection k K v))).trans
    (congrArg (fun u : ((σ • v).adicCompletion K)ˣ => (u : localClasses (σ • v) n))
      (uniformizerSection_smul σ v).symm)

/-- **The line at the image of a place is the image of the line at the place**, which is the form
the construction of a family of two places asks the lines in. -/
theorem uniformizerLine_zpowers_smul (n : ℕ) (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup.zpowers (uniformizerLine k n (σ • v))
      = Subgroup.zpowers (localClassesGalEquiv σ v n (uniformizerLine k n v)) := by
  rw [localClassesGalEquiv_uniformizerLine]

/-- **At a place carrying a uniformiser fixed by its decomposition group the valuation of the line
is one.** -/
theorem unitValModQuot_uniformizerLine (n : ℕ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ fixedUniformizerPlaces k K) :
    unitValModQuot (isUnitValGen_one (valued_adicCompletion_surjective v)) n
        (uniformizerLine k n v) = Multiplicative.ofAdd (((1 : ℤ) : ZMod n)) := by
  have h : unitValModQuot (isUnitValGen_one (valued_adicCompletion_surjective v)) n
      (uniformizerLine k n v)
      = Multiplicative.ofAdd ((unitValDiv (isUnitValGen_one
          (valued_adicCompletion_surjective v)) (uniformizerSection k K v) : ℤ) : ZMod n) := rfl
  rw [h, unitValDiv_uniformizerSection hv]

/-! ### A unit carrying the line is ramified -/

variable {n : ℕ}

/-- **A unit of the number field whose class at a place carrying a uniformiser fixed by its
decomposition group is the line there has value at that place congruent to one**, the valuation of
the line being one. -/
theorem placeValue_modEq_of_localClassHom_eq_uniformizerLine {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ fixedUniformizerPlaces k K) {a : Kˣ}
    (ha : localClassHom v n a = uniformizerLine k n v) :
    placeValue v a ≡ 1 [ZMOD (n : ℤ)] := by
  have hval := congrArg
    (unitValModQuot (isUnitValGen_one (valued_adicCompletion_surjective v)) n) ha
  rw [unitValModQuot_localClassHom, unitValModQuot_uniformizerLine n hv,
    Equiv.apply_eq_iff_eq] at hval
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hval

/-- **A unit of the number field whose class at a place carrying a uniformiser fixed by its
decomposition group is the line there is ramified there.** -/
theorem not_dvd_placeValue_of_localClassHom_eq_uniformizerLine (hn : 1 < n)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ fixedUniformizerPlaces k K) {a : Kˣ}
    (ha : localClassHom v n a = uniformizerLine k n v) : ¬ (n : ℤ) ∣ placeValue v a := by
  intro hdvd
  have hone : (n : ℤ) ∣ 1 := by
    simpa using dvd_add (placeValue_modEq_of_localClassHom_eq_uniformizerLine hv ha).dvd hdvd
  have hle := Int.le_of_dvd one_pos hone
  omega

end UniformizerLine

/-! ### Where the line is a uniformiser -/

section Unramified

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **A place unramified over the base carries a uniformiser fixed by its decomposition group**, so
the line there is the class of a uniformiser. -/
theorem mem_fixedUniformizerPlaces_of_isUnramifiedAt {v : HeightOneSpectrum (𝓞 K)}
    (h : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal) : v ∈ fixedUniformizerPlaces k K :=
  mem_fixedUniformizerPlaces_of_exists (exists_fixedUniformizer_of_isUnramifiedAt (k := k) v h)

end Unramified

end

end InverseGalois.CFT
