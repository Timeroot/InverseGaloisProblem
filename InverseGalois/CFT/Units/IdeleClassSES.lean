/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleClassH1Full

/-!
# The short exact sequence of units, ideles and idele classes

The units of a number field sit inside its ideles as the principal ideles, and the quotient is the
idele class group.  All three carry an action of the Galois group of the field over a base field,
and both maps are equivariant, so the three representations form a short exact sequence in the
category of representations of the Galois group.

The long exact cohomology sequence attached to it reads
`H¹(G, C) ⟶ H²(G, Kˣ) ⟶ H²(G, I)`, and the first term vanishes for every Galois extension of
number fields.  Consequently the second cohomology of the units injects into the second cohomology
of the ideles: a class of the Brauer group split by the extension is determined by its local
components.  This is the global half of the Albert–Brauer–Hasse–Noether theorem.

## Main definitions

* `InverseGalois.CFT.globalUnitsToIdele`: the principal ideles, as a map of representations.
* `InverseGalois.CFT.ideleToIdeleClass`: the passage to idele classes, as a map of
  representations.
* `InverseGalois.CFT.ideleClassShortComplex`: the three representations, assembled into a short
  complex.

## Main results

* `InverseGalois.CFT.ideleClassShortComplex_shortExact`: **the units, the ideles and the idele
  classes form a short exact sequence of representations of the Galois group.**
* `InverseGalois.CFT.mono_map_H2_globalUnits`, `InverseGalois.CFT.injective_map_H2_globalUnits`:
  **the second cohomology of the units injects into the second cohomology of the ideles.**

## Tags

number field, idele, idele class group, group cohomology, short exact sequence, Brauer group
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory groupCohomology

namespace InverseGalois.CFT

section SES

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The principal ideles, as a map of representations of the Galois group: an automorphism acts on
a principal idele through its action on the corresponding unit. -/
noncomputable def globalUnitsToIdele : globalUnitsRep k K ⟶ ideleRep k K where
  hom := ModuleCat.ofHom (ideleDiag K).toIntLinearMap
  comm := fun g => by
    ext a
    exact (ideleAut_ideleDiag g a).symm

/-- The passage to idele classes, as a map of representations of the Galois group. -/
noncomputable def ideleToIdeleClass : ideleRep k K ⟶ ideleClassRep k K where
  hom := ModuleCat.ofHom (QuotientAddGroup.mk' (ideleDiag K).range).toIntLinearMap
  comm := fun g => by
    ext a
    rfl

/-- The units, the ideles and the idele classes, assembled into a short complex of representations
of the Galois group. -/
noncomputable def ideleClassShortComplex : ShortComplex (Rep ℤ Gal(K/k)) where
  X₁ := globalUnitsRep k K
  X₂ := ideleRep k K
  X₃ := ideleClassRep k K
  f := globalUnitsToIdele k K
  g := ideleToIdeleClass k K
  zero := by
    ext a
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨a, rfl⟩

omit [NumberField k] in
/-- **The units, the ideles and the idele classes form a short exact sequence of representations of
the Galois group.**  The principal ideles are a copy of the units, and the idele class group is by
definition the quotient of the ideles by them. -/
theorem ideleClassShortComplex_shortExact : (ideleClassShortComplex k K).ShortExact where
  exact := (forget₂ _ (ModuleCat ℤ)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun _ hx =>
      (QuotientAddGroup.eq_zero_iff _).1 hx
  mono_f := (Rep.mono_iff_injective _).2 (ideleDiag_injective K)
  epi_g := (Rep.epi_iff_surjective _).2 QuotientAddGroup.mk_surjective

variable [IsGalois k K]

/-- **The second cohomology of the units injects into the second cohomology of the ideles.**  The
long exact sequence of the short exact sequence of units, ideles and idele classes begins with the
first cohomology of the idele classes, which vanishes. -/
theorem mono_map_H2_globalUnits :
    Mono ((groupCohomology.functor ℤ Gal(K/k) 2).map (globalUnitsToIdele k K)) := by
  have hX := ideleClassShortComplex_shortExact k K
  have hf : (mapShortComplex₁ hX (i := 1) (j := 2) rfl).f = 0 := by
    ext x
    rw [show x = 0 from eq_zero_H1_ideleClassRep_general x]
    simp
  exact (ShortComplex.exact_iff_mono _ hf).1 (mapShortComplex₁_exact hX rfl)

/-- **The second cohomology of the units injects into the second cohomology of the ideles**, stated
as injectivity of the underlying map. -/
theorem injective_map_H2_globalUnits :
    Function.Injective
      ((groupCohomology.functor ℤ Gal(K/k) 2).map (globalUnitsToIdele k K)).hom := by
  haveI := mono_map_H2_globalUnits k K
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

end SES

end InverseGalois.CFT
