/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Krull

/-!
# The finite Galois level an open normal subgroup fixes

The finite Galois levels of an infinite Galois extension are cofinal among the open normal
subgroups of its Galois group, and in fact each open normal subgroup *is* the subgroup fixing one
of them: an open subgroup of a topological group is closed, so the Galois correspondence for the
Krull topology returns it from the subfield it fixes, and that subfield is finite over the base
because the subgroup is open and Galois over it because the subgroup is normal.

Over a number field the level is again a number field, which is not something the instance search
finds on its own: the algebra structure of an intermediate field over the base competes with the
one every field of characteristic zero carries over the rationals, and the search settles on the
wrong one.  Stating the passage with an opaque base field and instantiating it afterwards avoids
the competition.

## Main results

* `InverseGalois.CFT.exists_level_fixingSubgroup_eq`: **an open normal subgroup of the Galois group
  of an infinite Galois extension is the subgroup fixing a finite Galois level.**
* `InverseGalois.CFT.numberField_of_finiteDimensional`: a finite subextension of an extension of a
  number field is a number field.

## Tags

infinite Galois theory, Krull topology, level, open normal subgroup, number field
-/

namespace InverseGalois.CFT

open NumberField

/-! ### The level -/

section Level

/-- **An open normal subgroup of the Galois group of an infinite Galois extension is the subgroup
fixing a finite Galois level.**  An open subgroup of a topological group is closed, so the Galois
correspondence for the Krull topology returns it from the subfield it fixes; that subfield is
finite over the base because the subgroup is open, and Galois over it because the subgroup is
normal. -/
theorem exists_level_fixingSubgroup_eq {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsGalois k K] {N : Subgroup Gal(K/k)} (hN : IsOpenNormal N) :
    ∃ E : IntermediateField k K, FiniteDimensional k ↥E ∧ IsGalois k ↥E ∧
      E.fixingSubgroup = N ∧ ∀ x : K, (∀ σ ∈ N, σ x = x) → x ∈ E := by
  haveI : N.Normal := hN.normal
  have hfix : (IntermediateField.fixedField N).fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, Subgroup.isClosed_of_isOpen N hN.isOpen⟩
  refine ⟨IntermediateField.fixedField N, ?_, ?_, hfix, ?_⟩
  · exact (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfix]; exact hN.isOpen)
  · exact (InfiniteGalois.normal_iff_isGalois _).1 (by rw [hfix]; exact hN.normal)
  · intro x hx
    exact (IntermediateField.mem_fixedField_iff N x).2 hx

/-- A finite subextension of an extension of a number field is a number field. -/
theorem numberField_of_finiteDimensional {k Ω : Type*} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (E : IntermediateField k Ω) [FiniteDimensional k ↥E] : NumberField ↥E :=
  NumberField.of_module_finite k ↥E

end Level

end InverseGalois.CFT
