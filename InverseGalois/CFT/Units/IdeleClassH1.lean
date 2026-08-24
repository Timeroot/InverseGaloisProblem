/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleRep
import InverseGalois.CFT.Units.HasseNorm
import InverseGalois.CFT.GroupCohomology.CyclicH1

/-!
# The first cohomology of the idele class group of a cyclic extension

For a cyclic extension of number fields the group `Ĥ⁻¹` of the idele class group is trivial: its
Herbrand quotient is the degree of the extension, and the order of `Ĥ⁰` is the index of the
principal ideles together with the norms, which is the degree as well.  The group `Ĥ⁻¹` is the
kernel of the norm operator modulo the image of `σ - 1` for a generator `σ`, so its vanishing says
exactly that every idele class killed by the norm operator is of the form `σ c - c`.

That is the hypothesis under which the first cohomology of a finite cyclic group vanishes.  The
norm operator of the representation of the Galois group on the idele classes is the Tate norm
operator of a generator, because the powers of a generator below its order run through the group
exactly once, so the two statements match up and the first cohomology of the idele class group
vanishes.

## Main results

* `InverseGalois.CFT.norm_ideleClassRep`: the norm operator of the representation on the idele
  class group is the Tate norm operator of a generator of the Galois group.
* `InverseGalois.CFT.eq_zero_H1_ideleClassRep`: **the first cohomology of the idele class group of
  a cyclic extension of number fields vanishes.**
* `InverseGalois.CFT.subsingleton_H1_ideleClassRep`: the same statement, as a `Subsingleton`
  instance.

## Tags

number field, idele class group, group cohomology, cyclic extension, Tate cohomology
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open IsDedekindDomain NumberField groupCohomology

namespace InverseGalois.CFT

section H1

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

omit [IsGalois k K] in
/-- The norm operator of the representation on the idele class group is the Tate norm operator of
a generator of the Galois group. -/
theorem norm_ideleClassRep {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)
    (a : IdeleClass K) :
    (ideleClassRep k K).ρ.norm a
      = normHom (ideleClassAut (k := k) σ) (Nat.card Gal(K/k)) a := by
  rw [Representation.norm, LinearMap.sum_apply, normHom_apply,
    ← sum_range_card_pow hgen fun g : Gal(K/k) => (ideleClassRep k K).ρ g a]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repOfAddAut_ρ_apply, map_pow]
  rfl

/-- **The first cohomology of the idele class group of a cyclic extension of number fields
vanishes.** -/
theorem eq_zero_H1_ideleClassRep [IsCyclic Gal(K/k)]
    (x : groupCohomology (ideleClassRep k K) 1) : x = 0 := by
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_generator (α := Gal(K/k))
  haveI : NeZero (Nat.card Gal(K/k)) := ⟨Nat.card_pos.ne'⟩
  haveI := subsingleton_tateHm1_ideleClassAut σ (rfl : Nat.card Gal(K/k) = _) hgen
  refine eq_zero_of_ker_norm hgen (fun a ha => ?_) x
  have ha' : normHom (ideleClassAut (k := k) σ) (Nat.card Gal(K/k)) a = 0 := by
    rw [← norm_ideleClassRep hgen]
    exact ha
  exact (tateHm1.mk_eq_zero_iff a ha').mp (Subsingleton.elim _ _)

/-- The first cohomology of the idele class group of a cyclic extension of number fields has at
most one element. -/
instance subsingleton_H1_ideleClassRep [IsCyclic Gal(K/k)] :
    Subsingleton (groupCohomology (ideleClassRep k K) 1) :=
  ⟨fun x y => by rw [eq_zero_H1_ideleClassRep x, eq_zero_H1_ideleClassRep y]⟩

end H1

end InverseGalois.CFT
