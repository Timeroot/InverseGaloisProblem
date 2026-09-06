/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Shifting

/-!
# The two defining sequences are split as sequences of modules

The two short exact sequences that define the shift and the coshift of a representation are split
once the action is forgotten.  For the sequence defining the coshift, a vector placed at the unit of
the group is a section of the summation map, and subtracting the vector so placed at the unit
retracts the functions on the group onto the kernel of that map.  For the sequence defining the
shift, the value at the unit of the group retracts the record of all the translates, and subtracting
the record of all the translates of that value is a projection which kills the translates and
therefore descends to a section of the passage to the quotient.

Neither splitting is equivariant, and neither can be: an equivariant splitting would make the
complete cohomology of the representation a summand of that of the functions on the group, which
vanishes.  What the splittings give is the hypothesis needed by the two comparisons of a sequence
with the sequences defining the shift and the coshift, and those comparisons are what remove a
connecting map.

## Main definitions

* `InverseGalois.CFT.Tate.deltaOne`: a vector, placed at the unit of the group.
* `InverseGalois.CFT.Tate.augRetract`: the retraction of the functions on the group onto the kernel
  of the summation map.
* `InverseGalois.CFT.Tate.shiftSection`: the section of the passage to the shift.

## Main results

* `InverseGalois.CFT.Tate.augMap_deltaOne`: **a vector placed at the unit of the group sums to that
  vector.**
* `InverseGalois.CFT.Tate.coshiftSeq_hom_deltaOne` and
  `InverseGalois.CFT.Tate.augRetract_coshiftSeq_f`: **the sequence defining the coshift is split
  as a sequence of modules.**
* `InverseGalois.CFT.Tate.shiftSeq_hom_shiftSection` and
  `InverseGalois.CFT.Tate.coindRetract_shiftSeq_f`: **the sequence defining the shift is split as a
  sequence of modules.**

## Tags

Tate cohomology, dimension shifting, split extension, induced representation
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### A vector placed at the unit of the group -/

section Single

variable (k G : Type*) {V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

open scoped Classical in
/-- **A vector, placed at the unit of the group.** -/
def deltaOne : V →ₗ[k] (G → V) := LinearMap.single k (fun _ : G => V) 1

/-- **The value of a function at the unit of the group.** -/
def coindRetract : (G → V) →ₗ[k] V := LinearMap.proj (1 : G)

variable {k G}

theorem coindRetract_apply (f : G → V) : coindRetract k G f = f 1 := rfl

open scoped Classical in
theorem deltaOne_apply_one (v : V) : deltaOne k G v (1 : G) = v :=
  Pi.single_eq_same (M := fun _ : G => V) (1 : G) v

open scoped Classical in
theorem deltaOne_apply_of_ne {x : G} (hx : x ≠ 1) (v : V) : deltaOne k G v x = 0 :=
  Pi.single_eq_of_ne (M := fun _ : G => V) hx v

variable [Finite G] (ρ : Representation k G V)

/-- **A vector placed at the unit of the group sums to that vector.** -/
theorem augMap_deltaOne (v : V) : augMap ρ (deltaOne k G v) = v := by
  letI := Fintype.ofFinite G
  rw [augMap_apply, Finset.sum_eq_single (1 : G)]
  · rw [deltaOne_apply_one, inv_one, map_one]
    rfl
  · intro x _ hx
    rw [deltaOne_apply_of_ne hx, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Single

/-! ### The sequence defining the coshift -/

section Coshift

variable {k G V : Type*} [CommRing k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- **Subtracting the sum of a function, placed at the unit of the group.** -/
def augProj : (G → V) →ₗ[k] (G → V) :=
  LinearMap.id (R := k) (M := G → V) - deltaOne k G ∘ₗ augMap ρ

omit [Finite G] in
theorem augProj_apply (f : G → V) : augProj ρ f = f - deltaOne k G (augMap ρ f) := rfl

theorem augMap_augProj (f : G → V) : augMap ρ (augProj ρ f) = 0 := by
  rw [augProj_apply, map_sub, augMap_deltaOne, sub_self]

/-- **The retraction of the functions on the group onto the kernel of the summation map.** -/
def augRetract : (G → V) →ₗ[k] ↥(LinearMap.ker (augMap ρ)) :=
  LinearMap.codRestrict _ (augProj ρ) fun f => LinearMap.mem_ker.2 (augMap_augProj ρ f)

/-- **The retraction onto the kernel of the summation map is a retraction.** -/
theorem augRetract_subtype (w : ↥(LinearMap.ker (augMap ρ))) :
    augRetract ρ ((LinearMap.ker (augMap ρ)).subtype w) = w := by
  refine Subtype.ext ?_
  show augProj ρ (w : G → V) = (w : G → V)
  rw [augProj_apply, LinearMap.mem_ker.1 w.2, map_zero, sub_zero]

end Coshift

/-! ### The sequence defining the shift -/

section Shift

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- **The value at the unit of the group of the record of all the translates of a vector is that
vector.** -/
theorem coindRetract_coindEmb (v : V) : coindRetract k G (coindEmb ρ v) = v := by
  rw [coindRetract_apply, coindEmb_apply, map_one]
  rfl

/-- **Subtracting the record of all the translates of the value at the unit of the group.** -/
def coindProj : (G → V) →ₗ[k] (G → V) :=
  LinearMap.id (R := k) (M := G → V) - coindEmb ρ ∘ₗ coindRetract k G

theorem coindProj_apply (f : G → V) : coindProj ρ f = f - coindEmb ρ (f 1) := rfl

theorem coindProj_coindEmb (v : V) : coindProj ρ (coindEmb ρ v) = 0 := by
  rw [coindProj_apply, coindEmb_apply, map_one]
  exact sub_eq_zero_of_eq rfl

/-- **The section of the passage to the shift.** -/
def shiftSection : ((G → V) ⧸ LinearMap.range (coindEmb ρ)) →ₗ[k] (G → V) :=
  Submodule.liftQ _ (coindProj ρ) (by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.mem_ker.2 (coindProj_coindEmb ρ v))

theorem shiftSection_mkQ (f : G → V) :
    shiftSection ρ ((LinearMap.range (coindEmb ρ)).mkQ f) = f - coindEmb ρ (f 1) := rfl

/-- **The section of the passage to the shift is a section.** -/
theorem mkQ_shiftSection (w : (G → V) ⧸ LinearMap.range (coindEmb ρ)) :
    (LinearMap.range (coindEmb ρ)).mkQ (shiftSection ρ w) = w := by
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb ρ)) w
  rw [shiftSection_mkQ]
  refine (Submodule.Quotient.eq _).2 ?_
  rw [sub_sub_cancel_left]
  exact ⟨-f 1, map_neg _ _⟩

end Shift

/-! ### The two splittings, for the two sequences -/

section Seq

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G)

/-- **A vector placed at the unit of the group is a section of the sequence defining the
coshift.** -/
theorem coshiftSeq_hom_deltaOne (v : ↥(coshiftSeq A).X₃.V) :
    (coshiftSeq A).g.hom.hom (deltaOne k G v) = v :=
  augMap_deltaOne A.ρ v

/-- **The kernel of the summation map is a summand of the functions on the group.** -/
theorem augRetract_coshiftSeq_f (a : ↥(coshiftSeq A).X₁.V) :
    augRetract A.ρ ((coshiftSeq A).f.hom.hom a) = a :=
  augRetract_subtype A.ρ a

omit [Finite G] in
/-- **The section of the passage to the shift is a section of the sequence defining the shift.** -/
theorem shiftSeq_hom_shiftSection (w : ↥(shiftSeq A).X₃.V) :
    (shiftSeq A).g.hom.hom (shiftSection A.ρ w) = w :=
  mkQ_shiftSection A.ρ w

omit [Finite G] in
/-- **A representation is a summand of the functions on the group with its values.** -/
theorem coindRetract_shiftSeq_f (a : ↥(shiftSeq A).X₁.V) :
    coindRetract k G ((shiftSeq A).f.hom.hom a) = a :=
  coindRetract_coindEmb A.ρ a

end Seq

end

end InverseGalois.CFT.Tate
