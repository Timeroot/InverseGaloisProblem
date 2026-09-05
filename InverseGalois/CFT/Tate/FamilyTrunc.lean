/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Family

/-!
# Correcting a section on a finite invariant set

A section of a family of abelian groups indexed by a set with an action of a finite group need not
be fixed by the group, but it may fail to be fixed only on a finite set of indices: the difference
between the transported section and the section itself vanishes outside a finite set.  Enlarging
that set to an invariant one and replacing the section by zero on it produces a section that *is*
fixed and differs from the original only on a finite set.

That correction is the mechanism behind the comparison of a product with the restricted product
inside it.  A section of the full product whose class in the quotient by the sections of finite
support is fixed by the group is exactly a section which the group moves only in finitely many
coordinates, and the correction turns it into a genuinely fixed section in the same class.  The
whole content is that a finite union of finite sets is finite and that a section vanishing at an
index has a transport vanishing at the image index.

## Main definitions

* `InverseGalois.CFT.truncOutside`: a section made to vanish on a set.
* `InverseGalois.CFT.finsuppSections`: **the sections vanishing outside a finite set.**

## Main results

* `InverseGalois.CFT.FamilyAction.familyAut_truncOutside`: **a section which the group does not move
  outside an invariant set is fixed once it is made to vanish on that set.**
* `InverseGalois.CFT.FamilyAction.exists_familyAut_invariant_sub_finsupp`: **a section which the
  group moves only in finitely many coordinates differs by a section of finite support from a
  section the group fixes.**

## Tags

family of modules, sections, finite support, restricted product, group action
-/

namespace InverseGalois.CFT

variable {X : Type*} {M : X → Type*} [∀ x, AddCommGroup (M x)]

/-! ### Sections of finite support -/

variable (M) in
/-- **The sections of a family vanishing outside a finite set.** -/
def finsuppSections : AddSubgroup (∀ x, M x) where
  carrier := {f | {x | f x ≠ 0}.Finite}
  add_mem' := fun {f g} hf hg => (hf.union hg).subset fun x hx => by
    rcases eq_or_ne (f x) 0 with h1 | h1
    · rcases eq_or_ne (g x) 0 with h2 | h2
      · exact absurd (show f x + g x = 0 by rw [h1, h2, add_zero]) hx
      · exact Set.mem_union_right _ h2
    · exact Set.mem_union_left _ h1
  zero_mem' := Set.Finite.subset Set.finite_empty fun _ hx => absurd rfl hx
  neg_mem' := fun {f} hf => hf.subset fun x hx hc => hx (show -f x = 0 by rw [hc, neg_zero])

theorem mem_finsuppSections {f : ∀ x, M x} : f ∈ finsuppSections M ↔ {x | f x ≠ 0}.Finite :=
  Iff.rfl

/-! ### Truncating a section on a set -/

open scoped Classical in
/-- **A section made to vanish on a set**: zero at the indices of the set, unchanged at the
others. -/
noncomputable def truncOutside (S : Set X) (f : ∀ x, M x) : ∀ x, M x :=
  fun x => if x ∈ S then 0 else f x

theorem truncOutside_of_mem {S : Set X} {x : X} (hx : x ∈ S) (f : ∀ x, M x) :
    truncOutside S f x = 0 :=
  if_pos hx

theorem truncOutside_of_notMem {S : Set X} {x : X} (hx : x ∉ S) (f : ∀ x, M x) :
    truncOutside S f x = f x :=
  if_neg hx

/-- A section made to vanish on a set differs from the section only on that set. -/
theorem sub_truncOutside_mem_finsuppSections {S : Set X} (hS : S.Finite) (f : ∀ x, M x) :
    f - truncOutside S f ∈ finsuppSections M :=
  hS.subset fun x hx => by
    by_contra hc
    exact hx (show f x - truncOutside S f x = 0 by rw [truncOutside_of_notMem hc, sub_self])

/-! ### The invariant saturation of a finite set -/

variable {G : Type*} [Group G] [MulAction G X]

/-- The indices carried into a set by some element of the group are finite in number when the set
is finite and the group is. -/
theorem finite_saturate [Finite G] {S₀ : Set X} (h : S₀.Finite) :
    {x : X | ∃ g : G, g • x ∈ S₀}.Finite := by
  refine Set.Finite.subset (Set.finite_iUnion fun g : G => h.image fun y => g⁻¹ • y) ?_
  rintro x ⟨g, hg⟩
  exact Set.mem_iUnion.2 ⟨g, ⟨g • x, hg, inv_smul_smul g x⟩⟩

/-- The indices carried into a set by some element of the group form an invariant set. -/
theorem saturate_stable {S₀ : Set X} (h : G) (x : X) :
    h • x ∈ {y : X | ∃ g : G, g • y ∈ S₀} ↔ x ∈ {y : X | ∃ g : G, g • y ∈ S₀} := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g * h, by rwa [mul_smul]⟩
  · rintro ⟨g, hg⟩
    exact ⟨g * h⁻¹, by rwa [mul_smul, inv_smul_smul]⟩

/-! ### The correction -/

namespace FamilyAction

variable (F : FamilyAction M G)

/-- The transport of a section of finite support has finite support. -/
theorem familyAut_mem_finsuppSections (g : G) {f : ∀ x, M x} (hf : f ∈ finsuppSections M) :
    F.familyAut g f ∈ finsuppSections M := by
  refine (hf.image fun y => g • y).subset fun x hx =>
    ⟨g⁻¹ • x, fun hc => hx ?_, smul_inv_smul g x⟩
  rw [F.familyAut_apply_eq_transport (smul_inv_smul g x) f, hc, _root_.map_zero]

/-- **A section which the group does not move outside an invariant set is fixed once it is made to
vanish on that set.**  At an index of the set both the section and its transport vanish, and at an
index off it the transport is the section by hypothesis. -/
theorem familyAut_truncOutside {S : Set X} (hS : ∀ (g : G) (x : X), g • x ∈ S ↔ x ∈ S)
    (f : ∀ x, M x) (g : G) (hf : ∀ x ∉ S, F.familyAut g f x = f x) :
    F.familyAut g (truncOutside S f) = truncOutside S f := by
  funext x
  have hgx : g⁻¹ • x ∈ S ↔ x ∈ S := hS g⁻¹ x
  have key : F.familyAut g (truncOutside S f) x
      = F.transport (smul_inv_smul g x) (truncOutside S f (g⁻¹ • x)) :=
    F.familyAut_apply_eq_transport (smul_inv_smul g x) _
  by_cases hx : x ∈ S
  · rw [key, truncOutside_of_mem (hgx.2 hx) f, _root_.map_zero, truncOutside_of_mem hx]
  · have hgx' : g⁻¹ • x ∉ S := fun hc => hx (hgx.1 hc)
    rw [key, truncOutside_of_notMem hgx' f, truncOutside_of_notMem hx]
    exact (F.familyAut_apply_eq_transport (smul_inv_smul g x) f).symm.trans (hf x hx)

/-- **A section which the group moves only in finitely many coordinates differs by a section of
finite support from a section the group fixes.**  The coordinates moved by any element of the group
form a finite set, its saturation under the group is still finite, and making the section vanish
there leaves a fixed section. -/
theorem exists_familyAut_invariant_sub_finsupp [Finite G] (f : ∀ x, M x)
    (hf : ∀ g : G, F.familyAut g f - f ∈ finsuppSections M) :
    ∃ f' : ∀ x, M x, (∀ g : G, F.familyAut g f' = f') ∧ f - f' ∈ finsuppSections M := by
  have hS₀ : (⋃ g : G, {x | (F.familyAut g f - f) x ≠ 0}).Finite :=
    Set.finite_iUnion fun g => hf g
  refine ⟨truncOutside {x : X | ∃ g : G, g • x ∈ ⋃ g : G, {x | (F.familyAut g f - f) x ≠ 0}} f,
    fun g => F.familyAut_truncOutside (fun h x => saturate_stable h x) f g fun x hx => ?_,
    sub_truncOutside_mem_finsuppSections (finite_saturate hS₀) f⟩
  have hzero : (F.familyAut g f - f) x = 0 := by
    by_contra hc
    exact hx ⟨1, by rw [one_smul]; exact Set.mem_iUnion.2 ⟨g, hc⟩⟩
  rw [Pi.sub_apply, sub_eq_zero] at hzero
  exact hzero

end FamilyAction

end InverseGalois.CFT
