import Mathlib
import InverseGalois.CFT.Local.Exp
import InverseGalois.CFT.Local.UnitFiltration

/-!
# Restricting a valuation to a subfield

A subfield of a valued field carries the restricted valuation, and the topology it induces is the
subspace topology.  This file builds that structure and records the properties that descend along
it: completeness, when the subfield is closed; the residue characteristic; and the finiteness of
the graded pieces of the additive filtration.

The construction is phrased for an arbitrary algebra map `S → A` rather than for a literal
subfield, so that it applies verbatim to an intermediate field of an extension, whose coercion to
`A` is an algebra map and not a subtype inclusion.

The valuation is restricted *without renormalisation*: the value group of `S` is a subgroup of the
value group of `A`, generally a proper one.  This keeps the residue characteristic datum of `A`
literally unchanged on `S`, which is what makes the descent usable in an induction that shrinks the
field.

## Main definitions

* `InverseGalois.CFT.subValued`: the valued field structure on `S` restricted from `A`.
* `InverseGalois.CFT.IsValuedExtension`: the compatibility of two valued field structures along an
  algebra map — the valuation is preserved, and the uniformity is induced.

## Main results

* `InverseGalois.CFT.isValuedExtension_subValued`: the restricted structure is compatible.
* `InverseGalois.CFT.IsValuedExtension.completeSpace`: a closed subfield of a complete valued field
  is complete.
* `InverseGalois.CFT.IsValuedExtension.hasResidueChar`: the residue characteristic datum descends.
* `InverseGalois.CFT.IsValuedExtension.finite_gradedAdd`: the graded pieces of the additive
  filtration descend.

## Tags

valuation, subfield, restricted valuation, complete field, residue characteristic
-/

namespace InverseGalois.CFT

open scoped WithZero
open Topology

/-! ### The restricted structure -/

/-- The uniformity induced on a field by an algebra map to a valued field. -/
def subUniformSpace (S A : Type*) [Field S] [Field A] [Valued A ℤᵐ⁰] [Algebra S A] :
    UniformSpace S :=
  UniformSpace.comap (algebraMap S A) inferInstance

/-- The algebra map is uniform inducing for the induced uniformity, by construction. -/
theorem isUniformInducing_algebraMap (S A : Type*) [Field S] [Field A] [Valued A ℤᵐ⁰]
    [Algebra S A] : @IsUniformInducing S A (subUniformSpace S A) _ (algebraMap S A) :=
  @IsUniformInducing.mk S A (subUniformSpace S A) _ _ rfl

/-- **A field mapping to a valued field is a valued field**, for the restricted valuation and the
induced uniformity: the balls of the restricted valuation are exactly the preimages of the balls
downstairs. -/
def subValued (S A : Type*) [Field S] [Field A] [Valued A ℤᵐ⁰] [Algebra S A] : Valued S ℤᵐ⁰ :=
  letI u : UniformSpace S := subUniformSpace S A
  { toUniformSpace := u
    toIsUniformAddGroup := IsUniformAddGroup.comap (algebraMap S A)
    v := (Valued.v : Valuation A ℤᵐ⁰).comap (algebraMap S A)
    is_topological_valuation := by
      intro s
      have hind : @IsInducing S A _ _ (algebraMap S A) :=
        (isUniformInducing_algebraMap S A).isInducing
      rw [hind.nhds_eq_comap, map_zero, Filter.mem_comap]
      constructor
      · rintro ⟨t, ht, hts⟩
        obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation t).mp ht
        exact ⟨γ, fun x hx => hts (hγ hx)⟩
      · rintro ⟨γ, hγ⟩
        exact ⟨{x : A | Valued.v x < γ},
          (Valued.is_topological_valuation _).mpr ⟨γ, subset_rfl⟩, hγ⟩ }

/-! ### The interface -/

/-- **A valued field extension**: the valuation of the larger field restricts to that of the
smaller one, and the uniformity of the smaller one is the induced one.  These are the two
properties of the restricted structure that the descent arguments use. -/
structure IsValuedExtension (S A : Type*) [Field S] [Field A] [Valued S ℤᵐ⁰] [Valued A ℤᵐ⁰]
    [Algebra S A] : Prop where
  /-- The valuation of the larger field restricts to that of the smaller one. -/
  val_algebraMap (x : S) : Valued.v (algebraMap S A x) = Valued.v x
  /-- The uniformity of the smaller field is induced from the larger one. -/
  isUniformInducing : IsUniformInducing (algebraMap S A)

/-- The restricted valued field structure is a valued field extension. -/
theorem isValuedExtension_subValued (S A : Type*) [Field S] [Field A] [Valued A ℤᵐ⁰]
    [Algebra S A] : @IsValuedExtension S A _ _ (subValued S A) _ _ :=
  @IsValuedExtension.mk S A _ _ (subValued S A) _ _ (fun _ => rfl)
    (isUniformInducing_algebraMap S A)

/-! ### What descends -/

variable {S A : Type*} [Field S] [Field A] [Valued S ℤᵐ⁰] [Valued A ℤᵐ⁰] [Algebra S A]

namespace IsValuedExtension

variable (h : IsValuedExtension S A)

include h

/-- **A closed subfield of a complete valued field is complete.** -/
theorem completeSpace [CompleteSpace A] (hclosed : IsClosed (Set.range (algebraMap S A))) :
    CompleteSpace S :=
  h.isUniformInducing.completeSpace hclosed.isComplete

/-- **The residue characteristic datum descends** to a subfield, with the same ramification index:
the valuation is restricted and not renormalised, so the valuation of the residue characteristic is
literally unchanged. -/
theorem hasResidueChar {p e : ℕ} (hA : HasResidueChar A p e) : HasResidueChar S p e where
  prime := hA.prime
  pos := hA.pos
  val_p := by rw [← h.val_algebraMap, map_natCast]; exact hA.val_p

/-- An element of a step of the additive filtration of a subfield lands in the corresponding step
downstairs. -/
theorem map_mem_valAddSubgroup {k : ℤ} {x : S} (hx : x ∈ valAddSubgroup S k) :
    algebraMap S A x ∈ valAddSubgroup A k := by
  rw [mem_valAddSubgroup, h.val_algebraMap]
  exact hx

/-- The map from a step of the additive filtration of a subfield to the corresponding graded piece
downstairs. -/
def toGradedAdd (k : ℤ) : ↥(valAddSubgroup S k) →+ gradedAdd A k :=
  (QuotientAddGroup.mk' _).comp
    { toFun := fun x => ⟨algebraMap S A x, h.map_mem_valAddSubgroup x.2⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }

/-- **The graded pieces of the additive filtration inject into those of the larger field**: an
element of a step of the filtration upstairs lies in the next step exactly when its image does. -/
theorem toGradedAdd_eq_zero_iff (k : ℤ) (x : ↥(valAddSubgroup S k)) :
    h.toGradedAdd k x = 0 ↔ (x : S) ∈ valAddSubgroup S (k + 1) := by
  rw [toGradedAdd]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, QuotientAddGroup.mk'_apply,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, mem_valAddSubgroup, h.val_algebraMap]

/-- **Finiteness of the graded pieces of the additive filtration descends** to a subfield. -/
theorem finite_gradedAdd [∀ k : ℤ, Finite (gradedAdd A k)] (k : ℤ) : Finite (gradedAdd S k) := by
  have hker : ∀ x : ↥(valAddSubgroup S k),
      x ∈ (valAddSubgroup S (k + 1)).addSubgroupOf (valAddSubgroup S k) →
        h.toGradedAdd k x = 0 := fun x hx => (h.toGradedAdd_eq_zero_iff k x).mpr hx
  refine Finite.of_injective (QuotientAddGroup.lift _ (h.toGradedAdd k) hker) ?_
  intro a b hab
  induction a using QuotientAddGroup.induction_on with
  | H x =>
    induction b using QuotientAddGroup.induction_on with
    | H y =>
      rw [QuotientAddGroup.lift_mk, QuotientAddGroup.lift_mk] at hab
      refine QuotientAddGroup.eq.mpr ?_
      have hsub : h.toGradedAdd k (-x + y) = 0 := by rw [map_add, map_neg, hab, neg_add_cancel]
      exact (h.toGradedAdd_eq_zero_iff k (-x + y)).mp hsub

end IsValuedExtension

end InverseGalois.CFT
