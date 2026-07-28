/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Family-agnostic primitivity of the geometric monodromy action

This file collects **reusable, polynomial-parameterized** lemmas that reduce the
*preprimitivity* of the Galois action on the roots of a separable polynomial to a single, sharp
field-theoretic statement — that a root generates an **atom** in the lattice of intermediate
fields (equivalently: `K(α)/K` has no proper intermediate subfield).

It is a direct generalization of the `Sₙ`-specific chain in
`InverseGalois/Hilbert/Analytic/NewtonPuiseux.lean`
(`morseGeomPoly_stabilizer_isCoatom`, `morseGeomPoly_primitive`), with the `morseGeomPoly`
family replaced by an *arbitrary* monic separable polynomial `p : K[X]`.  The point of the
generalization is the long-term **rigidity method** goal: every application of rigidity needs the
step "geometric monodromy is primitive", and everything here except the atom hypothesis is
family-independent Galois-correspondence bookkeeping.

## Main results

* `Primitivity.isCoatom_fixingSubgroup_iff_isAtom` — Galois correspondence: an intermediate field
  is an atom iff its fixing subgroup is a coatom.
* `Primitivity.stabilizer_isCoatom_of_isAtom` — if `K(α)` is an atom, the stabilizer of the root
  `α` in `p.Gal` is a coatom (maximal subgroup).
* `Primitivity.galAction_isPreprimitive_of_isAtom` — if every root generates an atom, the
  `p.Gal`-action on the root set is preprimitive.
* `Primitivity.galActionHom_range_isPreprimitive_of_isAtom` — the same conclusion transported to
  the **image** subgroup `(galActionHom p _).range ≤ Equiv.Perm (rootSet)`, which is the shape the
  monodromy applications need.

## The atom hypothesis

The atom hypothesis `IsAtom (IntermediateField.adjoin K {α})` is the *only* input that is genuinely
family-specific.  For a polynomial whose root field is a **rational** function field it follows from
Lüroth + indecomposability (`RittComposition.isCoatom_adjoin_of_indecomposable`, used in the `Sₙ`
Morse stack).  For families whose root field is the function field of a curve of **positive genus**
(e.g. the Serre `Aₙ` family, where the parameter enters quadratically) Lüroth does *not* apply and
the atom statement must be established by other means; see the discussion in
`AlternatingFamilyMonodromy`.
-/

open Polynomial

noncomputable section

namespace InverseGalois.Primitivity

open scoped Classical

/-- `Fact` instance: any polynomial splits in its own splitting field (needed so that
`Gal.galAction`/`Gal.galActionHom` over the splitting field typecheck). -/
local instance splitsInSplittingField (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

variable {K : Type*} [Field K]

/-- **[Galois correspondence, general]** For a finite-dimensional Galois extension `E/F`, an
intermediate field `M` is an atom (covers `⊥`) iff its fixing subgroup is a coatom (a maximal
proper subgroup).  This is the order-reversing Galois correspondence combined with the fact that an
order isomorphism onto an order dual sends atoms to coatoms.  (Generalized verbatim from
`NewtonPuiseux.isCoatom_fixingSubgroup_iff_isAtom`.) -/
theorem isCoatom_fixingSubgroup_iff_isAtom {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (M : IntermediateField F E) :
    IsCoatom M.fixingSubgroup ↔ IsAtom M :=
  OrderIso.isAtom_iff (IsGalois.intermediateFieldEquivSubgroup) M

/-- **[general]** The restriction endomorphism `Gal.restrict p SF : p.Gal →* p.Gal` (to the
splitting field itself) is bijective: surjective by normality (`Gal.restrict_surjective`), hence
also injective on the finite group `p.Gal`. -/
theorem restrict_bijective (p : K[X]) :
    Function.Bijective (Gal.restrict p p.SplittingField) :=
  ⟨Finite.injective_iff_surjective.mpr (Gal.restrict_surjective _ _),
    Gal.restrict_surjective _ _⟩

/-- **[general]** The stabilizer of a root `a` under the Galois action is the image, under the
bijective restriction endomorphism `Gal.restrict p SF`, of the fixing subgroup of the intermediate
field `K(a)` it generates.  (For `E = SF`, Mathlib's `Gal.galAction` is routed through the
conjugating bijection `rootsEquivRoots`, so the stabilizer is a `Gal.restrict`-image of the fixing
subgroup rather than the fixing subgroup itself; since `Gal.restrict p SF` is an automorphism this
does not affect `IsCoatom`.)  Generalized from
`NewtonPuiseux.morseGeomPoly_stabilizer_eq_map_fixingSubgroup`. -/
theorem stabilizer_eq_map_fixingSubgroup (p : K[X])
    (a : p.rootSet p.SplittingField) :
    (@MulAction.stabilizer p.Gal (↑(p.rootSet p.SplittingField)) _
      (Gal.galAction p p.SplittingField) a)
      = Subgroup.map (Gal.restrict p p.SplittingField)
          (IntermediateField.fixingSubgroup
            (IntermediateField.adjoin K {(↑a : p.SplittingField)})) := by
  refine le_antisymm ?_ ?_ <;> intro x hx <;> simp_all [Subgroup.mem_map]
  · obtain ⟨y, hy⟩ := (restrict_bijective p).surjective x
    refine ⟨y, ?_, hy⟩
    intro x hx
    induction hx using IntermediateField.adjoin_induction
    · replace hx := congr_arg Subtype.val hx
      aesop
    · exact y.commutes _
    · aesop
    · rw [map_inv₀, ‹y _ = _›]
    · aesop
  · obtain ⟨y, hy, rfl⟩ := hx
    rw [← Subtype.coe_inj]
    simp [Gal.restrict_smul]
    exact hy _ <| IntermediateField.subset_adjoin K _ <| Set.mem_singleton _

/-- **[general]** If the root `a` generates an atom `K(a)` in the intermediate-field lattice, then
the stabilizer of `a` under the `p.Gal`-action is a coatom (maximal subgroup).  Requires `p`
separable (so `SF/K` is Galois).  Generalized from `NewtonPuiseux.morseGeomPoly_stabilizer_isCoatom`. -/
theorem stabilizer_isCoatom_of_isAtom (p : K[X]) (hsep : p.Separable)
    (a : p.rootSet p.SplittingField)
    (hatom : IsAtom (IntermediateField.adjoin K {(↑a : p.SplittingField)})) :
    IsCoatom (@MulAction.stabilizer p.Gal (↑(p.rootSet p.SplittingField)) _
      (Gal.galAction p p.SplittingField) a) := by
  haveI : IsGalois K p.SplittingField := IsGalois.of_separable_splitting_field hsep
  rw [stabilizer_eq_map_fixingSubgroup p a]
  -- `Gal.restrict` is a bijective group endomorphism, so `Subgroup.map` by it is an order
  -- isomorphism of the subgroup lattice, preserving `IsCoatom`.
  let Re : p.Gal ≃* p.Gal := MulEquiv.ofBijective _ (restrict_bijective p)
  have key : IsCoatom (Subgroup.map (Re : p.Gal →* p.Gal)
        (IntermediateField.fixingSubgroup
          (IntermediateField.adjoin K {(↑a : p.SplittingField)})))
      ↔ IsAtom (IntermediateField.adjoin K {(↑a : p.SplittingField)}) := by
    rw [← MulEquiv.mapSubgroup_apply, (Re.mapSubgroup).isCoatom_iff,
        isCoatom_fixingSubgroup_iff_isAtom]
  exact key.mpr hatom

/-- **[general — the reduction]** If `p` is separable and irreducible, the root set is nontrivial,
and **every** root generates an atom `K(α)`, then the `p.Gal`-action on the root set is
preprimitive.  Generalized from `NewtonPuiseux.morseGeomPoly_primitive`.

The action is pretransitive (`Gal.galAction_isPretransitive` from irreducibility) on a nontrivial
set, so a maximal point-stabilizer (`stabilizer_isCoatom_of_isAtom`) makes the action preprimitive
via `MulAction.isCoatom_stabilizer_iff_preprimitive`. -/
theorem galAction_isPreprimitive_of_isAtom (p : K[X]) (hsep : p.Separable)
    (hirr : Irreducible p) (hnt : Nontrivial (p.rootSet p.SplittingField))
    (hatom : ∀ a : p.rootSet p.SplittingField,
        IsAtom (IntermediateField.adjoin K {(↑a : p.SplittingField)})) :
    @MulAction.IsPreprimitive p.Gal (↑(p.rootSet p.SplittingField))
      (Gal.galAction p p.SplittingField).toSMul := by
  -- Pin the ambient `MulAction p.Gal (rootSet)` to `Gal.galAction` (rather than the unconditional
  -- default `Gal.galActionAux`), so it matches the stabilizer computed by
  -- `stabilizer_isCoatom_of_isAtom` and the `galActionHom = toPermHom` identity used downstream.
  letI : MulAction p.Gal (↑(p.rootSet p.SplittingField)) := Gal.galAction p p.SplittingField
  haveI htrans : MulAction.IsPretransitive p.Gal (↑(p.rootSet p.SplittingField)) :=
    Gal.galAction_isPretransitive p p.SplittingField hirr
  haveI := hnt
  obtain ⟨a⟩ := (inferInstance : Nonempty (↑(p.rootSet p.SplittingField)))
  have hco := stabilizer_isCoatom_of_isAtom p hsep a (hatom a)
  rwa [MulAction.isCoatom_stabilizer_iff_preprimitive] at hco

/-- **[general — image form]** The same conclusion as `galAction_isPreprimitive_of_isAtom`, but for
the **image** subgroup `(galActionHom p SF).range ≤ Equiv.Perm (rootSet)` acting naturally on the
root set.  This is the shape needed by geometric-monodromy applications, where the acting object is
the permutation image of the Galois group (not the abstract Galois group).

Transported from the `p.Gal`-action along the surjection `p.Gal ↠ (galActionHom).range` via
`MulAction.IsPreprimitive.of_surjective`: the identity map on the root set is equivariant because
`galActionHom` is exactly `MulAction.toPermHom`, i.e. `(galActionHom g) x = g • x`. -/
theorem galActionHom_range_isPreprimitive_of_isAtom (p : K[X]) (hsep : p.Separable)
    (hirr : Irreducible p) (hnt : Nontrivial (p.rootSet p.SplittingField))
    (hatom : ∀ a : p.rootSet p.SplittingField,
        IsAtom (IntermediateField.adjoin K {(↑a : p.SplittingField)})) :
    MulAction.IsPreprimitive (Gal.galActionHom p p.SplittingField).range
      (p.rootSet p.SplittingField) := by
  letI : MulAction p.Gal (↑(p.rootSet p.SplittingField)) := Gal.galAction p p.SplittingField
  haveI : @MulAction.IsPreprimitive p.Gal (↑(p.rootSet p.SplittingField))
      (Gal.galAction p p.SplittingField).toSMul :=
    galAction_isPreprimitive_of_isAtom p hsep hirr hnt hatom
  -- Transport preprimitivity along the surjection `p.Gal ↠ (galActionHom).range`.  The identity map
  -- on the root set is equivariant because `galActionHom = MulAction.toPermHom` for `Gal.galAction`,
  -- i.e. `(galActionHom g) • x = g • x`; with the ambient action pinned to `Gal.galAction` this is
  -- `rfl`.
  refine MulAction.IsPreprimitive.of_surjective
    (φ := ⇑(Gal.galActionHom p p.SplittingField).rangeRestrict)
    (f := ⟨id, fun g x => rfl⟩) ?_
  intro y
  exact ⟨y, rfl⟩

end InverseGalois.Primitivity

end
