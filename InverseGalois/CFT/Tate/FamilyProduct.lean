/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyCoind
import InverseGalois.CFT.Tate.FamilyOrbits
import InverseGalois.CFT.TateCohomology.Product

/-!
# The sections of a family, orbit by orbit, in every degree

A set carrying a group action is the disjoint union of its orbits, so the sections of a family of
modules indexed by it are the product over the orbits of the sections over one orbit.  That
splitting respects the action, so it is an isomorphism of representations; the complete cohomology
of a product is the product of the complete cohomologies; and the sections over one orbit are
coinduced from the stabiliser of a base point.  Chaining the three gives **the complete cohomology
of the sections of a family as a product of local contributions, one for each orbit, each computed
in the stabiliser of a chosen point of that orbit**.

The index set is not assumed finite, and no hypothesis is placed on the group beyond finiteness:
in particular the group need not be cyclic, so this is the statement the Herbrand quotient
computations over one orbit could not reach.  For the group of ideles of a Galois extension of
number fields the orbits are the places of the base field, the stabiliser of a place above one of
them is its decomposition group, and the conclusion is the description of the cohomology of the
ideles as a product over the places of the base field of local cohomology groups.

## Main definitions

* `InverseGalois.CFT.sigmaSectionsIso`: the sections of a family over a disjoint union, as a
  product of representations.
* `InverseGalois.CFT.reindexSectionsIso`: reindexing a family along an equivalence respecting the
  actions does not change the representation carried by the sections.
* `InverseGalois.CFT.orbitsSectionsIso`: **the sections of a family are the product over the orbits
  of the sections over one orbit**, as representations.

## Main results

* `InverseGalois.CFT.tateOrbitsEquiv`: **the complete cohomology of the sections of a family is the
  product over the orbits of the complete cohomology of the sections over one orbit.**
* `InverseGalois.CFT.tateOrbitsLocalEquiv`: **the complete cohomology of the sections of a family is
  the product over the orbits of the complete cohomology of the stabiliser of a chosen point of the
  orbit with coefficients in the module there.**
* `InverseGalois.CFT.isZero_tateModule_orbitSectionsRep`: the sections have no complete cohomology
  in a degree as soon as none of the local contributions has any.

## Tags

Tate cohomology, orbit, product, Shapiro's lemma, decomposition group, idele
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate

noncomputable section

/-! ### The sections over a disjoint union -/

section Sigma

variable {G Y : Type} [Group G] {P : Y → Type} [∀ y, MulAction G (P y)]
  {N : (Σ y, P y) → Type} [∀ x, AddCommGroup (N x)] (F : FamilyAction N G)

/-- **The sections of a family over a disjoint union are the product over the pieces of the
sections over each piece**, as representations of the group. -/
def sigmaSectionsIso :
    orbitSectionsRep F ≅ piRep fun y => orbitSectionsRep (F.sigmaFiber y) :=
  Action.mkIso (sigmaFamilyEquiv (M := N)).toIntLinearEquiv.toModuleIso fun g => by
    ext u
    exact sigmaFamilyEquiv_familyAut F g u

end Sigma

/-! ### Reindexing -/

section Reindex

variable {G X X' : Type} [Group G] [MulAction G X] [MulAction G X']
  {M : X → Type} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G)
  (e : X' ≃ X) (he : ∀ (g : G) (x' : X'), e (g • x') = g • e x')

/-- **Reindexing a family along an equivalence respecting the actions does not change the
representation carried by the sections.** -/
def reindexSectionsIso : orbitSectionsRep F ≅ orbitSectionsRep (F.reindex e he) :=
  Action.mkIso (reindexFamilyEquiv (M := M) e).toIntLinearEquiv.toModuleIso fun g => by
    ext u
    exact reindexFamilyEquiv_familyAut F e he g u

end Reindex

/-! ### The decomposition into orbits -/

section Orbits

variable {G X : Type} [Group G] [MulAction G X]
  {M : X → Type} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G)

/-- **The sections of a family are the product over the orbits of the sections over one orbit**, as
representations of the group. -/
def orbitsSectionsIso :
    orbitSectionsRep F ≅
      piRep fun ω : orbitRel.Quotient G X => orbitSectionsRep (orbitFamily F ω) :=
  (reindexSectionsIso F (selfEquivSigmaOrbits' G X).symm
    equivariant_selfEquivSigmaOrbits).trans (sigmaSectionsIso _)

variable [Finite G]

/-- **The complete cohomology of the sections of a family is the product over the orbits of the
complete cohomology of the sections over one orbit.** -/
def tateOrbitsEquiv (n : ℤ) :
    tateModule (orbitSectionsRep F) n ≃+
      ∀ ω : orbitRel.Quotient G X, tateModule (orbitSectionsRep (orbitFamily F ω)) n :=
  let e := (tateMapIso (orbitsSectionsIso F) n).toLinearEquiv.trans
    (tatePiEquiv (fun ω : orbitRel.Quotient G X => orbitSectionsRep (orbitFamily F ω)) n)
  { toEquiv := e.toEquiv, map_add' := e.map_add }

variable (x₀ : ∀ ω : orbitRel.Quotient G X, ω.orbit) {H : orbitRel.Quotient G X → Subgroup G}
  (hH : ∀ (ω : orbitRel.Quotient G X) (g : G), g • x₀ ω = x₀ ω → g ∈ H ω)
  (hH' : ∀ (ω : orbitRel.Quotient G X) (g : ↥(H ω)), (g : G) • x₀ ω = x₀ ω)

include hH hH' in
/-- **The complete cohomology of the sections of a family is the product over the orbits of the
complete cohomology of the stabiliser of a chosen point of the orbit with coefficients in the module
there.**  The orbits contribute independently because the sections split as a product over them, and
each contributes locally because the sections over one orbit are coinduced. -/
def tateOrbitsLocalEquiv (n : ℤ) :
    tateModule (orbitSectionsRep F) n ≃+
      ∀ ω : orbitRel.Quotient G X,
        tateModule (orbitStabRep (x₀ ω) (hH' ω) (orbitFamily F ω)) n :=
  (tateOrbitsEquiv F n).trans <| AddEquiv.piCongrRight fun ω =>
    (orbitTateEquiv (x₀ ω) (fun y => exists_smul_eq G y (x₀ ω)) (hH ω) (hH' ω)
      (orbitFamily F ω) n).toAddEquiv

include hH hH' in
/-- **The sections of a family have no complete cohomology in a degree as soon as none of the local
contributions has any.** -/
theorem isZero_tateModule_orbitSectionsRep (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient G X,
      Limits.IsZero (tateModule (orbitStabRep (x₀ ω) (hH' ω) (orbitFamily F ω)) n)) :
    Limits.IsZero (tateModule (orbitSectionsRep F) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ ω : orbitRel.Quotient G X,
      Subsingleton ↥(tateModule (orbitStabRep (x₀ ω) (hH' ω) (orbitFamily F ω)) n) := fun ω =>
    ModuleCat.isZero_iff_subsingleton.1 (h ω)
  exact (tateOrbitsLocalEquiv F x₀ hH hH' n).injective.subsingleton

end Orbits

end

end InverseGalois.CFT
