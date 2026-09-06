/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyCoind
import InverseGalois.CFT.Tate.FamilyRestrictOrbit

/-!
# The sections of a restricted family over an orbit

The sections of a family of modules over a transitive orbit are coinduced from the module at a
chosen base point, so their complete cohomology is the complete cohomology of the stabiliser of that
point with coefficients in the module there.  When the family is a family of subgroups of an ambient
one, the module at the base point is the subgroup there, and the action of the stabiliser on it is
the restriction of its action on the ambient module.

That subgroup is usually met under another name: for the ideles that are units outside a finite set
of places it is the whole multiplicative group of a completion inside the set, and the units of a
valuation ring outside it, each carrying an action of the decomposition group defined without
reference to any family.  Identifying the two descriptions is an isomorphism of representations of
the stabiliser, and complete cohomology carries it along.  The consequence is the computation the
arithmetic wants: the contribution of one orbit is the complete cohomology of the stabiliser with
coefficients in the named group, and in particular it vanishes whenever that cohomology does.

## Main definitions

* `InverseGalois.CFT.repOfAddAutIso`: an identification of the underlying groups carrying one action
  by additive automorphisms to another is an isomorphism of the attached representations.
* `InverseGalois.CFT.restrictOrbitStabIso`, `InverseGalois.CFT.restrictTopOrbitStabIso`: the module
  at the base point of a restricted family is the group it is declared to be, with the given action.

## Main results

* `InverseGalois.CFT.restrictOrbitTateEquiv`: **the complete cohomology of the sections of a
  restricted family over a transitive orbit is the complete cohomology of the stabiliser of a base
  point with coefficients in the subgroup there**, read through any identification of that subgroup
  with a group carrying a named action.
* `InverseGalois.CFT.isZero_tateModule_orbitSectionsRep_restrict`: **an orbit contributes nothing
  when the named action has no complete cohomology.**
* `InverseGalois.CFT.restrictTopOrbitTateEquiv`: the same computation when the subgroup at the base
  point is the whole ambient module.

## Tags

Tate cohomology, Shapiro's lemma, coinduced representation, orbit, family of modules, subgroup,
idele
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate

noncomputable section

/-! ### Comparing two actions by additive automorphisms -/

section OfAddAut

variable {G A B : Type} [Group G] [AddCommGroup A] [AddCommGroup B]

/-- An identification of the underlying groups carrying one action by additive automorphisms to
another is an isomorphism of the attached representations. -/
def repOfAddAutIso {φ : G →* AddAut A} {ψ : G →* AddAut B} (e : A ≃+ B)
    (he : ∀ (g : G) (a : A), e (φ g a) = ψ g (e a)) : repOfAddAut φ ≅ repOfAddAut ψ :=
  Action.mkIso e.toIntLinearEquiv.toModuleIso fun g => by
    ext a
    exact he g a

end OfAddAut

/-! ### One orbit of a restricted family -/

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (N : ∀ x, AddSubgroup (M x))
  (hN : ∀ (g : G) (x : X), (N x).map (F.map g x).toAddMonoidHom = N (g • x))
  {ω : orbitRel.Quotient G X} (x₀ : ω.orbit)
  (htrans : ∀ y : ω.orbit, ∃ g : G, g • y = x₀)
  {H : Subgroup G} (hH : ∀ g : G, g • x₀ = x₀ → g ∈ H) (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀)
  (hH'' : ∀ g : ↥H, (g : G) • (x₀ : X) = (x₀ : X))

/-! ### The subgroup at the base point carries a named action -/

section Congr

variable {P : AddSubgroup (M (x₀ : X))} (hNP : N (x₀ : X) = P) (τ : ↥H →* AddAut ↥P)
  (hτ : ∀ (g : ↥H) (a : ↥P), ((τ g a : ↥P) : M (x₀ : X))
    = stabAut x₀ hH' (orbitFamily F ω) g ((a : ↥P) : M (x₀ : X)))

/-- **The module at the base point of a restricted family, as a representation of the stabiliser, is
the group it is declared to be with the given action.** -/
def restrictOrbitStabIso :
    orbitStabRep x₀ hH' (orbitFamily (F.restrict N hN) ω) ≅ repOfAddAut τ :=
  repOfAddAutIso (AddEquiv.addSubgroupCongr hNP) fun g a =>
    addSubgroupCongr_stabAut_orbitFamily_restrict F N hN x₀ hH' hH'' g hNP (τ g) (hτ g) a

variable [Finite G]

include htrans hH in
/-- **The complete cohomology of the sections of a restricted family over a transitive orbit is the
complete cohomology of the stabiliser of a base point with coefficients in the subgroup there**,
read through the given identification of that subgroup with a group carrying a named action. -/
def restrictOrbitTateEquiv (n : ℤ) :
    tateModule (orbitSectionsRep (orbitFamily (F.restrict N hN) ω)) n
      ≃ₗ[ℤ] tateModule (repOfAddAut τ) n :=
  (orbitTateEquiv x₀ htrans hH hH' (orbitFamily (F.restrict N hN) ω) n).trans
    (tateMapIso (restrictOrbitStabIso F N hN x₀ hH' hH'' hNP τ hτ) n).toLinearEquiv

include htrans hH hH' hH'' hNP hτ in
/-- **An orbit contributes nothing to the complete cohomology of the sections of a restricted
family** when the named action on the subgroup at a point of it has none. -/
theorem isZero_tateModule_orbitSectionsRep_restrict (n : ℤ)
    (h : Limits.IsZero (tateModule (repOfAddAut τ) n)) :
    Limits.IsZero (tateModule (orbitSectionsRep (orbitFamily (F.restrict N hN) ω)) n) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  haveI := h
  exact (restrictOrbitTateEquiv F N hN x₀ htrans hH hH' hH'' hNP τ hτ n).injective.subsingleton

end Congr

/-! ### The subgroup at the base point is everything -/

section Top

variable (hNtop : N (x₀ : X) = ⊤) (τ : ↥H →* AddAut (M (x₀ : X)))
  (hτ : ∀ (g : ↥H) (a : M (x₀ : X)), τ g a = stabAut x₀ hH' (orbitFamily F ω) g a)

/-- **The module at the base point of a restricted family whose subgroup there is everything is the
ambient module**, with the given action. -/
def restrictTopOrbitStabIso :
    orbitStabRep x₀ hH' (orbitFamily (F.restrict N hN) ω) ≅ repOfAddAut τ :=
  repOfAddAutIso ((AddEquiv.addSubgroupCongr hNtop).trans AddSubgroup.topEquiv) fun g a =>
    (coe_stabAut_orbitFamily_restrict F N hN x₀ hH' hH'' g a).trans (hτ g _).symm

variable [Finite G]

include htrans hH in
/-- **The complete cohomology of the sections of a restricted family over a transitive orbit on
which the subgroups are everything is the complete cohomology of the stabiliser of a base point with
coefficients in the ambient module there.** -/
def restrictTopOrbitTateEquiv (n : ℤ) :
    tateModule (orbitSectionsRep (orbitFamily (F.restrict N hN) ω)) n
      ≃ₗ[ℤ] tateModule (repOfAddAut τ) n :=
  (orbitTateEquiv x₀ htrans hH hH' (orbitFamily (F.restrict N hN) ω) n).trans
    (tateMapIso (restrictTopOrbitStabIso F N hN x₀ hH' hH'' hNtop τ hτ) n).toLinearEquiv

end Top

end

end InverseGalois.CFT
