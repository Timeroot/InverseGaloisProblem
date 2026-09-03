/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyProduct

/-!
# The functions from a set with a group action to a module

The simplest family of modules over a set carrying a group action is the one that is the same module
at every index, transported by a fixed action of the group on that module.  Its sections are the
functions from the index set to the module, acted on by moving the argument and the value at once,
and every permutation module of arithmetic — the local factors of the `p`-torsion of the ideles, for
instance, where the index set is the set of places and the module is the group of `p`-th roots of
unity — is of this shape.

The general orbit decomposition therefore applies, and applies without any hypothesis on the group
beyond finiteness: **the complete cohomology of the functions from a set with a group action to a
module is the product, over the orbits of the set, of the complete cohomology of the stabiliser of a
point of the orbit with coefficients in that module.**  This is Shapiro's lemma for permutation
modules, in every integer degree at once.

## Main definitions

* `InverseGalois.CFT.constFamily`: the family that is the same module at every index.

## Main results

* `InverseGalois.CFT.tateConstOrbitEquiv`: over one orbit, the complete cohomology of the functions
  to the module is the complete cohomology of the stabiliser of a point with coefficients in the
  module.
* `InverseGalois.CFT.tateConstEquiv`: **the complete cohomology of the functions from a set with a
  group action to a module is the product over the orbits of the local contributions.**
* `InverseGalois.CFT.isZero_tateModule_constFamily`: the functions have no complete cohomology in a
  degree as soon as no stabiliser contributes any.

## Tags

permutation module, Shapiro's lemma, orbit, stabiliser, Tate cohomology
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate

noncomputable section

variable {G X A : Type} [Group G] [MulAction G X] [AddCommGroup A]

/-! ### The family that does not vary -/

/-- Transporting a family that does not vary along an equality of indices does nothing. -/
@[simp]
theorem famCast_const {x y : X} (h : x = y) :
    famCast (fun _ : X => A) h = AddEquiv.refl A := by
  subst h
  rfl

/-- **The family that is the same module at every index**, transported by a fixed action of the
group on that module. -/
def constFamily (φ : G →* AddAut A) : FamilyAction (fun _ : X => A) G where
  map g _ := φ g
  map_one x a := by
    rw [famCast_const, map_one]
    rfl
  map_mul g h x a := by
    rw [famCast_const, map_mul, AddAut.mul_apply]
    rfl

@[simp]
theorem constFamily_map (φ : G →* AddAut A) (g : G) (x : X) :
    (constFamily (X := X) φ).map g x = φ g := rfl

/-- **A transport of the family that does not vary is the action on the module.** -/
theorem constFamily_transport (φ : G →* AddAut A) {g : G} {x y : X} (h : g • x = y) (a : A) :
    (constFamily (X := X) φ).transport h a = φ g a := by
  rw [FamilyAction.transport_apply, famCast_const]
  rfl

/-- **The sections of the family that does not vary are the functions from the index set to the
module**, acted on by moving the argument and the value at once. -/
theorem familyAut_constFamily_apply (φ : G →* AddAut A) (g : G) (f : X → A) (x : X) :
    (constFamily (X := X) φ).familyAut g f x = φ g (f (g⁻¹ • x)) :=
  ((constFamily (X := X) φ).familyAut_apply_eq_transport (smul_inv_smul g x) f).trans
    (constFamily_transport φ (smul_inv_smul g x) _)

/-! ### One orbit -/

section Orbit

variable (φ : G →* AddAut A) {ω : orbitRel.Quotient G X} (x₀ : ω.orbit)

/-- The stabiliser of a point of an orbit, as a subgroup fixing the corresponding point of the
orbit. -/
theorem smul_orbit_of_mem_stabilizer_val (g : ↥(stabilizer G (x₀ : X))) : (g : G) • x₀ = x₀ :=
  Subtype.ext (mem_stabilizer_iff.mp g.2)

/-- A group element fixing a point of an orbit fixes the underlying point of the set. -/
theorem mem_stabilizer_val_of_smul_orbit (g : G) (h : g • x₀ = x₀) : g ∈ stabilizer G (x₀ : X) :=
  congrArg Subtype.val h

/-- **The action of the stabiliser of a point of an orbit on the module there is the given action of
that subgroup on the module.** -/
theorem orbitStabRep_constFamily :
    orbitStabRep x₀ (smul_orbit_of_mem_stabilizer_val x₀)
        (orbitFamily (constFamily (X := X) φ) ω)
      = repOfAddAut (φ.comp (stabilizer G (x₀ : X)).subtype) :=
  congrArg repOfAddAut <| MonoidHom.ext fun g => AddEquiv.ext fun a =>
    (stabAut_orbitFamily (constFamily (X := X) φ) x₀ (smul_orbit_of_mem_stabilizer_val x₀)
        (fun s => mem_stabilizer_iff.mp s.2) g a).trans
      (constFamily_transport φ (mem_stabilizer_iff.mp g.2) a)

variable [Finite G]

/-- **Over one orbit the complete cohomology of the functions to the module is the complete
cohomology of the stabiliser of a point of the orbit with coefficients in the module.** -/
def tateConstOrbitEquiv (n : ℤ) :
    tateModule (orbitSectionsRep (orbitFamily (constFamily (X := X) φ) ω)) n ≃ₗ[ℤ]
      tateModule (repOfAddAut (φ.comp (stabilizer G (x₀ : X)).subtype)) n := by
  rw [← orbitStabRep_constFamily φ x₀]
  exact orbitTateEquiv x₀ (fun y => exists_smul_eq G y x₀) (mem_stabilizer_val_of_smul_orbit x₀)
    (smul_orbit_of_mem_stabilizer_val x₀) _ n

end Orbit

/-! ### All the orbits -/

section Orbits

variable [Finite G] (φ : G →* AddAut A)
  (x₀ : ∀ ω : orbitRel.Quotient G X, ω.orbit)

/-- **The complete cohomology of the functions from a set with a group action to a module is the
product, over the orbits of the set, of the complete cohomology of the stabiliser of a point of the
orbit with coefficients in the module.**  The set is the disjoint union of its orbits, so the
functions split accordingly, and the functions on one orbit are coinduced from the stabiliser of a
chosen point of it. -/
def tateConstEquiv (n : ℤ) :
    tateModule (orbitSectionsRep (constFamily (X := X) φ)) n ≃+
      ∀ ω : orbitRel.Quotient G X,
        tateModule (repOfAddAut (φ.comp (stabilizer G ((x₀ ω : ω.orbit) : X)).subtype)) n :=
  (tateOrbitsEquiv (constFamily (X := X) φ) n).trans <|
    AddEquiv.piCongrRight fun ω => (tateConstOrbitEquiv φ (x₀ ω) n).toAddEquiv

/-- **The functions from a set with a group action to a module have no complete cohomology in a
degree as soon as no stabiliser contributes any.** -/
theorem isZero_tateModule_constFamily (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient G X, Limits.IsZero
      (tateModule (repOfAddAut (φ.comp (stabilizer G ((x₀ ω : ω.orbit) : X)).subtype)) n)) :
    Limits.IsZero (tateModule (orbitSectionsRep (constFamily (X := X) φ)) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ ω : orbitRel.Quotient G X, Subsingleton
      ↥(tateModule (repOfAddAut (φ.comp (stabilizer G ((x₀ ω : ω.orbit) : X)).subtype)) n) :=
    fun ω => ModuleCat.isZero_iff_subsingleton.1 (h ω)
  exact (tateConstEquiv φ x₀ n).injective.subsingleton

end Orbits

end

end InverseGalois.CFT
