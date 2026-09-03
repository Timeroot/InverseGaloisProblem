/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyProduct
import InverseGalois.CFT.Tate.FamilyRestrictOrbit

/-!
# The elements of a family of modules killed by an integer

The elements of an abelian group killed by a fixed integer form a subgroup, and every isomorphism of
abelian groups carries that subgroup onto the corresponding one.  So a family of modules indexed by
a set with a group action has a subfamily of elements killed by the integer, the transports
restrict, and the sections of the subfamily are exactly the sections of the family killed by the
integer.

Applying the orbit decomposition to the subfamily gives **the complete cohomology of the sections
killed by an integer as a product, over the orbits of the index set, of the complete cohomology of
the stabiliser of a point with coefficients in the elements killed by that integer there**.  For the
group of ideles of a Galois extension of number fields the sections killed by a prime are the
`p`-torsion of the ideles, the orbits are the places of the base field, and the local coefficients
are the roots of unity of the completions: this is the description of the cohomology of the
`p`-torsion of the ideles that global duality uses.

## Main definitions

* `InverseGalois.CFT.torsionAut`: the action induced on the elements killed by an integer.
* `InverseGalois.CFT.torsionRep`: the elements killed by an integer, as a representation.
* `InverseGalois.CFT.FamilyAction.torsion`: **the subfamily of elements killed by an integer.**
* `InverseGalois.CFT.torsionSectionsIso`: the sections of the subfamily are the sections killed by
  the integer, as representations.

## Main results

* `InverseGalois.CFT.map_torsionBy`: an isomorphism of abelian groups carries the elements killed by
  an integer onto the elements killed by that integer.
* `InverseGalois.CFT.stabAut_torsion`: the action of the stabiliser of a point of an orbit on the
  elements killed by an integer is the one induced by its action on the module there.
* `InverseGalois.CFT.tateTorsionEquiv`: **the complete cohomology of the sections killed by an
  integer is the product over the orbits of the complete cohomology of the stabiliser of a chosen
  point of the orbit with coefficients in the elements killed by that integer.**
* `InverseGalois.CFT.isZero_tateModule_torsionRep`: the sections killed by an integer have no
  complete cohomology in a degree as soon as none of the local contributions has any.

## Tags

Tate cohomology, torsion, orbit, Shapiro's lemma, decomposition group, idele
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate

noncomputable section

/-! ### The elements killed by an integer -/

section Torsion

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Membership in the subgroup of elements killed by an integer. -/
theorem mem_torsionBy {m : ℤ} {a : A} : a ∈ AddSubgroup.torsionBy A m ↔ m • a = 0 :=
  Submodule.mem_torsionBy_iff m a

/-- **An isomorphism of abelian groups carries the elements killed by an integer onto the elements
killed by that integer.** -/
theorem map_torsionBy (m : ℤ) (e : A ≃+ B) :
    (AddSubgroup.torsionBy A m).map e.toAddMonoidHom = AddSubgroup.torsionBy B m := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine mem_torsionBy.2 ?_
    show m • e a = 0
    rw [← map_zsmul e, mem_torsionBy.1 ha, map_zero]
  · refine fun hb => ⟨e.symm b, mem_torsionBy.2 ?_, e.apply_symm_apply b⟩
    show m • e.symm b = 0
    rw [← map_zsmul e.symm, mem_torsionBy.1 hb, map_zero]

end Torsion

/-! ### The induced action -/

section Aut

variable {G A : Type} [Group G] [AddCommGroup A] (φ : G →* AddAut A) (m : ℤ)

/-- **The action induced on the elements killed by an integer.** -/
def torsionAut : G →* AddAut ↥(AddSubgroup.torsionBy A m) where
  toFun g :=
    { toFun := fun a => ⟨φ g a, mem_torsionBy.2 (by
        rw [← map_zsmul (φ g), mem_torsionBy.1 a.2, map_zero])⟩
      invFun := fun a => ⟨(φ g).symm a, mem_torsionBy.2 (by
        rw [← map_zsmul (φ g).symm, mem_torsionBy.1 a.2, map_zero])⟩
      left_inv := fun a => Subtype.ext ((φ g).symm_apply_apply (a : A))
      right_inv := fun a => Subtype.ext ((φ g).apply_symm_apply (a : A))
      map_add' := fun a b => Subtype.ext (map_add (φ g) (a : A) (b : A)) }
  map_one' := AddEquiv.ext fun a => Subtype.ext (by
    show (φ 1) (a : A) = (a : A)
    rw [map_one]
    rfl)
  map_mul' g h := AddEquiv.ext fun a => Subtype.ext (by
    show (φ (g * h)) (a : A) = (φ g) ((φ h) (a : A))
    rw [map_mul]
    rfl)

@[simp]
theorem coe_torsionAut_apply (g : G) (a : ↥(AddSubgroup.torsionBy A m)) :
    ((torsionAut φ m g a : ↥(AddSubgroup.torsionBy A m)) : A) = φ g (a : A) := rfl

/-- **The elements of a module killed by an integer, as a representation.** -/
def torsionRep : Rep ℤ G := repOfAddAut (torsionAut φ m)

end Aut

/-! ### The subfamily of elements killed by an integer -/

section Family

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (m : ℤ)

/-- **The subfamily of elements killed by an integer.** -/
def FamilyAction.torsion : FamilyAction (fun x => ↥(AddSubgroup.torsionBy (M x) m)) G :=
  F.restrict (fun x => AddSubgroup.torsionBy (M x) m) fun g x => map_torsionBy m (F.map g x)

@[simp]
theorem coe_torsion_transport {g : G} {x y : X} (h : g • x = y)
    (a : ↥(AddSubgroup.torsionBy (M x) m)) :
    (((F.torsion m).transport h a : ↥(AddSubgroup.torsionBy (M y) m)) : M y)
      = F.transport h (a : M x) :=
  F.coe_restrict_transport (fun x => AddSubgroup.torsionBy (M x) m)
    (fun g x => map_torsionBy m (F.map g x)) h a

end Family

/-! ### The sections -/

section Sections

variable {X : Type} {M : X → Type} [∀ x, AddCommGroup (M x)] (m : ℤ)

/-- **The sections of the subfamily of elements killed by an integer are the sections killed by that
integer.** -/
def piTorsionEquiv :
    (∀ x, ↥(AddSubgroup.torsionBy (M x) m)) ≃+ ↥(AddSubgroup.torsionBy (∀ x, M x) m) where
  toFun f := ⟨fun x => (f x : M x), mem_torsionBy.2 (funext fun x => mem_torsionBy.1 (f x).2)⟩
  invFun f := fun x => ⟨(f : ∀ x, M x) x, mem_torsionBy.2 (congrFun (mem_torsionBy.1 f.2) x)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_piTorsionEquiv (f : ∀ x, ↥(AddSubgroup.torsionBy (M x) m)) (x : X) :
    ((piTorsionEquiv m f : ↥(AddSubgroup.torsionBy (∀ x, M x) m)) : ∀ x, M x) x = (f x : M x) :=
  rfl

end Sections

section SectionsRep

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (m : ℤ)

/-- The splitting of the sections killed by an integer is compatible with the actions. -/
theorem piTorsionEquiv_familyAut (g : G) (f : ∀ x, ↥(AddSubgroup.torsionBy (M x) m)) :
    piTorsionEquiv m ((F.torsion m).familyAut g f)
      = torsionAut F.familyAut m g (piTorsionEquiv m f) := by
  refine Subtype.ext (funext fun x => ?_)
  show (((F.torsion m).familyAut g f x : ↥(AddSubgroup.torsionBy (M x) m)) : M x)
    = F.familyAut g (fun y => (f y : M y)) x
  rw [(F.torsion m).familyAut_apply_eq_transport (smul_inv_smul g x) f,
    F.familyAut_apply_eq_transport (smul_inv_smul g x) (fun y => (f y : M y)),
    coe_torsion_transport]

/-- **The sections of the subfamily of elements killed by an integer are the sections killed by that
integer**, as representations of the group. -/
def torsionSectionsIso : orbitSectionsRep (F.torsion m) ≅ torsionRep F.familyAut m :=
  Action.mkIso (piTorsionEquiv (M := M) m).toIntLinearEquiv.toModuleIso fun g => by
    ext u
    exact piTorsionEquiv_familyAut F m g u

end SectionsRep

/-! ### One orbit -/

section Orbit

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (m : ℤ) {ω : orbitRel.Quotient G X} (x₀ : ω.orbit) {H : Subgroup G}
  (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀)

include hH' in
/-- **The action of the stabiliser of a point of an orbit on the elements killed by an integer is
the one induced by its action on the module there.** -/
theorem stabAut_torsion :
    stabAut x₀ hH' (orbitFamily (F.torsion m) ω)
      = torsionAut (stabAut x₀ hH' (orbitFamily F ω)) m := by
  have hH'' : ∀ g : ↥H, (g : G) • (x₀ : X) = (x₀ : X) := fun g => congrArg Subtype.val (hH' g)
  refine MonoidHom.ext fun g => AddEquiv.ext fun a => Subtype.ext ?_
  exact coe_stabAut_orbitFamily_restrict F (fun x => AddSubgroup.torsionBy (M x) m)
    (fun g x => map_torsionBy m (F.map g x)) x₀ hH' hH'' g a

include hH' in
/-- The module of elements killed by an integer at a point of an orbit, as a representation of the
stabiliser of that point. -/
theorem orbitStabRep_torsion :
    orbitStabRep x₀ hH' (orbitFamily (F.torsion m) ω)
      = torsionRep (stabAut x₀ hH' (orbitFamily F ω)) m :=
  congrArg repOfAddAut (stabAut_torsion F m x₀ hH')

variable [Finite G]

include hH' in
/-- **Over one orbit the complete cohomology of the sections killed by an integer is the complete
cohomology of the stabiliser of a point with coefficients in the elements killed by that integer.**
-/
def tateTorsionOrbitEquiv (n : ℤ) :
    tateModule (orbitStabRep x₀ hH' (orbitFamily (F.torsion m) ω)) n ≃ₗ[ℤ]
      tateModule (torsionRep (stabAut x₀ hH' (orbitFamily F ω)) m) n := by
  rw [orbitStabRep_torsion F m x₀ hH']

end Orbit

/-! ### All the orbits -/

section Orbits

variable {G X : Type} [Group G] [MulAction G X] [Finite G] {M : X → Type}
  [∀ x, AddCommGroup (M x)] (F : FamilyAction M G) (m : ℤ)
  (x₀ : ∀ ω : orbitRel.Quotient G X, ω.orbit) {H : orbitRel.Quotient G X → Subgroup G}
  (hH : ∀ (ω : orbitRel.Quotient G X) (g : G), g • x₀ ω = x₀ ω → g ∈ H ω)
  (hH' : ∀ (ω : orbitRel.Quotient G X) (g : ↥(H ω)), (g : G) • x₀ ω = x₀ ω)

include hH hH' in
/-- **The complete cohomology of the sections of a family killed by an integer is the product over
the orbits of the complete cohomology of the stabiliser of a chosen point of the orbit with
coefficients in the elements killed by that integer.**  The elements killed by the integer form a
subfamily, and the orbit decomposition of the sections of a family applies to it. -/
def tateTorsionEquiv (n : ℤ) :
    tateModule (torsionRep F.familyAut m) n ≃+
      ∀ ω : orbitRel.Quotient G X,
        tateModule (torsionRep (stabAut (x₀ ω) (hH' ω) (orbitFamily F ω)) m) n :=
  ((tateMapIso (torsionSectionsIso F m) n).symm.toLinearEquiv.toAddEquiv).trans <|
    (tateOrbitsLocalEquiv (F.torsion m) x₀ hH hH' n).trans <|
      AddEquiv.piCongrRight fun ω =>
        (tateTorsionOrbitEquiv F m (x₀ ω) (hH' ω) n).toAddEquiv

include hH hH' in
/-- **The sections of a family killed by an integer have no complete cohomology in a degree as soon
as none of the local contributions has any.** -/
theorem isZero_tateModule_torsionRep (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient G X, Limits.IsZero
      (tateModule (torsionRep (stabAut (x₀ ω) (hH' ω) (orbitFamily F ω)) m) n)) :
    Limits.IsZero (tateModule (torsionRep F.familyAut m) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ ω : orbitRel.Quotient G X,
      Subsingleton ↥(tateModule (torsionRep (stabAut (x₀ ω) (hH' ω) (orbitFamily F ω)) m) n) :=
    fun ω => ModuleCat.isZero_iff_subsingleton.1 (h ω)
  exact (tateTorsionEquiv F m x₀ hH hH' n).injective.subsingleton

end Orbits

end

end InverseGalois.CFT
