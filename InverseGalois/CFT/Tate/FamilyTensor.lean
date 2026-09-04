/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyTorsion
import InverseGalois.CFT.TateCohomology.Restrict
import InverseGalois.CFT.TateCohomology.TensorFunctor
import InverseGalois.CFT.TateCohomology.TensorPi

/-!
# Tensoring the sections of a family with coefficients

The sections of a family of modules indexed by a set with a group action are a product, and a
tensor product does not commute with an infinite product.  It does, however, when the second factor
is finite over the prime field and every module of the family is killed by that prime, and this is
exactly the situation of the roots of unity in the group of ideles: the local factors are killed by
the prime, and the coefficients of global duality are a finite dimensional vector space over the
prime field.

Under those hypotheses the tensor product of the sections with a representation is the sections of
the family whose module at an index is the module there tensored with the representation, the group
acting diagonally.  The orbit decomposition of the sections then applies to the tensored family, and
the module at a base point of an orbit is the module there tensored with the representation
restricted to the stabiliser.  So **the complete cohomology of the sections tensored with the
coefficients is again a product of local contributions, one for each orbit, each computed in the
stabiliser of a point with coefficients restricted there**.

The same is recorded for the subfamily of elements killed by the prime, which is the form the
description of the cohomology of the roots of unity in the ideles takes.

## Main definitions

* `InverseGalois.CFT.FamilyAction.tensorRight`: **the family whose module at an index is tensored
  with a representation**, the group acting diagonally.
* `InverseGalois.CFT.sectionsTensorMap`: the map spreading a tensor of a section with a vector over
  the indices.
* `InverseGalois.CFT.tensorSectionsIso`: **the sections of a family tensored with the coefficients
  are the sections of the tensored family.**

## Main results

* `InverseGalois.CFT.bijective_sectionsTensorMap`: the spreading map is bijective.
* `InverseGalois.CFT.orbitStabTensorIso`: at a base point of an orbit the tensored family gives the
  module there tensored with the coefficients restricted to the stabiliser.
* `InverseGalois.CFT.isZero_tateModule_tensor_orbitSectionsRep`: **the sections tensored with the
  coefficients have no complete cohomology in a degree as soon as none of the local contributions
  has any.**
* `InverseGalois.CFT.isZero_tateModule_tensor_torsionRep`: the same for the sections killed by the
  prime.

## Tags

Tate cohomology, tensor product, orbit, Shapiro's lemma, decomposition group, idele, torsion
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate

open scoped TensorProduct

noncomputable section

/-! ### The tensor product of a family with a representation -/

section Def

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (W : Rep ℤ G)

omit [MulAction G X] in
/-- Transporting a tensor along an equality of indices transports the first factor. -/
theorem famCast_tensorRight_tmul {x y : X} (h : x = y) (a : M x) (w : ↥W.V) :
    famCast (fun z => M z ⊗[ℤ] ↥W.V) h (a ⊗ₜ[ℤ] w) = famCast M h a ⊗ₜ[ℤ] w := by
  subst h
  rfl

/-- The transport of a tensored family attached to a group element: the first factor moves along
the family and the second is acted on by the representation. -/
def tensorRightMap (g : G) (x : X) : (M x ⊗[ℤ] ↥W.V) ≃+ (M (g • x) ⊗[ℤ] ↥W.V) :=
  (TensorProduct.congr (F.map g x).toIntLinearEquiv (repAut W.ρ g)).toAddEquiv

@[simp]
theorem tensorRightMap_tmul (g : G) (x : X) (a : M x) (w : ↥W.V) :
    tensorRightMap F W g x (a ⊗ₜ[ℤ] w) = F.map g x a ⊗ₜ[ℤ] W.ρ g w := rfl

/-- **The family whose module at an index is the module there tensored with a representation**, the
group transporting the first factor along the family and acting on the second. -/
def FamilyAction.tensorRight : FamilyAction (fun x => M x ⊗[ℤ] ↥W.V) G where
  map := tensorRightMap F W
  map_one x a := by
    induction a using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b w =>
      rw [tensorRightMap_tmul, famCast_tensorRight_tmul, F.map_one, _root_.map_one]
      rfl
    | add a a' ha ha' => simp only [map_add, ha, ha']
  map_mul g h x a := by
    induction a using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b w =>
      rw [tensorRightMap_tmul, tensorRightMap_tmul, tensorRightMap_tmul,
        famCast_tensorRight_tmul, F.map_mul, _root_.map_mul]
      rfl
    | add a a' ha ha' => simp only [map_add, ha, ha']

@[simp]
theorem tensorRight_map_tmul (g : G) (x : X) (a : M x) (w : ↥W.V) :
    (F.tensorRight W).map g x (a ⊗ₜ[ℤ] w) = F.map g x a ⊗ₜ[ℤ] W.ρ g w := rfl

/-- **A transport of the tensored family transports the first factor and acts on the second.** -/
theorem tensorRight_transport_tmul {g : G} {x y : X} (h : g • x = y) (a : M x) (w : ↥W.V) :
    (F.tensorRight W).transport h (a ⊗ₜ[ℤ] w) = F.transport h a ⊗ₜ[ℤ] W.ρ g w := by
  rw [FamilyAction.transport_apply, FamilyAction.transport_apply, tensorRight_map_tmul,
    famCast_tensorRight_tmul]

end Def

/-! ### The sections of the tensored family -/

section Sections

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (W : Rep ℤ G)

/-- The value of a section at an index, as a linear map. -/
def sectionsProj (x : X) : ↥(orbitSectionsRep F).V →ₗ[ℤ] M x :=
  intLinearOfAddHom { toFun := fun u => u x, map_zero' := rfl, map_add' := fun _ _ => rfl }

@[simp]
theorem sectionsProj_apply (x : X) (u : ↥(orbitSectionsRep F).V) : sectionsProj F x u = u x := rfl

/-- **The map spreading a tensor of a section with a vector over the indices.** -/
def sectionsTensorMap :
    ↥(tensorObj (orbitSectionsRep F) W).V →ₗ[ℤ] ↥(orbitSectionsRep (F.tensorRight W)).V :=
  TensorProduct.lift <| intLinearOfAddHom
    { toFun := fun u => intLinearOfAddHom
        { toFun := fun w x => u x ⊗ₜ[ℤ] w
          map_zero' := funext fun x => TensorProduct.tmul_zero _ (u x)
          map_add' := fun w w' => funext fun x => TensorProduct.tmul_add (u x) w w' }
      map_zero' := by
        refine LinearMap.ext fun w => funext fun x => ?_
        exact TensorProduct.zero_tmul _ w
      map_add' := fun u u' => by
        refine LinearMap.ext fun w => funext fun x => ?_
        exact TensorProduct.add_tmul (u x) (u' x) w }

@[simp]
theorem sectionsTensorMap_tmul (u : ↥(orbitSectionsRep F).V) (w : ↥W.V) (x : X) :
    sectionsTensorMap F W (u ⊗ₜ[ℤ] w) x = u x ⊗ₜ[ℤ] w := rfl

/-- The spreading map is the projection to an index tensored with the identity. -/
theorem sectionsTensorMap_apply (x : X) (t : ↥(tensorObj (orbitSectionsRep F) W).V) :
    sectionsTensorMap F W t x = TensorProduct.map (sectionsProj F x) LinearMap.id t := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | tmul u w => rfl
  | add t t' ht ht' =>
    rw [map_add, map_add]
    show sectionsTensorMap F W t x + sectionsTensorMap F W t' x = _
    rw [ht, ht']

/-- The spreading map is compatible with the actions. -/
theorem sectionsTensorMap_equivariant (g : G) :
    sectionsTensorMap F W ∘ₗ (tensorObj (orbitSectionsRep F) W).ρ g
      = (orbitSectionsRep (F.tensorRight W)).ρ g ∘ₗ sectionsTensorMap F W :=
  TensorProduct.ext' fun u w => funext fun x => by
    show sectionsTensorMap F W (F.familyAut g u ⊗ₜ[ℤ] W.ρ g w) x
      = (F.tensorRight W).familyAut g (fun y => u y ⊗ₜ[ℤ] w) x
    rw [sectionsTensorMap_tmul,
      (F.tensorRight W).familyAut_apply_eq_transport (smul_inv_smul g x)
        (fun y => u y ⊗ₜ[ℤ] w),
      tensorRight_transport_tmul, ← F.familyAut_apply_eq_transport (smul_inv_smul g x) u]

/-- **The sections of a family tensored with a representation map to the sections of the tensored
family.** -/
def tensorSectionsHom : tensorObj (orbitSectionsRep F) W ⟶ orbitSectionsRep (F.tensorRight W) :=
  mkHom (sectionsTensorMap F W) (sectionsTensorMap_equivariant F W)

variable {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))
  (hM : ∀ (x : X) (a : M x), p • a = 0)

omit [Fact p.Prime] in
include hM in
/-- A section of a family whose modules are killed by a prime is killed by that prime. -/
theorem nsmul_eq_zero_sections (u : ↥(orbitSectionsRep F).V) : p • u = 0 :=
  funext fun x => hM x (u x)

include e hM in
/-- **The spreading map is bijective** when the coefficients are finite over the prime field and
every module of the family is killed by the prime.  Both directions are read in coordinates: a
choice of basis of the coefficients turns a tensor with them into a tuple, and the spreading map
becomes the identity on tuples of sections. -/
theorem bijective_sectionsTensorMap : Function.Bijective (sectionsTensorMap F W) := by
  have hpi : ∀ u : ↥(orbitSectionsRep F).V, p • u = 0 := nsmul_eq_zero_sections F hM
  have hkey : ∀ (t : ↥(tensorObj (orbitSectionsRep F) W).V) (x : X) (j : Fin d),
      coordMap e (hM x) (sectionsTensorMap F W t x) j = coordMap e hpi t j x := by
    intro t x j
    rw [sectionsTensorMap_apply]
    exact coordMap_map e (sectionsProj F x) hpi (hM x) t j
  constructor
  · refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun t ht => ?_)
    refine (coordEquiv e hpi).injective (funext fun j => funext fun x => ?_)
    have ht' : sectionsTensorMap F W t x = 0 := congrFun ht x
    have h := hkey t x j
    rw [ht', map_zero, Pi.zero_apply] at h
    show coordMap e hpi t j x = coordMap e hpi 0 j x
    simp only [map_zero, Pi.zero_apply]
    exact h.symm
  · intro s
    refine ⟨(coordEquiv e hpi).symm fun j x => coordMap e (hM x) (s x) j, funext fun x => ?_⟩
    refine (coordEquiv e (hM x)).injective (funext fun j => ?_)
    have hsymm : coordMap e hpi ((coordEquiv e hpi).symm fun j x => coordMap e (hM x) (s x) j)
        = fun j x => coordMap e (hM x) (s x) j := (coordEquiv e hpi).apply_symm_apply _
    show coordMap e (hM x) (sectionsTensorMap F W
      ((coordEquiv e hpi).symm fun j x => coordMap e (hM x) (s x) j) x) j
        = coordMap e (hM x) (s x) j
    rw [hkey, hsymm]

include e hM in
/-- **The sections of a family tensored with the coefficients are the sections of the tensored
family**, when the coefficients are finite over the prime field and every module of the family is
killed by the prime. -/
def tensorSectionsIso : tensorObj (orbitSectionsRep F) W ≅ orbitSectionsRep (F.tensorRight W) :=
  isoOfBijective (tensorSectionsHom F W) (bijective_sectionsTensorMap F W e hM)

end Sections

/-! ### Elements killed by a prime -/

section TorsionNsmul

variable {A : Type*} [AddCommGroup A] {p : ℕ}

/-- An element killed by a prime read as an integer is killed by it read as a natural number. -/
theorem nsmul_eq_zero_torsionBy (a : ↥(AddSubgroup.torsionBy A (p : ℤ))) : p • a = 0 := by
  refine Subtype.ext ?_
  show p • (a : A) = 0
  rw [← natCast_zsmul]
  exact mem_torsionBy.1 a.2

end TorsionNsmul

/-! ### One orbit -/

section Orbit

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (W : Rep ℤ G) {ω : orbitRel.Quotient G X} (x₀ : ω.orbit)
  {H : Subgroup G} (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀)

include hH' in
/-- The action of the stabiliser of a point of an orbit on the tensored family is its action on the
module there together with its action on the coefficients. -/
theorem stabAut_tensorRight_tmul (g : ↥H) (a : M (x₀ : X)) (w : ↥W.V) :
    stabAut x₀ hH' (orbitFamily (F.tensorRight W) ω) g (a ⊗ₜ[ℤ] w)
      = stabAut x₀ hH' (orbitFamily F ω) g a ⊗ₜ[ℤ] W.ρ (g : G) w := by
  have hH'' : ∀ g : ↥H, (g : G) • (x₀ : X) = (x₀ : X) := fun g => congrArg Subtype.val (hH' g)
  rw [stabAut_orbitFamily (F.tensorRight W) x₀ hH' hH'' g, tensorRight_transport_tmul,
    stabAut_orbitFamily F x₀ hH' hH'' g]

include hH' in
/-- **At a base point of an orbit the tensored family gives the module there tensored with the
coefficients restricted to the stabiliser.** -/
def orbitStabTensorIso :
    orbitStabRep x₀ hH' (orbitFamily (F.tensorRight W) ω)
      ≅ tensorObj (orbitStabRep x₀ hH' (orbitFamily F ω)) (resObj H W) :=
  Action.mkIso (AddEquiv.refl _).toIntLinearEquiv.toModuleIso fun g => by
    ext a
    induction a using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul b w => exact stabAut_tensorRight_tmul F W x₀ hH' g b w
    | add a a' ha ha' => rw [map_add, map_add, ha, ha']

end Orbit

/-! ### All the orbits -/

section Orbits

variable {G X : Type} [Group G] [MulAction G X] [Finite G] {M : X → Type}
  [∀ x, AddCommGroup (M x)] (F : FamilyAction M G) (W : Rep ℤ G) {p d : ℕ} [Fact p.Prime]
  (e : ↥W.V ≃+ (Fin d → ZMod p)) (hM : ∀ (x : X) (a : M x), p • a = 0)
  (x₀ : ∀ ω : orbitRel.Quotient G X, ω.orbit) {H : orbitRel.Quotient G X → Subgroup G}
  (hH : ∀ (ω : orbitRel.Quotient G X) (g : G), g • x₀ ω = x₀ ω → g ∈ H ω)
  (hH' : ∀ (ω : orbitRel.Quotient G X) (g : ↥(H ω)), (g : G) • x₀ ω = x₀ ω)

include e hM hH hH' in
/-- **The sections of a family tensored with the coefficients have no complete cohomology in a
degree as soon as none of the local contributions has any.**  The tensor product passes through the
product of sections because the coefficients are finite over the prime field, and the orbit
decomposition then applies to the tensored family. -/
theorem isZero_tateModule_tensor_orbitSectionsRep (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient G X, Limits.IsZero
      (tateModule (tensorObj (orbitStabRep (x₀ ω) (hH' ω) (orbitFamily F ω))
        (resObj (H ω) W)) n)) :
    Limits.IsZero (tateModule (tensorObj (orbitSectionsRep F) W) n) := by
  refine isZero_tateModule_of_iso (tensorSectionsIso F W e hM) n ?_
  refine isZero_tateModule_orbitSectionsRep (F.tensorRight W) x₀ hH hH' n fun ω => ?_
  exact isZero_tateModule_of_iso (orbitStabTensorIso F W (x₀ ω) (hH' ω)) n (h ω)

include e hH hH' in
/-- **The sections of a family killed by a prime, tensored with the coefficients, have no complete
cohomology in a degree as soon as none of the local contributions has any.**  This is the shape the
roots of unity in the group of ideles take: the local contribution at a place is the roots of unity
of the completion tensored with the coefficients, read in the decomposition group. -/
theorem isZero_tateModule_tensor_torsionRep (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient G X, Limits.IsZero
      (tateModule (tensorObj (torsionRep (stabAut (x₀ ω) (hH' ω) (orbitFamily F ω)) (p : ℤ))
        (resObj (H ω) W)) n)) :
    Limits.IsZero (tateModule (tensorObj (torsionRep F.familyAut (p : ℤ)) W) n) := by
  have hM : ∀ (x : X) (a : ↥(AddSubgroup.torsionBy (M x) (p : ℤ))), p • a = 0 :=
    fun _ a => nsmul_eq_zero_torsionBy a
  refine isZero_tateModule_of_iso (tensorIsoLeft W (torsionSectionsIso F (p : ℤ))).symm n ?_
  refine isZero_tateModule_tensor_orbitSectionsRep (F.torsion (p : ℤ)) W e hM x₀ hH hH' n
    fun ω => ?_
  rw [orbitStabRep_torsion F (p : ℤ) (x₀ ω) (hH' ω)]
  exact h ω

end Orbits

end

end InverseGalois.CFT
