/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyTensorOrbit

/-!
# Tensoring the sections of an arbitrary family with finite coefficients

Coefficients of finite rank over the field with `p` elements pass through an arbitrary product:
the sections of a family of abelian groups tensored with such coefficients are the sections of the
tensored family, **with no hypothesis at all on the groups of the family**.  Only the coefficients
have to be finite; the modules indexed by the set may be as large as one likes.

The mechanism is a coordinate device.  A basis of the coefficients over the prime field writes
every element of a tensor product as a sum of pure tensors along the basis vectors, so the
coordinates of an element are a family of elements of the module, and the element determines them
up to multiples of the prime.  Divisibility by the prime is exactly what the quotient by the
multiples of the prime detects, and that quotient *is* killed by the prime, so the coordinate map
available for modules of finite exponent applies to it and reads the coordinates off.  An element
of the tensor product whose coordinates all vanish is therefore a sum of pure tensors whose left
factors are multiples of the prime, and the prime may be moved across the tensor sign onto the
basis vectors, where it kills them.

That is what removes the hypothesis of finite exponent from the modules of the family, and it is
what makes the orbit decomposition of complete cohomology usable for the groups that actually
occur in class field theory: the units of the completions of a number field at its places, which
are killed by nothing.

## Main definitions

* `InverseGalois.CFT.Tate.nsmulAddSubgroup`: the multiples of a natural number in an abelian group.
* `InverseGalois.CFT.tensorSectionsIsoOfEquivPi`: **the sections of an arbitrary family tensored
  with finite coefficients are the sections of the tensored family.**
* `InverseGalois.CFT.tateTensorOrbitsEquivOfEquivPi`: **the complete cohomology of the sections of
  an arbitrary family tensored with finite coefficients, as a product of local contributions, one
  for each orbit of the index set.**

## Main results

* `InverseGalois.CFT.Tate.exists_nsmul_of_coordInv_eq_zero`: a family of elements whose associated
  sum of pure tensors vanishes consists of multiples of the prime.
* `InverseGalois.CFT.bijective_sectionsTensorMap_of_equivPi`: the comparison map of the sections
  with the tensored family is bijective.
* `InverseGalois.CFT.isZero_tateModule_tensor_orbitSectionsRep_of_equivPi`: the complete cohomology
  of the tensored sections vanishes when every local contribution does.

## Tags

Tate cohomology, tensor product, orbit, Shapiro's lemma, decomposition group, idele
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate

open scoped TensorProduct

noncomputable section

namespace Tate

/-! ### The quotient by the multiples of a prime -/

section Quot

variable (p : ℕ) (M : Type*) [AddCommGroup M]

/-- The multiples of a natural number in an abelian group, as a subgroup: an element belongs
exactly when it is that many times some element. -/
def nsmulAddSubgroup : AddSubgroup M where
  carrier := {x | ∃ y : M, p • y = x}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [smul_add]⟩
  zero_mem' := ⟨0, smul_zero _⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by rw [smul_neg]⟩

/-- Membership in the multiples of a natural number is divisibility by it. -/
theorem mem_nsmulAddSubgroup {x : M} :
    x ∈ nsmulAddSubgroup p M ↔ ∃ y : M, p • y = x := Iff.rfl

/-- **The quotient of an abelian group by the multiples of a natural number is killed by that
number**, whatever the group. -/
theorem nsmul_quotient_eq_zero (y : M ⧸ nsmulAddSubgroup p M) : p • y = 0 := by
  obtain ⟨m, rfl⟩ := QuotientAddGroup.mk_surjective y
  show p • (QuotientAddGroup.mk' (nsmulAddSubgroup p M) m) = 0
  rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨m, rfl⟩

end Quot

/-! ### Coordinates without a hypothesis on the module -/

section Coord

variable {p d : ℕ} [Fact p.Prime] {W M N : Type*} [AddCommGroup W] [Module ℤ W]
  [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  (e : W ≃+ (Fin d → ZMod p))

/-- Assembling a family of elements into a sum of pure tensors along a basis of the coefficients is
natural in the module. -/
theorem coordInv_map (f : M →ₗ[ℤ] N) (g : Fin d → M) :
    TensorProduct.map f LinearMap.id (coordInv M e g) = coordInv N e (fun j => f (g j)) := by
  rw [coordInv_apply, map_sum, coordInv_apply]
  exact Finset.sum_congr rfl fun j _ => TensorProduct.map_tmul _ _ _ _

/-- **Every element of a module tensored with coefficients of finite rank over the prime field is a
sum of pure tensors along a basis of the coefficients.**  No hypothesis on the module is needed:
the coordinates of a pure tensor are read off from the coordinates of its right factor. -/
theorem surjective_coordInv : Function.Surjective (coordInv M e) := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul m x =>
    refine ⟨fun j => (e x j).val • m, ?_⟩
    rw [coordInv_apply]
    calc ∑ j, ((e x j).val • m) ⊗ₜ[ℤ] coordVec e j
        = ∑ j, m ⊗ₜ[ℤ] ((e x j).val • coordVec e j) :=
          Finset.sum_congr rfl fun j _ => nsmul_tmul _ _ _
      _ = m ⊗ₜ[ℤ] ∑ j, (e x j).val • coordVec e j := by rw [TensorProduct.tmul_sum]
      _ = m ⊗ₜ[ℤ] x := by rw [sum_nsmul_coordVec]
  | add t t' ht ht' =>
    obtain ⟨g, rfl⟩ := ht
    obtain ⟨g', rfl⟩ := ht'
    exact ⟨g + g', map_add _ _ _⟩

/-- **A family of elements of a module whose associated sum of pure tensors vanishes consists of
multiples of the prime.**  The family is pushed into the quotient by those multiples, which is
killed by the prime, so the coordinate map available there returns it unchanged; the sum of pure
tensors having vanished, the family in the quotient is zero. -/
theorem exists_nsmul_of_coordInv_eq_zero (g : Fin d → M) (hg : coordInv M e g = 0) (j : Fin d) :
    ∃ m : M, p • m = g j := by
  have hq : coordInv (M ⧸ nsmulAddSubgroup p M) e
      (fun i => intLinearOfAddHom (QuotientAddGroup.mk' (nsmulAddSubgroup p M)) (g i)) = 0 := by
    rw [← coordInv_map e (intLinearOfAddHom (QuotientAddGroup.mk' (nsmulAddSubgroup p M))) g, hg,
      map_zero]
  have hcc := coordMap_coordInv e (nsmul_quotient_eq_zero p M)
    (fun i => intLinearOfAddHom (QuotientAddGroup.mk' (nsmulAddSubgroup p M)) (g i))
  rw [hq, map_zero] at hcc
  have h1 : QuotientAddGroup.mk' (nsmulAddSubgroup p M) (g j) = 0 := by
    have hj := congrFun hcc j
    rw [Pi.zero_apply] at hj
    exact hj.symm
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h1
  exact h1

end Coord

end Tate

/-! ### The sections of an arbitrary family -/

section Sections

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (W : Rep ℤ G) {p d : ℕ} [Fact p.Prime]
  (e : ↥W.V ≃+ (Fin d → ZMod p))

include e in
/-- **Coefficients of finite rank over the prime field pass through the sections of an arbitrary
family.**  Surjectivity is coordinatewise: a section of the tensored family is a family of
coordinates at each index, and those coordinates assemble to a section.  Injectivity is the
divisibility criterion: the coordinates of an element of the kernel are divisible by the prime at
every index, so the prime may be moved onto the basis vectors of the coefficients, which it
kills. -/
theorem bijective_sectionsTensorMap_of_equivPi : Function.Bijective (sectionsTensorMap F W) := by
  constructor
  · refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun t ht => ?_)
    obtain ⟨g, rfl⟩ := Tate.surjective_coordInv (M := ↥(orbitSectionsRep F).V) e t
    have hx : ∀ (x : X) (j : Fin d), ∃ m : M x, p • m = g j x := by
      intro x
      have hmap : TensorProduct.map (sectionsProj F x) LinearMap.id
          (coordInv (↥(orbitSectionsRep F).V) e g) = coordInv (M x) e (fun j => g j x) :=
        Tate.coordInv_map e (sectionsProj F x) g
      refine Tate.exists_nsmul_of_coordInv_eq_zero e (fun j => g j x) ?_
      rw [← hmap, ← sectionsTensorMap_apply]
      exact congrFun ht x
    choose c hc using hx
    rw [coordInv_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : g j = p • (fun x => c x j : ↥(orbitSectionsRep F).V) :=
      funext fun x => (hc x j).symm
    rw [hj, nsmul_tmul, nsmul_eq_zero_of_equivPi e, TensorProduct.tmul_zero]
  · intro s
    choose f hf using fun x : X => Tate.surjective_coordInv (M := M x) e (s x)
    refine ⟨coordInv (↥(orbitSectionsRep F).V) e (fun j => (fun x => f x j)), funext fun x => ?_⟩
    rw [sectionsTensorMap_apply, Tate.coordInv_map]
    exact hf x

include e in
/-- **The sections of an arbitrary family tensored with coefficients of finite rank over the prime
field are the sections of the tensored family.** -/
def tensorSectionsIsoOfEquivPi :
    tensorObj (orbitSectionsRep F) W ≅ orbitSectionsRep (F.tensorRight W) :=
  isoOfBijective (tensorSectionsHom F W) (bijective_sectionsTensorMap_of_equivPi F W e)

end Sections

/-! ### The orbit decomposition for an arbitrary family -/

section Orbits

variable {G X : Type} [Group G] [MulAction G X] [Finite G] {M : X → Type}
  [∀ x, AddCommGroup (M x)] (F : FamilyAction M G) (W : Rep ℤ G) {p d : ℕ} [Fact p.Prime]
  (e : ↥W.V ≃+ (Fin d → ZMod p))
  (x₀ : ∀ ω : orbitRel.Quotient G X, ω.orbit) {H : orbitRel.Quotient G X → Subgroup G}
  (hH : ∀ (ω : orbitRel.Quotient G X) (g : G), g • x₀ ω = x₀ ω → g ∈ H ω)
  (hH' : ∀ (ω : orbitRel.Quotient G X) (g : ↥(H ω)), (g : G) • x₀ ω = x₀ ω)

include e hH hH' in
/-- **The complete cohomology of the sections of an arbitrary family tensored with coefficients of
finite rank over the prime field is the product, over the orbits of the index set, of the complete
cohomology of the stabiliser of a chosen point of the orbit with coefficients in the module there
tensored with the restricted coefficients.**  This is the shape the group of ideles takes: the
contribution at a place is the units of the completion tensored with the coefficients, read in the
decomposition group of the place. -/
def tateTensorOrbitsEquivOfEquivPi (n : ℤ) :
    tateModule (tensorObj (orbitSectionsRep F) W) n ≃+
      ∀ ω : orbitRel.Quotient G X,
        tateModule (tensorObj (orbitStabRep (x₀ ω) (hH' ω) (orbitFamily F ω))
          (resObj (H ω) W)) n :=
  (tateMapIso (tensorSectionsIsoOfEquivPi F W e) n).toLinearEquiv.toAddEquiv.trans <|
    (tateOrbitsLocalEquiv (F.tensorRight W) x₀ hH hH' n).trans <|
      AddEquiv.piCongrRight fun ω =>
        (tateMapIso (orbitStabTensorIso F W (x₀ ω) (hH' ω)) n).toLinearEquiv.toAddEquiv

include e hH hH' in
/-- **The complete cohomology of the tensored sections of an arbitrary family vanishes as soon as
every local contribution vanishes.** -/
theorem isZero_tateModule_tensor_orbitSectionsRep_of_equivPi (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient G X, Limits.IsZero
      (tateModule (tensorObj (orbitStabRep (x₀ ω) (hH' ω) (orbitFamily F ω))
        (resObj (H ω) W)) n)) :
    Limits.IsZero (tateModule (tensorObj (orbitSectionsRep F) W) n) := by
  refine isZero_tateModule_of_iso (tensorSectionsIsoOfEquivPi F W e) n ?_
  refine isZero_tateModule_orbitSectionsRep (F.tensorRight W) x₀ hH hH' n fun ω => ?_
  exact isZero_tateModule_of_iso (orbitStabTensorIso F W (x₀ ω) (hH' ω)) n (h ω)

end Orbits

end

end InverseGalois.CFT
