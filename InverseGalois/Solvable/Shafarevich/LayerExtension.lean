/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.SemidirectExtension
import InverseGalois.Solvable.Shafarevich.Layer
import InverseGalois.Solvable.Shafarevich.QuotientChar

/-!
# One layer of the descending `p`-central series, as an extension

The terms of the descending `p`-central series are characteristic, so a group with operators hands
its operators down to every quotient by one of them, and the projection of one quotient onto the
previous one commutes with the operators.  Dividing by one term rather than the next therefore
gives an extension of semidirect products

`1 → layer → (P / pCentral (j + 1)) ⋊ U → (P / pCentral j) ⋊ U → 1`

whose kernel is the layer of the series, the operator group being carried along untouched.  That is
the extension a group is built out of one layer at a time, and its class is the obstruction to
carrying a solution of an embedding problem from one quotient of the series to the next.

The kernel is central in the normal factor, so conjugation inside the extension moves it only by
the operators: the quotient acts on the layer through the projection of the semidirect product onto
the operator group.  That is the identification a cohomological reading needs, since the class of
the extension is formed for conjugation while the shrinking count is formed for the operators.

Finally a homomorphism of the underlying groups commuting with the operators induces a morphism of
the whole picture, in the shape a comparison of the two classes asks for: it is a homomorphism of
the middle terms carrying the kernel of one extension into the kernel of the other and covering a
homomorphism of the quotients.

## Main definitions

* `InverseGalois.Shafarevich.pCentralAut` — the operators, on a quotient by a term of the series.
* `InverseGalois.Shafarevich.pCentralProj` — the projection of one quotient onto the previous.
* `InverseGalois.Shafarevich.pCentralMap` — the map of quotients induced by a homomorphism.
* `InverseGalois.Shafarevich.layerExtension` — **the extension of semidirect products given by one
  layer of the descending `p`-central series.**
* `InverseGalois.Shafarevich.layerSemidirectAction` — the quotient acts on the layer through the
  operator group.

## Main results

* `InverseGalois.Shafarevich.ker_pCentralProj` — the kernel of the projection is the layer.
* `InverseGalois.Shafarevich.conjActHom_layerExtension` — **conjugation inside the extension is the
  action of the operator group.**
* `InverseGalois.Shafarevich.smul_eq_conjActHom_layerExtension` — the compatibility the class of an
  extension is formed with.
* `InverseGalois.Shafarevich.inl_layerSemidirectMap` and
  `InverseGalois.Shafarevich.rightHom_layerSemidirectMap` — **an equivariant homomorphism induces a
  morphism of the two extensions.**
* `InverseGalois.Shafarevich.layerSemidirectMap_surjective` — an equivariant homomorphism which is
  onto induces a morphism which is onto.

## Tags

p-central series, group extension, semidirect product, operator group, embedding problem
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

/-! ### The operators on a quotient of the series -/

section Aut

variable (p : ℕ) {P U : Type*} [Group P] [Group U] (χ : U →* MulAut P) (n : ℕ)

/-- **The operators of a group act on every quotient of its descending `p`-central series**, the
terms of that series being characteristic. -/
def pCentralAut : U →* MulAut (P ⧸ pCentral p P n) :=
  (_root_.Shafarevich.quotientChar (pCentral p P n)).comp χ

@[simp]
theorem pCentralAut_mk (u : U) (x : P) :
    pCentralAut p χ n u (QuotientGroup.mk x) = QuotientGroup.mk (χ u x) := rfl

end Aut

/-! ### The projections and the maps of quotients -/

section Proj

variable (p : ℕ) (P : Type*) {Q : Type*} [Group P] [Group Q] (n : ℕ)

/-- The projection of one quotient of the descending `p`-central series onto the previous one. -/
def pCentralProj : P ⧸ pCentral p P (n + 1) →* P ⧸ pCentral p P n :=
  QuotientGroup.map _ _ (MonoidHom.id P) fun _ hx => pCentral_succ_le p n hx

@[simp]
theorem pCentralProj_mk (x : P) :
    pCentralProj p P n (QuotientGroup.mk x) = QuotientGroup.mk x := rfl

theorem pCentralProj_surjective : Function.Surjective (pCentralProj p P n) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | _ x => exact ⟨QuotientGroup.mk x, rfl⟩

/-- **The kernel of the projection is the layer of the series.** -/
theorem ker_pCentralProj : (pCentralProj p P n).ker = layerSub p P n := by
  ext y
  induction y using QuotientGroup.induction_on with
  | _ x =>
    rw [MonoidHom.mem_ker, pCentralProj_mk, QuotientGroup.eq_one_iff]
    refine ⟨fun hx => mk_mem_layerSub hx, ?_⟩
    rintro ⟨z, hz, hzx⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hzx
    simpa using mul_mem hz (pCentral_succ_le p n hzx)

theorem range_subtype_eq_ker_pCentralProj :
    (layerSub p P n).subtype.range = (pCentralProj p P n).ker := by
  rw [Subgroup.range_subtype, ker_pCentralProj]

variable {P}

/-- The map of quotients of the descending `p`-central series induced by a homomorphism. -/
def pCentralMap (f : P →* Q) : P ⧸ pCentral p P n →* Q ⧸ pCentral p Q n :=
  QuotientGroup.map _ _ f (Subgroup.map_le_iff_le_comap.mp (map_pCentral_le p f n))

@[simp]
theorem pCentralMap_mk (f : P →* Q) (x : P) :
    pCentralMap p n f (QuotientGroup.mk x) = QuotientGroup.mk (f x) := rfl

theorem pCentralMap_succ (f : P →* Q) : pCentralMap p (n + 1) f = quotientMap p f n := rfl

/-- The projection commutes with the map induced by a homomorphism. -/
theorem pCentralProj_comp_pCentralMap (f : P →* Q) :
    (pCentralProj p Q n).comp (pCentralMap p (n + 1) f)
      = (pCentralMap p n f).comp (pCentralProj p P n) := by
  refine MonoidHom.ext fun y => ?_
  induction y using QuotientGroup.induction_on with
  | _ x => rfl

variable {U : Type*} [Group U] (χ : U →* MulAut P) (χ' : U →* MulAut Q)

/-- The projection commutes with the operators. -/
theorem pCentralProj_comp_pCentralAut (u : U) :
    (pCentralProj p P n).comp (pCentralAut p χ (n + 1) u).toMonoidHom
      = (pCentralAut p χ n u).toMonoidHom.comp (pCentralProj p P n) := by
  refine MonoidHom.ext fun y => ?_
  induction y using QuotientGroup.induction_on with
  | _ x => rfl

/-- The map induced by an equivariant homomorphism commutes with the operators. -/
theorem pCentralMap_comp_pCentralAut {f : P →* Q}
    (hf : ∀ u : U, f.comp (χ u).toMonoidHom = (χ' u).toMonoidHom.comp f) (u : U) :
    (pCentralMap p n f).comp (pCentralAut p χ n u).toMonoidHom
      = (pCentralAut p χ' n u).toMonoidHom.comp (pCentralMap p n f) := by
  refine MonoidHom.ext fun y => ?_
  induction y using QuotientGroup.induction_on with
  | _ x => exact congrArg QuotientGroup.mk (DFunLike.congr_fun (hf u) x)

end Proj

/-! ### The extension -/

section Extension

variable (p : ℕ) {P U : Type*} [Group P] [Group U] (χ : U →* MulAut P) (j : ℕ)

/-- **The extension of semidirect products given by one layer of the descending `p`-central
series.**  The operator group is carried along untouched, and the kernel is the layer. -/
def layerExtension : GroupExtension ↥(layerSub p P j)
    ((P ⧸ pCentral p P (j + 1)) ⋊[pCentralAut p χ (j + 1)] U)
    ((P ⧸ pCentral p P j) ⋊[pCentralAut p χ j] U) :=
  CFT.semidirectExtension (layerSub p P j).subtype (pCentralProj p P j)
    (layerSub p P j).subtype_injective (pCentralProj_surjective p P j)
    (range_subtype_eq_ker_pCentralProj p P j) (pCentralProj_comp_pCentralAut p j χ)

@[simp]
theorem layerExtension_inl (v : ↥(layerSub p P j)) :
    (layerExtension p χ j).inl v = SemidirectProduct.inl (v : P ⧸ pCentral p P (j + 1)) := rfl

@[simp]
theorem layerExtension_rightHom (x : (P ⧸ pCentral p P (j + 1)) ⋊[pCentralAut p χ (j + 1)] U) :
    (layerExtension p χ j).rightHom x = ⟨pCentralProj p P j x.left, x.right⟩ := rfl

/-- **The quotient of the extension acts on the layer through the operator group.** -/
def layerSemidirectAction [MulDistribMulAction U ↥(layerSub p P j)] :
    MulDistribMulAction ((P ⧸ pCentral p P j) ⋊[pCentralAut p χ j] U) ↥(layerSub p P j) :=
  MulDistribMulAction.compHom _ (SemidirectProduct.rightHom : _ →* U)

attribute [local instance] layerSemidirectAction

variable [MulDistribMulAction U ↥(layerSub p P j)]
  (hsmul : ∀ (u : U) (v : ↥(layerSub p P j)), u • v = layerSubMap p (χ u).toMonoidHom j v)

omit [MulDistribMulAction U ↥(layerSub p P j)] in
/-- The kernel of the extension is central in the normal factor. -/
theorem layerSub_central (v : ↥(layerSub p P j)) (e : P ⧸ pCentral p P (j + 1)) :
    (v : P ⧸ pCentral p P (j + 1)) * e = e * v :=
  (Subgroup.mem_center_iff.mp (layerSub_le_center v.2) e).symm

include hsmul in
/-- The operators move the kernel of the extension as they move the layer. -/
theorem pCentralAut_subtype (u : U) (v : ↥(layerSub p P j)) :
    pCentralAut p χ (j + 1) u ((layerSub p P j).subtype v)
      = (layerSub p P j).subtype (u • v) := by
  rw [hsmul]
  rfl

include hsmul in
/-- **Conjugation inside the extension is the action of the operator group.** -/
theorem conjActHom_layerExtension (x : (P ⧸ pCentral p P j) ⋊[pCentralAut p χ j] U)
    (v : ↥(layerSub p P j)) :
    (layerExtension p χ j).conjActHom x v = x.right • v :=
  CFT.conjActHom_semidirectExtension _ _ _ _ _ _ (layerSub_central p j)
    (pCentralAut_subtype p χ j hsmul) x v

include hsmul in
/-- **The action of the quotient on the layer is conjugation inside the extension**, which is the
compatibility the class of an extension is formed with. -/
theorem smul_eq_conjActHom_layerExtension
    (x : (P ⧸ pCentral p P j) ⋊[pCentralAut p χ j] U) (v : ↥(layerSub p P j)) :
    x • v = (layerExtension p χ j).conjActHom x v :=
  (conjActHom_layerExtension p χ j hsmul x v).symm

end Extension

/-! ### A morphism of two such extensions -/

section Morphism

variable (p : ℕ) {P Q U : Type*} [Group P] [Group Q] [Group U] {χ : U →* MulAut P}
  {χ' : U →* MulAut Q} (j : ℕ) {f : P →* Q}
  (hf : ∀ u : U, f.comp (χ u).toMonoidHom = (χ' u).toMonoidHom.comp f)

/-- The homomorphism of semidirect products induced by an equivariant homomorphism. -/
def layerSemidirectMap (n : ℕ) :
    (P ⧸ pCentral p P n) ⋊[pCentralAut p χ n] U →* (Q ⧸ pCentral p Q n) ⋊[pCentralAut p χ' n] U :=
  SemidirectProduct.map (pCentralMap p n f) (MonoidHom.id U)
    (pCentralMap_comp_pCentralAut p n χ χ' hf)

@[simp]
theorem layerSemidirectMap_apply (n : ℕ) (x : (P ⧸ pCentral p P n) ⋊[pCentralAut p χ n] U) :
    layerSemidirectMap p hf n x = ⟨pCentralMap p n f x.left, x.right⟩ := rfl

/-- **An equivariant homomorphism which is onto induces a morphism of semidirect products which is
onto**, the operator group being carried along untouched. -/
theorem layerSemidirectMap_surjective (n : ℕ) (hfs : Function.Surjective f) :
    Function.Surjective (layerSemidirectMap p hf n) := by
  rintro ⟨y, u⟩
  induction y using QuotientGroup.induction_on with
  | _ x =>
    obtain ⟨z, rfl⟩ := hfs x
    exact ⟨⟨QuotientGroup.mk z, u⟩, rfl⟩

/-- **The morphism of extensions carries the kernel above into the kernel below**, the map of the
kernels being the map of layers. -/
theorem inl_layerSemidirectMap (v : ↥(layerSub p P j)) :
    layerSemidirectMap p hf (j + 1) ((layerExtension p χ j).inl v)
      = (layerExtension p χ' j).inl (layerSubMap p f j v) := rfl

/-- **The morphism of extensions covers the morphism of the quotients.** -/
theorem rightHom_layerSemidirectMap
    (x : (P ⧸ pCentral p P (j + 1)) ⋊[pCentralAut p χ (j + 1)] U) :
    (layerExtension p χ' j).rightHom (layerSemidirectMap p hf (j + 1) x)
      = layerSemidirectMap p hf j ((layerExtension p χ j).rightHom x) := by
  refine SemidirectProduct.ext ?_ rfl
  exact DFunLike.congr_fun (pCentralProj_comp_pCentralMap p j f) x.left

end Morphism

end InverseGalois.Shafarevich
