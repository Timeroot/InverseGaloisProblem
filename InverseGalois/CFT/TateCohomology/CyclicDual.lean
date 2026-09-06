/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DualityFinite

/-!
# The duality of a cyclic representation

Fix a representation whose underlying group is finite and cyclic, and a second representation
killed by the order of the first.  The maps of the second into the first and the maps of the first
into the second are then dual to one another: composing a map into the cyclic representation with
a map out of it produces an endomorphism of the cyclic group, evaluation at a generator turns that
endomorphism into an element, and an injective character of the cyclic group reads the element off
as a value in the rational circle.

The resulting pairing is a bijection because it factors as the composition of two bijections:
evaluation at a generator identifies the maps out of the cyclic representation with the elements
of the target, and composing with an injective character identifies the maps into the cyclic
representation with the characters of the target.  It respects the action of the group because the
endomorphisms of a cyclic group commute, so conjugating the composite by a group element leaves it
alone.  Complete cohomology therefore carries the pairing to a bijection in every degree, and
combining that with the duality between the classes of a representation and the characters of the
classes of its functionals gives the duality in the title.

## Main definitions

* `InverseGalois.CFT.Tate.cyclicChar`: an injective character of a finite cyclic group.
* `InverseGalois.CFT.Tate.linHomObj`: the linear maps between two representations, with the group
  acting by conjugation.
* `InverseGalois.CFT.Tate.cartierIso`: **the maps into a cyclic representation are the functionals
  on the maps out of it.**
* `InverseGalois.CFT.Tate.cartierPairing`: **the complete cohomology of the maps out of a cyclic
  representation is dual to the complete cohomology of the maps into it.**

## Main results

* `InverseGalois.CFT.Tate.exists_comp_cyclicChar`: every character of a group killed by the order
  of a finite cyclic group factors through an injective character of it.
* `InverseGalois.CFT.Tate.bijective_evalGen`: **evaluation at a generator is a bijection of the
  homomorphisms of a cyclic group onto a group killed by its order.**
* `InverseGalois.CFT.Tate.comp_comm_of_isAddCyclic`: the endomorphisms of a cyclic group commute.
* `InverseGalois.CFT.Tate.exists_cartierPairing_eq`: **every character of a submodule of the
  complete cohomology of the maps out of a cyclic representation is realised by the pairing.**

## Tags

cyclic group, character, duality, complete cohomology, Tate cohomology, representation
-/

namespace InverseGalois.CFT.Tate

open AddSubgroup CategoryTheory

universe u

noncomputable section

/-! ### An injective character of a finite cyclic group -/

section CyclicChar

theorem card_zmultiples_circleGen {n : ℕ} (hn : 0 < n) :
    Nat.card ↥(zmultiples (circleGen n)) = n := by
  rw [Nat.card_zmultiples, addOrderOf_circleGen hn]

variable (M : Type*) [AddCommGroup M] [IsAddCyclic M] [Finite M]

/-- **A finite cyclic group is the torsion of the rational circle of its order.** -/
def cyclicCircleEquiv : M ≃+ ↥(zmultiples (circleGen (Nat.card M))) :=
  addEquivOfAddCyclicCardEq (card_zmultiples_circleGen Nat.card_pos).symm

/-- **An injective character of a finite cyclic group.** -/
def cyclicChar : M →+ AddCircle (1 : ℚ) :=
  (zmultiples (circleGen (Nat.card M))).subtype.comp (cyclicCircleEquiv M).toAddMonoidHom

theorem cyclicChar_apply (a : M) : cyclicChar M a = ((cyclicCircleEquiv M a : AddCircle (1 : ℚ))) :=
  rfl

theorem cyclicChar_injective : Function.Injective (cyclicChar M) :=
  Subtype.val_injective.comp (cyclicCircleEquiv M).injective

variable {M}

/-- **Every character of a group killed by the order of a finite cyclic group factors through an
injective character of it.** -/
theorem exists_comp_cyclicChar {B : Type*} [AddCommGroup B] (hB : ∀ b : B, Nat.card M • b = 0)
    (χ : B →+ AddCircle (1 : ℚ)) : ∃ f : B →+ M, (cyclicChar M).comp f = χ := by
  have hmem : ∀ b : B, χ b ∈ zmultiples (circleGen (Nat.card M)) := by
    intro b
    refine (nsmul_eq_zero_iff_mem_zmultiples Nat.card_pos _).1 ?_
    rw [← _root_.map_nsmul, hB b, _root_.map_zero]
  refine ⟨(cyclicCircleEquiv M).symm.toAddMonoidHom.comp (χ.codRestrict _ hmem), ?_⟩
  refine AddMonoidHom.ext fun b => ?_
  show ((cyclicCircleEquiv M) ((cyclicCircleEquiv M).symm ⟨χ b, hmem b⟩) : AddCircle (1 : ℚ)) = χ b
  rw [AddEquiv.apply_symm_apply]

end CyclicChar

/-! ### Homomorphisms out of a cyclic group -/

section Eval

/-- Precomposition with an isomorphism, as a bijection of the homomorphisms. -/
def precompEquiv {X Y B : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup B]
    (e : X ≃+ Y) : (Y →+ B) ≃ (X →+ B) where
  toFun h := h.comp e.toAddMonoidHom
  invFun h := h.comp e.symm.toAddMonoidHom
  left_inv h := by ext y; simp
  right_inv h := by ext x; simp

theorem zmodHomEquiv_symm_apply {n : ℕ} {B : Type*} [AddCommGroup B] (h : ZMod n →+ B) :
    ((zmodHomEquiv n B).symm h).1 = h 1 := by
  conv_rhs => rw [← Equiv.apply_symm_apply (zmodHomEquiv n B) h]
  rw [zmodHomEquiv_apply_one]

variable (M : Type*) [AddCommGroup M] [IsAddCyclic M]

/-- A cyclic group is the integers modulo its order. -/
def zmodCyclicEquiv : ZMod (Nat.card M) ≃+ M := zmodAddCyclicAddEquiv inferInstance

/-- A generator of a cyclic group. -/
def cyclicGen : M := zmodCyclicEquiv M 1

/-- **The homomorphisms of a cyclic group into a group killed by its order are the elements of that
group**, by evaluation at a generator. -/
def cyclicHomEquiv {B : Type*} [AddCommGroup B] (hB : ∀ b : B, Nat.card M • b = 0) :
    (M →+ B) ≃ B :=
  ((precompEquiv (zmodCyclicEquiv M)).trans
    (zmodHomEquiv (Nat.card M) B).symm).trans (Equiv.subtypeUnivEquiv hB)

theorem cyclicHomEquiv_apply {B : Type*} [AddCommGroup B] (hB : ∀ b : B, Nat.card M • b = 0)
    (x : M →+ B) : cyclicHomEquiv M hB x = x (cyclicGen M) :=
  zmodHomEquiv_symm_apply (x.comp (zmodCyclicEquiv M).toAddMonoidHom)

/-- **Evaluation at a generator is a bijection of the homomorphisms of a cyclic group onto a group
killed by its order.** -/
theorem bijective_evalGen {B : Type*} [AddCommGroup B] (hB : ∀ b : B, Nat.card M • b = 0) :
    Function.Bijective (fun x : M →+ B => x (cyclicGen M)) := by
  have h : (fun x : M →+ B => x (cyclicGen M)) = cyclicHomEquiv M hB :=
    funext fun x => (cyclicHomEquiv_apply M hB x).symm
  rw [h]
  exact (cyclicHomEquiv M hB).bijective

end Eval

/-! ### The endomorphisms of a cyclic group commute -/

section Comm

variable {M : Type*} [AddCommGroup M] [Module ℤ M] [IsAddCyclic M]

/-- **The endomorphisms of a cyclic group commute with one another.** -/
theorem comp_comm_of_isAddCyclic (φ ψ : M →ₗ[ℤ] M) : φ ∘ₗ ψ = ψ ∘ₗ φ := by
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := M)
  obtain ⟨m, hm⟩ := hg (φ g)
  obtain ⟨l, hl⟩ := hg (ψ g)
  have hm' : m • g = φ g := hm
  have hl' : l • g = ψ g := hl
  have key : φ (ψ g) = ψ (φ g) := by
    rw [← hl', ← hm', _root_.map_zsmul, _root_.map_zsmul, ← hm', ← hl', smul_comm]
  refine LinearMap.ext fun x => ?_
  obtain ⟨k, hk⟩ := hg x
  have hk' : k • g = x := hk
  show φ (ψ x) = ψ (φ x)
  rw [← hk', _root_.map_zsmul, _root_.map_zsmul, _root_.map_zsmul, _root_.map_zsmul, key]

end Comm

/-! ### The maps between two representations -/

section LinHom

variable {k G : Type u} [CommRing k] [Group G] (A B : Rep k G)

/-- The linear maps between two representations, with the group acting by conjugation. -/
def linHomObj : Rep k G := Rep.of (Representation.linHom A.ρ B.ρ)

theorem linHomObj_rho : (linHomObj A B).ρ = Representation.linHom A.ρ B.ρ := rfl

instance finite_linHomObj [Finite ↥A.V] [Finite ↥B.V] : Finite ↥(linHomObj A B).V := by
  have h : Finite (↥A.V →ₗ[k] ↥B.V) :=
    Finite.of_injective (fun f : ↥A.V →ₗ[k] ↥B.V => (f : ↥A.V → ↥B.V)) DFunLike.coe_injective
  exact h

end LinHom

/-! ### The pairing of a cyclic representation -/

section Cartier

variable {G : Type} [Group G] (A B : Rep ℤ G) [IsAddCyclic ↥A.V] [Finite ↥A.V]

/-- Evaluation at a generator of a cyclic representation. -/
def evalGen : ↥(linHomObj A B).V →ₗ[ℤ] ↥B.V := LinearMap.applyₗ (cyclicGen ↥A.V)

omit [Finite ↥A.V] in
theorem evalGen_apply (x : ↥A.V →ₗ[ℤ] ↥B.V) : evalGen A B x = x (cyclicGen ↥A.V) := rfl

omit [Finite ↥A.V] in
/-- **Evaluation at a generator identifies the maps out of a cyclic representation with the vectors
of a representation killed by its order.** -/
theorem bijective_evalGen_linear (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0) :
    Function.Bijective (evalGen A B) := by
  have h : (evalGen A B : ↥(linHomObj A B).V → ↥B.V)
      = (fun x : ↥A.V →+ ↥B.V => x (cyclicGen ↥A.V)) ∘ intLinearEquiv.symm := rfl
  rw [h]
  exact (bijective_evalGen ↥A.V hB).comp intLinearEquiv.symm.bijective

/-- **The functional attached to a map into a cyclic representation**: compose, evaluate at a
generator, and read the result off with an injective character. -/
def cartierFun (f : ↥B.V →ₗ[ℤ] ↥A.V) : ↥(linHomObj A B).V →ₗ[ℤ] AddCircle (1 : ℚ) :=
  (intLinear (cyclicChar ↥A.V)).comp (f.comp (evalGen A B))

theorem cartierFun_apply (f : ↥B.V →ₗ[ℤ] ↥A.V) (x : ↥A.V →ₗ[ℤ] ↥B.V) :
    cartierFun A B f x = cyclicChar ↥A.V (f (x (cyclicGen ↥A.V))) := rfl

theorem cartierFun_injective (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0) :
    Function.Injective (cartierFun A B) := by
  intro f₁ f₂ h
  refine LinearMap.ext fun b => cyclicChar_injective ↥A.V ?_
  obtain ⟨x, hx⟩ := (bijective_evalGen_linear A B hB).2 b
  have hfx : cyclicChar ↥A.V (f₁ (evalGen A B x)) = cyclicChar ↥A.V (f₂ (evalGen A B x)) :=
    LinearMap.congr_fun h x
  rwa [hx] at hfx

theorem cartierFun_surjective (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0) :
    Function.Surjective (cartierFun A B) := by
  intro F
  let e : ↥(linHomObj A B).V ≃ₗ[ℤ] ↥B.V :=
    LinearEquiv.ofBijective (evalGen A B) (bijective_evalGen_linear A B hB)
  obtain ⟨f, hf⟩ := exists_comp_cyclicChar (M := ↥A.V) hB
    (F.comp (e.symm : ↥B.V →ₗ[ℤ] ↥(linHomObj A B).V)).toAddMonoidHom
  refine ⟨intLinear f, LinearMap.ext fun x => ?_⟩
  have h1 : cyclicChar ↥A.V (f (evalGen A B x)) = F (e.symm (evalGen A B x)) :=
    DFunLike.congr_fun hf (evalGen A B x)
  show cyclicChar ↥A.V (f (evalGen A B x)) = F x
  rw [h1]
  exact congrArg F (e.symm_apply_apply x)

/-- The pairing of the maps into a cyclic representation with the maps out of it, as a map of
additive groups. -/
def cartierAddHom :
    ↥(linHomObj B A).V →+ ↥(coeffDualObj (linHomObj A B) (AddCircle (1 : ℚ))).V where
  toFun f := cartierFun A B f
  map_zero' := LinearMap.ext fun _ => _root_.map_zero (intLinear (cyclicChar ↥A.V))
  map_add' _ _ := LinearMap.ext fun _ => _root_.map_add (intLinear (cyclicChar ↥A.V)) _ _

/-- **The pairing of the maps into a cyclic representation with the maps out of it.** -/
def cartierLinear :
    ↥(linHomObj B A).V →ₗ[ℤ] ↥(coeffDualObj (linHomObj A B) (AddCircle (1 : ℚ))).V :=
  intLinear (cartierAddHom A B)

theorem cartierLinear_eq (f : ↥B.V →ₗ[ℤ] ↥A.V) : cartierLinear A B f = cartierFun A B f := rfl

/-- The pairing respects the action of the group, the endomorphisms of a cyclic group commuting
with one another. -/
theorem cartierLinear_equivariant (g : G) :
    cartierLinear A B ∘ₗ (linHomObj B A).ρ g
      = (coeffDualObj (linHomObj A B) (AddCircle (1 : ℚ))).ρ g ∘ₗ cartierLinear A B := by
  refine LinearMap.ext fun (f : ↥B.V →ₗ[ℤ] ↥A.V) =>
    LinearMap.ext fun (x : ↥A.V →ₗ[ℤ] ↥B.V) => ?_
  have key : A.ρ g ∘ₗ (f ∘ₗ B.ρ g⁻¹ ∘ₗ x) = (f ∘ₗ B.ρ g⁻¹ ∘ₗ x) ∘ₗ A.ρ g :=
    comp_comm_of_isAddCyclic _ _
  show cyclicChar ↥A.V (A.ρ g (f (B.ρ g⁻¹ (x (cyclicGen ↥A.V)))))
      = cyclicChar ↥A.V (f (B.ρ g⁻¹ (x (A.ρ g⁻¹⁻¹ (cyclicGen ↥A.V)))))
  rw [inv_inv]
  exact congrArg (cyclicChar ↥A.V) (LinearMap.congr_fun key (cyclicGen ↥A.V))

theorem bijective_cartierLinear (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0) :
    Function.Bijective (cartierLinear A B) :=
  ⟨cartierFun_injective A B hB, cartierFun_surjective A B hB⟩

/-- The comparison of the maps into a cyclic representation with the functionals on the maps out
of it. -/
def cartierHom : linHomObj B A ⟶ coeffDualObj (linHomObj A B) (AddCircle (1 : ℚ)) :=
  mkHom (cartierLinear A B) (cartierLinear_equivariant A B)

theorem isIso_cartierHom (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0) : IsIso (cartierHom A B) := by
  haveI : IsIso (cartierHom A B).hom :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_cartierLinear A B hB)
  infer_instance

/-- **The maps into a cyclic representation are the functionals on the maps out of it.** -/
def cartierIso (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0) :
    linHomObj B A ≅ coeffDualObj (linHomObj A B) (AddCircle (1 : ℚ)) :=
  haveI := isIso_cartierHom A B hB
  asIso (cartierHom A B)

end Cartier

/-! ### The complete cohomology of a cyclic representation -/

section CartierTate

variable {G : Type} [Group G] [Finite G] (A B : Rep ℤ G) [IsAddCyclic ↥A.V] [Finite ↥A.V]
  [Finite ↥B.V] (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0)

omit [Finite ↥B.V] in
include hB in
theorem bijective_tateMap_cartierHom (n : ℤ) :
    Function.Bijective (tateMap (cartierHom A B) n) :=
  haveI := isIso_cartierHom A B hB
  bijective_tateMap_of_comp _ (CategoryTheory.inv (cartierHom A B))
    (IsIso.hom_inv_id _) (IsIso.inv_hom_id _) n

/-- **The complete cohomology of the maps out of a cyclic representation is dual to the complete
cohomology of the maps into it.** -/
def cartierPairing (n : ℤ) :
    ↥(tateModule (linHomObj A B) n) ≃ₗ[ℤ]
      (↥(tateModule (linHomObj B A) (-n - 1)) →ₗ[ℤ] AddCircle (1 : ℚ)) :=
  (tateDualPairing (linHomObj A B) n).trans
    (LinearEquiv.arrowCongr
      (LinearEquiv.ofBijective (tateMap (cartierHom A B) (-n - 1)).hom
        (bijective_tateMap_cartierHom A B hB (-n - 1)))
      (LinearEquiv.refl ℤ (AddCircle (1 : ℚ)))).symm

/-- **Every character of a submodule of the complete cohomology of the maps out of a cyclic
representation is realised by the pairing.** -/
theorem exists_cartierPairing_eq (n : ℤ) {T : Type} [AddCommGroup T] [Module ℤ T]
    (ι : T →ₗ[ℤ] ↥(tateModule (linHomObj B A) (-n - 1))) (hι : Function.Injective ι)
    (χ : T →ₗ[ℤ] AddCircle (1 : ℚ)) :
    ∃ x : ↥(tateModule (linHomObj A B) n), ∀ t : T, cartierPairing A B hB n x (ι t) = χ t := by
  obtain ⟨χ', hχ'⟩ := baer_addCircle.extension_property ι hι χ
  refine ⟨(cartierPairing A B hB n).symm χ', fun t => ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun hχ' t

end CartierTate

end

end InverseGalois.CFT.Tate
