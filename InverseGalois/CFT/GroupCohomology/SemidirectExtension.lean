/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.ToCocycle

/-!
# The extension of semidirect products attached to a central quotient

A group with operators, divided by a central subgroup which the operators preserve, gives an
extension of the semidirect product below by that subgroup: the operators are carried along
untouched and only the normal factor is divided.  This is the shape in which a group is built up one
layer of a central series at a time, the operator group staying fixed while the normal factor grows.

The kernel is commutative and central in the normal factor, so conjugation inside the extension
moves it only by the operators, and the action of the quotient on it is the action of the operator
group read through the projection of the semidirect product.  That identification is what a
cohomological reading of the extension needs, since the class of an extension is formed for the
action by conjugation and the count which kills it is formed for the action of the operator group.

## Main definitions

* `InverseGalois.CFT.semidirectExtension`: **the extension of semidirect products** determined by
  an operator-equivariant surjection with a prescribed kernel.

## Main results

* `InverseGalois.CFT.conjActHom_semidirectExtension`: **conjugation inside the extension is the
  action of the operator group**, when the kernel is central in the normal factor.
* `InverseGalois.CFT.smul_eq_conjActHom_semidirectExtension`: the same, read as the compatibility
  a class of an extension asks of an action of the quotient.

## Tags

group extension, semidirect product, central series, operator group, conjugation action
-/

namespace InverseGalois.CFT

open GroupExtension

/-! ### The extension -/

section Semidirect

variable {N E G U : Type*} [CommGroup N] [Group E] [Group G] [Group U]
  {φ : U →* MulAut E} {ψ : U →* MulAut G}
  (ι : N →* E) (f : E →* G) (hι : Function.Injective ι) (hf : Function.Surjective f)
  (hrange : ι.range = f.ker)
  (hfφ : ∀ u : U, f.comp (φ u).toMonoidHom = (ψ u).toMonoidHom.comp f)

/-- **The extension of semidirect products determined by an equivariant surjection.**  The operator
group is carried along untouched, so the kernel is the kernel of the surjection of the normal
factors. -/
def semidirectExtension : GroupExtension N (E ⋊[φ] U) (G ⋊[ψ] U) where
  inl := SemidirectProduct.inl.comp ι
  rightHom := SemidirectProduct.map f (MonoidHom.id U) hfφ
  inl_injective := SemidirectProduct.inl_injective.comp hι
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      have hn : f (ι n) = 1 := by
        rw [← MonoidHom.mem_ker, ← hrange]
        exact ⟨n, rfl⟩
      rw [MonoidHom.mem_ker]
      ext
      · exact hn
      · rfl
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hl : f x.left = 1 := congrArg SemidirectProduct.left hx
      have hr : x.right = 1 := congrArg SemidirectProduct.right hx
      have hmem : x.left ∈ ι.range := by
        rw [hrange, MonoidHom.mem_ker]
        exact hl
      obtain ⟨n, hn⟩ := hmem
      refine ⟨n, ?_⟩
      ext
      · exact hn
      · exact hr.symm
  rightHom_surjective := fun y => by
    obtain ⟨e, he⟩ := hf y.left
    refine ⟨⟨e, y.right⟩, ?_⟩
    ext
    · exact he
    · rfl

/-- The kernel of the extension sits in the normal factor. -/
theorem semidirectExtension_inl (n : N) :
    (semidirectExtension ι f hι hf hrange hfφ).inl n = SemidirectProduct.inl (ι n) := rfl

/-- The projection of the extension divides the normal factor and leaves the operators alone. -/
theorem semidirectExtension_rightHom (x : E ⋊[φ] U) :
    (semidirectExtension ι f hι hf hrange hfφ).rightHom x = ⟨f x.left, x.right⟩ := rfl

/-! ### The action on the kernel -/

variable [MulDistribMulAction U N]
  (hcentral : ∀ (n : N) (e : E), ι n * e = e * ι n)
  (hφι : ∀ (u : U) (n : N), φ u (ι n) = ι (u • n))

include hcentral hφι in
/-- **Conjugation inside the extension is the action of the operator group.**  A lift of an element
of the quotient is an element of the normal factor together with an operator; the operator moves the
kernel as it is meant to, and the element of the normal factor does not move it at all, the kernel
being central there. -/
theorem conjActHom_semidirectExtension (x : G ⋊[ψ] U) (n : N) :
    (semidirectExtension ι f hι hf hrange hfφ).conjActHom x n = x.right • n := by
  set S := semidirectExtension ι f hι hf hrange hfφ with hS
  obtain ⟨e, he⟩ := hf x.left
  have hx : S.rightHom (⟨e, x.right⟩ : E ⋊[φ] U) = x := by
    ext
    · exact he
    · rfl
  have key := S.inl_conjActHom (⟨e, x.right⟩ : E ⋊[φ] U) n
  rw [hx] at key
  refine S.inl_injective ?_
  rw [key]
  show (⟨e, x.right⟩ : E ⋊[φ] U) * SemidirectProduct.inl (ι n) * (⟨e, x.right⟩ : E ⋊[φ] U)⁻¹
    = SemidirectProduct.inl (ι (x.right • n))
  ext
  · have hinv : (φ x.right) ((φ x.right⁻¹) e⁻¹) = e⁻¹ := by
      have h1 : ((φ x.right) * (φ x.right⁻¹)) e⁻¹ = e⁻¹ := by
        rw [← _root_.map_mul, mul_inv_cancel, _root_.map_one]
        rfl
      exact h1
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, mul_one]
    rw [hinv, hφι, ← hcentral, mul_inv_cancel_right]
  · show x.right * 1 * x.right⁻¹ = 1
    simp

include hcentral hφι in
/-- **The action of the quotient on the kernel through the operator group is conjugation inside the
extension**, which is the compatibility the class of an extension is formed with. -/
theorem smul_eq_conjActHom_semidirectExtension [MulDistribMulAction (G ⋊[ψ] U) N]
    (hsmul : ∀ (x : G ⋊[ψ] U) (n : N), x • n = x.right • n) (x : G ⋊[ψ] U) (n : N) :
    x • n = (semidirectExtension ι f hι hf hrange hfφ).conjActHom x n := by
  rw [hsmul, conjActHom_semidirectExtension ι f hι hf hrange hfφ hcentral hφι]

end Semidirect

end InverseGalois.CFT
