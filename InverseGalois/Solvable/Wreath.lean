/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.Basic
import InverseGalois.Rigidity.RET.RegularQuotient

/-!
# Semidirect products as quotients of regular wreath products

Let `A` be a finite abelian group, `H` a finite group and `φ : H →* MulAut A` an action of `H`
on `A`.  The regular wreath product `A ≀ᵣ H` carries the *permutation* action of `H` on the
coordinates of `H → A`, which knows nothing about `φ`; the semidirect product `A ⋊[φ] H` carries
`φ` itself.  The two are nevertheless linked by the twisted total product
`π a = ∏ x : H, φ x (a x)`, which is well defined because `A` is commutative, and which turns the
coordinate shift `a ↦ a ∘ (p⁻¹ * ·)` into the automorphism `φ p`.  Consequently
`(a, p) ↦ (π a, p)` is a surjective group homomorphism `A ≀ᵣ H →* A ⋊[φ] H`.

This is the standard universal property of the wreath product in the shape that matters for the
inverse Galois problem: *every* split extension of `H` by an abelian group `A` — with an arbitrary
action `φ`, so an unbounded supply of groups for a fixed pair `(A, H)` — is a quotient of the one
group `A ≀ᵣ H`.  Since realizability over `ℚ`, and likewise regular realizability over `ℚ(T)`, is
closed under quotients, a single realization of `A ≀ᵣ H` realizes all of them at once.  This is the
engine behind the embedding-problem approach to solvable groups, where one climbs a chain of
abelian extensions and only ever has to realize wreath products.

## Main results

* `RegularWreathProduct.twistedProd` — the twisted total product `∏ x, φ x (a x)` of a family
  `a : H → A`, and its two structural properties `twistedProd_mul` and `twistedProd_comp_mul_left`.
* `RegularWreathProduct.toSemidirectProduct` — the homomorphism `A ≀ᵣ H →* A ⋊[φ] H`.
* `RegularWreathProduct.toSemidirectProduct_surjective` — it is surjective.
* `IsInverseGalois.semidirectProduct_of_wreath` — if `A ≀ᵣ H` is an inverse Galois group over `ℚ`,
  then so is `A ⋊[φ] H`, for every action `φ`.
* `IsRegularInverseGalois.semidirectProduct_of_wreath` — the same statement for regular
  realizations over `ℚ(T)`.
-/

namespace RegularWreathProduct

variable {A H : Type*} [CommGroup A] [Group H]

section Fintype

variable [Fintype H] (φ : H →* MulAut A)

/-- The **twisted total product** of a family `a : H → A`, namely `∏ x : H, φ x (a x)`.

The twist by `φ` is what makes this compatible with the coordinate shift built into the
multiplication of the regular wreath product; the product is well defined because `A` is
commutative. -/
def twistedProd (a : H → A) : A := ∏ x : H, φ x (a x)

@[simp]
theorem twistedProd_one : twistedProd φ (1 : H → A) = 1 := by
  simp [twistedProd]

/-- The twisted total product is multiplicative in the family. -/
theorem twistedProd_mul (a b : H → A) :
    twistedProd φ (a * b) = twistedProd φ a * twistedProd φ b := by
  simp [twistedProd, Finset.prod_mul_distrib]

/-- Shifting the coordinates of a family by `p` acts on the twisted total product as the
automorphism `φ p`. -/
theorem twistedProd_comp_mul_left (p : H) (b : H → A) :
    twistedProd φ (fun x ↦ b (p⁻¹ * x)) = φ p (twistedProd φ b) := by
  rw [twistedProd, twistedProd, map_prod]
  refine Fintype.prod_equiv (Equiv.mulLeft p⁻¹) _ _ fun x ↦ ?_
  rw [Equiv.coe_mulLeft, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]

/-- The canonical homomorphism from the regular wreath product `A ≀ᵣ H` onto the semidirect
product `A ⋊[φ] H`, collapsing a family `a : H → A` to its twisted total product
`∏ x, φ x (a x)` and leaving the `H`-coordinate alone. -/
def toSemidirectProduct : A ≀ᵣ H →* A ⋊[φ] H where
  toFun w := ⟨twistedProd φ w.left, w.right⟩
  map_one' := by
    ext
    · exact twistedProd_one φ
    · rfl
  map_mul' a b := by
    ext
    · show twistedProd φ (a.left * fun x ↦ b.left (a.right⁻¹ * x)) = _
      rw [twistedProd_mul, twistedProd_comp_mul_left]
      rfl
    · rfl

@[simp]
theorem toSemidirectProduct_left (w : A ≀ᵣ H) :
    (toSemidirectProduct φ w).left = twistedProd φ w.left := rfl

@[simp]
theorem toSemidirectProduct_right (w : A ≀ᵣ H) :
    (toSemidirectProduct φ w).right = w.right := rfl

/-- **Every semidirect product `A ⋊[φ] H` with `A` abelian is a quotient of the regular wreath
product `A ≀ᵣ H`.**  A pair `(d, q)` is hit by the family supported at the identity with value
`d` there. -/
theorem toSemidirectProduct_surjective :
    Function.Surjective (toSemidirectProduct φ) := by
  classical
  rintro ⟨d, q⟩
  refine ⟨⟨Pi.mulSingle 1 d, q⟩, ?_⟩
  ext
  · show twistedProd φ (Pi.mulSingle 1 d) = d
    rw [twistedProd, Finset.prod_eq_single (1 : H)]
    · simp
    · intro x _ hx
      simp [Pi.mulSingle_eq_of_ne hx]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rfl

end Fintype

end RegularWreathProduct

/-- If the regular wreath product `A ≀ᵣ H` of a finite abelian group `A` by a finite group `H` is
an inverse Galois group over `ℚ`, then so is every semidirect product `A ⋊[φ] H`. -/
theorem IsInverseGalois.semidirectProduct_of_wreath {A H : Type*} [CommGroup A] [Finite A]
    [Group H] [Finite H] (φ : H →* MulAut A)
    (h : IsInverseGalois (A ≀ᵣ H)) : IsInverseGalois (A ⋊[φ] H) := by
  letI := Fintype.ofFinite H
  exact h.of_surjective (RegularWreathProduct.toSemidirectProduct φ)
    (RegularWreathProduct.toSemidirectProduct_surjective φ)

/-- If the regular wreath product `A ≀ᵣ H` of a finite abelian group `A` by a finite group `H` is
a regular inverse Galois group over `ℚ(T)`, then so is every semidirect product `A ⋊[φ] H`. -/
theorem IsRegularInverseGalois.semidirectProduct_of_wreath {A H : Type*} [CommGroup A] [Finite A]
    [Group H] [Finite H] (φ : H →* MulAut A)
    (h : IsRegularInverseGalois (A ≀ᵣ H)) : IsRegularInverseGalois (A ⋊[φ] H) := by
  letI := Fintype.ofFinite H
  exact h.of_surjective (RegularWreathProduct.toSemidirectProduct φ)
    (RegularWreathProduct.toSemidirectProduct_surjective φ)
