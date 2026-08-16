/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.CoverLift

/-!
# The Galois cover of a region attached to a quotient of its fundamental group

A homomorphism from the fundamental group of a region of the plane to a finite group is the same
thing as a system of labels for the paths of the region, and the cover built from those labels in
`RET/Pi1/Topological/CoverFibre.lean` is the cover the homomorphism names.  This file makes the
translation: a monoid homomorphism out of `FundamentalGroup` gives monodromy data, surjective
homomorphisms give connected covers, and the group acts on the cover simply transitively over the
region.

Multiplication in the fundamental group is composition of arrows, which reverses the order of
concatenation of paths, so the labels attached to a homomorphism are its *inverses*; that is the
usual passage between the left action of the fundamental group on a fibre and the right action of
the deck group commuting with it.  Read on the fibre over the base point, the two actions are the
two translations of the group on itself: transport backwards along a loop multiplies a label on
the left by the value of the homomorphism, while a deck transformation multiplies it on the right.

## Main definitions

* `Rigidity.RET.MonodromyData.ofHom` — the monodromy data of a homomorphism out of the fundamental
  group.

## Main results

* `Rigidity.RET.MonodromyData.isCoveringMap_proj_ofHom` — the cover it names is a covering space.
* `Rigidity.RET.MonodromyData.pathConnectedSpace_total_ofHom` — a surjective homomorphism gives a
  connected cover.
* `Rigidity.RET.MonodromyData.fibEquiv_restrict` — transport along a loop is left translation.
* `Rigidity.RET.MonodromyData.fibEquiv_rmul` — a deck transformation is right translation.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET.MonodromyData

variable {X : Set ℂ} {x₀ : ↥X} {H : Type*} [Group H]

/-! ### Monodromy data from a homomorphism out of the fundamental group -/

/-- **The monodromy data named by a homomorphism out of the fundamental group of the region.**
Composition of arrows in the fundamental groupoid concatenates paths in the reverse order, so the
label of a loop is the inverse of the value of the homomorphism on it. -/
def ofHom (hX : IsOpen X) (φ : FundamentalGroup ↥X x₀ →* H) : MonodromyData x₀ H where
  isOpen_region := hX
  toFun g := (φ (FundamentalGroup.fromPath g))⁻¹
  map_trans' a b := by
    have hab : FundamentalGroup.fromPath (a.trans b)
        = FundamentalGroup.fromPath b * FundamentalGroup.fromPath a := rfl
    show (φ (FundamentalGroup.fromPath (a.trans b)))⁻¹ = _
    rw [hab, map_mul, mul_inv_rev]

@[simp] theorem toFun_ofHom (hX : IsOpen X) (φ : FundamentalGroup ↥X x₀ →* H)
    (g : Path.Homotopic.Quotient x₀ x₀) :
    (ofHom hX φ).toFun g = (φ (FundamentalGroup.fromPath g))⁻¹ := rfl

/-- The labels of a surjective homomorphism exhaust the group. -/
theorem surjective_toFun_ofHom (hX : IsOpen X) {φ : FundamentalGroup ↥X x₀ →* H}
    (hφ : Function.Surjective φ) : Function.Surjective (ofHom hX φ).toFun := by
  intro h
  obtain ⟨p, hp⟩ := hφ h⁻¹
  refine ⟨FundamentalGroup.toPath p, ?_⟩
  rw [toFun_ofHom]
  show (φ p)⁻¹ = h
  rw [hp, inv_inv]

/-! ### The two translations on the fibre over the base point -/

variable (D : MonodromyData x₀ H)

/-- **Transport backwards along a loop is left translation of the group on the fibre over the base
point.** -/
@[simp] theorem fibEquiv_restrict (g : Path.Homotopic.Quotient x₀ x₀) (s : D.Fib x₀) :
    D.fibEquiv (Path.Homotopic.Quotient.refl x₀) (D.restrict g s)
      = D.toFun g * D.fibEquiv (Path.Homotopic.Quotient.refl x₀) s := by
  show s.1 ((Path.Homotopic.Quotient.refl x₀).trans g)
    = D.toFun g * s.1 (Path.Homotopic.Quotient.refl x₀)
  rw [Path.Homotopic.Quotient.refl_trans]
  conv_lhs => rw [← Path.Homotopic.Quotient.trans_refl g]
  exact s.2 g (Path.Homotopic.Quotient.refl x₀)

/-- **A deck transformation is right translation of the group on the fibre over the base point.**
The two translations commute, which is why the deck action is defined at all. -/
@[simp] theorem fibEquiv_rmul {x : ↥X} (q₀ : Path.Homotopic.Quotient x₀ x) (s : D.Fib x) (h : H) :
    D.fibEquiv q₀ (D.rmul s h) = D.fibEquiv q₀ s * h := rfl

/-! ### The cover named by a homomorphism -/

variable (hX : IsOpen X) (φ : FundamentalGroup ↥X x₀ →* H)

/-- **The cover named by a homomorphism out of the fundamental group is a covering space.** -/
theorem isCoveringMap_proj_ofHom : IsCoveringMap (ofHom hX φ).proj :=
  (ofHom hX φ).isCoveringMap_proj

/-- **The cover named by a surjective homomorphism is connected.** -/
theorem pathConnectedSpace_total_ofHom [PathConnectedSpace ↥X]
    (hφ : Function.Surjective φ) : PathConnectedSpace (ofHom hX φ).Total :=
  (ofHom hX φ).pathConnectedSpace_total
    (fun x => nonempty_quotient_of_pathConnected (x₀ := x₀) x)
    (surjective_toFun_ofHom hX hφ)

/-- **The group acts on the cover it names by deck transformations**, freely and transitively over
each point of the region. -/
theorem deckHom_injective_ofHom [PathConnectedSpace ↥X] :
    Function.Injective (ofHom hX φ).deckHom :=
  (ofHom hX φ).deckHom_injective
    (Classical.choice (nonempty_quotient_of_pathConnected (x₀ := x₀) x₀))

end Rigidity.RET.MonodromyData

end
