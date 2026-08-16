/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.CoverTopology

/-!
# The deck action on the cover attached to a monodromy homomorphism

The cover built from a monodromy homomorphism `φ : (loops at x₀) → H` carries an action of `H`
itself: a label is a function to `H`, and multiplying it on the right by a fixed element of `H`
is again a label, because the equivariance condition constrains labels on the left.  Right
multiplication therefore commutes with transport along paths, so it moves each sheet to a sheet
and is a homeomorphism of the total space over the region — a deck transformation.

The action is free and transitive on every fibre over a point that can be joined to the base
point, since over such a point the labels are a copy of `H` and right multiplication of `H` on
itself is simply transitive.  So the cover is a principal `H`-bundle over the part of the region
joined to the base point: exactly the Galois cover with group `H` that the monodromy
homomorphism is meant to produce.

Multiplication composes in the reverse order, as it must for a right action; the associated left
action, used to package the deck transformations as a homomorphism into a permutation group, is
by inverses.

## Main definitions

* `Rigidity.RET.MonodromyData.rmul` — right multiplication of `H` on a label.
* `Rigidity.RET.MonodromyData.deck` — the deck transformation attached to an element of `H`.
* `Rigidity.RET.MonodromyData.deckHomeo` — a deck transformation as a homeomorphism.
* `Rigidity.RET.MonodromyData.deckHom` — the deck transformations as a group homomorphism.

## Main results

* `Rigidity.RET.MonodromyData.restrict_rmul` — the deck action commutes with transport.
* `Rigidity.RET.MonodromyData.proj_deck` — deck transformations lie over the region.
* `Rigidity.RET.MonodromyData.deckHom_injective` — the action is free.
* `Rigidity.RET.MonodromyData.exists_deck_eq` — the action is transitive on a fibre.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET.MonodromyData

variable {X : Set ℂ} {x₀ : ↥X} {H : Type*} [Group H] (D : MonodromyData x₀ H)

/-! ### Right multiplication on labels -/

/-- **Right multiplication of `H` on a label.**  The equivariance condition on a label constrains
it on the left, so multiplying all its values on the right by a fixed element gives a label
again. -/
def rmul {x : ↥X} (s : D.Fib x) (h : H) : D.Fib x :=
  ⟨fun q => s.1 q * h, fun g q => by
    show s.1 (g.trans q) * h = D.toFun g * (s.1 q * h)
    rw [s.2 g q, mul_assoc]⟩

@[simp] theorem rmul_apply {x : ↥X} (s : D.Fib x) (h : H) (q : Path.Homotopic.Quotient x₀ x) :
    (D.rmul s h).1 q = s.1 q * h := rfl

@[simp] theorem rmul_one {x : ↥X} (s : D.Fib x) : D.rmul s 1 = s := by
  ext q
  rw [rmul_apply, mul_one]

@[simp] theorem rmul_rmul {x : ↥X} (s : D.Fib x) (h₁ h₂ : H) :
    D.rmul (D.rmul s h₁) h₂ = D.rmul s (h₁ * h₂) := by
  ext q
  rw [rmul_apply, rmul_apply, rmul_apply, mul_assoc]

/-- **Right multiplication commutes with transport along a path**: the label transported and then
multiplied is the label multiplied and then transported. -/
theorem restrict_rmul {x y : ↥X} (c : Path.Homotopic.Quotient y x) (s : D.Fib x) (h : H) :
    D.restrict c (D.rmul s h) = D.rmul (D.restrict c s) h := rfl

/-- Right multiplication by a fixed element is injective on labels. -/
theorem rmul_right_injective {x : ↥X} (h : H) :
    Function.Injective fun s : D.Fib x => D.rmul s h := by
  intro s t hst
  ext q
  have hq : s.1 q * h = t.1 q * h := congrArg (fun u : D.Fib x => u.1 q) hst
  exact mul_right_cancel hq

/-- **Right multiplication on the labels over a point joined to the base point is free.** -/
theorem rmul_left_injective {x : ↥X} (q₀ : Path.Homotopic.Quotient x₀ x) (s : D.Fib x) :
    Function.Injective (D.rmul s) := by
  intro h₁ h₂ h
  have hq : s.1 q₀ * h₁ = s.1 q₀ * h₂ := congrArg (fun u : D.Fib x => u.1 q₀) h
  exact mul_left_cancel hq

/-- **Right multiplication on the labels over a point joined to the base point is transitive.** -/
theorem exists_rmul_eq {x : ↥X} (q₀ : Path.Homotopic.Quotient x₀ x) (s t : D.Fib x) :
    ∃ h : H, D.rmul s h = t :=
  ⟨(s.1 q₀)⁻¹ * t.1 q₀, Fib.eq_of_apply_eq D q₀ (by rw [rmul_apply, mul_inv_cancel_left])⟩

/-! ### Deck transformations -/

/-- **The deck transformation of the cover attached to an element of `H`**: multiply the label at
each point of the total space on the right. -/
def deck (h : H) (y : D.Total) : D.Total := ⟨y.1, D.rmul y.2 h⟩

@[simp] theorem proj_deck (h : H) (y : D.Total) : D.proj (D.deck h y) = D.proj y := rfl

@[simp] theorem deck_mk (h : H) (x : ↥X) (s : D.Fib x) :
    D.deck h ⟨x, s⟩ = ⟨x, D.rmul s h⟩ := rfl

/-- Two points of the total space over the same point of the region agree as soon as their labels
do. -/
theorem total_mk_inj {x : ↥X} {s t : D.Fib x} (h : (⟨x, s⟩ : D.Total) = ⟨x, t⟩) : s = t := by
  injection h

@[simp] theorem deck_one (y : D.Total) : D.deck 1 y = y := by
  show (⟨y.1, D.rmul y.2 1⟩ : D.Total) = y
  rw [D.rmul_one]
  rfl

/-- The deck transformations compose in the reverse order: the action is a right action. -/
@[simp] theorem deck_deck (h₁ h₂ : H) (y : D.Total) :
    D.deck h₂ (D.deck h₁ y) = D.deck (h₁ * h₂) y := by
  show (⟨y.1, D.rmul (D.rmul y.2 h₁) h₂⟩ : D.Total) = ⟨y.1, D.rmul y.2 (h₁ * h₂)⟩
  rw [D.rmul_rmul]

theorem deck_injective (h : H) : Function.Injective (D.deck h) := by
  intro y z hyz
  have hd := congrArg (D.deck h⁻¹) hyz
  simpa using hd

/-! ### Deck transformations are homeomorphisms -/

/-- **A deck transformation carries a sheet to a sheet**, since it commutes with transport. -/
theorem preimage_deck_sheet {K : Set ℂ} (hK : IsFlat X K) {x : ↥X} (hx : (x : ℂ) ∈ K)
    (s : D.Fib x) (h : H) :
    D.deck h ⁻¹' D.sheet hK hx s = D.sheet hK hx (D.rmul s h⁻¹) := by
  ext y
  simp only [Set.mem_preimage, mem_sheet_iff]
  constructor
  · rintro ⟨hy, hy2⟩
    refine ⟨hy, ?_⟩
    have hy2' : D.rmul y.2 h = D.restrict (segClass hK hy hx) s := hy2
    rw [D.restrict_rmul, ← hy2', D.rmul_rmul, mul_inv_cancel, D.rmul_one]
  · rintro ⟨hy, hy2⟩
    refine ⟨hy, ?_⟩
    show D.rmul y.2 h = D.restrict (segClass hK hy hx) s
    rw [hy2, D.restrict_rmul, D.rmul_rmul, inv_mul_cancel, D.rmul_one]

theorem continuous_deck (h : H) : Continuous (D.deck h) := by
  refine (D.isTopologicalBasis_sheets).continuous_iff.mpr ?_
  rintro _ ⟨K, hK, x, hx, s, rfl⟩
  rw [D.preimage_deck_sheet]
  exact D.isOpen_sheet hK hx _

/-- **A deck transformation is a homeomorphism of the total space.** -/
def deckHomeo (h : H) : D.Total ≃ₜ D.Total where
  toFun := D.deck h
  invFun := D.deck h⁻¹
  left_inv y := by simp
  right_inv y := by simp
  continuous_toFun := D.continuous_deck h
  continuous_invFun := D.continuous_deck h⁻¹

@[simp] theorem deckHomeo_apply (h : H) (y : D.Total) : D.deckHomeo h y = D.deck h y := rfl

@[simp] theorem deckHomeo_symm_apply (h : H) (y : D.Total) :
    (D.deckHomeo h).symm y = D.deck h⁻¹ y := rfl

/-- **The deck transformations as a group homomorphism.**  Right multiplication composes in the
reverse order, so the left action attached to it is by inverses. -/
def deckHom : H →* Equiv.Perm D.Total where
  toFun h := (D.deckHomeo h⁻¹).toEquiv
  map_one' := by
    ext y
    simp
  map_mul' h₁ h₂ := by
    ext y
    show D.deck (h₁ * h₂)⁻¹ y = D.deck h₁⁻¹ (D.deck h₂⁻¹ y)
    rw [D.deck_deck, mul_inv_rev]

@[simp] theorem deckHom_apply (h : H) (y : D.Total) : D.deckHom h y = D.deck h⁻¹ y := rfl

theorem proj_deckHom (h : H) (y : D.Total) : D.proj (D.deckHom h y) = D.proj y := rfl

/-! ### The action on a fibre is simply transitive -/

/-- **The deck action is free** as soon as some point of the region is joined to the base point:
a deck transformation with a fixed point is the identity. -/
theorem deckHom_injective {x : ↥X} (q₀ : Path.Homotopic.Quotient x₀ x) :
    Function.Injective D.deckHom := by
  refine (injective_iff_map_eq_one _).mpr fun h hh => ?_
  set s : D.Fib x := Fib.of D q₀ 1 with hs
  have hy : D.deckHom h (⟨x, s⟩ : D.Total) = (⟨x, s⟩ : D.Total) := by
    rw [hh]
    rfl
  rw [D.deckHom_apply, D.deck_mk] at hy
  have h2 : D.rmul s h⁻¹ = D.rmul s 1 := by
    rw [D.rmul_one]
    exact D.total_mk_inj hy
  have h3 := D.rmul_left_injective q₀ s h2
  rw [inv_eq_one] at h3
  exact h3

/-- **The deck action is transitive on a fibre** over a point joined to the base point. -/
theorem exists_deck_eq {x : ↥X} (q₀ : Path.Homotopic.Quotient x₀ x) (s t : D.Fib x) :
    ∃ h : H, D.deck h ⟨x, s⟩ = ⟨x, t⟩ := by
  obtain ⟨h, hh⟩ := D.exists_rmul_eq q₀ s t
  exact ⟨h, by rw [D.deck_mk, hh]⟩

/-- **The deck action is transitive on each fibre of the projection.** -/
theorem exists_deck_eq_of_proj_eq (y z : D.Total) (hyz : D.proj y = D.proj z)
    (q₀ : Path.Homotopic.Quotient x₀ (D.proj y)) : ∃ h : H, D.deck h y = z := by
  obtain ⟨x, s⟩ := y
  obtain ⟨x', t⟩ := z
  cases hyz
  exact D.exists_deck_eq q₀ s t

end Rigidity.RET.MonodromyData

end
