/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A square root generating a quadratic character

A character of the Galois group of a finite Galois extension whose image has two elements is cut
out by a square root: there is an element of the extension whose square lies in the base and which
is fixed by exactly the kernel of the character.

The construction is the difference `y = x - τ x` of an element `x` fixed by the kernel with its
image under an automorphism `τ` outside the kernel.  The kernel is normal, so it fixes `τ x` as
well as `x`, and `τ` squares into the kernel, so it exchanges `x` and `τ x` and therefore negates
`y`.  Every automorphism thus multiplies `y` by a sign, so its square is fixed by the whole group
and lies in the base field, and the automorphisms fixing `y` are exactly those in the kernel.  The
element `x` exists because the kernel is the subgroup fixing its own fixed field, so an
automorphism outside it must move some element of that fixed field.

## Main results

* `InverseGalois.CFT.exists_sq_algebraMap_eq_iff_mem_ker`: **a character with two values is cut out
  by a square root of an element of the base field.**

## Tags

Galois theory, Kummer theory, quadratic extension, character, fixed field
-/

namespace InverseGalois.CFT

open IntermediateField

variable {Z M : Type*} [Field Z] [Field M] [Algebra Z M] [FiniteDimensional Z M]
variable [IsGalois Z M] [CharZero M]
variable {C : Type*} [Group C] {μ : Gal(M/Z) →* C} {τ : Gal(M/Z)}

/-- **A character with two values is cut out by a square root of an element of the base field.**
The difference of an element fixed by the kernel with its image under an automorphism outside the
kernel is negated by that automorphism and fixed by the kernel, so its square lies in the base
field and it is fixed by exactly the kernel. -/
theorem exists_sq_algebraMap_eq_iff_mem_ker (hτ : μ τ ≠ 1)
    (h2 : ∀ σ : Gal(M/Z), μ σ = 1 ∨ μ σ = μ τ) :
    ∃ y : M, y ≠ 0 ∧ (∃ β : Z, y ^ 2 = algebraMap Z M β) ∧
      ∀ σ : Gal(M/Z), σ y = y ↔ σ ∈ μ.ker := by
  have hτH : τ ∉ μ.ker := fun h => hτ (MonoidHom.mem_ker.mp h)
  -- an element of the fixed field of the kernel which the chosen automorphism moves
  obtain ⟨x, hxF, hxτ⟩ : ∃ x : M, x ∈ fixedField μ.ker ∧ τ x ≠ x := by
    by_contra hcon
    push_neg at hcon
    refine hτH ?_
    rw [← fixingSubgroup_fixedField (μ.ker), IntermediateField.mem_fixingSubgroup_iff]
    exact fun y hy => hcon y hy
  set y : M := x - τ x with hy
  have hy0 : y ≠ 0 := sub_ne_zero.mpr fun h => hxτ h.symm
  -- the kernel fixes both terms, being normal
  have hker : ∀ σ : Gal(M/Z), σ ∈ μ.ker → σ y = y := by
    intro σ hσ
    have h1 : σ x = x := (mem_fixedField_iff _ x).mp hxF σ hσ
    have h2' : σ (τ x) = τ x := by
      have hcon : τ⁻¹ * σ * τ ∈ μ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hσ, mul_one,
          inv_mul_cancel]
      have hfx := (mem_fixedField_iff _ x).mp hxF _ hcon
      have hg : τ * (τ⁻¹ * σ * τ) = σ * τ := by group
      calc σ (τ x) = (σ * τ) x := rfl
        _ = (τ * (τ⁻¹ * σ * τ)) x := by rw [hg]
        _ = τ ((τ⁻¹ * σ * τ) x) := rfl
        _ = τ x := by rw [hfx]
    rw [hy, map_sub, h1, h2']
  -- the chosen automorphism exchanges the two terms
  have hsq : μ (τ * τ) = 1 := by
    rcases h2 (τ * τ) with h | h
    · exact h
    · rw [map_mul] at h
      have h1 : μ τ * μ τ = 1 * μ τ := by rw [one_mul]; exact h
      exact absurd (mul_right_cancel h1) hτ
  have hτy : τ y = -y := by
    have hxx : τ (τ x) = x :=
      (mem_fixedField_iff _ x).mp hxF _ (MonoidHom.mem_ker.mpr hsq)
    rw [hy, map_sub, hxx]
    ring
  -- every automorphism multiplies the element by a sign
  have hsign : ∀ σ : Gal(M/Z), σ y = y ∨ σ y = -y := by
    intro σ
    rcases h2 σ with h | h
    · exact Or.inl (hker σ (MonoidHom.mem_ker.mpr h))
    · refine Or.inr ?_
      have hmem : τ⁻¹ * σ ∈ μ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
      have hfy := hker _ hmem
      calc σ y = (τ * (τ⁻¹ * σ)) y := by rw [mul_inv_cancel_left]
        _ = τ ((τ⁻¹ * σ) y) := rfl
        _ = τ y := by rw [hfy]
        _ = -y := hτy
  refine ⟨y, hy0, ?_, fun σ => ⟨fun h => ?_, hker σ⟩⟩
  · have hmem : y ^ 2 ∈ (⊥ : IntermediateField Z M) :=
      (IsGalois.mem_bot_iff_fixed (y ^ 2)).mpr fun σ => by
        rcases hsign σ with h | h
        · rw [map_pow, h]
        · rw [map_pow, h]
          ring
    obtain ⟨β, hβ⟩ := IntermediateField.mem_bot.mp hmem
    exact ⟨β, hβ.symm⟩
  · rcases h2 σ with hσ | hσ
    · exact MonoidHom.mem_ker.mpr hσ
    · exfalso
      have hneg : σ y = -y := by
        have hmem : τ⁻¹ * σ ∈ μ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
        calc σ y = (τ * (τ⁻¹ * σ)) y := by rw [mul_inv_cancel_left]
          _ = τ ((τ⁻¹ * σ) y) := rfl
          _ = τ y := by rw [hker _ hmem]
          _ = -y := hτy
      rw [h] at hneg
      have h2y : (2 : M) * y = 0 := by linear_combination hneg
      exact hy0 ((mul_eq_zero.mp h2y).resolve_left (by norm_num))

end InverseGalois.CFT
