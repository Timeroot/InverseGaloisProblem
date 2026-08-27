/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Multiquadratic

/-!
# A character annihilated by a family of characters is a subset sum of it

Let `chi` be a finite family of homomorphisms from a group to `ZMod 2` whose joint values exhaust
all vectors, and let `ξ` be a further such homomorphism vanishing wherever the whole family
vanishes.  Then `ξ` is the sum of a subfamily.

The joint map is a surjection onto the vector space of vectors, so `ξ` factors through it as a
linear form; a linear form on a finite product of copies of a field is the pairing with a vector of
coefficients, and over the field with two elements a coefficient vector is the indicator of a
subset.

## Main results

* `InverseGalois.CFT.exists_finset_forall_eq_sum`: **a character vanishing wherever a surjective
  finite family of characters vanishes is the sum of a subfamily.**

## Tags

character, dual space, field with two elements, subset sum
-/

namespace InverseGalois.CFT

variable {Γ ι : Type*} [Group Γ] [Fintype ι] [DecidableEq ι]

/-- A homomorphism from a group to `ZMod 2` takes the same value at an element and at its
inverse. -/
theorem apply_inv_eq_of_forall_mul {f : Γ → ZMod 2} (hf : ∀ σ τ : Γ, f (σ * τ) = f σ + f τ)
    (σ : Γ) : f σ⁻¹ = f σ := by
  have h1 : f 1 = 0 := by
    have h := hf 1 1
    rw [one_mul] at h
    exact add_left_cancel (a := f 1) (by rw [add_zero]; exact h.symm)
  have h2 : f σ + f σ⁻¹ = 0 := by rw [← hf, mul_inv_cancel, h1]
  rcases eq_zero_or_one_zmod_two (f σ) with h | h <;>
      rcases eq_zero_or_one_zmod_two (f σ⁻¹) with h' | h' <;> rw [h, h'] at h2 ⊢ <;> revert h2 <;>
    decide

/-- **A character vanishing wherever a surjective finite family of characters vanishes is the sum
of a subfamily.**  The joint map of the family is a surjection onto the space of vectors, so the
character factors through it as a linear form, and a linear form over the field with two elements
is the pairing with the indicator vector of a subset. -/
theorem exists_finset_forall_eq_sum (chi : ι → Γ → ZMod 2)
    (hchi : ∀ (i : ι) (σ τ : Γ), chi i (σ * τ) = chi i σ + chi i τ)
    (hsurj : Function.Surjective fun (σ : Γ) (i : ι) => chi i σ)
    (ξ : Γ → ZMod 2) (hξ : ∀ σ τ : Γ, ξ (σ * τ) = ξ σ + ξ τ)
    (hker : ∀ σ : Γ, (∀ i, chi i σ = 0) → ξ σ = 0) :
    ∃ J : Finset ι, ∀ σ : Γ, ξ σ = ∑ i ∈ J, chi i σ := by
  classical
  set c : Γ → ι → ZMod 2 := fun σ i => chi i σ with hcdef
  have hcmul : ∀ σ τ : Γ, c (σ * τ) = c σ + c τ := fun σ τ => funext fun i => hchi i σ τ
  have hkerc : ∀ σ : Γ, c σ = 0 → ξ σ = 0 := fun σ h => hker σ fun i => congrFun h i
  -- the character is constant on the fibres of the joint map
  have hwd : ∀ σ τ : Γ, c σ = c τ → ξ σ = ξ τ := by
    intro σ τ h
    have hinv : c τ⁻¹ = c τ := funext fun i => apply_inv_eq_of_forall_mul (fun a b => hchi i a b) τ
    have hzero : c (σ * τ⁻¹) = 0 := by
      refine funext fun i => ?_
      have hi : chi i (σ * τ⁻¹) = chi i σ + chi i τ := by
        rw [hchi, apply_inv_eq_of_forall_mul (fun a b => hchi i a b) τ]
      have hστ : chi i σ = chi i τ := congrFun h i
      show chi i (σ * τ⁻¹) = 0
      rw [hi, hστ]
      rcases eq_zero_or_one_zmod_two (chi i τ) with h' | h' <;> rw [h'] <;> decide
    have h0 : ξ (σ * τ⁻¹) = 0 := hkerc _ hzero
    rw [hξ, apply_inv_eq_of_forall_mul hξ τ] at h0
    rcases eq_zero_or_one_zmod_two (ξ σ) with h' | h' <;>
        rcases eq_zero_or_one_zmod_two (ξ τ) with h'' | h'' <;> rw [h', h''] at h0 ⊢ <;>
      revert h0 <;> decide
  -- the induced linear form on the space of vectors
  have hchoose : ∀ x : ι → ZMod 2, c (hsurj x).choose = x := fun x => (hsurj x).choose_spec
  obtain ⟨φ, hφc⟩ : ∃ φ : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2, ∀ σ : Γ, φ (c σ) = ξ σ := by
    refine ⟨{ toFun := fun x => ξ (hsurj x).choose, map_add' := ?_, map_smul' := ?_ },
      fun σ => hwd _ _ (hchoose (c σ))⟩
    · intro x y
      have h : c ((hsurj x).choose * (hsurj y).choose) = c (hsurj (x + y)).choose := by
        rw [hcmul, hchoose, hchoose, hchoose]
      rw [← hwd _ _ h, hξ]
    · intro r x
      rcases eq_zero_or_one_zmod_two r with rfl | rfl
      · have h : c (hsurj ((0 : ZMod 2) • x)).choose = 0 := by rw [hchoose, zero_smul]
        show ξ (hsurj ((0 : ZMod 2) • x)).choose = (RingHom.id (ZMod 2)) 0 * ξ (hsurj x).choose
        rw [RingHom.id_apply, zero_mul]
        exact hkerc _ h
      · show ξ (hsurj ((1 : ZMod 2) • x)).choose = (RingHom.id (ZMod 2)) 1 * ξ (hsurj x).choose
        rw [RingHom.id_apply, one_mul, one_smul]
  obtain ⟨a, ha⟩ := exists_forall_eq_sum_mul φ
  refine ⟨Finset.univ.filter fun i => a i = 1, fun σ => ?_⟩
  rw [← hφc σ, ha, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_zero_or_one_zmod_two (a i) with h | h <;> rw [h] <;> simp [hcdef]

end InverseGalois.CFT
