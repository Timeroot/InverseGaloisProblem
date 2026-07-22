/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Monic Associate of a Bivariate Polynomial

For an irreducible `f ∈ ℚ[T][X]` with leading coefficient `a ∈ ℚ[T]`, we construct
a monic polynomial `g ∈ ℚ[T][X]` such that `g(T, a(T)·X) = a(T)^{d-1} · f(T, X)`,
where `d = f.natDegree`. This `g` is monic, irreducible, and has the same degree.

## Key Identity

`g(T, a·X) = a^{d-1} · f(T, X)`, which means:
- Over `ℚ(T)`: `g` is an associate of `f` (up to the automorphism `X ↦ a⁻¹X`).
- For `t` with `a(t) ≠ 0`: `Irreducible(g(t,X)) ↔ Irreducible(f(t,X))`.
-/

open Polynomial

noncomputable section

/-- The **monic associate** of `f ∈ ℚ[T][X]`.
If `a = f.leadingCoeff` and `d = f.natDegree`, define `g` with:
- `g.coeff i = f.coeff i * a^{d-1-i}` for `i < d`
- `g.coeff d = 1`

This equals `(1/a) · f.scaleRoots(a)` over `ℚ(T)`. -/
def monicAssociate (f : Polynomial (Polynomial ℚ)) : Polynomial (Polynomial ℚ) :=
  ∑ i ∈ Finset.range f.natDegree,
    Polynomial.C (f.coeff i * f.leadingCoeff ^ (f.natDegree - 1 - i)) *
      Polynomial.X ^ i
  + Polynomial.X ^ f.natDegree

/-
The monic associate is monic.
-/
lemma monicAssociate_monic (f : Polynomial (Polynomial ℚ)) (_hf : f.natDegree ≥ 1) :
    (monicAssociate f).Monic := by
  erw [Polynomial.Monic.def, Polynomial.leadingCoeff_add_of_degree_lt] <;>
    norm_num [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [Polynomial.coeff_mul, Finset.sum_eq_zero]
  intros
  simp only [ge_iff_le, Finset.mem_range, Finset.mem_antidiagonal, coeff_C_mul, coeff_X_pow,
    mul_ite, mul_one, mul_zero, ite_eq_right_iff, mul_eq_zero] at *
  intro h
  refine Or.inr (Polynomial.coeff_eq_zero_of_natDegree_lt ?_)
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_C]
  norm_num
  omega

/-
The monic associate has the same natDegree.
-/
lemma monicAssociate_natDegree (f : Polynomial (Polynomial ℚ)) (hf : f.natDegree ≥ 1) :
    (monicAssociate f).natDegree = f.natDegree := by
  rw [monicAssociate, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
  · norm_num
  · refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) (Finset.sup_lt_iff ?_ |>.2 ?_)
    · aesop
    · intro b hb
      by_cases h : f.coeff b = 0 <;> by_cases h' : f.leadingCoeff = 0 <;> simp_all [Polynomial.natDegree_mul']
      linarith

/-
Key identity: `g(T, a·X) = a^{d-1} · f(T, X)`.
-/
lemma monicAssociate_comp_identity (f : Polynomial (Polynomial ℚ)) (hf : f.natDegree ≥ 1) :
    (monicAssociate f).comp (Polynomial.C f.leadingCoeff * Polynomial.X) =
    Polynomial.C (f.leadingCoeff ^ (f.natDegree - 1)) * f := by
  unfold monicAssociate
  refine Polynomial.funext fun x ↦ ?_
  simp [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [Polynomial.eval_eq_sum_range]
  simp [Finset.sum_range_succ, mul_pow, mul_assoc, mul_comm, mul_left_comm]
  simp [mul_add, mul_assoc, mul_comm, Finset.mul_sum, ← pow_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [add_tsub_cancel_of_le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))]
  · have hpow : f.leadingCoeff ^ f.natDegree
        = f.leadingCoeff * f.leadingCoeff ^ (f.natDegree - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hf]
    rw [hpow]
    ring

/-
The monic associate is irreducible when `f` is.
-/
lemma monicAssociate_irreducible (f : Polynomial (Polynomial ℚ))
    (hf_irr : Irreducible f) (hf_deg : f.natDegree ≥ 2) :
    Irreducible (monicAssociate f) := by
  have hf1 : f.natDegree ≥ 1 := by linarith
  have h_monic : (monicAssociate f).Monic := monicAssociate_monic f hf1
  set φ := algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))
  have h_map_irr : Irreducible (Polynomial.map φ f) := by
    have h_prim : Polynomial.IsPrimitive f := by
      grind only [Irreducible.isPrimitive]
    exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map h_prim).mp hf_irr
  have h_scaled_irr : Irreducible (Polynomial.C (φ f.leadingCoeff ^ (f.natDegree - 1))
      * Polynomial.map φ f) := by
    rw [irreducible_mul_iff]
    refine Or.inr ⟨h_map_irr, ?_⟩
    apply Polynomial.isUnit_C.mpr
    apply isUnit_iff_ne_zero.mpr
    apply pow_ne_zero
    aesop
  have h_comp_irr : Irreducible (Polynomial.comp (Polynomial.map φ (monicAssociate f))
      (Polynomial.C (φ f.leadingCoeff) * Polynomial.X)) := by
    convert h_scaled_irr using 1
    convert congr_arg (Polynomial.map φ) (monicAssociate_comp_identity f hf1) using 1 <;>
      norm_num [Polynomial.map_comp]
  have h_irred_g : Irreducible ((monicAssociate f).map φ) := by
    constructor
    · intro h
      have := Polynomial.natDegree_eq_zero_of_isUnit h
      simp_all
    · intro a b hab
      have h_comp : Polynomial.comp (Polynomial.map φ (monicAssociate f))
          (Polynomial.C (φ f.leadingCoeff) * Polynomial.X)
          = Polynomial.comp a (Polynomial.C (φ f.leadingCoeff) * Polynomial.X)
            * Polynomial.comp b (Polynomial.C (φ f.leadingCoeff) * Polynomial.X) := by
        rw [hab, Polynomial.mul_comp]
      have := h_comp_irr.2 h_comp
      rcases this with (h | h) <;> have := Polynomial.natDegree_eq_zero_of_isUnit h <;>
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_mul'] at this <;> norm_num at *
      · rw [Polynomial.eq_C_of_natDegree_eq_zero this] at h ⊢
        aesop
      · aesop
      · rw [Polynomial.eq_C_of_natDegree_eq_zero this] at h ⊢
        aesop
      · aesop
  exact (Polynomial.Monic.isPrimitive h_monic).irreducible_iff_irreducible_map_fraction_map.mpr
    h_irred_g

/-
For `t` with `a(t) ≠ 0`, irreducibility of specializations is equivalent.
-/
lemma monicAssociate_specialize_iff (f : Polynomial (Polynomial ℚ))
    (hf_deg : f.natDegree ≥ 1) (t : ℤ)
    (ht : Polynomial.eval (t : ℚ) f.leadingCoeff ≠ 0) :
    Irreducible ((monicAssociate f).map (Polynomial.evalRingHom (t : ℚ))) ↔
    Irreducible (f.map (Polynomial.evalRingHom (t : ℚ))) := by
  set c := eval (t : ℚ) f.leadingCoeff
  constructor <;> intro h
  · -- By the identity `g(T, a·X) = a^(d-1) · f(T, X)`, we have `g(t, a(t)·X) = a(t)^(d-1) · f(t, X)`.
    have h_identity : (map (evalRingHom (t : ℚ)) (monicAssociate f)).comp
        (Polynomial.C c * Polynomial.X)
        = Polynomial.C (c ^ (f.natDegree - 1)) * (map (evalRingHom (t : ℚ)) f) := by
      have hc : c = eval (t : ℚ) f.leadingCoeff := rfl
      convert congr_arg (Polynomial.map (Polynomial.evalRingHom (t : ℚ)))
        (monicAssociate_comp_identity f hf_deg) using 1 <;> simp [Polynomial.map_comp, hc]
    have h_g_irr : Irreducible ((map (evalRingHom (t : ℚ)) (monicAssociate f)).comp
        (Polynomial.C c * Polynomial.X)) := by
      constructor
      · intro H
        have := Polynomial.natDegree_eq_zero_of_isUnit H
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_mul'] at this <;> simp_all
        rw [Polynomial.eq_C_of_natDegree_eq_zero this] at h
        have := h.1
        aesop
      · intro a b hab
        have h_factor : (map (evalRingHom (t : ℚ)) (monicAssociate f))
            = (a.comp (Polynomial.C c⁻¹ * Polynomial.X))
              * (b.comp (Polynomial.C c⁻¹ * Polynomial.X)) := by
          convert congr_arg (Polynomial.comp · (Polynomial.C c⁻¹ * Polynomial.X)) hab using 1 <;>
            norm_num [Polynomial.comp_assoc]
          rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ ht, Polynomial.C_1, one_mul,
            Polynomial.comp_X]
        have := h.isUnit_or_isUnit h_factor
        have ha : a ≠ 0 := fun h ↦ by simp_all
        have hb : b ≠ 0 := fun h ↦ by simp_all
        simp_all [Polynomial.isUnit_iff_degree_eq_zero]
        have hac : a.comp (C c⁻¹ * X) ≠ 0 := fun h ↦ by simp_all
        have hbc : b.comp (C c⁻¹ * X) ≠ 0 := fun h ↦ by simp_all
        simp_all [Polynomial.degree_eq_natDegree ha, Polynomial.degree_eq_natDegree hb]
        simp_all [Polynomial.degree_eq_natDegree hac, Polynomial.degree_eq_natDegree hbc]
        simp_all [Polynomial.natDegree_comp, Polynomial.natDegree_mul']
    rw [h_identity, irreducible_mul_iff] at h_g_irr
    exact h_g_irr.resolve_left
      (fun ⟨h₁, h₂⟩ ↦ absurd h₁ (Polynomial.not_irreducible_C _)) |>.1
  · -- By the identity `g(T, a·X) = a^(d-1) · f(T, X)`, we have `g(t, a(t)·X) = a(t)^(d-1) · f(t, X)`.
    have h_identity : (Polynomial.map (evalRingHom (t : ℚ)) (monicAssociate f)).comp
        (Polynomial.C c * Polynomial.X)
        = Polynomial.C (c ^ (f.natDegree - 1)) * (Polynomial.map (evalRingHom (t : ℚ)) f) := by
      have hc : c = eval (t : ℚ) f.leadingCoeff := rfl
      convert congr_arg (Polynomial.map (evalRingHom (t : ℚ)))
        (monicAssociate_comp_identity f hf_deg) using 1 <;> simp [Polynomial.map_comp, hc]
    -- Since `a(t) ≠ 0`, we can divide both sides of the equation by `a(t)^(d-1)`.
    have h_div : Irreducible ((Polynomial.map (evalRingHom (t : ℚ)) (monicAssociate f)).comp
        (Polynomial.C c * Polynomial.X)) := by
      rw [h_identity, irreducible_mul_iff]
      exact Or.inr ⟨h, Polynomial.isUnit_C.mpr <| isUnit_iff_ne_zero.mpr <| pow_ne_zero _ ht⟩
    have h_reduce : ∀ {p : Polynomial ℚ}, Irreducible (p.comp (Polynomial.C c * Polynomial.X))
        → Irreducible p := by
      intro p hp
      constructor
      · intro H
        have := Polynomial.degree_eq_zero_of_isUnit H
        rw [Polynomial.eq_C_of_degree_eq_zero this] at hp
        simp at hp
        exact absurd hp (Polynomial.not_irreducible_C _)
      · intro a b hab
        have ha : a ≠ 0 := fun h ↦ by simp_all
        have hb : b ≠ 0 := fun h ↦ by simp_all
        have := hp.2 (show p.comp (C c * X)
            = (a.comp (C c * X)) * (b.comp (C c * X)) by rw [hab, Polynomial.mul_comp])
        simp_all [Polynomial.isUnit_iff_degree_eq_zero]
        have hac : a.comp (C c * X) ≠ 0 := fun h ↦ by simp_all
        have hbc : b.comp (C c * X) ≠ 0 := fun h ↦ by simp_all
        simp_all [Polynomial.degree_eq_natDegree ha, Polynomial.degree_eq_natDegree hb]
        simp_all [Polynomial.degree_eq_natDegree hac, Polynomial.degree_eq_natDegree hbc,
          Polynomial.natDegree_comp, Polynomial.natDegree_mul']
    exact h_reduce h_div

/-
The set of integers where the leading coefficient vanishes is finite.
-/
lemma leadingCoeff_roots_finite (f : Polynomial (Polynomial ℚ))
    (hf : f.leadingCoeff ≠ 0) :
    Set.Finite {t : ℤ | Polynomial.eval (t : ℚ) f.leadingCoeff = 0} := by
  -- The polynomial `f.leadingCoeff` is nonzero, so the set of integers `t` for which it
  -- evaluates to zero is finite by the Fundamental Theorem of Algebra.
  have h_fTA : Set.Finite {t : ℚ | Polynomial.eval t f.leadingCoeff = 0} := by
    apply Set.Finite.subset f.leadingCoeff.roots.toFinset.finite_toSet
    intro x hx
    aesop
  apply Set.Finite.subset (h_fTA.preimage ?_) fun x hx ↦ hx
  intro t _ t' _ h
  aesop

end
