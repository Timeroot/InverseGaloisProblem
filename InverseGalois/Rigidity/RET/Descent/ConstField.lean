/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.GeometricIrreducibility

/-!
# The constant-field base `k_Ω(T)` of a finite extension `Ω/ℚ(T)`

For a finite (char-0) extension `Ω/ℚ(T)`, the **constant-field base** `constFieldBase Ω = k_Ω(T)` is
the intermediate field generated over `ℚ(T)` by the field of constants `k_Ω = algebraicClosure ℚ Ω`
(the elements of `Ω` algebraic over `ℚ`).  This is the canonical `geomBase` of the function-field
descent: it contains all constants (`const_le_constFieldBase`) and — for `Ω/ℚ(T)` Galois — is normal
over `ℚ(T)` (`constFieldBase_normal`), because the constant field `k_Ω/ℚ` is normal
(`constFieldBase_constNormal`) and normality is preserved under the base change `k_Ω ↦ k_Ω(T)`.

Extracted from `Descent.Tower` so that both `Descent.Tower` (the model packaging) and
`Descent.RegularityInf` (the regularity intersection) can depend on it without a cycle.
-/

open Polynomial


/-- The **constant-field base** of a finite extension `Ω/ℚ(T)`: the intermediate field `k_Ω(T)`
generated over `ℚ(T)` by the field of constants `k_Ω = algebraicClosure ℚ Ω` (the elements of `Ω`
algebraic over `ℚ`).  This is the canonical `geomBase` of the descent: it contains all constants by
construction (`const_le_constFieldBase`), and — for `Ω/ℚ(T)` Galois — is normal over `ℚ(T)`
(`constFieldBase_normal`), because the constant field `k_Ω/ℚ` is normal (Galois) and normality is
preserved under the base change `k_Ω ↦ k_Ω(T)`. -/
def constFieldBase (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω] [CharZero Ω]
    [IsScalarTower ℚ (RatFunc ℚ) Ω] : IntermediateField (RatFunc ℚ) Ω :=
  IntermediateField.adjoin (RatFunc ℚ) (algebraicClosure ℚ Ω : Set Ω)

/-- The constant-field base contains all constants: `k_Ω ≤ k_Ω(T)`.  Immediate from
`IntermediateField.subset_adjoin`. -/
theorem const_le_constFieldBase (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω] [CharZero Ω]
    [IsScalarTower ℚ (RatFunc ℚ) Ω] :
    algebraicClosure ℚ Ω ≤ (constFieldBase Ω).restrictScalars ℚ := by
  intro x hx
  rw [IntermediateField.mem_restrictScalars]
  exact IntermediateField.subset_adjoin (RatFunc ℚ) (algebraicClosure ℚ Ω : Set Ω) hx

/-- **The constant field is normal over `ℚ`.**  For `Ω/ℚ(T)` finite Galois (char 0), the field of
constants `k_Ω = algebraicClosure ℚ Ω` is normal over `ℚ`: the `ℚ(T)`-minimal polynomial of a
constant `x` has coefficients in `ℚ` (they are algebraic over `ℚ` — symmetric functions of the
conjugates, which are constants — *and* lie in `ℚ(T)`, hence in `ℚ` since `ℚ` is relatively
algebraically closed in `ℚ(T)`, `regular_ratFunc`), so it equals `minpoly ℚ x`, which therefore
splits in `Ω` with all roots constants. -/
theorem constFieldBase_constNormal (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω]
    [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω] [CharZero Ω]
    [IsScalarTower ℚ (RatFunc ℚ) Ω] :
    Normal ℚ (algebraicClosure ℚ Ω) := by
  classical
  set K := algebraicClosure ℚ Ω with hK
  haveI : Normal (RatFunc ℚ) Ω := IsGalois.to_normal
  rw [normal_iff]
  intro y
  -- `z = ↑y ∈ Ω` is the underlying constant; it is integral over `ℚ`.
  set z : Ω := (algebraMap K Ω) y with hz
  have hinj : Function.Injective (algebraMap K Ω) := (algebraMap K Ω).injective
  have hzint : IsIntegral ℚ z := mem_algebraicClosure_iff'.1 (hz ▸ y.2)
  have hyint : IsIntegral ℚ y := (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℚ K Ω) hinj).1 hzint
  refine ⟨hyint, ?_⟩
  -- Work with `p := minpoly ℚ z = minpoly ℚ y`.
  set p : ℚ[X] := minpoly ℚ z with hp
  have hpmy : minpoly ℚ y = p := (minpoly.algebraMap_eq hinj y).symm
  have hpmonic : p.Monic := minpoly.monic hzint
  have hpirr : Irreducible p := minpoly.irreducible hzint
  -- KEY: `minpoly ℚ(T) z = p.map (ℚ → ℚ(T))` — the `ℚ(T)`-minpoly is the base change of the
  -- `ℚ`-minpoly, since `p` stays irreducible over `ℚ(T)` (`ℚ` relatively closed in `ℚ(T)`).
  have hpmap_irr : Irreducible (p.map (algebraMap ℚ (RatFunc ℚ))) :=
    Rigidity.RET.irreducible_map_of_algClosure_eq_bot Rigidity.RET.regular_ratFunc hpmonic hpirr
  have hpmap_aeval : (aeval z) (p.map (algebraMap ℚ (RatFunc ℚ))) = 0 := by
    rw [aeval_map_algebraMap]; exact minpoly.aeval ℚ z
  have hzint' : IsIntegral (RatFunc ℚ) z := IsIntegral.of_finite (RatFunc ℚ) z
  have hminT : minpoly (RatFunc ℚ) z = p.map (algebraMap ℚ (RatFunc ℚ)) :=
    (minpoly.eq_of_irreducible_of_monic hpmap_irr hpmap_aeval (hpmonic.map _)).symm
  -- `minpoly ℚ(T) z` splits in `Ω` (`Ω/ℚ(T)` normal); pull that back to `p` splitting in `Ω`.
  have hsplitΩ : Splits (p.map (algebraMap ℚ Ω)) := by
    have hnorm := Normal.splits (F := RatFunc ℚ) (K := Ω) inferInstance z
    rw [hminT] at hnorm
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ (RatFunc ℚ) Ω] at hnorm
  -- Descend the split from `Ω` to `K`: all roots are integral over `ℚ`, hence in `K`.
  rw [hpmy]
  refine Splits.of_splits_map (algebraMap K Ω) ?_ ?_
  · rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ K Ω]
  · intro a ha
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ K Ω] at ha
    have haroot : (aeval a) p = 0 := by
      have hmem := (Polynomial.mem_roots (by
        exact (Polynomial.map_ne_zero_iff (algebraMap ℚ Ω).injective).2 hpmonic.ne_zero)).1 ha
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact hmem
    have haint : IsIntegral ℚ a := ⟨p, hpmonic, haroot⟩
    have haK : a ∈ K := mem_algebraicClosure_iff'.2 haint
    exact ⟨⟨a, haK⟩, rfl⟩

/-! ## The constant field is a number field with a primitive element

The constants of `Ω` form a finite extension of `ℚ`: the `ℚ(T)`-minimal polynomial of a constant is
the base change of its `ℚ`-minimal polynomial (`minpoly_ratFunc_const`), so the `ℚ`-degrees of the
constants are bounded by `[Ω : ℚ(T)]` (`natDegree_minpoly_const_le`); a constant of maximal degree
then generates all of them (`exists_primitive_const`). -/

/-- **The `ℚ(T)`-minimal polynomial of a constant is the base change of its `ℚ`-minimal
polynomial.**  The `ℚ`-minimal polynomial stays irreducible over `ℚ(T)` because `ℚ` is relatively
algebraically closed in `ℚ(T)` (`regular_ratFunc`). -/
theorem minpoly_ratFunc_const (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω] [CharZero Ω]
    [IsScalarTower ℚ (RatFunc ℚ) Ω] {z : Ω} (hz : IsIntegral ℚ z) :
    minpoly (RatFunc ℚ) z = (minpoly ℚ z).map (algebraMap ℚ (RatFunc ℚ)) := by
  have hpmonic : (minpoly ℚ z).Monic := minpoly.monic hz
  have hpirr : Irreducible (minpoly ℚ z) := minpoly.irreducible hz
  have hpmap_irr : Irreducible ((minpoly ℚ z).map (algebraMap ℚ (RatFunc ℚ))) :=
    Rigidity.RET.irreducible_map_of_algClosure_eq_bot Rigidity.RET.regular_ratFunc hpmonic hpirr
  have hpmap_aeval : (aeval z) ((minpoly ℚ z).map (algebraMap ℚ (RatFunc ℚ))) = 0 := by
    rw [aeval_map_algebraMap]; exact minpoly.aeval ℚ z
  exact (minpoly.eq_of_irreducible_of_monic hpmap_irr hpmap_aeval (hpmonic.map _)).symm

set_option synthInstance.maxHeartbeats 200000 in
/-- **The `ℚ`-degree of a constant is bounded by `[Ω : ℚ(T)]`.**  Its `ℚ`-minimal polynomial is its
`ℚ(T)`-minimal polynomial after base change (`minpoly_ratFunc_const`), and the degree of the latter
is the degree of the simple extension `ℚ(T)(z) ⊆ Ω`. -/
theorem natDegree_minpoly_const_le (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω]
    [FiniteDimensional (RatFunc ℚ) Ω] [CharZero Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω]
    {z : Ω} (hz : IsIntegral ℚ z) :
    (minpoly ℚ z).natDegree ≤ Module.finrank (RatFunc ℚ) Ω := by
  have h1 : (minpoly (RatFunc ℚ) z).natDegree = (minpoly ℚ z).natDegree := by
    rw [minpoly_ratFunc_const Ω hz, natDegree_map]
  have h2 : Module.finrank (RatFunc ℚ) (IntermediateField.adjoin (RatFunc ℚ) {z})
      = (minpoly (RatFunc ℚ) z).natDegree :=
    IntermediateField.adjoin.finrank (IsIntegral.of_finite (RatFunc ℚ) z)
  have h3 : Module.finrank (RatFunc ℚ) (IntermediateField.adjoin (RatFunc ℚ) {z})
      ≤ Module.finrank (RatFunc ℚ) Ω :=
    Submodule.finrank_le (IntermediateField.adjoin (RatFunc ℚ) {z}).toSubmodule
  omega

/-- **The constant field has a primitive element.**  The `ℚ`-degrees of the constants are bounded
(`natDegree_minpoly_const_le`), so some constant `α` has maximal degree; for any other constant `x`
the finite extension `ℚ(α, x)` has a primitive element `β`, whose degree is at least that of `α` and
at most the maximum, so `ℚ⟮α⟯ = ℚ(α, x) ∋ x`. -/
theorem exists_primitive_const (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω]
    [FiniteDimensional (RatFunc ℚ) Ω] [CharZero Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω] :
    ∃ α : Ω, IsIntegral ℚ α ∧ algebraicClosure ℚ Ω = IntermediateField.adjoin ℚ {α} := by
  classical
  set S : Set ℕ := {n | ∃ z : Ω, IsIntegral ℚ z ∧ (minpoly ℚ z).natDegree = n} with hS
  have hne : S.Nonempty := ⟨(minpoly ℚ (0 : Ω)).natDegree, 0, isIntegral_zero, rfl⟩
  have hbdd : BddAbove S := ⟨Module.finrank (RatFunc ℚ) Ω, by
    rintro n ⟨z, hz, rfl⟩; exact natDegree_minpoly_const_le Ω hz⟩
  obtain ⟨α, hα, hαdeg⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ z : Ω, IsIntegral ℚ z → (minpoly ℚ z).natDegree ≤ (minpoly ℚ α).natDegree := by
    intro z hz
    rw [hαdeg]
    exact le_csSup hbdd ⟨z, hz, rfl⟩
  refine ⟨α, hα, le_antisymm ?_ ?_⟩
  · intro x hx
    have hxint : IsIntegral ℚ x := mem_algebraicClosure_iff'.1 hx
    set F : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({α, x} : Set Ω) with hF
    haveI : FiniteDimensional ℚ F := by
      refine IntermediateField.finiteDimensional_adjoin ?_
      rintro y hy
      rcases hy with rfl | rfl
      · exact hα
      · exact hxint
    obtain ⟨β, hβ⟩ := Field.exists_primitive_element ℚ F
    set b : Ω := (algebraMap F Ω) β with hb
    have hbint : IsIntegral ℚ b :=
      (IsIntegral.of_finite ℚ β).map (IsScalarTower.toAlgHom ℚ F Ω)
    have hminb : minpoly ℚ b = minpoly ℚ β :=
      minpoly.algebraMap_eq (algebraMap F Ω).injective β
    have hrankF : Module.finrank ℚ F = (minpoly ℚ β).natDegree := by
      have h1 : Module.finrank ℚ (IntermediateField.adjoin ℚ {β} : IntermediateField ℚ F)
          = (minpoly ℚ β).natDegree :=
        IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ β)
      rw [hβ] at h1
      rw [← h1]
      exact IntermediateField.finrank_top'.symm
    have hle : (IntermediateField.adjoin ℚ {α} : IntermediateField ℚ Ω) ≤ F := by
      rw [IntermediateField.adjoin_simple_le_iff, hF]
      exact IntermediateField.subset_adjoin ℚ _ (by simp)
    have hrankα : Module.finrank ℚ (IntermediateField.adjoin ℚ {α} : IntermediateField ℚ Ω)
        = (minpoly ℚ α).natDegree := IntermediateField.adjoin.finrank hα
    have heq : (IntermediateField.adjoin ℚ {α} : IntermediateField ℚ Ω) = F := by
      refine IntermediateField.eq_of_le_of_finrank_le hle ?_
      rw [hrankα, hrankF, ← hminb]
      exact hmax b hbint
    rw [heq, hF]
    exact IntermediateField.subset_adjoin ℚ _ (by simp)
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact mem_algebraicClosure_iff'.2 hα

set_option synthInstance.maxHeartbeats 200000 in
/-- **The constant-field base is normal over `ℚ(T)`.**  `k_Ω(T)/ℚ(T)` is normal because `k_Ω/ℚ` is
normal (`constFieldBase_constNormal`) and normality is preserved under the base change to `ℚ(T)`
(a `ℚ(T)`-embedding of `k_Ω(T)` restricts to a `ℚ`-embedding of `k_Ω`, whose image is again `k_Ω`,
so the embedding maps `k_Ω(T)` into itself). -/
theorem constFieldBase_normal (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω]
    [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω] [CharZero Ω]
    [IsScalarTower ℚ (RatFunc ℚ) Ω] :
    Normal (RatFunc ℚ) (constFieldBase Ω) := by
  haveI : Normal (RatFunc ℚ) Ω := IsGalois.to_normal
  rw [IntermediateField.normal_iff_forall_map_le']
  intro σ
  simp only [constFieldBase]
  rw [IntermediateField.adjoin_map]
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  -- `σ` restricts to a `ℚ`-algebra map, so it preserves integrality over `ℚ`; hence `σ x` is again
  -- a constant, so it lies in the constant-field base.
  have hxint : IsIntegral ℚ x := mem_algebraicClosure_iff'.1 hx
  have hσxint : IsIntegral ℚ (σ x) :=
    hxint.map ((σ.restrictScalars ℚ).toAlgHom)
  have hσxK : σ x ∈ algebraicClosure ℚ Ω := mem_algebraicClosure_iff'.2 hσxint
  exact IntermediateField.subset_adjoin (RatFunc ℚ) _ hσxK

/-- **Two automorphisms agreeing on the constants differ by an element of `Gal(Ω/k_Ω(T))`.**  If
`σ` and `τ` agree on every constant then `τ σ⁻¹` fixes every constant (the constants are stable
under `σ⁻¹`), hence fixes the field `k_Ω(T)` they generate over `ℚ(T)` pointwise. -/
theorem mul_inv_mem_fixingSubgroup_constFieldBase (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω]
    [CharZero Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω] {σ τ : Ω ≃ₐ[RatFunc ℚ] Ω}
    (h : ∀ x ∈ algebraicClosure ℚ Ω, σ x = τ x) :
    τ * σ⁻¹ ∈ (constFieldBase Ω).fixingSubgroup := by
  -- `τ σ⁻¹` fixes each constant: `σ⁻¹ y` is again a constant, and there `σ` and `τ` agree.
  have hfix : ∀ y ∈ (algebraicClosure ℚ Ω : Set Ω), (τ * σ⁻¹) y = y := by
    intro y hy
    have hyint : IsIntegral ℚ y := mem_algebraicClosure_iff'.1 hy
    have hz : σ.symm y ∈ algebraicClosure ℚ Ω :=
      mem_algebraicClosure_iff'.2 (hyint.map (σ.symm.restrictScalars ℚ).toAlgHom)
    have hst := h _ hz
    show τ (σ.symm y) = y
    rw [← hst, σ.apply_symm_apply]
  -- hence it fixes the field the constants generate over `ℚ(T)`
  have hle : constFieldBase Ω ≤ IntermediateField.fixedField (Subgroup.zpowers (τ * σ⁻¹)) := by
    rw [constFieldBase]
    refine IntermediateField.adjoin_le_iff.2 ?_
    intro y hy
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hstab : Subgroup.zpowers (τ * σ⁻¹) ≤ MulAction.stabilizer (Ω ≃ₐ[RatFunc ℚ] Ω) y :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 (hfix y hy))
    exact hstab hf
  exact (IntermediateField.le_iff_le _ _).1 hle (Subgroup.mem_zpowers _)
