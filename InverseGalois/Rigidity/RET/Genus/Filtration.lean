/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The filtration cut out by two charts

A function on a cover of the line is measured by two rings: the functions regular over the first
chart, and the functions regular over the second.  Multiplying by a power of the coordinate of the
second chart before asking for regularity there gives a nested family of spaces of functions, each
one allowing a pole of one more order at the far end of the line than the last.

Differentiating along the coordinate of the line moves this family down by one step: a function
with a pole of order at most `m + 1` at the far end differentiates to one with a pole of order at
most `m`, because the extra order of vanishing gained by differentiating at the far end exactly
offsets the order lost.  What is asked of the second chart for this is only that the *logarithmic*
derivation `x · D` — the derivation with a simple zero at the far end — preserve the functions
regular there.  Differentiation is injective up to the constants, so each step of the family is at
most one dimension larger than the last, and the whole family grows at most linearly.

## Main definitions

* `Rigidity.RET.filt` — the space of functions regular on the first chart with a pole of bounded
  order at the far end of the second.

## Main results

* `Rigidity.RET.deriv_mem_filt` — differentiating moves the family down by one step.
* `Rigidity.RET.finrank_filt_le` — the family grows at most linearly.
-/

open Module

noncomputable section

namespace Rigidity.RET

section Filtration

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **The functions regular on the first chart with a pole of order at most `m` at the far end of
the second.**  Here `x` is the coordinate of the line and `B₁`, `B₂` are the functions regular over
the two charts. -/
def filt (x : F) (B₁ B₂ : Subalgebra k F) (m : ℕ) : Submodule k F :=
  Subalgebra.toSubmodule B₁ ⊓
    Submodule.comap (LinearMap.mulLeft k (x⁻¹ ^ m)) (Subalgebra.toSubmodule B₂)

variable {x : F} {B₁ B₂ : Subalgebra k F}

theorem mem_filt {m : ℕ} {y : F} :
    y ∈ filt x B₁ B₂ m ↔ y ∈ B₁ ∧ x⁻¹ ^ m * y ∈ B₂ := Iff.rfl

/-! ## Differentiating moves the filtration down -/

variable (D : Derivation k F F)

theorem ne_zero_of_deriv_eq_one (hx : D x = 1) : x ≠ 0 := by
  rintro rfl
  simpa using hx.symm

/-- **Differentiating moves the filtration down by one step.** -/
theorem deriv_mem_filt (hx : D x = 1) (hD₁ : ∀ y ∈ B₁, D y ∈ B₁)
    (hD₂ : ∀ y ∈ B₂, x * D y ∈ B₂) {m : ℕ} {y : F} (hy : y ∈ filt x B₁ B₂ (m + 1)) :
    D y ∈ filt x B₁ B₂ m := by
  obtain ⟨hy₁, hy₂⟩ := mem_filt.1 hy
  have hx0 : x ≠ 0 := ne_zero_of_deriv_eq_one D hx
  set b : F := x⁻¹ ^ (m + 1) * y with hb
  have hb₂ : b ∈ B₂ := hy₂
  have hxu : x ^ m * x⁻¹ ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx0, one_pow]
  have hyb : y = x ^ (m + 1) * b := by
    rw [hb, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0, one_pow, one_mul]
  have hDy : D y = x ^ (m + 1) * D b + ((m : F) + 1) * (b * x ^ m) := by
    conv_lhs => rw [hyb]
    rw [Derivation.leibniz, Derivation.leibniz_pow, hx, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      nsmul_eq_mul]
    push_cast
    ring
  refine ⟨(Subalgebra.mem_toSubmodule _).2 (hD₁ y hy₁), ?_⟩
  have key : x⁻¹ ^ m * D y = x * D b + ((m : ℕ) + 1) • b := by
    rw [hDy, nsmul_eq_mul]
    push_cast
    linear_combination (x * D b + ((m : F) + 1) * b) * hxu
  show x⁻¹ ^ m * D y ∈ Subalgebra.toSubmodule B₂
  rw [Subalgebra.mem_toSubmodule, key]
  exact add_mem (hD₂ b hb₂) (nsmul_mem hb₂ _)

/-! ## The filtration grows at most linearly -/

/-- The restriction of the derivation to one step of the filtration. -/
def filtDeriv (hx : D x = 1) (hD₁ : ∀ y ∈ B₁, D y ∈ B₁)
    (hD₂ : ∀ y ∈ B₂, x * D y ∈ B₂) (m : ℕ) :
    ↥(filt x B₁ B₂ (m + 1)) →ₗ[k] ↥(filt x B₁ B₂ m) :=
  LinearMap.restrict D.toLinearMap fun _ hy => deriv_mem_filt D hx hD₁ hD₂ hy

theorem finrank_one_submodule : finrank k ↥(1 : Submodule k F) = 1 := by
  rw [Submodule.one_eq_span, finrank_span_singleton (one_ne_zero' F)]

theorem finiteDimensional_one_submodule : FiniteDimensional k ↥(1 : Submodule k F) := by
  rw [Submodule.one_eq_span]
  exact FiniteDimensional.span_singleton k (1 : F)

/-- **The filtration grows at most linearly**: each step is at most one dimension larger than the
last, since a function whose derivative vanishes and which is regular on the first chart is
constant. -/
theorem finite_and_finrank_filt_le (hx : D x = 1) (hD₁ : ∀ y ∈ B₁, D y ∈ B₁)
    (hD₂ : ∀ y ∈ B₂, x * D y ∈ B₂)
    (hker : ∀ y ∈ B₁, D y = 0 → y ∈ (1 : Submodule k F))
    [FiniteDimensional k ↥(filt x B₁ B₂ 0)] (m : ℕ) :
    FiniteDimensional k ↥(filt x B₁ B₂ m) ∧
      finrank k ↥(filt x B₁ B₂ m) ≤ finrank k ↥(filt x B₁ B₂ 0) + m := by
  haveI := finiteDimensional_one_submodule (k := k) (F := F)
  induction m with
  | zero => exact ⟨inferInstance, le_rfl⟩
  | succ m ih =>
    obtain ⟨hfin, hle⟩ := ih
    haveI := hfin
    set T := filtDeriv D hx hD₁ hD₂ m with hT
    -- the kernel is at most one dimensional
    have hkerin : ∀ z : ↥(LinearMap.ker T), (z : F) ∈ (1 : Submodule k F) := by
      rintro ⟨⟨y, hy₁, hy₂⟩, hz⟩
      have hDy : D y = 0 := congrArg Subtype.val hz
      exact hker y ((Subalgebra.mem_toSubmodule _).1 hy₁) hDy
    let e : ↥(LinearMap.ker T) →ₗ[k] ↥(1 : Submodule k F) :=
      { toFun := fun z => ⟨(z : F), hkerin z⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have he : Function.Injective e := by
      intro z₁ z₂ h
      have h' := Subtype.ext_iff.1 h
      exact Subtype.ext (Subtype.ext h')
    haveI : FiniteDimensional k ↥(LinearMap.ker T) := FiniteDimensional.of_injective e he
    have hkerle : finrank k ↥(LinearMap.ker T) ≤ 1 := by
      have h1 : finrank k ↥(LinearMap.ker T) ≤ finrank k ↥(1 : Submodule k F) :=
        LinearMap.finrank_le_finrank_of_injective he
      rwa [finrank_one_submodule] at h1
    -- the range sits inside the previous step
    haveI : FiniteDimensional k ↥(LinearMap.range T) := inferInstance
    have hrangele : finrank k ↥(LinearMap.range T) ≤ finrank k ↥(filt x B₁ B₂ m) :=
      Submodule.finrank_le _
    -- hence the whole step is finite dimensional
    haveI : Module.Finite k (↥(filt x B₁ B₂ (m + 1)) ⧸ LinearMap.ker T) :=
      Module.Finite.equiv (LinearMap.quotKerEquivRange T).symm
    haveI : FiniteDimensional k ↥(filt x B₁ B₂ (m + 1)) :=
      Module.Finite.of_submodule_quotient (LinearMap.ker T)
    refine ⟨inferInstance, ?_⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker T
    omega

theorem finrank_filt_le (hx : D x = 1) (hD₁ : ∀ y ∈ B₁, D y ∈ B₁)
    (hD₂ : ∀ y ∈ B₂, x * D y ∈ B₂)
    (hker : ∀ y ∈ B₁, D y = 0 → y ∈ (1 : Submodule k F))
    [FiniteDimensional k ↥(filt x B₁ B₂ 0)] (m : ℕ) :
    finrank k ↥(filt x B₁ B₂ m) ≤ finrank k ↥(filt x B₁ B₂ 0) + m :=
  (finite_and_finrank_filt_le D hx hD₁ hD₂ hker m).2

end Filtration

end Rigidity.RET
