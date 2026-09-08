/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.EmbeddingClass

/-!
# Twisting a lift by a one cocycle

Once an embedding problem has one solution it has many, and they differ by the first cohomology of
the kernel.  Multiplying a lift pointwise by a one cocycle with values in the kernel gives again a
homomorphism, and again one over the same map to the quotient: the cocycle condition is exactly
what makes the product multiplicative, conjugation inside the extension being the action, and the
kernel is killed by the projection so the twist is invisible downstairs.  Smoothness is preserved,
the two open normal subgroups on whose cosets the lift and the cocycle are constant having an open
normal intersection.

The reading this is for is a lift asked to be trivial along a family of subgroups.  Along a
subgroup on which the map to the quotient is trivial the lift lands in the kernel, where it is a
homomorphism into a commutative group; the twist changes it there by the restriction of the
cocycle, and choosing the cocycle to restrict to the inverse of that homomorphism makes the twisted
lift trivial along the subgroup.  So the whole of the remaining question is one about restricting
classes of the first cohomology.

## Main definitions

* `InverseGalois.CFT.twistLift`: **a lift twisted by a one cocycle**, again a lift.

## Main results

* `InverseGalois.CFT.rightHom_twistLift`, `InverseGalois.CFT.isSmooth₁_twistLift` — the twisted
  lift is again over the same map and again smooth.
* `InverseGalois.CFT.exists_hom_inl_eq` — **along a subgroup where the map to the quotient is
  trivial a lift is a homomorphism into the kernel.**
* `InverseGalois.CFT.twistLift_eq_one` — **a twist by a cocycle restricting to the inverse of that
  homomorphism is trivial along the subgroup.**

## Tags

group extension, embedding problem, lift, one cocycle, torsor, Galois cohomology
-/

namespace InverseGalois.CFT

open GroupExtension groupCohomology

section Twist

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {N E G : Type*} [CommGroup N] [Group E]
  [Group G] (S : GroupExtension N E G) {ρ : Γ →* G} [MulDistribMulAction Γ N]
variable (hact : ∀ (γ : Γ) (n : N), γ • n = S.conjActHom (ρ γ) n) {f : Γ →* E}
  (hf : ∀ γ : Γ, S.rightHom (f γ) = ρ γ) {c : Γ → N} (hc : IsMulCocycle₁ c)

/-! ### The twist -/

omit [TopologicalSpace Γ] in
include hact hf in
/-- The action on the kernel is conjugation by any lift. -/
theorem inl_smul_eq_conj (γ : Γ) (n : N) : S.inl (γ • n) = f γ * S.inl n * (f γ)⁻¹ := by
  rw [hact γ n, ← hf γ, conjActHom_rightHom, inl_conjAct_comm]

omit [TopologicalSpace Γ] in
include hact hf hc in
/-- **The cocycle condition is exactly what makes the twisted lift multiplicative.** -/
theorem inl_mul_lift_mul (γ δ : Γ) :
    S.inl (c (γ * δ)) * f (γ * δ) = S.inl (c γ) * f γ * (S.inl (c δ) * f δ) := by
  rw [hc γ δ, mul_comm (γ • c δ) (c γ), _root_.map_mul S.inl,
    inl_smul_eq_conj S hact hf γ (c δ), _root_.map_mul f]
  group

omit [TopologicalSpace Γ] in
include hact hf hc in
/-- **A lift twisted by a one cocycle with values in the kernel.** -/
def twistLift : Γ →* E :=
  MonoidHom.mk' (fun γ => S.inl (c γ) * f γ) (inl_mul_lift_mul S hact hf hc)

omit [TopologicalSpace Γ] in
@[simp]
theorem twistLift_apply (γ : Γ) : twistLift S hact hf hc γ = S.inl (c γ) * f γ := rfl

omit [TopologicalSpace Γ] in
/-- **The twist is invisible downstairs**, the kernel being killed by the projection. -/
theorem rightHom_twistLift (γ : Γ) : S.rightHom (twistLift S hact hf hc γ) = ρ γ := by
  rw [twistLift_apply, _root_.map_mul, S.rightHom_inl, one_mul, hf]

/-- **A twist of a smooth lift by a smooth cocycle is smooth**, the two open normal subgroups on
whose cosets they are constant having an open normal intersection. -/
theorem isSmooth₁_twistLift (hfs : IsSmooth₁ (f : Γ → E)) (hcs : IsSmooth₁ c) :
    IsSmooth₁ (twistLift S hact hf hc : Γ → E) := by
  obtain ⟨A, hA, hAf⟩ := hfs
  obtain ⟨B, hB, hBc⟩ := hcs
  refine ⟨A ⊓ B, hA.inf hB, fun x n hn => ?_⟩
  show S.inl (c (x * n)) * f (x * n) = S.inl (c x) * f x
  rw [hBc x n hn.2, hAf x n hn.1]

section SmoothHom

variable [TopologicalSpace E]

/-- A twist of a smooth lift by a smooth cocycle is a smooth homomorphism. -/
theorem isSmoothHom_twistLift (hfs : IsSmooth₁ (f : Γ → E)) (hcs : IsSmooth₁ c) :
    IsSmoothHom (twistLift S hact hf hc) :=
  isSmoothHom_of_isSmooth₁ (isSmooth₁_twistLift S hact hf hc hfs hcs)

end SmoothHom

/-! ### The defect along a subgroup where the base is trivial -/

omit [TopologicalSpace Γ] [MulDistribMulAction Γ N] in
include hf in
/-- **Along a subgroup where the map to the quotient is trivial a lift is a homomorphism into the
kernel.** -/
theorem exists_hom_inl_eq (D : Subgroup Γ) (hD : ∀ x ∈ D, ρ x = 1) :
    ∃ a : ↥D →* N, ∀ x : ↥D, S.inl (a x) = f (x : Γ) := by
  have hmem : ∀ x : ↥D, (f.comp D.subtype) x ∈ S.inl.range := by
    intro x
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    show S.rightHom (f (x : Γ)) = 1
    rw [hf, hD (x : Γ) x.2]
  refine ⟨(MonoidHom.ofInjective S.inl_injective).symm.toMonoidHom.comp
    ((f.comp D.subtype).codRestrict S.inl.range hmem), fun x => ?_⟩
  have hval : ((MonoidHom.ofInjective S.inl_injective)
      ((MonoidHom.ofInjective S.inl_injective).symm ⟨f (x : Γ), hmem x⟩) : E) = f (x : Γ) :=
    congrArg Subtype.val
      ((MonoidHom.ofInjective S.inl_injective).apply_symm_apply ⟨f (x : Γ), hmem x⟩)
  rw [← hval, MonoidHom.ofInjective_apply]
  rfl

omit [TopologicalSpace Γ] in
include hact hf hc in
/-- **A twist by a cocycle restricting to the inverse of the defect is trivial along the
subgroup.** -/
theorem twistLift_eq_one {D : Subgroup Γ} {a : Γ → N} (ha : ∀ x ∈ D, S.inl (a x) = f x)
    (hca : ∀ x ∈ D, c x * a x = 1) {x : Γ} (hx : x ∈ D) : twistLift S hact hf hc x = 1 := by
  rw [twistLift_apply, ← ha x hx, ← _root_.map_mul, hca x hx, _root_.map_one]

end Twist

end InverseGalois.CFT
