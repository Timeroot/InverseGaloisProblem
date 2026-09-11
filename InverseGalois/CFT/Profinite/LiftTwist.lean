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
* `InverseGalois.CFT.HasCocyclePrescription`: **the restrictions of a smooth one cocycle along a
  family of subgroups can be prescribed at will.**

## Main results

* `InverseGalois.CFT.rightHom_twistLift`, `InverseGalois.CFT.isSmooth₁_twistLift` — the twisted
  lift is again over the same map and again smooth.
* `InverseGalois.CFT.exists_hom_inl_eq` and `InverseGalois.CFT.isSmooth₁_of_inl_comp` — **along a
  subgroup where the map to the quotient is trivial a lift is a smooth homomorphism into the
  kernel.**
* `InverseGalois.CFT.twistLift_eq_one` — **a twist by a cocycle restricting to the inverse of that
  homomorphism is trivial along the subgroup.**
* `InverseGalois.CFT.exists_lift_eq_one_of_hasCocyclePrescription` — **a lift can be corrected to
  one which is trivial along a whole family of subgroups**, as soon as restrictions of cocycles
  along that family can be prescribed.

## Tags

group extension, embedding problem, lift, one cocycle, torsor, Galois cohomology
-/

namespace InverseGalois.CFT

open GroupExtension groupCohomology

/-! ### Prescribing the restrictions of a cocycle -/

/-- **The restrictions of a smooth one cocycle along a family of subgroups can be prescribed at
will.**

The family is asked to act trivially on the coefficients, which is what makes the question
well posed: on a subgroup acting trivially a one cocycle restricts to a homomorphism, and two
cohomologous cocycles restrict to the *same* homomorphism, there being no coboundaries left.  So
this says exactly that the map from the first cohomology to the product of the groups of smooth
homomorphisms of the members of the family is onto.  Smoothness is asked of what is prescribed
because the restriction of a smooth cocycle is smooth. -/
def HasCocyclePrescription {Γ : Type*} [Group Γ] [TopologicalSpace Γ] (M : Type*) [CommGroup M]
    [MulDistribMulAction Γ M] {t : ℕ} (D : Fin t → Subgroup Γ) : Prop :=
  (∀ (ν : Fin t), ∀ x ∈ D ν, ∀ m : M, x • m = m) →
    ∀ a : (ν : Fin t) → ↥(D ν) →* M, (∀ ν : Fin t, IsSmooth₁ ((a ν : ↥(D ν) →* M) : ↥(D ν) → M)) →
      ∃ c : Γ → M, IsMulCocycle₁ c ∧ IsSmooth₁ c ∧
        ∀ (ν : Fin t) (x : ↥(D ν)), c (x : Γ) = a ν x

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

omit [MulDistribMulAction Γ N] in
/-- **That homomorphism is smooth**, the lift being smooth and the kernel embedded. -/
theorem isSmooth₁_of_inl_comp {D : Subgroup Γ} {a : ↥D → N}
    (ha : ∀ x : ↥D, S.inl (a x) = f (x : Γ)) (hfs : IsSmooth₁ (f : Γ → E)) : IsSmooth₁ a := by
  obtain ⟨A, hA, hAf⟩ := isSmooth₁_comp (continuous_subtype D) hfs
  refine ⟨A, hA, fun x m hm => S.inl_injective ?_⟩
  rw [ha, ha]
  exact hAf x m hm

omit [TopologicalSpace Γ] in
include hact hf hc in
/-- **A twist by a cocycle restricting to the inverse of the defect is trivial along the
subgroup.** -/
theorem twistLift_eq_one {D : Subgroup Γ} {a : Γ → N} (ha : ∀ x ∈ D, S.inl (a x) = f x)
    (hca : ∀ x ∈ D, c x * a x = 1) {x : Γ} (hx : x ∈ D) : twistLift S hact hf hc x = 1 := by
  rw [twistLift_apply, ← ha x hx, ← _root_.map_mul, hca x hx, _root_.map_one]

/-! ### Correcting a lift along a whole family -/

include hact hf in
/-- **A lift can be corrected to one which is trivial along a whole family of subgroups**, as soon
as the restrictions of a cocycle along that family can be prescribed.  Along each member the lift
is a homomorphism into the kernel; a cocycle restricting to the inverses of those homomorphisms
twists the lift into one which is trivial along every member at once, and the twist disturbs
neither the map to the quotient nor smoothness. -/
theorem exists_lift_eq_one_of_hasCocyclePrescription {t : ℕ} (D : Fin t → Subgroup Γ)
    (hD : ∀ (ν : Fin t), ∀ x ∈ D ν, ρ x = 1) (hpres : HasCocyclePrescription N D)
    (hfs : IsSmooth₁ (f : Γ → E)) :
    ∃ g : Γ →* E, (∀ γ : Γ, S.rightHom (g γ) = ρ γ) ∧ IsSmooth₁ (g : Γ → E) ∧
      ∀ (ν : Fin t), ∀ x ∈ D ν, g x = 1 := by
  have htriv : ∀ (ν : Fin t), ∀ x ∈ D ν, ∀ m : N, x • m = m := by
    intro ν x hx m
    have h1 : S.conjActHom (ρ x) = 1 := by rw [hD ν x hx, _root_.map_one]
    rw [hact x m, h1]
    rfl
  choose a ha using fun ν => exists_hom_inl_eq S hf (D ν) (hD ν)
  have hbs : ∀ ν : Fin t, IsSmooth₁ (((a ν)⁻¹ : ↥(D ν) →* N) : ↥(D ν) → N) := by
    intro ν
    obtain ⟨A, hA, hAa⟩ := isSmooth₁_of_inl_comp S (ha ν) hfs
    refine ⟨A, hA, fun x m hm => ?_⟩
    show (a ν (x * m))⁻¹ = (a ν x)⁻¹
    rw [hAa x m hm]
  obtain ⟨c, hc, hcs, hca⟩ := hpres htriv (fun ν => (a ν)⁻¹) hbs
  refine ⟨twistLift S hact hf hc, rightHom_twistLift S hact hf hc,
    isSmooth₁_twistLift S hact hf hc hfs hcs, fun ν x hx => ?_⟩
  have h1 : S.inl (a ν ⟨x, hx⟩) = f x := ha ν ⟨x, hx⟩
  have h2 : c x = (a ν ⟨x, hx⟩)⁻¹ := hca ν ⟨x, hx⟩
  rw [twistLift_apply, ← h1, h2, ← _root_.map_mul, inv_mul_cancel, _root_.map_one]

end Twist

end InverseGalois.CFT
