import Mathlib

/-!
# From a group extension with abelian kernel to a two-cocycle

Let `1 → N → E → G → 1` be an extension of groups with `N` commutative.  Conjugation inside `E`
descends to an action of `G` on `N`, and every set-theoretic section `σ : G → E` gives rise to a
*factor set* `f (g, h)`, the element of `N` measuring the failure of `σ` to be a homomorphism.
This file constructs that data, shows that a factor set is a multiplicative two-cocycle, that
changing the section changes the factor set by a multiplicative two-coboundary, and hence that a
group extension with abelian kernel has a well-defined class in `groupCohomology.H2`.  That class
vanishes exactly when the extension splits.

## Main definitions

* `GroupExtension.conjActHom`: the homomorphism `G →* MulAut N` induced by conjugation in `E`.
* `GroupExtension.mulDistribMulAction`: the same action packaged as a `MulDistribMulAction G N`.
  This is deliberately a `def` rather than an `instance`, since it depends on the extension.
* `GroupExtension.factorSet`: the factor set `G × G → N` attached to a section.
* `GroupExtension.sectionRatio`: the element of `N` comparing two sections at a point of `G`.
* `GroupExtension.splittingOfIsMulCoboundary₂`: the splitting obtained by correcting a section
  whose factor set is a multiplicative two-coboundary.
* `GroupExtension.cohomologyClass`: the class of the factor set in
  `groupCohomology.H2 (Rep.ofMulDistribMulAction G N)`.
* `GroupExtension.splittingOfCohomologyClassEqZero`: the splitting obtained from an extension
  whose cohomology class vanishes.

## Main results

* `GroupExtension.isMulCocycle₂_factorSet`: a factor set is a multiplicative two-cocycle.
* `GroupExtension.isMulCoboundary₂_factorSet_div`: the pointwise ratio of the factor sets of two
  sections is a multiplicative two-coboundary.
* `GroupExtension.H2π_factorSet_eq` and `GroupExtension.cohomologyClass_eq`: every section
  computes the same cohomology class.
* `GroupExtension.cohomologyClass_eq_zero_iff`: the cohomology class vanishes if and only if the
  extension splits.

-/

open groupCohomology

namespace GroupExtension

section Cocycle

variable {N E G : Type*} [CommGroup N] [Group E] [Group G] (S : GroupExtension N E G)

/-! ### The action of `G` on the abelian kernel -/

/-- Conjugation by an element of the image of the commutative kernel acts trivially on it. -/
theorem conjAct_apply_inl (n m : N) : S.conjAct (S.inl n) m = m := by
  apply S.inl_injective
  rw [inl_conjAct_comm, ← map_inv, ← map_mul, ← map_mul, mul_comm n m, mul_inv_cancel_right]

/-- Conjugation by an element of the image of the commutative kernel is the identity
automorphism. -/
theorem conjAct_eq_one_of_mem_range_inl {e : E} (he : e ∈ S.inl.range) : S.conjAct e = 1 := by
  obtain ⟨n, rfl⟩ := he
  ext m
  simpa only [MulAut.one_apply] using S.conjAct_apply_inl n m

/-- The action of `G` on the commutative kernel `N` induced by conjugation in `E`.  It is obtained
from `GroupExtension.conjAct` by factoring through the quotient `E ⧸ S.inl.range ≃* G`. -/
noncomputable def conjActHom : G →* MulAut N :=
  (QuotientGroup.lift S.inl.range S.conjAct fun _ he ↦ S.conjAct_eq_one_of_mem_range_inl he).comp
    (S.quotientRangeInlEquivRight.symm : G →* E ⧸ S.inl.range)

@[simp]
theorem conjActHom_rightHom (e : E) : S.conjActHom (S.rightHom e) = S.conjAct e := by
  have h : S.quotientRangeInlEquivRight (QuotientGroup.mk e) = S.rightHom e := rfl
  rw [← h, conjActHom]
  simp

/-- The induced action of `G` on `N` is computed by conjugation in `E`. -/
theorem inl_conjActHom (e : E) (n : N) :
    S.inl (S.conjActHom (S.rightHom e) n) = e * S.inl n * e⁻¹ := by
  rw [conjActHom_rightHom, inl_conjAct_comm]

/-- The induced action of `G` on `N` is computed by conjugation by any section. -/
theorem inl_conjActHom_section (σ : S.Section) (g : G) (n : N) :
    S.inl (S.conjActHom g n) = σ g * S.inl n * (σ g)⁻¹ := by
  conv_lhs => rw [← Section.rightHom_section σ g]
  rw [inl_conjActHom]

/-- The action of `G` on the commutative kernel `N`, as a `MulDistribMulAction`.  This is a `def`
rather than an `instance` because it depends on the extension `S`; use `letI` to bring it into
scope. -/
noncomputable def mulDistribMulAction : MulDistribMulAction G N :=
  MulDistribMulAction.compHom N S.conjActHom

theorem mulDistribMulAction_smul (g : G) (n : N) :
    letI := S.mulDistribMulAction
    g • n = S.conjActHom g n := rfl

/-! ### Factor sets -/

/-- The factor set of a section `σ` of `S`: the unique element `n` of `N` satisfying
`S.inl n = σ g * σ h * (σ (g * h))⁻¹`. -/
noncomputable def factorSet (σ : S.Section) (p : G × G) : N :=
  Function.invFun S.inl (σ p.1 * σ p.2 * (σ (p.1 * p.2))⁻¹)

@[simp]
theorem inl_factorSet (σ : S.Section) (g h : G) :
    S.inl (S.factorSet σ (g, h)) = σ g * σ h * (σ (g * h))⁻¹ :=
  Function.invFun_eq (MonoidHom.mem_range.mp (Section.mul_mul_mul_inv_mem_range_inl σ g h))

/-- A section is multiplicative up to its factor set. -/
theorem section_mul (σ : S.Section) (g h : G) :
    σ g * σ h = S.inl (S.factorSet σ (g, h)) * σ (g * h) := by
  rw [inl_factorSet, inv_mul_cancel_right]

/-- The factor set of a section is a multiplicative two-cocycle for the conjugation action. -/
theorem isMulCocycle₂_factorSet (σ : S.Section) :
    letI := S.mulDistribMulAction
    IsMulCocycle₂ (S.factorSet σ) := by
  letI := S.mulDistribMulAction
  show IsMulCocycle₂ (S.factorSet σ)
  have hsmul : ∀ (g : G) (n : N), g • n = S.conjActHom g n := fun _ _ ↦ rfl
  intro g h j
  have h1 : σ g * σ h * σ j
      = S.inl (S.factorSet σ (g, h) * S.factorSet σ (g * h, j)) * σ (g * h * j) := by
    rw [map_mul, S.section_mul σ g h, mul_assoc, S.section_mul σ (g * h) j, ← mul_assoc]
  have h2 : σ g * (σ h * σ j)
      = S.inl (S.conjActHom g (S.factorSet σ (h, j)) * S.factorSet σ (g, h * j))
        * σ (g * h * j) := by
    rw [map_mul, S.inl_conjActHom_section σ g, mul_assoc, mul_assoc g h j,
      ← S.section_mul σ g (h * j), S.section_mul σ h j]
    group
  have key : S.factorSet σ (g, h) * S.factorSet σ (g * h, j)
      = S.conjActHom g (S.factorSet σ (h, j)) * S.factorSet σ (g, h * j) := by
    apply S.inl_injective
    apply mul_right_cancel (b := σ (g * h * j))
    rw [← h1, ← h2, mul_assoc]
  rw [hsmul, mul_comm (S.factorSet σ (g * h, j)), key]

/-! ### Changing the section -/

/-- The element of `N` comparing the values of two sections at a point of `G`. -/
noncomputable def sectionRatio (σ τ : S.Section) (g : G) : N :=
  Function.invFun S.inl (σ g * (τ g)⁻¹)

@[simp]
theorem inl_sectionRatio (σ τ : S.Section) (g : G) :
    S.inl (S.sectionRatio σ τ g) = σ g * (τ g)⁻¹ :=
  Function.invFun_eq (MonoidHom.mem_range.mp (Section.mul_inv_mem_range_inl σ τ g))

/-- The factor set of `σ` in terms of the factor set of `τ` and the ratio of the two sections. -/
theorem factorSet_eq_mul (σ τ : S.Section) (g h : G) :
    S.factorSet σ (g, h)
      = S.sectionRatio σ τ g * S.conjActHom g (S.sectionRatio σ τ h) * S.factorSet τ (g, h)
        * (S.sectionRatio σ τ (g * h))⁻¹ := by
  apply S.inl_injective
  simp only [map_mul, map_inv, S.inl_conjActHom_section τ, inl_sectionRatio, inl_factorSet]
  group

/-- The pointwise ratio of the factor sets of two sections is a multiplicative two-coboundary. -/
theorem isMulCoboundary₂_factorSet_div (σ τ : S.Section) :
    letI := S.mulDistribMulAction
    IsMulCoboundary₂ (S.factorSet σ / S.factorSet τ) := by
  letI := S.mulDistribMulAction
  show IsMulCoboundary₂ (S.factorSet σ / S.factorSet τ)
  have hsmul : ∀ (a : G) (n : N), a • n = S.conjActHom a n := fun _ _ ↦ rfl
  refine ⟨S.sectionRatio σ τ, fun g h ↦ ?_⟩
  rw [hsmul, Pi.div_apply, S.factorSet_eq_mul σ τ g h]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-! ### Splittings -/

/-- Correcting a section by a function `x : G → N` exhibiting its factor set as a multiplicative
two-coboundary produces a splitting of the extension. -/
noncomputable def splittingOfIsMulCoboundary₂ (σ : S.Section) (x : G → N)
    (hx : ∀ g h : G, S.conjActHom g (x h) / x (g * h) * x g = S.factorSet σ (g, h)) :
    S.Splitting :=
  ⟨MonoidHom.mk' (fun g ↦ (S.inl (x g))⁻¹ * σ g) (by
    intro a b
    have h2 : (S.inl (S.conjActHom a (x b)))⁻¹ * σ a = σ a * (S.inl (x b))⁻¹ := by
      rw [← map_inv, ← map_inv, S.inl_conjActHom_section σ a, inv_mul_cancel_right, map_inv]
    have hf : S.factorSet σ (a, b) = S.conjActHom a (x b) * x a * (x (a * b))⁻¹ := by
      rw [← hx a b, div_eq_mul_inv, mul_right_comm]
    have hn : (x a)⁻¹ * (S.conjActHom a (x b))⁻¹ * S.factorSet σ (a, b) = (x (a * b))⁻¹ := by
      rw [hf]
      group
    calc (S.inl (x (a * b)))⁻¹ * σ (a * b)
        = S.inl ((x a)⁻¹ * (S.conjActHom a (x b))⁻¹ * S.factorSet σ (a, b)) * σ (a * b) := by
          rw [hn, map_inv]
      _ = (S.inl (x a))⁻¹ * ((S.inl (S.conjActHom a (x b)))⁻¹
            * (S.inl (S.factorSet σ (a, b)) * σ (a * b))) := by
          simp only [map_mul, map_inv]
          group
      _ = (S.inl (x a))⁻¹ * ((S.inl (S.conjActHom a (x b)))⁻¹ * σ a * σ b) := by
          rw [← S.section_mul σ a b, mul_assoc]
      _ = (S.inl (x a))⁻¹ * σ a * ((S.inl (x b))⁻¹ * σ b) := by
          rw [h2]
          group), by
    intro g
    simp⟩

/-- The factor set of the section underlying a splitting is trivial. -/
theorem factorSet_splitting (s : S.Splitting) (g h : G) : S.factorSet s.toSection (g, h) = 1 := by
  apply S.inl_injective
  rw [inl_factorSet, map_one]
  show (s g) * (s h) * (s (g * h))⁻¹ = 1
  rw [map_mul, mul_inv_cancel]

end Cocycle

/-! ### The cohomology class of an extension

`Rep.ofMulDistribMulAction` is stated for groups and modules in `Type`, so the results below are
restricted accordingly; the middle group `E` may still live in any universe. -/

section CohomologyClass

variable {N G : Type} {E : Type*} [CommGroup N] [Group E] [Group G] (S : GroupExtension N E G)

/-- Any two sections define the same class in `groupCohomology.H2`. -/
theorem H2π_factorSet_eq (σ τ : S.Section) :
    letI := S.mulDistribMulAction
    groupCohomology.H2π _ (cocyclesOfIsMulCocycle₂ (S.isMulCocycle₂_factorSet σ))
      = groupCohomology.H2π _ (cocyclesOfIsMulCocycle₂ (S.isMulCocycle₂_factorSet τ)) := by
  letI := S.mulDistribMulAction
  show groupCohomology.H2π _ _ = groupCohomology.H2π _ _
  rw [groupCohomology.H2π_eq_iff]
  exact (coboundariesOfIsMulCoboundary₂ (S.isMulCoboundary₂_factorSet_div σ τ)).2

/-- The class in `groupCohomology.H2` of a group extension with commutative kernel. -/
noncomputable def cohomologyClass :
    letI := S.mulDistribMulAction
    groupCohomology.H2 (Rep.ofMulDistribMulAction G N) :=
  letI := S.mulDistribMulAction
  groupCohomology.H2π _ (cocyclesOfIsMulCocycle₂ (S.isMulCocycle₂_factorSet S.surjInvRightHom))

/-- The cohomology class of an extension is computed by the factor set of any section. -/
theorem cohomologyClass_eq (σ : S.Section) :
    letI := S.mulDistribMulAction
    S.cohomologyClass
      = groupCohomology.H2π _ (cocyclesOfIsMulCocycle₂ (S.isMulCocycle₂_factorSet σ)) :=
  S.H2π_factorSet_eq S.surjInvRightHom σ

/-- A split extension has vanishing cohomology class. -/
theorem cohomologyClass_eq_zero_of_splitting (s : S.Splitting) :
    letI := S.mulDistribMulAction
    S.cohomologyClass = 0 := by
  letI := S.mulDistribMulAction
  rw [S.cohomologyClass_eq s.toSection]
  have hz : cocyclesOfIsMulCocycle₂ (S.isMulCocycle₂_factorSet s.toSection) = 0 := by
    ext g h
    show Additive.ofMul (S.factorSet s.toSection (g, h)) = (0 : Additive N)
    rw [S.factorSet_splitting]
    rfl
  rw [hz, map_zero]

/-- If the cohomology class of an extension vanishes, then the factor set of every section is a
multiplicative two-coboundary. -/
theorem isMulCoboundary₂_factorSet_of_cohomologyClass_eq_zero
    (h : letI := S.mulDistribMulAction; S.cohomologyClass = 0) (σ : S.Section) :
    letI := S.mulDistribMulAction
    IsMulCoboundary₂ (S.factorSet σ) := by
  letI := S.mulDistribMulAction
  rw [S.cohomologyClass_eq σ, groupCohomology.H2π_eq_zero_iff] at h
  exact isMulCoboundary₂_of_mem_coboundaries₂ _ h

/-- A splitting of an extension whose cohomology class vanishes. -/
noncomputable def splittingOfCohomologyClassEqZero
    (h : letI := S.mulDistribMulAction; S.cohomologyClass = 0) : S.Splitting :=
  letI := S.mulDistribMulAction
  S.splittingOfIsMulCoboundary₂ S.surjInvRightHom
    (S.isMulCoboundary₂_factorSet_of_cohomologyClass_eq_zero h S.surjInvRightHom).choose
    (S.isMulCoboundary₂_factorSet_of_cohomologyClass_eq_zero h S.surjInvRightHom).choose_spec

/-- A group extension with commutative kernel splits if and only if its class in
`groupCohomology.H2` vanishes. -/
theorem cohomologyClass_eq_zero_iff :
    letI := S.mulDistribMulAction
    S.cohomologyClass = 0 ↔ Nonempty S.Splitting :=
  letI := S.mulDistribMulAction
  ⟨fun h ↦ ⟨S.splittingOfCohomologyClassEqZero h⟩,
    fun ⟨s⟩ ↦ S.cohomologyClass_eq_zero_of_splitting s⟩

end CohomologyClass

end GroupExtension
