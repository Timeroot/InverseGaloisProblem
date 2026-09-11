/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.Pullback
import InverseGalois.CFT.Profinite.Comap
import InverseGalois.CFT.Profinite.Res

/-!
# The obstruction to a continuous solution of an embedding problem

An embedding problem over a topological group `Γ` is a homomorphism `ρ : Γ → G` together with an
extension `1 → N → E → G → 1`, and to solve it is to lift `ρ` to a homomorphism `Γ → E`.  For an
abstract group the lifts are counted by the cohomology class of the extension pulled back along
`ρ`, and the problem is solvable exactly when that class vanishes.  Over a topological group the
question is a different one: the lift has to be continuous, so the class has to be taken in the
cohomology of smooth cochains rather than of all cochains.

This file proves that the same criterion holds there.  The obstruction is the factor set of a
set-theoretic section of the extension, read through `ρ`; it is a smooth two cocycle as soon as the
kernel of `ρ` is open, because then *every* cochain composed with `ρ` is smooth.  Its class does not
depend on the section, two sections differing by a one cochain which is again composed with `ρ`.
And the class is trivial exactly when a smooth lift exists.

Both directions go through the fibre product of the extension with `Γ`, which turns a lift into a
splitting.  A trivialising one cochain corrects the section into a splitting of the fibre product,
and the resulting homomorphism is smooth because the cochain and `ρ` both are; conversely a smooth
lift is a splitting of the fibre product, and comparing it with the section produces a one cochain
which is smooth because a value of the comparison is determined by the values of the lift and of
`ρ`.

In the arithmetic situation `Γ` is the absolute Galois group of a number field and `G` is the Galois
group of a finite extension, so the kernel of `ρ` is open and the criterion applies.  A smooth
homomorphism onto a finite group is one with an open kernel, so the solutions the criterion produces
really are field extensions.

## Main definitions

* `GroupExtension.pullbackSection`: the section of the fibre product induced by a section of the
  extension.
* `InverseGalois.CFT.liftObstruction`: the factor set of a section, read through the given
  homomorphism.
* `InverseGalois.CFT.liftObstructionClass`: **the obstruction class of an embedding problem**, in
  the second cohomology of smooth cochains.

## Main results

* `GroupExtension.factorSet_pullbackSection`: the factor set of the induced section of the fibre
  product is the factor set of the given section read through the homomorphism.
* `InverseGalois.CFT.liftObstructionClass_eq`: the obstruction class does not depend on the section.
* `InverseGalois.CFT.liftObstructionClass_eq_one_iff`: **an embedding problem over a topological
  group, with commutative kernel and a homomorphism with open kernel, has a smooth solution exactly
  when its obstruction class vanishes.**
* `InverseGalois.CFT.liftObstructionClass_mem_sha2`: **an embedding problem solvable over every
  subgroup of a family has an obstruction class trivial on that family.**
* `InverseGalois.CFT.exists_smooth_lift_of_sha2_eq_bot`: **a locally solvable embedding problem is
  solvable** as soon as there is no everywhere locally trivial class.
* `InverseGalois.CFT.isOpenNormal_ker_of_isSmooth₁`,
  `InverseGalois.CFT.isSmooth₁_of_isOpenNormal_ker`: for a homomorphism of topological groups,
  smoothness is having an open kernel.

## Tags

profinite group, Galois cohomology, embedding problem, group extension, obstruction, smooth cochain
-/

namespace GroupExtension

/-! ### The section of a fibre product induced by a section -/

section PullbackSection

variable {N E G Γ : Type*} [Group N] [Group E] [Group G] [Group Γ]

/-- **The section of the fibre product induced by a section of the extension**: the value of the
section at the image of a point, paired with the point itself. -/
def pullbackSection (S : GroupExtension N E G) (ρ : Γ →* G) (σ : S.Section) :
    (S.pullback ρ).Section where
  toFun γ := ⟨(σ (ρ γ), γ), σ.rightInverse_rightHom (ρ γ)⟩
  rightInverse_rightHom _ := rfl

@[simp]
theorem coe_pullbackSection (S : GroupExtension N E G) (ρ : Γ →* G) (σ : S.Section) (γ : Γ) :
    ((pullbackSection S ρ σ γ : S.pullbackSubgroup ρ) : E × Γ) = (σ (ρ γ), γ) := rfl

end PullbackSection

section PullbackFactorSet

variable {N E G Γ : Type*} [CommGroup N] [Group E] [Group G] [Group Γ]

/-- **The factor set of the induced section of the fibre product is the factor set of the given
section, read through the homomorphism.**  In the second coordinate the fibre product is the group
itself, where a section is the identity and contributes nothing. -/
theorem factorSet_pullbackSection (S : GroupExtension N E G) (ρ : Γ →* G) (σ : S.Section)
    (g h : Γ) :
    (S.pullback ρ).factorSet (pullbackSection S ρ σ) (g, h) = S.factorSet σ (ρ g, ρ h) := by
  refine (S.pullback ρ).inl_injective ?_
  rw [inl_factorSet]
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show σ (ρ g) * σ (ρ h) * (σ (ρ (g * h)))⁻¹ = S.inl (S.factorSet σ (ρ g, ρ h))
    rw [inl_factorSet, map_mul]
  · show g * h * (g * h)⁻¹ = 1
    rw [mul_inv_cancel]

end PullbackFactorSet

end GroupExtension

namespace InverseGalois.CFT

open GroupExtension groupCohomology

/-! ### Smoothness of a homomorphism into a discrete group -/

section SmoothHom

variable {Γ E : Type*} [Group Γ] [TopologicalSpace Γ] [Group E]

/-- **A homomorphism which is smooth as a cochain has an open kernel**, the kernel containing the
open normal subgroup on whose cosets the homomorphism is constant. -/
theorem isOpenNormal_ker_of_isSmooth₁ [ContinuousMul Γ] {f : Γ →* E}
    (hf : IsSmooth₁ (f : Γ → E)) : IsOpenNormal f.ker := by
  obtain ⟨N₁, hN₁, h₁⟩ := hf
  refine ⟨f.normal_ker, Subgroup.isOpen_mono (H₁ := N₁) (fun n hn => ?_) hN₁.isOpen⟩
  have hn' : f n = f 1 := by simpa using h₁ 1 n hn
  rw [MonoidHom.mem_ker, hn', _root_.map_one]

/-- **A homomorphism with an open kernel is smooth as a cochain.** -/
theorem isSmooth₁_of_isOpenNormal_ker {f : Γ →* E} (h : IsOpenNormal f.ker) :
    IsSmooth₁ (f : Γ → E) :=
  ⟨f.ker, h, fun x n hn => by
    rw [_root_.map_mul, MonoidHom.mem_ker.mp hn, mul_one]⟩

end SmoothHom

/-! ### The obstruction class -/

section Obstruction

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
variable {N E G : Type*} [CommGroup N] [Group E] [Group G]
variable (S : GroupExtension N E G) (ρ : Γ →* G) [MulDistribMulAction Γ N]
variable (hact : ∀ (γ : Γ) (n : N), γ • n = S.conjActHom (ρ γ) n)

/-- **The obstruction cochain of an embedding problem**: the factor set of a section of the
extension, read through the given homomorphism. -/
noncomputable def liftObstruction (σ : S.Section) : Γ × Γ → N := comap₂ ρ (S.factorSet σ)

omit [TopologicalSpace Γ] [MulDistribMulAction Γ N] in
theorem liftObstruction_apply (σ : S.Section) (g h : Γ) :
    liftObstruction S ρ σ (g, h) = S.factorSet σ (ρ g, ρ h) := rfl

omit [TopologicalSpace Γ] in
include hact in
/-- The obstruction cochain is a two cocycle, being one already over the quotient. -/
theorem isMulCocycle₂_liftObstruction (σ : S.Section) : IsMulCocycle₂ (liftObstruction S ρ σ) := by
  letI := S.mulDistribMulAction
  exact isMulCocycle₂_comap₂ ρ (fun γ n => hact γ n) (S.isMulCocycle₂_factorSet σ)

omit [MulDistribMulAction Γ N] in
/-- The obstruction cochain is smooth, a homomorphism with open kernel making every composed
cochain smooth. -/
theorem isSmooth₂_liftObstruction (hker : IsOpenNormal ρ.ker) (σ : S.Section) :
    IsSmooth₂ (liftObstruction S ρ σ) :=
  isSmooth₂_comap₂_of_isOpenNormal_ker ρ hker _

/-- **The obstruction class of an embedding problem**, in the second cohomology of smooth
cochains. -/
noncomputable def liftObstructionClass (hker : IsOpenNormal ρ.ker) (σ : S.Section) :
    SmoothH2 Γ N :=
  smoothH2Mk _ (isMulCocycle₂_liftObstruction S ρ hact σ) (isSmooth₂_liftObstruction S ρ hker σ)

/-- **The obstruction class does not depend on the section.**  Two sections differ by a one
cochain over the quotient, which composed with the homomorphism is again smooth. -/
theorem liftObstructionClass_eq (hker : IsOpenNormal ρ.ker) (σ τ : S.Section) :
    liftObstructionClass S ρ hact hker σ = liftObstructionClass S ρ hact hker τ := by
  unfold liftObstructionClass
  refine (smoothH2Mk_eq_iff _ _ _ _).2 ⟨comap₁ ρ (S.sectionRatio σ τ),
    isSmooth₁_comap₁_of_isOpenNormal_ker ρ hker _, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  rw [coboundary₂_apply, hact]
  simp only [comap₁_apply, liftObstruction_apply, map_mul]
  rw [S.factorSet_eq_mul σ τ (ρ g) (ρ h)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

include hact in
/-- **An embedding problem over a topological group, with commutative kernel and a homomorphism
with open kernel, has a smooth solution exactly when its obstruction class vanishes.**

A trivialising one cochain corrects the induced section of the fibre product into a splitting, and
the homomorphism it produces is smooth because the cochain and the given homomorphism both are.
Conversely a smooth lift splits the fibre product, and comparing that splitting with the induced
section produces a smooth one cochain trivialising the obstruction. -/
theorem liftObstructionClass_eq_one_iff (hker : IsOpenNormal ρ.ker) (σ : S.Section) :
    liftObstructionClass S ρ hact hker σ = 1 ↔
      ∃ f : Γ →* E, IsSmooth₁ (f : Γ → E) ∧ ∀ γ, S.rightHom (f γ) = ρ γ := by
  unfold liftObstructionClass
  rw [smoothH2Mk_eq_one_iff]
  constructor
  · rintro ⟨x, hxs, hx⟩
    have hx' : ∀ g h : Γ, (S.pullback ρ).conjActHom g (x h) / x (g * h) * x g
        = (S.pullback ρ).factorSet (pullbackSection S ρ σ) (g, h) := by
      intro g h
      rw [pullback_conjActHom, factorSet_pullbackSection, ← hact]
      exact congrFun hx (g, h)
    set s := (S.pullback ρ).splittingOfIsMulCoboundary₂ (pullbackSection S ρ σ) x hx' with hs
    refine ⟨(S.pullbackFst ρ).comp s.toMonoidHom, ?_, ?_⟩
    · obtain ⟨N₁, hN₁, hx₁⟩ := hxs
      refine ⟨N₁ ⊓ ρ.ker, hN₁.inf hker, fun γ n hn => ?_⟩
      show (S.inl (x (γ * n)))⁻¹ * σ (ρ (γ * n)) = (S.inl (x γ))⁻¹ * σ (ρ γ)
      rw [hx₁ γ n hn.1, _root_.map_mul, MonoidHom.mem_ker.mp hn.2, mul_one]
    · intro γ
      rw [MonoidHom.comp_apply, rightHom_pullbackFst]
      exact congrArg ρ (s.rightInverse_rightHom γ)
  · rintro ⟨f, hfs, hf⟩
    set s := pullbackSplitting S ρ f hf with hs
    have hinl : ∀ γ : Γ,
        S.inl ((S.pullback ρ).sectionRatio (pullbackSection S ρ σ) s.toSection γ)
          = σ (ρ γ) * (f γ)⁻¹ := fun γ =>
      congrArg (fun y : E × Γ => y.1)
        (congrArg Subtype.val
          ((S.pullback ρ).inl_sectionRatio (pullbackSection S ρ σ) s.toSection γ))
    refine ⟨(S.pullback ρ).sectionRatio (pullbackSection S ρ σ) s.toSection, ?_, ?_⟩
    · obtain ⟨N₁, hN₁, hf₁⟩ := hfs
      refine ⟨N₁ ⊓ ρ.ker, hN₁.inf hker, fun γ n hn => ?_⟩
      refine S.inl_injective ?_
      rw [hinl, hinl, hf₁ γ n hn.1, _root_.map_mul, MonoidHom.mem_ker.mp hn.2, mul_one]
    · funext p
      obtain ⟨g, h⟩ := p
      have hcmp := (S.pullback ρ).factorSet_eq_mul (pullbackSection S ρ σ) s.toSection g h
      rw [factorSet_pullbackSection, factorSet_splitting, mul_one, pullback_conjActHom] at hcmp
      rw [coboundary₂_apply, hact, liftObstruction_apply, hcmp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_div]
      abel

end Obstruction

/-! ### The obstruction on a subgroup -/

section Restrict

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
variable {N E G : Type*} [CommGroup N] [Group E] [Group G]
variable (S : GroupExtension N E G) (ρ : Γ →* G) [MulDistribMulAction Γ N]
variable (hact : ∀ (γ : Γ) (n : N), γ • n = S.conjActHom (ρ γ) n)

omit [MulDistribMulAction Γ N] in
/-- A homomorphism with an open kernel still has one after restriction to a subgroup. -/
theorem isOpenNormal_ker_comp_subtype (hker : IsOpenNormal ρ.ker) (D : Subgroup Γ) :
    IsOpenNormal (ρ.comp D.subtype).ker :=
  isOpenNormal_comap_subtype D hker

include hact in
/-- **The obstruction class restricted to a subgroup is the obstruction class of the embedding
problem restricted to that subgroup.**  Both are the factor set of the same section, read through
the same homomorphism. -/
theorem resH2_liftObstructionClass (hker : IsOpenNormal ρ.ker) (σ : S.Section) (D : Subgroup Γ) :
    resH2 D (liftObstructionClass S ρ hact hker σ)
      = liftObstructionClass S (ρ.comp D.subtype) (fun d n => hact (d : Γ) n)
        (isOpenNormal_ker_comp_subtype ρ hker D) σ := rfl

include hact in
/-- **The obstruction class dies on a subgroup exactly when the embedding problem restricted to
that subgroup has a smooth solution.** -/
theorem resH2_liftObstructionClass_eq_one_iff (hker : IsOpenNormal ρ.ker) (σ : S.Section)
    (D : Subgroup Γ) :
    resH2 D (liftObstructionClass S ρ hact hker σ) = 1 ↔
      ∃ f : ↥D →* E, IsSmooth₁ (f : ↥D → E) ∧ ∀ d : ↥D, S.rightHom (f d) = ρ (d : Γ) := by
  rw [resH2_liftObstructionClass S ρ hact hker σ D]
  exact liftObstructionClass_eq_one_iff S (ρ.comp D.subtype) (fun d n => hact (d : Γ) n)
    (isOpenNormal_ker_comp_subtype ρ hker D) σ

include hact in
/-- **An embedding problem which is solvable over every subgroup of a family has an obstruction
class trivial on that family.**  Over a number field the family is the decomposition subgroups, and
this says that a locally solvable embedding problem has an everywhere locally trivial
obstruction. -/
theorem liftObstructionClass_mem_sha2 (hker : IsOpenNormal ρ.ker) (σ : S.Section)
    {T : Set (Subgroup Γ)}
    (h : ∀ D ∈ T, ∃ f : ↥D →* E, IsSmooth₁ (f : ↥D → E) ∧ ∀ d : ↥D, S.rightHom (f d) = ρ (d : Γ)) :
    liftObstructionClass S ρ hact hker σ ∈ sha2 N T := by
  refine mem_sha2.2 fun D hD => ?_
  exact (resH2_liftObstructionClass_eq_one_iff S ρ hact hker σ D).2 (h D hD)

include hact in
/-- **A locally solvable embedding problem is solvable as soon as there is no everywhere locally
trivial class.**  The obstruction lies in that group, so it vanishes and the solution is the lift
its vanishing produces. -/
theorem exists_smooth_lift_of_sha2_eq_bot (hker : IsOpenNormal ρ.ker) (σ : S.Section)
    {T : Set (Subgroup Γ)} (hbot : sha2 N T = ⊥)
    (h : ∀ D ∈ T, ∃ f : ↥D →* E, IsSmooth₁ (f : ↥D → E) ∧ ∀ d : ↥D, S.rightHom (f d) = ρ (d : Γ)) :
    ∃ f : Γ →* E, IsSmooth₁ (f : Γ → E) ∧ ∀ γ, S.rightHom (f γ) = ρ γ :=
  (liftObstructionClass_eq_one_iff S ρ hact hker σ).1 <|
    (Subgroup.eq_bot_iff_forall _).1 hbot _ (liftObstructionClass_mem_sha2 S ρ hact hker σ h)

end Restrict

end InverseGalois.CFT
