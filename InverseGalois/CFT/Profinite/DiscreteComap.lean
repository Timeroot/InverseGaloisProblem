/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Coeff
import InverseGalois.CFT.Profinite.Discrete
import InverseGalois.CFT.Profinite.Res

/-!
# The comparison with ordinary cohomology respects the maps on both sides

The comparison between the smooth cohomology of a group and the ordinary cohomology of the additive
copy of its coefficients is built cocycle by cocycle, and both languages move a cocycle in the same
two ways: along a homomorphism of the acting group, and along an equivariant homomorphism of the
coefficients.  The comparison therefore commutes with both, and the two squares are proved by
reading off the same function on both sides.

That is what makes the smooth language and the language of representations interchangeable in
practice.  A class of an embedding problem is naturally written with smooth cochains, because that
is where a lift of a homomorphism lives; a vanishing theorem is naturally proved with
representations, because that is where a counting argument on cochains with coefficients in a module
over a finite ring lives.  The squares below let a statement proved on one side be used on the
other, and in particular turn the triviality of the restriction of a smooth class to a subgroup into
the vanishing of an ordinary restriction map.

## Main definitions

* `InverseGalois.CFT.discreteRepHom`: the identity of the coefficients, read as a morphism from the
  representation restricted along a homomorphism to the representation of the source.
* `InverseGalois.CFT.discreteResRepHom`: the same for the inclusion of a subgroup.
* `InverseGalois.CFT.discreteCoeffRepHom`: an equivariant homomorphism of the coefficients, read as
  a morphism of the associated representations.

## Main results

* `InverseGalois.CFT.discreteSmoothH1Hom_comapH1`,
  `InverseGalois.CFT.discreteSmoothH2Hom_comapH2`: **the comparison carries pullback along a smooth
  homomorphism to the induced map in ordinary cohomology.**
* `InverseGalois.CFT.discreteSmoothH1Hom_coeffH1`,
  `InverseGalois.CFT.discreteSmoothH2Hom_coeffH2`: **the comparison carries an equivariant
  homomorphism of the coefficients to the induced map in ordinary cohomology.**
* `InverseGalois.CFT.resH2_eq_one_iff_map_eq_zero`: **the restriction of a smooth class to a
  subgroup is trivial exactly when the ordinary restriction of its class vanishes.**
* `InverseGalois.CFT.mem_sha2_iff_forall_map_eq_zero`: the everywhere locally trivial classes read
  off in the language of representations.

## Tags

group cohomology, discrete group, smooth cochain, restriction, comparison
-/

namespace InverseGalois.CFT

open CategoryTheory groupCohomology

/-! ### Along a homomorphism of the acting group -/

section Comap

variable {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [TopologicalSpace G] [CommGroup M]
variable [MulDistribMulAction Γ M] [MulDistribMulAction G M]
variable (ρ : Γ →* G) (hact : ∀ (γ : Γ) (m : M), γ • m = ρ γ • m)

/-- **The identity of the coefficients as a morphism of representations**, from the representation
of the target restricted along a homomorphism to the representation of the source.  The two actions
agree because the source acts through the homomorphism. -/
noncomputable def discreteRepHom :
    (Action.res _ ρ).obj (Rep.ofMulDistribMulAction G M) ⟶ Rep.ofMulDistribMulAction Γ M where
  hom := 𝟙 _
  comm γ := by
    ext m
    exact congrArg Additive.ofMul (hact γ (Additive.toMul m)).symm

omit [TopologicalSpace Γ] [TopologicalSpace G] in
/-- The comparison morphism is the identity on the underlying module. -/
theorem discreteRepHom_hom : (discreteRepHom ρ hact).hom = 𝟙 _ := rfl

instance isIso_discreteRepHom : IsIso (discreteRepHom ρ hact) := by
  have : IsIso (discreteRepHom ρ hact).hom := by
    rw [discreteRepHom_hom]
    infer_instance
  infer_instance

/-- **The comparison carries pullback along a smooth homomorphism to the induced map in ordinary
cohomology**, in degree one. -/
theorem discreteSmoothH1Hom_comapH1 (hsm : IsSmoothHom ρ) (x : SmoothH1 G M) :
    discreteSmoothH1Hom Γ M (comapH1 ρ hact hsm x)
      = Multiplicative.ofAdd (groupCohomology.map ρ (discreteRepHom ρ hact) 1
          (Multiplicative.toAdd (discreteSmoothH1Hom G M x))) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rw [comapH1_smoothH1Mk, discreteSmoothH1Hom_smoothH1Mk, discreteSmoothH1Hom_smoothH1Mk]
  simp only [_root_.toAdd_ofAdd]
  congr 1
  rw [groupCohomology.H1π_comp_map_apply]
  exact congrArg _ (Subtype.ext rfl)

/-- **The comparison carries pullback along a smooth homomorphism to the induced map in ordinary
cohomology**, in degree two. -/
theorem discreteSmoothH2Hom_comapH2 (hsm : IsSmoothHom ρ) (x : SmoothH2 G M) :
    discreteSmoothH2Hom Γ M (comapH2 ρ hact hsm x)
      = Multiplicative.ofAdd (groupCohomology.map ρ (discreteRepHom ρ hact) 2
          (Multiplicative.toAdd (discreteSmoothH2Hom G M x))) := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  rw [comapH2_smoothH2Mk, discreteSmoothH2Hom_smoothH2Mk, discreteSmoothH2Hom_smoothH2Mk]
  simp only [_root_.toAdd_ofAdd]
  congr 1
  rw [groupCohomology.H2π_comp_map_apply]
  exact congrArg _ (Subtype.ext rfl)

end Comap

/-! ### Restriction to a subgroup -/

section Res

variable {G M : Type} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
variable (H : Subgroup G)

/-- **The identity of the coefficients as a morphism of representations**, from the representation
restricted along the inclusion of a subgroup to the representation of the subgroup. -/
noncomputable def discreteResRepHom :
    (Action.res _ H.subtype).obj (Rep.ofMulDistribMulAction G M) ⟶
      Rep.ofMulDistribMulAction ↥H M :=
  discreteRepHom H.subtype fun _ _ => rfl

/-- **The comparison carries restriction to a subgroup to the ordinary restriction map**, in degree
one. -/
theorem discreteSmoothH1Hom_resH1 (x : SmoothH1 G M) :
    discreteSmoothH1Hom ↥H M (resH1 H x)
      = Multiplicative.ofAdd (groupCohomology.map H.subtype (discreteResRepHom H) 1
          (Multiplicative.toAdd (discreteSmoothH1Hom G M x))) :=
  discreteSmoothH1Hom_comapH1 H.subtype (fun _ _ => rfl) (isSmoothHom_subtype H) x

/-- **The comparison carries restriction to a subgroup to the ordinary restriction map**, in degree
two. -/
theorem discreteSmoothH2Hom_resH2 (x : SmoothH2 G M) :
    discreteSmoothH2Hom ↥H M (resH2 H x)
      = Multiplicative.ofAdd (groupCohomology.map H.subtype (discreteResRepHom H) 2
          (Multiplicative.toAdd (discreteSmoothH2Hom G M x))) :=
  discreteSmoothH2Hom_comapH2 H.subtype (fun _ _ => rfl) (isSmoothHom_subtype H) x

/-- **The restriction of a smooth class of the first cohomology to a subgroup is trivial exactly
when the ordinary restriction of its class vanishes.** -/
theorem resH1_eq_one_iff_map_eq_zero (x : SmoothH1 G M) :
    resH1 H x = 1 ↔ groupCohomology.map H.subtype (discreteResRepHom H) 1
      (Multiplicative.toAdd (discreteSmoothH1Hom G M x)) = 0 := by
  constructor
  · intro h
    have h' := congrArg (discreteSmoothH1Hom ↥H M) h
    rw [discreteSmoothH1Hom_resH1, _root_.map_one] at h'
    exact Multiplicative.ofAdd.injective h'
  · intro h
    refine discreteSmoothH1Hom_injective ↥H M ?_
    rw [discreteSmoothH1Hom_resH1, h, _root_.map_one]
    rfl

variable {H} in
/-- **A class of the first cohomology is locally trivial exactly when the ordinary restriction of
its class vanishes on every subgroup of the family.** -/
theorem mem_sha1_iff_forall_map_eq_zero {T : Set (Subgroup G)} (x : SmoothH1 G M) :
    x ∈ sha1 M T ↔ ∀ D ∈ T, groupCohomology.map D.subtype (discreteResRepHom D) 1
      (Multiplicative.toAdd (discreteSmoothH1Hom G M x)) = 0 := by
  simp only [mem_sha1, resH1_eq_one_iff_map_eq_zero]

variable [DiscreteTopology G]

/-- **The restriction of a smooth class of the second cohomology to a subgroup is trivial exactly
when the ordinary restriction of its class vanishes.** -/
theorem resH2_eq_one_iff_map_eq_zero (x : SmoothH2 G M) :
    resH2 H x = 1 ↔ groupCohomology.map H.subtype (discreteResRepHom H) 2
      (Multiplicative.toAdd (discreteSmoothH2Hom G M x)) = 0 := by
  constructor
  · intro h
    have h' := congrArg (discreteSmoothH2Hom ↥H M) h
    rw [discreteSmoothH2Hom_resH2, _root_.map_one] at h'
    exact Multiplicative.ofAdd.injective h'
  · intro h
    refine discreteSmoothH2Hom_injective ↥H M ?_
    rw [discreteSmoothH2Hom_resH2, h, _root_.map_one]
    rfl

variable {H} in
/-- **A class of the second cohomology is locally trivial exactly when the ordinary restriction of
its class vanishes on every subgroup of the family.** -/
theorem mem_sha2_iff_forall_map_eq_zero {T : Set (Subgroup G)} (x : SmoothH2 G M) :
    x ∈ sha2 M T ↔ ∀ D ∈ T, groupCohomology.map D.subtype (discreteResRepHom D) 2
      (Multiplicative.toAdd (discreteSmoothH2Hom G M x)) = 0 := by
  simp only [mem_sha2, resH2_eq_one_iff_map_eq_zero]

end Res

/-! ### Along a homomorphism of the coefficients -/

section Coeff

variable {G M N : Type} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N]
variable [MulDistribMulAction G M] [MulDistribMulAction G N]
variable (φ : M →* N) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)

/-- **An equivariant homomorphism of the coefficients as a morphism of the associated
representations.** -/
noncomputable def discreteCoeffRepHom :
    Rep.ofMulDistribMulAction G M ⟶ Rep.ofMulDistribMulAction G N where
  hom := ModuleCat.ofHom (MonoidHom.toAdditive φ).toIntLinearMap
  comm g := by
    ext m
    exact congrArg Additive.ofMul (hφ g (Additive.toMul m))

/-- **The comparison carries an equivariant homomorphism of the coefficients to the induced map in
ordinary cohomology**, in degree one. -/
theorem discreteSmoothH1Hom_coeffH1 (x : SmoothH1 G M) :
    discreteSmoothH1Hom G N (coeffH1 φ hφ x)
      = Multiplicative.ofAdd (groupCohomology.map (MonoidHom.id G) (discreteCoeffRepHom φ hφ) 1
          (Multiplicative.toAdd (discreteSmoothH1Hom G M x))) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rw [coeffH1_smoothH1Mk, discreteSmoothH1Hom_smoothH1Mk, discreteSmoothH1Hom_smoothH1Mk]
  simp only [_root_.toAdd_ofAdd]
  congr 1
  rw [groupCohomology.H1π_comp_map_apply]
  exact congrArg _ (Subtype.ext rfl)

/-- **The comparison carries an equivariant homomorphism of the coefficients to the induced map in
ordinary cohomology**, in degree two. -/
theorem discreteSmoothH2Hom_coeffH2 (x : SmoothH2 G M) :
    discreteSmoothH2Hom G N (coeffH2 φ hφ x)
      = Multiplicative.ofAdd (groupCohomology.map (MonoidHom.id G) (discreteCoeffRepHom φ hφ) 2
          (Multiplicative.toAdd (discreteSmoothH2Hom G M x))) := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  rw [coeffH2_smoothH2Mk, discreteSmoothH2Hom_smoothH2Mk, discreteSmoothH2Hom_smoothH2Mk]
  simp only [_root_.toAdd_ofAdd]
  congr 1
  rw [groupCohomology.H2π_comp_map_apply]
  exact congrArg _ (Subtype.ext rfl)

end Coeff

end InverseGalois.CFT
