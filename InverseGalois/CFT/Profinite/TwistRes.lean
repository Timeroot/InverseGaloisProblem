/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.TransgressionRestrict
import InverseGalois.CFT.Profinite.Twist

/-!
# Localising a twisted class

The twisting construction builds a class of the first cohomology with coefficients in a finite
module out of an element of a group and a homomorphism of the coefficients.  Read on the Galois
group of a number field the group is the units of a field, and the class of the first cohomology
has to be localised at every place: restricted to a decomposition subgroup, where the units of the
field are replaced by the units of a larger one.

**Both constructions are functorial in the group, and the two are compatible.**  A homomorphism of
groups induces a map of the first cohomologies by composing a cocycle with it, a homomorphism of
the coefficients induces one by composing on the other side, and the two compositions commute on
the nose.  So the twisting map is natural: if the class attached to an element of the base group is
carried by the map of the groups to the class attached to its image under some homomorphism of base
groups, then the whole twisting map is carried to the twisting map of the image, tensored with the
identity on the homomorphisms of the coefficients.

The two cases used are the restriction along an inclusion of subgroups, and the restriction of the
first cohomology of a normal subgroup to the part of it lying inside another subgroup, which is
what localisation at a place is.

## Main definitions

* `InverseGalois.CFT.resInclH1`: restriction of a class of the first cohomology along an inclusion
  of subgroups.

## Main results

* `InverseGalois.CFT.comapH1_coeffH1`: **a homomorphism of the coefficients commutes with the map
  induced by a homomorphism of the groups.**
* `InverseGalois.CFT.comapH1_twistMap`: **the twisting map is natural in the group.**
* `InverseGalois.CFT.resSubH1_twistClass`, `InverseGalois.CFT.resSubH1_twistMap`: the same, for the
  localisation of the first cohomology of a normal subgroup at a subgroup.

## Tags

Galois cohomology, twist, restriction, localisation, tensor product, naturality
-/

namespace InverseGalois.CFT

open groupCohomology TensorProduct

/-! ### A map of the coefficients and a map of the groups -/

section Comap

variable {G Q : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
variable {M E : Type*} [CommGroup M] [CommGroup E]
variable [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable [MulDistribMulAction G E] [MulDistribMulAction Q E]
variable (π : G →* Q) (hπM : ∀ (g : G) (m : M), g • m = π g • m)
  (hπE : ∀ (g : G) (e : E), g • e = π g • e) (hsm : IsSmoothHom π)
variable (w : M →* E) (hw : ∀ (q : Q) (m : M), w (q • m) = q • w m)
  (hw' : ∀ (g : G) (m : M), w (g • m) = g • w m)

/-- **A homomorphism of the coefficients commutes with the map induced by a homomorphism of the
groups**: both sides compose the cocycle with the homomorphism of groups on one side and with the
homomorphism of coefficients on the other. -/
theorem comapH1_coeffH1 (z : SmoothH1 Q M) :
    comapH1 π hπE hsm (coeffH1 w hw z) = coeffH1 w hw' (comapH1 π hπM hsm z) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  rw [coeffH1_smoothH1Mk, comapH1_smoothH1Mk, comapH1_smoothH1Mk, coeffH1_smoothH1Mk]
  exact smoothH1Mk_congr rfl _ _ _ _

end Comap

/-! ### Naturality of the twisting map -/

section TwistComap

variable {G Q : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
variable {M E A A' : Type*} [CommGroup M] [CommGroup E] [CommGroup A] [CommGroup A']
variable [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable [MulDistribMulAction G E] [MulDistribMulAction Q E]
variable (π : G →* Q) (hπM : ∀ (g : G) (m : M), g • m = π g • m)
  (hπE : ∀ (g : G) (e : E), g • e = π g • e) (hsm : IsSmoothHom π)
variable (htrivM : ∀ (q : Q) (m : M), q • m = m) (htrivE : ∀ (q : Q) (e : E), q • e = e)
variable (htrivM' : ∀ (g : G) (m : M), g • m = m) (htrivE' : ∀ (g : G) (e : E), g • e = e)
variable (κ : A →* SmoothH1 Q M) (κ' : A' →* SmoothH1 G M) (ν : A →* A')

/-- **The class attached to an element of the base group and a homomorphism of the coefficients is
carried by a homomorphism of the groups to the class attached to the image of the element.** -/
theorem comapH1_twistClass (a : A) (w : M →* E) :
    comapH1 π hπE hsm (twistClass htrivM htrivE κ a w)
      = twistClass htrivM' htrivE' ((comapH1 π hπM hsm).comp κ) a w :=
  comapH1_coeffH1 π hπM hπE hsm w _ _ (κ a)

/-- The same, when the map of the groups is known on the base group. -/
theorem comapH1_twistClass_comp (hν : ∀ a : A, comapH1 π hπM hsm (κ a) = κ' (ν a)) (a : A)
    (w : M →* E) :
    comapH1 π hπE hsm (twistClass htrivM htrivE κ a w)
      = twistClass htrivM' htrivE' κ' (ν a) w := by
  rw [comapH1_twistClass π hπM hπE hsm htrivM htrivE htrivM' htrivE' κ a w, twistClass, twistClass,
    MonoidHom.comp_apply, hν]

/-- **The twisting map is natural in the group**: it commutes with the map of the base groups
tensored with the identity on the homomorphisms of the coefficients. -/
theorem comapH1_twistMap (hν : ∀ a : A, comapH1 π hπM hsm (κ a) = κ' (ν a))
    (z : Additive A ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (comapH1 π hπE hsm) (twistMap htrivM htrivE κ z)
      = twistMap htrivM' htrivE' κ'
        (TensorProduct.map (MonoidHom.toAdditive ν).toIntLinearMap LinearMap.id z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul x y =>
    rw [TensorProduct.map_tmul]
    exact congrArg Additive.ofMul (comapH1_twistClass_comp π hπM hπE hsm htrivM htrivE htrivM'
      htrivE' κ κ' ν hν x.toMul y.toMul)

end TwistComap

/-! ### Restriction along an inclusion of subgroups -/

section Incl

variable {G : Type*} [Group G] [TopologicalSpace G] {H H' : Subgroup G} (hle : H ≤ H')
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- The inclusion of a subgroup in a larger one is a smooth homomorphism. -/
theorem isSmoothHom_inclusion : IsSmoothHom (Subgroup.inclusion hle) :=
  isSmoothHom_of_continuous (continuous_inclusion H hle)

/-- **Restriction of a class of the first cohomology along an inclusion of subgroups.** -/
def resInclH1 : SmoothH1 ↥H' M →* SmoothH1 ↥H M :=
  comapH1 (Subgroup.inclusion hle) (fun _ _ => rfl) (isSmoothHom_inclusion hle)

/-- Restriction along an inclusion of subgroups is computed on cocycles. -/
theorem resInclH1_smoothH1Mk {u : ↥H' → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    resInclH1 hle (smoothH1Mk u hu hs)
      = smoothH1Mk (comap₁ (Subgroup.inclusion hle) u)
        (isMulCocycle₁_comap₁ _ (fun _ _ => rfl) hu)
        ((isSmoothHom_inclusion hle).isSmooth₁ hs) := rfl

variable {E A A' : Type*} [CommGroup E] [CommGroup A] [CommGroup A'] [MulDistribMulAction G E]
variable (htrivM : ∀ (x : ↥H') (m : M), x • m = m) (htrivE : ∀ (x : ↥H') (e : E), x • e = e)
variable (htrivM' : ∀ (x : ↥H) (m : M), x • m = m) (htrivE' : ∀ (x : ↥H) (e : E), x • e = e)
variable (κ : A →* SmoothH1 ↥H' M) (κ' : A' →* SmoothH1 ↥H M) (ν : A →* A')

/-- **A twisted class restricts along an inclusion of subgroups to the twisted class of the
restriction.** -/
theorem resInclH1_twistClass (hν : ∀ a : A, resInclH1 hle (κ a) = κ' (ν a)) (a : A)
    (w : M →* E) :
    resInclH1 hle (twistClass htrivM htrivE κ a w)
      = twistClass htrivM' htrivE' κ' (ν a) w :=
  comapH1_twistClass_comp (Subgroup.inclusion hle) (fun _ _ => rfl) (fun _ _ => rfl)
    (isSmoothHom_inclusion hle) htrivM htrivE htrivM' htrivE' κ κ' ν hν a w

/-- **The twisting map is natural for restriction along an inclusion of subgroups.** -/
theorem resInclH1_twistMap (hν : ∀ a : A, resInclH1 hle (κ a) = κ' (ν a))
    (z : Additive A ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (resInclH1 hle) (twistMap htrivM htrivE κ z)
      = twistMap htrivM' htrivE' κ'
        (TensorProduct.map (MonoidHom.toAdditive ν).toIntLinearMap LinearMap.id z) :=
  comapH1_twistMap (Subgroup.inclusion hle) (fun _ _ => rfl) (fun _ _ => rfl)
    (isSmoothHom_inclusion hle) htrivM htrivE htrivM' htrivE' κ κ' ν hν z

end Incl

/-! ### Localisation of the first cohomology of a normal subgroup -/

section Sub

variable {G : Type*} [Group G] [TopologicalSpace G] (N D : Subgroup G)
variable {M E A A' : Type*} [CommGroup M] [CommGroup E] [CommGroup A] [CommGroup A']
variable [MulDistribMulAction G M] [MulDistribMulAction G E]

omit [TopologicalSpace G] in
/-- A subgroup acting trivially still acts trivially on the part of it inside another subgroup. -/
theorem smul_subgroupOf_eq_of_trivial (htriv : ∀ (x : ↥N) (m : M), x • m = m)
    (y : ↥(N.subgroupOf D)) (m : M) : y • m = m :=
  htriv ⟨(y : ↥D), Subgroup.mem_subgroupOf.1 y.2⟩ m

variable (htrivM : ∀ (x : ↥N) (m : M), x • m = m) (htrivE : ∀ (x : ↥N) (e : E), x • e = e)
variable (htrivM' : ∀ (y : ↥(N.subgroupOf D)) (m : M), y • m = m)
  (htrivE' : ∀ (y : ↥(N.subgroupOf D)) (e : E), y • e = e)
variable (κ : A →* SmoothH1 ↥N M) (κ' : A' →* SmoothH1 ↥(N.subgroupOf D) M) (ν : A →* A')

/-- **A twisted class localises to the twisted class of the localisation.** -/
theorem resSubH1_twistClass (hν : ∀ a : A, resSubH1 N D (κ a) = κ' (ν a)) (a : A) (w : M →* E) :
    resSubH1 N D (twistClass htrivM htrivE κ a w)
      = twistClass htrivM' htrivE' κ' (ν a) w :=
  comapH1_twistClass_comp (interSubHom N D) (fun _ _ => rfl) (fun _ _ => rfl)
    (isSmoothHom_interSubHom N D) htrivM htrivE htrivM' htrivE' κ κ' ν hν a w

/-- **The twisting map is natural for localisation at a subgroup.** -/
theorem resSubH1_twistMap (hν : ∀ a : A, resSubH1 N D (κ a) = κ' (ν a))
    (z : Additive A ⊗[ℤ] Additive (M →* E)) :
    MonoidHom.toAdditive (resSubH1 N D) (twistMap htrivM htrivE κ z)
      = twistMap htrivM' htrivE' κ'
        (TensorProduct.map (MonoidHom.toAdditive ν).toIntLinearMap LinearMap.id z) :=
  comapH1_twistMap (interSubHom N D) (fun _ _ => rfl) (fun _ _ => rfl)
    (isSmoothHom_interSubHom N D) htrivM htrivE htrivM' htrivE' κ κ' ν hν z

end Sub

end InverseGalois.CFT
