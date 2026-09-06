/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerLocalQuot
import InverseGalois.CFT.Profinite.KummerTransport

/-!
# Local triviality of a twisted Kummer class, read by restriction and a map of representations

A class of the first cohomology which is locally trivial everywhere has been transported twice: once
across the twisted Kummer identification, which replaces the first cohomology of the subgroup fixing
a level by the units of that level tensored with the homomorphisms of the roots of unity into the
kernel, and once along the identification of the quotient by that subgroup with the Galois group of
the level.  What class field theory does with the result is restrict it to a decomposition subgroup
and push the coefficients forward to a local representation.  The point of this file is that those
two operations kill the class, and that the whole computation is driven by a single additive map of
the coefficients.

The local data are packaged as one additive map from the twisted Kummer coefficients to the
coefficients of the local representation, asked to kill what the inclusion of the units kills, to be
equivariant for the decomposition group, and to agree with the map of representations.  Everything
else is bookkeeping: a representation of a subgroup pulled back along an isomorphism of groups gives
the multiplicative action the localisation of the coefficients needs, the additive map becomes a
homomorphism into the multiplicative copy of the local coefficients, and the identification of the
two readings of the local coefficients is the identity.  With that in place, **the restriction of an
everywhere locally trivial twisted Kummer class to a decomposition subgroup dies under any map of
representations induced by such a local map**.

## Main definitions

* `InverseGalois.CFT.repPullDistribMulAction`, `InverseGalois.CFT.repPullMulDistribMulAction`: the
  action of a group on the coefficients of a representation of another group, pulled back along a
  homomorphism, additively and multiplicatively.
* `InverseGalois.CFT.repPullEquiv`: the two readings of those coefficients agree.
* `InverseGalois.CFT.locCoeffHom`: **an additive map of the coefficients, read as a localisation of
  the coefficients of the first cohomology.**

## Main results

* `InverseGalois.CFT.locCoeffHom_smul`: the localisation it defines is equivariant.
* `InverseGalois.CFT.tateMap_tateRes_eq_zero_of_locCoeffHom_comapH1_eq_one`: a class killed by that
  localisation after restriction is killed by restriction followed by the map of representations.
* `InverseGalois.CFT.tateMap_tateRes_kummerFiniteH1Equiv_eq_zero`: **an everywhere locally trivial
  class, read over the Galois group of the level, dies under restriction to a decomposition subgroup
  followed by any map of representations induced by a local map of the coefficients.**

## Tags

Kummer theory, Galois cohomology, decomposition group, localisation, Tate cohomology
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace InverseGalois.CFT

open CategoryTheory groupCohomology Tate TensorProduct

/-! ### A representation of a group, pulled back along a homomorphism -/

section RepPull

variable {Q H : Type} [Group Q] [Group H] (f : Q →* H) (B : Rep ℤ H)

/-- **The coefficients of a representation, acted on by another group through a homomorphism.** -/
noncomputable def repPullDistribMulAction : DistribMulAction Q ↥B.V where
  smul g t := B.ρ (f g) t
  one_smul t := by
    show B.ρ (f 1) t = t
    rw [_root_.map_one, _root_.map_one]
    rfl
  mul_smul g h t := by
    show B.ρ (f (g * h)) t = B.ρ (f g) (B.ρ (f h) t)
    rw [_root_.map_mul, _root_.map_mul]
    rfl
  smul_zero g := _root_.map_zero (B.ρ (f g))
  smul_add g a b := _root_.map_add (B.ρ (f g)) a b

/-- **The same action, on the multiplicative copy of those coefficients.** -/
noncomputable def repPullMulDistribMulAction :
    MulDistribMulAction Q (Multiplicative ↥B.V) where
  smul g s := Multiplicative.ofAdd (B.ρ (f g) (Multiplicative.toAdd s))
  one_smul s := by
    show Multiplicative.ofAdd (B.ρ (f 1) (Multiplicative.toAdd s)) = s
    rw [_root_.map_one, _root_.map_one]
    rfl
  mul_smul g h s := by
    show Multiplicative.ofAdd (B.ρ (f (g * h)) (Multiplicative.toAdd s))
      = Multiplicative.ofAdd (B.ρ (f g) (B.ρ (f h) (Multiplicative.toAdd s)))
    rw [_root_.map_mul, _root_.map_mul]
    rfl
  smul_one g := congrArg Multiplicative.ofAdd (_root_.map_zero (B.ρ (f g)))
  smul_mul g a b := congrArg Multiplicative.ofAdd
    (_root_.map_add (B.ρ (f g)) (Multiplicative.toAdd a) (Multiplicative.toAdd b))

/-- The coefficients of a representation and the additive copy of their multiplicative copy are the
same abelian group. -/
noncomputable def repPullEquiv : ↥B.V ≃+ Additive (Multiplicative ↥B.V) := AddEquiv.refl _

end RepPull

/-! ### An additive map of the coefficients, read as a localisation -/

section Pull

variable {Q G : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Group G] [Finite G]
variable {S : Type} [CommGroup S] [MulDistribMulAction Q S]
variable {T : Type} [AddCommGroup T] [DistribMulAction Q T]
variable (κ : T ≃+ Additive S)
  (hκ : ∀ (g : Q) (t : T), κ (g • t) = Additive.ofMul (g • (κ t).toMul))
variable (e : Q ≃* G) (B : Rep ℤ G) (φ : T ≃+ ↥B.V)
  (hφ : ∀ (g : Q) (t : T), φ (g • t) = B.ρ (e g) (φ t))
variable {Q' : Type} [Group Q'] [TopologicalSpace Q'] [DiscreteTopology Q']
  [MulDistribMulAction Q' S]
variable {H : Subgroup G} (e' : Q' ≃* ↥H) (B' : Rep ℤ ↥H)
variable [MulDistribMulAction Q' (Multiplicative ↥B'.V)] [DistribMulAction Q' ↥B'.V]
variable (hact : ∀ (g : Q') (x : Multiplicative ↥B'.V),
  g • x = Multiplicative.ofAdd (B'.ρ (e' g) (Multiplicative.toAdd x)))
variable (hactT : ∀ (g : Q') (t : ↥B'.V), g • t = B'.ρ (e' g) t)
variable (π : Q' →* Q) (hπ : ∀ (g : Q') (s : S), g • s = π g • s) (hsm : IsSmoothHom π)
variable (Φ : resObj H B ⟶ B') (loc : T →+ ↥B'.V)
variable (hloc : ∀ (g : Q') (t : T), loc (π g • t) = B'.ρ (e' g) (loc t))

/-- **An additive map of the coefficients, read as a map of the multiplicative group they are
identified with.**  This is the localisation of the coefficients that a local condition on a class
of the first cohomology is expressed by. -/
noncomputable def locCoeffHom : S →* Multiplicative ↥B'.V where
  toFun z := Multiplicative.ofAdd (loc (κ.symm (Additive.ofMul z)))
  map_one' := by
    show Multiplicative.ofAdd (loc (κ.symm 0)) = 1
    rw [_root_.map_zero, _root_.map_zero]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (loc (κ.symm (Additive.ofMul (a * b)))) = _
    show Multiplicative.ofAdd (loc (κ.symm (Additive.ofMul a + Additive.ofMul b))) = _
    rw [_root_.map_add, _root_.map_add]
    rfl

omit [TopologicalSpace Q] [DiscreteTopology Q] [Finite G] [TopologicalSpace Q']
  [DiscreteTopology Q'] [DistribMulAction Q' (B'.V : Type)] in
include hκ hπ hact hloc in
/-- The localisation defined by an equivariant additive map of the coefficients is equivariant. -/
theorem locCoeffHom_smul (g : Q') (z : S) :
    locCoeffHom κ B' loc (g • z) = g • locCoeffHom κ B' loc z := by
  have ht : κ.symm (Additive.ofMul (g • z)) = π g • κ.symm (Additive.ofMul z) := by
    rw [hπ g z, AddEquiv.symm_apply_eq, hκ, κ.apply_symm_apply]
    rfl
  show Multiplicative.ofAdd (loc (κ.symm (Additive.ofMul (g • z)))) = _
  rw [ht, hloc, hact]
  rfl

omit [Finite G] [TopologicalSpace Q'] [DiscreteTopology Q'] in
include hactT hact in
/-- Reading the coefficients of a representation as the additive copy of their multiplicative copy
is equivariant. -/
theorem repPullEquiv_smul (g : Q') (t : ↥B'.V) :
    repPullEquiv B' (g • t) = Additive.ofMul (g • (repPullEquiv B' t).toMul) := by
  rw [hactT, hact]
  rfl

omit [Finite G] [TopologicalSpace Q'] [DiscreteTopology Q']
  [MulDistribMulAction Q' (Multiplicative (B'.V : Type))] in
include hactT in
/-- The coefficients of a representation are identified with themselves equivariantly. -/
theorem repPullRefl_smul (g : Q') (t : ↥B'.V) :
    (AddEquiv.refl ↥B'.V) (g • t) = B'.ρ (e' g) ((AddEquiv.refl ↥B'.V) t) := hactT g t

include hκ hφ hact hactT hloc in
/-- **A class of the first cohomology killed by the localisation of its restriction is killed by
restriction to the subgroup followed by the map of representations**, when the map of
representations is the additive map the localisation was defined by. -/
theorem tateMap_tateRes_eq_zero_of_locCoeffHom_comapH1_eq_one {u : Q → S} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u)
    (hcoef : ∀ t : T, Φ.hom.hom (φ t) = loc t)
    (hcomm : ∀ g : Q', ((e' g : ↥H) : G) = e (π g))
    (hx : coeffH1 (locCoeffHom κ B' loc) (locCoeffHom_smul κ hκ e' B' hact π hπ loc hloc)
      (comapH1 π hπ hsm (smoothH1Mk u hu hs)) = 1) :
    tateMap Φ 1 (tateRes H B 1 (Multiplicative.toAdd
      (h1MulEquivOfSmul e B φ hφ
        (smoothH1EquivOfAddEquiv Q S T κ hκ (smoothH1Mk u hu hs))))) = 0 := by
  refine tateMap_tateRes_eq_zero_of_coeffH1_comapH1_eq_one κ hκ e B φ hφ
    (repPullEquiv B') (repPullEquiv_smul e' B' hact hactT) e' B' (AddEquiv.refl ↥B'.V)
    (repPullRefl_smul e' B' hactT) π hπ hsm (locCoeffHom κ B' loc)
    (locCoeffHom_smul κ hκ e' B' hact π hπ loc hloc) Φ hcomm ?_ hu hs hx
  intro t
  show Φ.hom.hom (φ t) = loc (κ.symm (κ t))
  rw [κ.symm_apply_apply]
  exact hcoef t

end Pull

/-! ### The everywhere locally trivial classes of a twisted Kummer identification -/

section Arith

open IntermediateField

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K F : IntermediateField k Ω} [K.fixingSubgroup.Normal] [Normal k ↥K]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/↥(K ⊔ F)) M] [MulDistribMulAction Gal(Ω/k) M]
variable {ιK : M →* (↥K)ˣ} {ιL : M →* (↥(K ⊔ F))ˣ} {p : ℕ} [NeZero p] [IsCyclic M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (hK : IsKummerData ↥K Ω M ιK p) (hL : IsKummerData ↥(K ⊔ F) Ω M ιL p)
variable (j : (↥K)ˣ →* (↥(K ⊔ F))ˣ)
variable (hj : ∀ a : (↥K)ˣ, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (j a)
  = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)
variable (hιj : ∀ m : M, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (ιL m)
  = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m))
variable {D : Subgroup Gal(Ω/k)} (hD : F.fixingSubgroup = D)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivEK : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable (htrivEL : ∀ (x : ↥(K ⊔ F).fixingSubgroup) (e : E), x • e = e)
variable {J : Type} [Fintype J] [DecidableEq J] (α : E ≃* (J → M)) (hEp : ∀ e : E, e ^ p = 1)
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ιK m))
variable [ActsTrivially K.fixingSubgroup (M →* E)] [Finite Gal(↥K/k)]
variable (B : Rep ℤ Gal(↥K/k))
  (φ : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E) ≃+ ↥B.V)
  (hφ : ∀ (g : Gal(Ω/k) ⧸ K.fixingSubgroup) (t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)),
    φ (g • t) = B.ρ (quotientFixingSubgroupEquiv K g) (φ t))
variable {H : Subgroup Gal(↥K/k)}
  (e' : (↥D ⧸ K.fixingSubgroup.subgroupOf D) ≃* ↥H) (B' : Rep ℤ ↥H)
  (Φ : resObj H B ⟶ B')
  (loc : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E) →+ ↥B'.V)

include hK hL hj hιj hD htriv htrivEK htrivEL α hEp hfix hφ in
/-- **A class of the first cohomology which is locally trivial at every subgroup of a family, read
over the Galois group of the level, dies under restriction to a decomposition subgroup followed by a
map of representations.**  The map of representations has to come from a map of the coefficients
which kills the twisted Kummer data that the inclusion of the units of the level into the units of a
compositum kills, and which is equivariant for the decomposition subgroup; and the inclusion of the
units has to be surjective on the twisted Kummer data.  Local triviality is read at the level of the
quotient by the subgroup fixing the level, where the comparison of the level with the compositum
says that such a map kills the class; and the twisted Kummer identification carries that vanishing
across to the representation. -/
theorem tateMap_tateRes_kummerFiniteH1Equiv_eq_zero
    (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k)))
    (hsurj : Function.Surjective (TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap
      (LinearMap.id : Additive (M →* E) →ₗ[ℤ] Additive (M →* E))))
    (hlocker : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id t = 0 → loc t = 0)
    (hloc : ∀ (g : ↥D ⧸ K.fixingSubgroup.subgroupOf D)
      (t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E)),
      loc (quotSubHom K.fixingSubgroup D g • t) = B'.ρ (e' g) (loc t))
    (hcoef : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E), Φ.hom.hom (φ t) = loc t)
    (hcomm : ∀ g : ↥D ⧸ K.fixingSubgroup.subgroupOf D, ((e' g : ↥H) : Gal(↥K/k))
      = quotientFixingSubgroupEquiv K (quotSubHom K.fixingSubgroup D g))
    {S : Set (Subgroup Gal(Ω/k))} (hDS : D ∈ S)
    {z : SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E)}
    (hz : z ∈ sha1Level E K.fixingSubgroup hop S) :
    tateMap Φ 1 (tateRes H B 1 (Multiplicative.toAdd
      (kummerFiniteH1Equiv hK htriv htrivEK α hEp hfix B φ hφ hop z))) = 0 := by
  haveI : DiscreteTopology (Gal(Ω/k) ⧸ K.fixingSubgroup) := QuotientGroup.discreteTopology hop
  haveI : DiscreteTopology (↥D ⧸ K.fixingSubgroup.subgroupOf D) :=
    QuotientGroup.discreteTopology (isOpen_subgroupOf (N := K.fixingSubgroup) (D := D) hop)
  letI := repPullMulDistribMulAction (e' : (↥D ⧸ K.fixingSubgroup.subgroupOf D) →* ↥H) B'
  letI := repPullDistribMulAction (e' : (↥D ⧸ K.fixingSubgroup.subgroupOf D) →* ↥H) B'
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  refine tateMap_tateRes_eq_zero_of_locCoeffHom_comapH1_eq_one
    (kummerTwistEquiv hK htriv htrivEK α hEp) (kummerTwistEquiv_smul hK htriv htrivEK α hEp hfix)
    (quotientFixingSubgroupEquiv K) B φ hφ e' B' (fun _ _ => rfl) (fun _ _ => rfl)
    (quotSubHom K.fixingSubgroup D) (quotSubHom_smul D) (isSmoothHom_quotSubHom D hop)
    Φ loc hloc hu hs hcoef hcomm ?_
  refine coeffH1_resQuotH1_eq_one_of_mem_sha1Level hK hL j hj hιj hD htriv htrivEK htrivEL α hEp
    _ _ hop hsurj (fun t ht => ?_) hDS hz
  show Multiplicative.ofAdd (loc ((kummerTwistEquiv hK htriv htrivEK α hEp).symm
    ((kummerTwistEquiv hK htriv htrivEK α hEp) t))) = 1
  rw [AddEquiv.symm_apply_apply, hlocker t ht]
  rfl

end Arith

end InverseGalois.CFT
