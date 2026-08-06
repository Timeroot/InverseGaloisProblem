/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.SphereCompletion

/-!
# The tame fundamental group as the automorphism group of the fibre functor

The category of finite `SphereGroup r`-sets, `Action FintypeCat (SphereGroup r)`, is a Galois
category whose fibre functor is the forgetful functor to `FintypeCat` (Mathlib,
`CategoryTheory.Galois.Examples`).  Its fundamental group — the automorphism group `Aut F` of the
fibre functor — is the profinite completion of the sphere group, i.e. `sphereCompletion r`.

This module makes that identification precise: the profinite completion acts on every finite
`SphereGroup r`-set through the universal property, this action makes `sphereCompletion r` a
fundamental group of the fibre functor (`IsFundamentalGroup`), and hence

  `sphereCompletion r ≃* Aut (Action.forget FintypeCat (SphereGroup r))`.

The action of `sphereCompletion r` on a finite set `X.V` is obtained by extending the tautological
action homomorphism `SphereGroup r →* Equiv.Perm X.V` — whose target is finite — along the
profinite completion, and the fundamental-group axioms are verified from density of the image of
`SphereGroup r` together with the connectedness/transitivity dictionary of the Galois category.

## Main definitions / results

* `completionMulAction` — the action of `sphereCompletion r` on a finite `SphereGroup r`-set.
* `sphereIsFundamentalGroup` — `sphereCompletion r` is a fundamental group of the fibre functor.
* `sphereCompletion_mulEquiv_aut` — `sphereCompletion r ≃* Aut F`.
-/

namespace Rigidity.RET

open CategoryTheory PreGaloisCategory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion
open scoped CategoryTheory.PreGaloisCategory

variable {r : ℕ}

/-- The fibre functor of the Galois category of finite `SphereGroup r`-sets. -/
noncomputable abbrev sphereFiber (r : ℕ) : Action FintypeCat (SphereGroup r) ⥤ FintypeCat :=
  Action.forget FintypeCat (SphereGroup r)

/-- The continuous homomorphism `sphereCompletion r → Equiv.Perm X.V` extending the tautological
action of the sphere group on the finite set `X.V`. -/
noncomputable def completionPermHom (X : Action FintypeCat (SphereGroup r)) :
    sphereCompletion r ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm X.V)) :=
  (homEquiv (GrpCat.of (SphereGroup r))
      (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm X.V)))).symm
    (GrpCat.ofHom (MulAction.toPermHom (SphereGroup r) X.V))

/-- The underlying homomorphism `sphereCompletion r →* Equiv.Perm X.V`. -/
noncomputable def completionPerm (X : Action FintypeCat (SphereGroup r)) :
    sphereCompletion r →* Equiv.Perm X.V :=
  (completionPermHom X).hom.toMonoidHom

/-- The action of the profinite completion on a finite `SphereGroup r`-set. -/
noncomputable instance completionMulAction (X : Action FintypeCat (SphereGroup r)) :
    MulAction (sphereCompletion r) ((sphereFiber r).obj X) :=
  MulAction.compHom X.V (completionPerm X)

theorem completion_smul_def (X : Action FintypeCat (SphereGroup r))
    (g : sphereCompletion r) (x : (sphereFiber r).obj X) : g • x = completionPerm X g x := rfl

/-- The discrete topology on the fibre `(sphereFiber r).obj X`, phrased so instance search unifies
against the concrete fibre functor (the general scoped instance keyed on an arbitrary `F.obj X` does
not fire once the fibre reduces to `X.V`). -/
instance fiberTopology (X : Action FintypeCat (SphereGroup r)) :
    TopologicalSpace ((sphereFiber r).obj X) := ⊥

instance fiberDiscrete (X : Action FintypeCat (SphereGroup r)) :
    DiscreteTopology ((sphereFiber r).obj X) := ⟨rfl⟩

instance vTopology (X : Action FintypeCat (SphereGroup r)) :
    TopologicalSpace (X.V : Type _) := ⊥

instance vDiscrete (X : Action FintypeCat (SphereGroup r)) :
    DiscreteTopology (X.V : Type _) := ⟨rfl⟩

/-- The completion unit `SphereGroup r →* sphereCompletion r`. -/
noncomputable def sphereEta : SphereGroup r →* sphereCompletion r :=
  (eta (GrpCat.of (SphereGroup r))).hom

theorem sphereEta_denseRange :
    DenseRange (sphereEta : SphereGroup r → sphereCompletion r) :=
  ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of (SphereGroup r))

/-- The completion action, restricted along the unit, recovers the tautological permutation. -/
theorem completionPerm_eta (X : Action FintypeCat (SphereGroup r)) (g : SphereGroup r) :
    completionPerm X (sphereEta g) = MulAction.toPermHom (SphereGroup r) X.V g := by
  have hrw : (homEquiv (GrpCat.of (SphereGroup r))
        (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm X.V))))
      (completionPermHom X) = GrpCat.ofHom (MulAction.toPermHom (SphereGroup r) X.V) := by
    simp only [completionPermHom, Equiv.apply_symm_apply]
  have happ := sphereCompletionInduced_apply (H := Equiv.Perm X.V) (completionPermHom X) g
  rw [sphereCompletionInduced, completionInduced, hrw] at happ
  simpa [completionPerm, sphereEta] using happ.symm

/-- On the image of the sphere group, the completion action is the tautological permutation. -/
theorem eta_smul (X : Action FintypeCat (SphereGroup r)) (g : SphereGroup r)
    (x : (sphereFiber r).obj X) :
    (sphereEta g) • x = MulAction.toPermHom (SphereGroup r) X.V g x := by
  rw [completion_smul_def, completionPerm_eta]

/-- A morphism of finite `SphereGroup r`-sets is equivariant for the sphere-group action. -/
theorem hom_smul {X Y : Action FintypeCat (SphereGroup r)} (f : X ⟶ Y) (s : SphereGroup r)
    (x : X.V) : f.hom (s • x) = s • f.hom x :=
  DFunLike.congr_fun (f.comm s) x

/-- The action of `sphereCompletion r` on a finite `SphereGroup r`-set is continuous. -/
theorem completion_continuousSMul (X : Action FintypeCat (SphereGroup r)) :
    ContinuousSMul (sphereCompletion r) ((sphereFiber r).obj X) := by
  haveI : DiscreteTopology
      (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm X.V)) : Type) := ⟨rfl⟩
  constructor
  rw [continuous_prod_of_discrete_right]
  intro x
  have hc : Continuous (completionPermHom X).hom := (completionPermHom X).hom.continuous
  have hev : Continuous (fun p : (ProfiniteGrp.ofFiniteGrp
      (FiniteGrp.of (Equiv.Perm X.V)) : Type) => (show Equiv.Perm X.V from p) x) :=
    continuous_of_discreteTopology
  exact hev.comp hc

/-- Evaluating the action at a point is continuous. -/
theorem continuous_smul_pt (X : Action FintypeCat (SphereGroup r)) (x : (sphereFiber r).obj X) :
    Continuous (fun g : sphereCompletion r => g • x) := by
  haveI : DiscreteTopology
      (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm X.V)) : Type) := ⟨rfl⟩
  have hc : Continuous (completionPermHom X).hom := (completionPermHom X).hom.continuous
  have hev : Continuous (fun p : (ProfiniteGrp.ofFiniteGrp
      (FiniteGrp.of (Equiv.Perm X.V)) : Type) => (show Equiv.Perm X.V from p) x) :=
    continuous_of_discreteTopology
  exact hev.comp hc

/-- The action of `sphereCompletion r` is transitive on the fibre of a Galois (connected) object. -/
theorem completion_transitive (X : Action FintypeCat (SphereGroup r)) [IsGalois X] :
    MulAction.IsPretransitive (sphereCompletion r) ((sphereFiber r).obj X) := by
  have hG := FintypeCat.Action.pretransitive_of_isConnected (SphereGroup r) X
  refine ⟨fun x y => ?_⟩
  obtain ⟨s, hs⟩ := hG.exists_smul_eq x y
  exact ⟨sphereEta s, by rw [eta_smul]; exact hs⟩

/-- The completion action is natural in the finite `SphereGroup r`-set. -/
noncomputable instance : IsNaturalSMul (sphereFiber r) (sphereCompletion r) where
  naturality g X Y f x := by
    have hden : DenseRange (sphereEta : SphereGroup r → sphereCompletion r) := sphereEta_denseRange
    have h1 : Continuous (fun a : sphereCompletion r => (sphereFiber r).map f (a • x)) :=
      continuous_of_discreteTopology.comp (continuous_smul_pt X x)
    have h2 : Continuous (fun a : sphereCompletion r => a • (sphereFiber r).map f x) :=
      continuous_smul_pt Y _
    have key : (fun a : sphereCompletion r => (sphereFiber r).map f (a • x)) ∘ sphereEta
             = (fun a : sphereCompletion r => a • (sphereFiber r).map f x) ∘ sphereEta := by
      funext s
      simp only [Function.comp_apply]
      rw [eta_smul, eta_smul]
      exact hom_smul f s x
    exact congrFun (hden.equalizer h1 h2 key) g

/-! ### Separating finite quotients

To see that only the identity of `sphereCompletion r` acts trivially on every finite
`SphereGroup r`-set, we separate points of the profinite completion by its open normal subgroups:
for each such `H`, the finite quotient `sphereCompletion r ⧸ H` is a finite `SphereGroup r`-set on
which the completion acts through the quotient map, and the completion element in question is sent to
the identity coset. -/

section Separating

variable (H : OpenNormalSubgroup (sphereCompletion r))

/-- The finite quotient of the completion by an open normal subgroup. -/
abbrev sepQ := sphereCompletion r ⧸ H.toSubgroup

/-- The quotient homomorphism onto the separating finite quotient. -/
noncomputable def qhom : sphereCompletion r →* sepQ H := QuotientGroup.mk' H.toSubgroup

theorem qhom_continuous : Continuous (qhom H) := continuous_quotient_mk'

/-- The sphere group acts on the separating quotient through the quotient map. -/
noncomputable def sepPsi : SphereGroup r →* sepQ H := (qhom H).comp sphereEta

noncomputable instance sepAction : MulAction (SphereGroup r) (sepQ H) :=
  MulAction.compHom _ (sepPsi H)

noncomputable instance : Fintype (sepQ H) := Fintype.ofFinite _

/-- The separating finite `SphereGroup r`-set attached to an open normal subgroup. -/
noncomputable def sepObj : Action FintypeCat (SphereGroup r) :=
  Action.FintypeCat.ofMulAction (SphereGroup r) (FintypeCat.of (sepQ H))

/-- The base point of the separating object: the identity coset. -/
noncomputable def sepPt : (sphereFiber r).obj (sepObj H) := (1 : sepQ H)

/-- The quotient map is continuous into the (discrete) fibre of the separating object. -/
theorem qhom_continuous_fiber :
    @Continuous _ ((sphereFiber r).obj (sepObj H)) _ (fiberTopology (sepObj H))
      (fun a : sphereCompletion r => (qhom H a : (sphereFiber r).obj (sepObj H))) := by
  have hqc : Continuous (qhom H) := qhom_continuous H
  convert hqc using 2
  show (⊥ : TopologicalSpace (sepQ H)) = _
  exact (DiscreteTopology.eq_bot).symm

/-- The completion action on the separating object, at the identity coset, is the quotient map:
`g • [1] = [g]`.  Both sides are continuous and agree on the dense image of the sphere group. -/
theorem sep_smul_eq (g : sphereCompletion r) :
    g • sepPt H = (qhom H g : (sphereFiber r).obj (sepObj H)) := by
  have hden : DenseRange (sphereEta : SphereGroup r → sphereCompletion r) := sphereEta_denseRange
  have h1 : Continuous (fun a : sphereCompletion r => a • sepPt H) :=
    continuous_smul_pt (sepObj H) (sepPt H)
  have h2 := qhom_continuous_fiber H
  have key : (fun a : sphereCompletion r => a • sepPt H) ∘ sphereEta
           = (fun a : sphereCompletion r => (qhom H a : (sphereFiber r).obj (sepObj H))) ∘ sphereEta := by
    funext s
    simp only [Function.comp_apply]
    rw [eta_smul]
    show sepPsi H s * (1 : sepQ H) = (qhom H (sphereEta s) : (sphereFiber r).obj (sepObj H))
    rw [mul_one]; rfl
  exact congrFun (hden.equalizer h1 h2 key) g

end Separating

/-- `sphereCompletion r` is a fundamental group of the fibre functor of finite
`SphereGroup r`-sets. -/
noncomputable instance sphereIsFundamentalGroup :
    IsFundamentalGroup (sphereFiber r) (sphereCompletion r) where
  transitive_of_isGalois X := completion_transitive X
  continuous_smul X := completion_continuousSMul X
  non_trivial' g h := by
    by_contra hg1
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isOpen_compl_singleton) (Set.mem_compl_singleton_iff.mpr (Ne.symm hg1))
    have hfix := h (sepObj H) (sepPt H)
    rw [sep_smul_eq] at hfix
    have hq : qhom H g = 1 := hfix
    have hmem : g ∈ H.toSubgroup := (QuotientGroup.eq_one_iff g).mp hq
    exact (hH hmem) rfl

/-- **The tame fundamental group of the `r`-punctured line is `sphereCompletion r`.**  The profinite
completion of the sphere group is isomorphic, as a group, to the automorphism group of the fibre
functor of the Galois category of finite `SphereGroup r`-sets. -/
noncomputable def sphereCompletion_mulEquiv_aut :
    sphereCompletion r ≃* Aut (sphereFiber r) :=
  toAutMulEquiv (sphereFiber r) (sphereCompletion r)

/-- The identification `sphereCompletion r ≃* Aut F` is also a homeomorphism: the automorphism group
of the fibre functor is the profinite completion of the sphere group not merely as a group but as a
topological group. -/
noncomputable def sphereCompletion_homeo_aut :
    sphereCompletion r ≃ₜ Aut (sphereFiber r) :=
  toAutHomeo (sphereFiber r) (sphereCompletion r)

theorem sphereCompletion_mulEquiv_aut_isHomeomorph :
    IsHomeomorph (sphereCompletion_mulEquiv_aut : sphereCompletion r → Aut (sphereFiber r)) :=
  toAutMulEquiv_isHomeomorph (sphereFiber r) (sphereCompletion r)

/-- The group isomorphism `sphereCompletion r ≃* Aut F` and the homeomorphism
`sphereCompletion r ≃ₜ Aut F` agree on inverses. -/
theorem mulEquiv_symm_eq_homeo_symm (x : Aut (sphereFiber r)) :
    (sphereCompletion_mulEquiv_aut).symm x = (sphereCompletion_homeo_aut).symm x := by
  apply (sphereCompletion_mulEquiv_aut (r := r)).injective
  rw [MulEquiv.apply_symm_apply]
  show _ = sphereCompletion_mulEquiv_aut (sphereCompletion_homeo_aut.symm x)
  rw [show (sphereCompletion_mulEquiv_aut (sphereCompletion_homeo_aut.symm x))
        = sphereCompletion_homeo_aut (sphereCompletion_homeo_aut.symm x) from rfl,
    Homeomorph.apply_symm_apply]

/-- The inverse identification `Aut F → sphereCompletion r` is continuous. -/
theorem mulEquiv_aut_symm_continuous :
    Continuous (sphereCompletion_mulEquiv_aut.symm : Aut (sphereFiber r) → sphereCompletion r) := by
  have h : Continuous (sphereCompletion_homeo_aut.symm : Aut (sphereFiber r) → sphereCompletion r) :=
    sphereCompletion_homeo_aut.continuous_invFun
  exact h.congr (fun x => (mulEquiv_symm_eq_homeo_symm x).symm)

/-- The fundamental-group identification as a continuous monoid homomorphism
`sphereCompletion r →ₜ* Aut F`. -/
noncomputable def cmhSphereToAut : ContinuousMonoidHom (sphereCompletion r) (Aut (sphereFiber r)) :=
  ⟨sphereCompletion_mulEquiv_aut.toMonoidHom,
    sphereCompletion_mulEquiv_aut_isHomeomorph.continuous⟩

/-- The inverse identification as a continuous monoid homomorphism
`Aut F →ₜ* sphereCompletion r`. -/
noncomputable def cmhAutToSphere : ContinuousMonoidHom (Aut (sphereFiber r)) (sphereCompletion r) :=
  ⟨sphereCompletion_mulEquiv_aut.symm.toMonoidHom, mulEquiv_aut_symm_continuous⟩

theorem cmhSphereToAut_surjective :
    Function.Surjective (cmhSphereToAut : sphereCompletion r → Aut (sphereFiber r)) :=
  sphereCompletion_mulEquiv_aut.surjective

theorem cmhAutToSphere_surjective :
    Function.Surjective (cmhAutToSphere : Aut (sphereFiber r) → sphereCompletion r) :=
  sphereCompletion_mulEquiv_aut.symm.surjective

end Rigidity.RET
