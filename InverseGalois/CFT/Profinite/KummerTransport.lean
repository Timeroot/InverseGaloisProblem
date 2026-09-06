/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.H2Transport
import InverseGalois.CFT.Profinite.Coeff
import InverseGalois.CFT.Profinite.Comap
import InverseGalois.CFT.Profinite.KummerFinite
import InverseGalois.CFT.TateCohomology.NakayamaNatural
import InverseGalois.CFT.TateCohomology.RestrictOne

/-!
# The twisted Kummer identification, computed on cocycles

The identification of the smooth first cohomology of a discrete group with values in a group of
units with the first cohomology of a representation of a finite group is assembled from two
transports: one along an identification of the coefficients, one along an isomorphism of the acting
groups.  Both are isomorphisms of abstract groups, and as such say nothing about a cocycle; but
everything one wants to do to a class of the first cohomology — restrict it to a subgroup, push it
along a map of the coefficients — is defined on cocycles.

Both transports are computed.  Each is the map induced by a homomorphism of the acting groups
together with a map of the representations, in the *forward* direction, so a smooth one cocycle
with values in the units has an explicit image: the one cocycle obtained by reading it at the
inverse isomorphism of the groups and carrying its values across the identification of the
coefficients.

With both sides written on cocycles, comparing a class with its localisation is a pointwise
identity.  Restriction to a subgroup reads a cocycle at the elements of the subgroup and a map of
representations applies to its values; on the smooth side, composition with a homomorphism of the
acting groups and with a map of the coefficients does exactly the same.  When the two homomorphisms
of the acting groups agree and the two identifications of the coefficients agree, the two cocycles
agree, and so **a smooth class whose localisation is trivial has vanishing image in the complete
cohomology of the subgroup**.

## Main definitions

* `InverseGalois.CFT.transportUnitsEquiv`: the identification of a group of units with the
  coefficients of a representation, read as a linear isomorphism.
* `InverseGalois.CFT.transportCocycles₁`: the one cocycle of the representation that a smooth one
  cocycle with values in the units becomes.

## Main results

* `InverseGalois.CFT.h1MulEquivOfSmul_symm_ofAdd`,
  `InverseGalois.CFT.smoothH1EquivOfAddEquiv_symm_ofAdd`: the two transports, each computed as the
  map induced by a homomorphism of the acting groups and a map of the representations.
* `InverseGalois.CFT.h1MulEquivOfSmul_smoothH1Mk`: **the class of a smooth one cocycle is the class
  of the transported one cocycle.**
* `InverseGalois.CFT.tateMap_tateRes_eq_zero_of_coeffH1_comapH1_eq_one`: **a smooth class whose
  localisation at a subgroup is trivial has vanishing image in the complete cohomology of that
  subgroup.**

## Tags

Kummer theory, group cohomology, cocycle, Tate cohomology, restriction, localisation
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory groupCohomology Tate

/-! ### The transported cocycle -/

section Generic

variable {Q G : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Group G]
variable {S : Type} [CommGroup S] [MulDistribMulAction Q S]
variable {T : Type} [AddCommGroup T] [DistribMulAction Q T]
variable (κ : T ≃+ Additive S)
  (hκ : ∀ (g : Q) (t : T), κ (g • t) = Additive.ofMul (g • (κ t).toMul))
variable (e : Q ≃* G) (B : Rep ℤ G) (φ : T ≃+ ↥B.V)
  (hφ : ∀ (g : Q) (t : T), φ (g • t) = B.ρ (e g) (φ t))

omit [TopologicalSpace Q] [DiscreteTopology Q] in
/-- The transport of the first cohomology along an isomorphism of the acting groups is the map
induced by that isomorphism together with the identification of the coefficients. -/
theorem h1MulEquivOfSmul_symm_ofAdd (z : ↥(groupCohomology B 1)) :
    (h1MulEquivOfSmul e B φ hφ).symm (Multiplicative.ofAdd z)
      = Multiplicative.ofAdd (groupCohomology.map (e : Q →* G)
          (repIsoOfEquivSmul e B φ hφ).hom 1 z) := rfl

/-- The transport of the smooth first cohomology along an identification of the coefficients is the
map induced by that identification. -/
theorem smoothH1EquivOfAddEquiv_symm_ofAdd
    (z : ↥(groupCohomology (Rep.ofDistribMulAction ℤ Q T) 1)) :
    (smoothH1EquivOfAddEquiv Q S T κ hκ).symm (Multiplicative.ofAdd z)
      = (discreteSmoothH1Equiv Q S).symm (Multiplicative.ofAdd
          (groupCohomology.map (MonoidHom.id Q) (repIsoOfAddEquiv Q S T κ hκ).hom 1 z)) := rfl

/-- **A smooth one cocycle and a one cocycle of the representation whose values correspond under
the identification of the coefficients have the same class** under the twisted Kummer
identification. -/
theorem h1MulEquivOfSmul_smoothH1Mk_eq (b : groupCohomology.cocycles₁ B) {u : Q → S}
    (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u)
    (hub : ∀ q : Q, Additive.ofMul (u q) = κ (φ.symm (b (e q)))) :
    h1MulEquivOfSmul e B φ hφ (smoothH1EquivOfAddEquiv Q S T κ hκ (smoothH1Mk u hu hs))
      = Multiplicative.ofAdd (groupCohomology.H1π B b) := by
  rw [← MulEquiv.eq_symm_apply, ← MulEquiv.eq_symm_apply, h1MulEquivOfSmul_symm_ofAdd,
    smoothH1EquivOfAddEquiv_symm_ofAdd, MulEquiv.eq_symm_apply,
    groupCohomology.H1π_comp_map_apply, groupCohomology.H1π_comp_map_apply]
  show Multiplicative.ofAdd (H1π (Rep.ofMulDistribMulAction Q S) (cocyclesOfIsMulCocycle₁ hu)) = _
  exact congrArg (fun c => Multiplicative.ofAdd (H1π (Rep.ofMulDistribMulAction Q S) c))
    (Subtype.ext (funext fun q => hub q))

/-- **The identification of a group of units with the coefficients of a representation, read as a
linear isomorphism** of the representation the units carry with that representation. -/
noncomputable def transportUnitsEquiv : Rep.ofMulDistribMulAction Q S ≃ₗ[ℤ] B :=
  (κ.symm.trans φ).toIntLinearEquiv

omit [TopologicalSpace Q] [DiscreteTopology Q] in
include hκ hφ in
/-- The identification of the units with the coefficients intertwines the two actions along the
isomorphism of the acting groups. -/
theorem transportUnitsEquiv_intertwine (g : Q) (a : Rep.ofMulDistribMulAction Q S) :
    transportUnitsEquiv κ B φ ((Rep.ofMulDistribMulAction Q S).ρ g a)
      = B.ρ (e g) (transportUnitsEquiv κ B φ a) := by
  show φ (κ.symm (Additive.ofMul (g • (@Additive.toMul S (@id (Additive S) a)))))
    = B.ρ (e g) (φ (κ.symm (@id (Additive S) a)))
  have h1 : Additive.ofMul (g • (@Additive.toMul S (@id (Additive S) a)))
      = κ (g • κ.symm (@id (Additive S) a)) := by
    rw [hκ, κ.apply_symm_apply]
  rw [h1, κ.symm_apply_apply, hφ]

/-- **The one cocycle of the representation that a smooth one cocycle with values in the units
becomes**: it is read at the inverse isomorphism of the acting groups, and its values are carried
across the identification of the coefficients. -/
noncomputable def transportCocycles₁ {u : Q → S} (hu : IsMulCocycle₁ u) :
    groupCohomology.cocycles₁ B :=
  mapCocycles₁ (e.symm : G →* Q)
    (transportRepHom e (transportUnitsEquiv κ B φ) (transportUnitsEquiv_intertwine κ hκ e B φ hφ))
    (cocyclesOfIsMulCocycle₁ hu)

omit [TopologicalSpace Q] [DiscreteTopology Q] in
/-- The transported one cocycle is computed pointwise. -/
theorem transportCocycles₁_apply {u : Q → S} (hu : IsMulCocycle₁ u) (g : G) :
    transportCocycles₁ κ hκ e B φ hφ hu g = φ (κ.symm (Additive.ofMul (u (e.symm g)))) := rfl

/-- **The class of a smooth one cocycle under the twisted Kummer identification is the class of the
transported one cocycle.** -/
theorem h1MulEquivOfSmul_smoothH1Mk {u : Q → S} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    h1MulEquivOfSmul e B φ hφ (smoothH1EquivOfAddEquiv Q S T κ hκ (smoothH1Mk u hu hs))
      = Multiplicative.ofAdd (groupCohomology.H1π B (transportCocycles₁ κ hκ e B φ hφ hu)) :=
  h1MulEquivOfSmul_smoothH1Mk_eq κ hκ e B φ hφ _ hu hs fun q => by
    rw [transportCocycles₁_apply, φ.symm_apply_apply, κ.apply_symm_apply, e.symm_apply_apply]

end Generic

/-! ### A class trivial at a subgroup -/

section Square

variable {Q G : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Group G] [Finite G]
variable {S : Type} [CommGroup S] [MulDistribMulAction Q S]
variable {T : Type} [AddCommGroup T] [DistribMulAction Q T]
variable (κ : T ≃+ Additive S)
  (hκ : ∀ (g : Q) (t : T), κ (g • t) = Additive.ofMul (g • (κ t).toMul))
variable (e : Q ≃* G) (B : Rep ℤ G) (φ : T ≃+ ↥B.V)
  (hφ : ∀ (g : Q) (t : T), φ (g • t) = B.ρ (e g) (φ t))
variable {Q' : Type} [Group Q'] [TopologicalSpace Q'] [DiscreteTopology Q']
variable {S' : Type} [CommGroup S'] [MulDistribMulAction Q' S'] [MulDistribMulAction Q' S]
variable {T' : Type} [AddCommGroup T'] [DistribMulAction Q' T']
variable (κ' : T' ≃+ Additive S')
  (hκ' : ∀ (g : Q') (t : T'), κ' (g • t) = Additive.ofMul (g • (κ' t).toMul))
variable {H : Subgroup G} (e' : Q' ≃* ↥H) (B' : Rep ℤ ↥H) (φ' : T' ≃+ ↥B'.V)
  (hφ' : ∀ (g : Q') (t : T'), φ' (g • t) = B'.ρ (e' g) (φ' t))
variable (π : Q' →* Q) (hπ : ∀ (g : Q') (s : S), g • s = π g • s) (hsm : IsSmoothHom π)
variable (ψ : S →* S') (hψ : ∀ (g : Q') (s : S), ψ (g • s) = g • ψ s)
variable (Φ : resObj H B ⟶ B')
variable (hcomm : ∀ g : Q', ((e' g : ↥H) : G) = e (π g))
variable (hcoef : ∀ t : T,
  Φ.hom.hom (φ t) = φ' (κ'.symm (Additive.ofMul (ψ (Additive.toMul (κ t))))))

include κ' hκ' e' φ' hφ' hcomm hcoef in
/-- **A smooth class whose localisation at a subgroup is trivial has vanishing image in the complete
cohomology of that subgroup.**  Both sides are computed on cocycles: the image of the class is the
transported cocycle read at the elements of the subgroup and pushed along the map of
representations, while the localisation is the cocycle composed with the homomorphism of the acting
groups and with the map of the coefficients.  The two homomorphisms of the acting groups agree and
the two identifications of the coefficients agree, so the two cocycles are equal, and one of them
has trivial class. -/
theorem tateMap_tateRes_eq_zero_of_coeffH1_comapH1_eq_one {u : Q → S} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u)
    (hx : coeffH1 ψ hψ (comapH1 π hπ hsm (smoothH1Mk u hu hs)) = 1) :
    tateMap Φ 1 (tateRes H B 1 (Multiplicative.toAdd
      (h1MulEquivOfSmul e B φ hφ
        (smoothH1EquivOfAddEquiv Q S T κ hκ (smoothH1Mk u hu hs))))) = 0 := by
  rw [h1MulEquivOfSmul_smoothH1Mk κ hκ e B φ hφ hu hs]
  show tateMap Φ 1 (tateRes H B 1 (H1π B (transportCocycles₁ κ hκ e B φ hφ hu))) = 0
  rw [tateRes_one_H1π, tateMap_one_H1π]
  rw [comapH1_smoothH1Mk, coeffH1_smoothH1Mk] at hx
  have hloc := h1MulEquivOfSmul_smoothH1Mk κ' hκ' e' B' φ' hφ'
    (isMulCocycle₁_coeffMap₁ ψ hψ (isMulCocycle₁_comap₁ π hπ hu))
    ((hsm.isSmooth₁ hs).coeffMap₁ ψ)
  rw [hx, _root_.map_one, _root_.map_one] at hloc
  have hb : homCocycles₁ Φ (resCocycles₁ H B (transportCocycles₁ κ hκ e B φ hφ hu))
      = transportCocycles₁ κ' hκ' e' B' φ' hφ'
        (isMulCocycle₁_coeffMap₁ ψ hψ (isMulCocycle₁_comap₁ π hπ hu)) := by
    refine Subtype.ext (funext fun h => ?_)
    show Φ.hom.hom (φ (κ.symm (Additive.ofMul (u (e.symm (h : G))))))
      = φ' (κ'.symm (Additive.ofMul (ψ (u (π (e'.symm h))))))
    have hh : e.symm (h : G) = π (e'.symm h) := by
      rw [MulEquiv.symm_apply_eq, ← hcomm (e'.symm h), e'.apply_symm_apply]
    rw [hh, hcoef, κ.apply_symm_apply]
    rfl
  rw [hb]
  have hz : (1 : Multiplicative ↥(H1 B')) = Multiplicative.ofAdd (0 : ↥(H1 B')) := rfl
  rw [hz] at hloc
  exact (Multiplicative.ofAdd.injective hloc).symm

end Square

end InverseGalois.CFT
