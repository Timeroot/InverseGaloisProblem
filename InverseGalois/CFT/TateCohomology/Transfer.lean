/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Norm

/-!
# The transfer between a finite group and a subgroup

Choosing a representative of every coset of a subgroup writes each element of the group in exactly
one way as a representative times an element of the subgroup, and also in exactly one way as an
element of the subgroup times the inverse of a representative.  Summing the action of the chosen
representatives, or of their inverses, therefore factors the norm of the group through the norm of
the subgroup in two ways: on one side the norm of the group is the transfer of the norm of the
subgroup, and on the other it is the norm of the subgroup of the opposite transfer.

Those two factorisations are what is needed to compare the two middle Tate groups of the group with
those of the subgroup.  In degree zero the restriction is the inclusion of the invariants and the
corestriction is the transfer; in degree minus one the restriction is the opposite transfer and the
corestriction is the natural map of coinvariants.  Composing the two in either of the two middle
degrees replaces a class by the sum of its images under the chosen representatives, and a class
already coming from the whole group is fixed by each of them: the composite is the number of cosets
times the class.

## Main definitions

* `InverseGalois.CFT.Tate.restrictRep`: the restriction of a representation to a subgroup.
* `InverseGalois.CFT.Tate.cosetLeftEquiv`, `InverseGalois.CFT.Tate.cosetRightEquiv`: the two
  decompositions of a group along the cosets of a subgroup.
* `InverseGalois.CFT.Tate.transferLeft`, `InverseGalois.CFT.Tate.transferRight`: the sum of the
  actions of the chosen representatives of the cosets, and of their inverses.
* `InverseGalois.CFT.Tate.res0`, `InverseGalois.CFT.Tate.cor0`,
  `InverseGalois.CFT.Tate.resm1`, `InverseGalois.CFT.Tate.corm1`: the restriction and the
  corestriction in the two middle degrees.

## Main results

* `InverseGalois.CFT.Tate.normMap_eq_transferLeft`,
  `InverseGalois.CFT.Tate.normMap_eq_transferRight`: **the norm of the group factors through the
  norm of the subgroup in two ways.**
* `InverseGalois.CFT.Tate.cor0_res0`, `InverseGalois.CFT.Tate.corm1_resm1`: **the corestriction of
  the restriction is the index of the subgroup**, in either of the two middle degrees.

## Tags

Tate cohomology, transfer, restriction, corestriction, coset, finite group
-/

namespace InverseGalois.CFT.Tate

open Representation

noncomputable section

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-! ### Two decompositions of a group along a subgroup -/

section Cosets

variable (H : Subgroup G)

theorem out_inv_mul_mem (g : G) : ((QuotientGroup.mk g : G ⧸ H).out)⁻¹ * g ∈ H :=
  QuotientGroup.eq.1 (QuotientGroup.out_eq' _)

/-- **A group is the product of the cosets of a subgroup and the subgroup**: an element is the
chosen representative of its coset times an element of the subgroup. -/
def cosetLeftEquiv : (G ⧸ H) × H ≃ G where
  toFun p := p.1.out * (p.2 : G)
  invFun g := (QuotientGroup.mk g, ⟨_, out_inv_mul_mem H g⟩)
  left_inv := by
    rintro ⟨c, h⟩
    have key : (QuotientGroup.mk (c.out * (h : G)) : G ⧸ H) = c :=
      (QuotientGroup.mk_mul_of_mem c.out h.2).trans (QuotientGroup.out_eq' c)
    refine Prod.ext key (Subtype.ext ?_)
    show (QuotientGroup.mk (c.out * (h : G)) : G ⧸ H).out⁻¹ * (c.out * (h : G)) = (h : G)
    rw [key, inv_mul_cancel_left]
  right_inv g := mul_inv_cancel_left _ _

@[simp]
theorem cosetLeftEquiv_apply (p : (G ⧸ H) × H) : cosetLeftEquiv H p = p.1.out * (p.2 : G) := rfl

/-- **A group is the product of the cosets of a subgroup and the subgroup** in a second way: an
element is an element of the subgroup times the inverse of the chosen representative. -/
def cosetRightEquiv : (G ⧸ H) × H ≃ G where
  toFun p := (p.2 : G) * p.1.out⁻¹
  invFun g := (QuotientGroup.mk g⁻¹, ⟨g * (QuotientGroup.mk g⁻¹ : G ⧸ H).out, by
    simpa using H.inv_mem (out_inv_mul_mem H g⁻¹)⟩)
  left_inv := by
    rintro ⟨c, h⟩
    have key : (QuotientGroup.mk ((h : G) * c.out⁻¹)⁻¹ : G ⧸ H) = c := by
      rw [mul_inv_rev, inv_inv]
      exact (QuotientGroup.mk_mul_of_mem c.out (H.inv_mem h.2)).trans (QuotientGroup.out_eq' c)
    refine Prod.ext key (Subtype.ext ?_)
    show (h : G) * c.out⁻¹ * (QuotientGroup.mk ((h : G) * c.out⁻¹)⁻¹ : G ⧸ H).out = (h : G)
    rw [key, inv_mul_cancel_right]
  right_inv g := mul_inv_cancel_right _ _

@[simp]
theorem cosetRightEquiv_apply (p : (G ⧸ H) × H) :
    cosetRightEquiv H p = (p.2 : G) * p.1.out⁻¹ := rfl

end Cosets

/-! ### Restricting a representation to a subgroup -/

section Restrict

variable (H : Subgroup G) (ρ : Representation k G V)

/-- **The restriction of a representation to a subgroup.** -/
def restrictRep : Representation k H V := ρ.comp H.subtype

@[simp]
theorem restrictRep_apply (h : H) : restrictRep H ρ h = ρ (h : G) := rfl

/-- **A vector fixed by the subgroup only sees the coset of the acting element.** -/
theorem apply_eq_apply_of_mk_eq {x : V} (hx : x ∈ (restrictRep H ρ).invariants) {y z : G}
    (h : (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk z) : ρ y x = ρ z x := by
  have hx' : ρ (y⁻¹ * z) x = x := hx ⟨y⁻¹ * z, QuotientGroup.eq.1 h⟩
  calc ρ y x = ρ y (ρ (y⁻¹ * z) x) := by rw [hx']
    _ = ρ z x := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

/-- **In the coinvariants of the subgroup only the right coset of the acting element matters.** -/
theorem mk_apply_eq_mk_apply {y z : G} (hmem : y * z⁻¹ ∈ H) (x : V) :
    Coinvariants.mk (restrictRep H ρ) (ρ y x)
      = Coinvariants.mk (restrictRep H ρ) (ρ z x) := by
  have h : ρ y x = restrictRep H ρ ⟨y * z⁻¹, hmem⟩ (ρ z x) := by
    show ρ y x = ρ (y * z⁻¹) (ρ z x)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  rw [h, Coinvariants.mk_self_apply]

theorem invariants_le_invariants_restrictRep :
    ρ.invariants ≤ (restrictRep H ρ).invariants := fun _ hx h => hx (h : G)

/-- **The restriction of an invariant vector to the subgroup.** -/
def resInvariants : ρ.invariants →ₗ[k] (restrictRep H ρ).invariants :=
  Submodule.inclusion (invariants_le_invariants_restrictRep H ρ)

@[simp]
theorem resInvariants_coe (x : ρ.invariants) : (resInvariants H ρ x : V) = (x : V) := rfl

/-- **The corestriction of a class of coinvariants of the subgroup**: its class for the whole
group. -/
def corCoinvariants : Coinvariants (restrictRep H ρ) →ₗ[k] Coinvariants ρ :=
  Coinvariants.lift (restrictRep H ρ) (Coinvariants.mk ρ) fun h =>
    LinearMap.ext fun x => Coinvariants.mk_self_apply ρ (h : G) x

@[simp]
theorem corCoinvariants_mk (x : V) :
    corCoinvariants H ρ (Coinvariants.mk (restrictRep H ρ) x) = Coinvariants.mk ρ x := rfl

end Restrict

/-! ### The two transfers -/

section Transfer

variable [Finite G] (H : Subgroup G) (ρ : Representation k G V)

/-- **The transfer to a subgroup**: the sum of the actions of the chosen representatives of the
cosets. -/
def transferLeft : V →ₗ[k] V := ∑ᶠ c : G ⧸ H, ρ c.out

/-- **The opposite transfer to a subgroup**: the sum of the actions of the inverses of the chosen
representatives of the cosets. -/
def transferRight : V →ₗ[k] V := ∑ᶠ c : G ⧸ H, ρ c.out⁻¹

omit [Finite G] in
theorem transferLeft_apply [Fintype (G ⧸ H)] (x : V) :
    transferLeft H ρ x = ∑ c : G ⧸ H, ρ c.out x := by
  rw [transferLeft, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

omit [Finite G] in
theorem transferRight_apply [Fintype (G ⧸ H)] (x : V) :
    transferRight H ρ x = ∑ c : G ⧸ H, ρ c.out⁻¹ x := by
  rw [transferRight, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

/-- **The norm of the group is the transfer of the norm of the subgroup.** -/
theorem normMap_eq_transferLeft (x : V) :
    normMap ρ x = transferLeft H ρ (normMap (restrictRep H ρ) x) := by
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite ↥H
  letI := Fintype.ofFinite (G ⧸ H)
  have hsum : ∑ g : G, ρ g x = ∑ c : G ⧸ H, ∑ h : H, ρ (c.out * (h : G)) x := by
    rw [← Fintype.sum_equiv (cosetLeftEquiv H) (fun p => ρ (p.1.out * (p.2 : G)) x)
      (fun g => ρ g x) fun _ => rfl, Fintype.sum_prod_type]
  rw [normMap_apply, hsum, transferLeft_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [normMap_apply, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul, Module.End.mul_apply]
  rfl

/-- **The norm of the group is the norm of the subgroup of the opposite transfer.** -/
theorem normMap_eq_transferRight (x : V) :
    normMap ρ x = normMap (restrictRep H ρ) (transferRight H ρ x) := by
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite ↥H
  letI := Fintype.ofFinite (G ⧸ H)
  have hsum : ∑ g : G, ρ g x = ∑ c : G ⧸ H, ∑ h : H, ρ ((h : G) * c.out⁻¹) x := by
    rw [← Fintype.sum_equiv (cosetRightEquiv H) (fun p => ρ ((p.2 : G) * p.1.out⁻¹) x)
      (fun g => ρ g x) fun _ => rfl, Fintype.sum_prod_type]
  rw [normMap_apply, hsum, Finset.sum_comm, normMap_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [transferRight_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, Module.End.mul_apply]
  rfl

/-- **The transfer of a vector fixed by the subgroup is fixed by the group.** -/
theorem transferLeft_mem_invariants {x : V} (hx : x ∈ (restrictRep H ρ).invariants) :
    transferLeft H ρ x ∈ ρ.invariants := by
  letI := Fintype.ofFinite (G ⧸ H)
  intro g
  rw [transferLeft_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm g : Equiv.Perm (G ⧸ H)) _ _ fun c => ?_
  show ρ g (ρ c.out x) = ρ ((g • c).out) x
  rw [← Module.End.mul_apply, ← map_mul]
  refine apply_eq_apply_of_mk_eq H ρ hx ?_
  rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]

/-- **The transfer of a vector fixed by the group is the number of cosets times the vector.** -/
theorem transferLeft_of_mem_invariants {x : V} (hx : x ∈ ρ.invariants) :
    transferLeft H ρ x = H.index • x := by
  letI := Fintype.ofFinite (G ⧸ H)
  rw [transferLeft_apply, Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.sum_const]
  exact Finset.sum_congr rfl fun c _ => hx c.out

/-- **In the coinvariants the opposite transfer of a class is the number of cosets times the
class.** -/
theorem mk_transferRight (x : V) :
    Coinvariants.mk ρ (transferRight H ρ x) = H.index • Coinvariants.mk ρ x := by
  letI := Fintype.ofFinite (G ⧸ H)
  rw [transferRight_apply, map_sum, Subgroup.index_eq_card, Nat.card_eq_fintype_card,
    ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun c _ => Coinvariants.mk_self_apply ρ _ x

/-- **The opposite transfer descends to the coinvariants of the subgroup.** -/
theorem mk_transferRight_apply (g : G) (x : V) :
    Coinvariants.mk (restrictRep H ρ) (transferRight H ρ (ρ g x))
      = Coinvariants.mk (restrictRep H ρ) (transferRight H ρ x) := by
  letI := Fintype.ofFinite (G ⧸ H)
  rw [transferRight_apply, transferRight_apply, map_sum, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm g⁻¹ : Equiv.Perm (G ⧸ H)) _ _ fun c => ?_
  show Coinvariants.mk (restrictRep H ρ) (ρ c.out⁻¹ (ρ g x))
    = Coinvariants.mk (restrictRep H ρ) (ρ ((g⁻¹ • c).out)⁻¹ x)
  rw [← Module.End.mul_apply, ← map_mul]
  refine mk_apply_eq_mk_apply H ρ ?_ x
  have key : (g⁻¹ * c.out)⁻¹ * (g⁻¹ • c).out ∈ H :=
    QuotientGroup.eq.1 (by rw [QuotientGroup.out_eq', ← smul_eq_mul,
      MulAction.Quotient.mk_smul_out])
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using key

end Transfer

/-! ### The four maps in the two middle degrees -/

section Middle

variable [Finite G] (H : Subgroup G) (ρ : Representation k G V)

/-- **The corestriction of a vector fixed by the subgroup**: its transfer. -/
def corInvariants : (restrictRep H ρ).invariants →ₗ[k] ρ.invariants :=
  ((transferLeft H ρ).domRestrict _).codRestrict ρ.invariants fun c =>
    transferLeft_mem_invariants H ρ c.2

@[simp]
theorem corInvariants_coe (x : (restrictRep H ρ).invariants) :
    (corInvariants H ρ x : V) = transferLeft H ρ (x : V) := rfl

/-- **The restriction of a class of coinvariants to the subgroup**: its opposite transfer. -/
def resCoinvariants : Coinvariants ρ →ₗ[k] Coinvariants (restrictRep H ρ) :=
  Coinvariants.lift ρ (Coinvariants.mk (restrictRep H ρ) ∘ₗ transferRight H ρ) fun g =>
    LinearMap.ext fun x => mk_transferRight_apply H ρ g x

@[simp]
theorem resCoinvariants_mk (x : V) :
    resCoinvariants H ρ (Coinvariants.mk ρ x)
      = Coinvariants.mk (restrictRep H ρ) (transferRight H ρ x) := rfl

/-- **The restriction in degree zero.** -/
def res0 : H0 ρ →ₗ[k] H0 (restrictRep H ρ) :=
  Submodule.mapQ _ _ (resInvariants H ρ) <| by
    rintro _ ⟨c, rfl⟩
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ c
    exact ⟨Coinvariants.mk (restrictRep H ρ) (transferRight H ρ v),
      Subtype.ext (normMap_eq_transferRight H ρ v).symm⟩

@[simp]
theorem res0_H0mk (x : ρ.invariants) :
    res0 H ρ (H0mk ρ x) = H0mk (restrictRep H ρ) (resInvariants H ρ x) := rfl

/-- **The corestriction in degree zero.** -/
def cor0 : H0 (restrictRep H ρ) →ₗ[k] H0 ρ :=
  Submodule.mapQ _ _ (corInvariants H ρ) <| by
    rintro _ ⟨c, rfl⟩
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective (restrictRep H ρ) c
    exact ⟨Coinvariants.mk ρ v, Subtype.ext (normMap_eq_transferLeft H ρ v)⟩

@[simp]
theorem cor0_H0mk (x : (restrictRep H ρ).invariants) :
    cor0 H ρ (H0mk (restrictRep H ρ) x) = H0mk ρ (corInvariants H ρ x) := rfl

/-- **The restriction in degree minus one.** -/
def resm1 : Hm1 ρ →ₗ[k] Hm1 (restrictRep H ρ) :=
  (resCoinvariants H ρ).restrict fun c hc => by
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ c
    rw [LinearMap.mem_ker] at hc ⊢
    rw [resCoinvariants_mk, coinvariantsNorm_eq_zero_iff, ← normMap_eq_transferRight]
    exact (coinvariantsNorm_eq_zero_iff ρ v).1 hc

@[simp]
theorem resm1_coe (x : Hm1 ρ) :
    (resm1 H ρ x : Coinvariants (restrictRep H ρ))
      = resCoinvariants H ρ (x : Coinvariants ρ) := rfl

/-- **The corestriction in degree minus one.** -/
def corm1 : Hm1 (restrictRep H ρ) →ₗ[k] Hm1 ρ :=
  (corCoinvariants H ρ).restrict fun c hc => by
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective (restrictRep H ρ) c
    rw [LinearMap.mem_ker] at hc ⊢
    rw [corCoinvariants_mk, coinvariantsNorm_eq_zero_iff, normMap_eq_transferLeft,
      (coinvariantsNorm_eq_zero_iff (restrictRep H ρ) v).1 hc, map_zero]

@[simp]
theorem corm1_coe (x : Hm1 (restrictRep H ρ)) :
    (corm1 H ρ x : Coinvariants ρ)
      = corCoinvariants H ρ (x : Coinvariants (restrictRep H ρ)) := rfl

/-! ### The composite is the index -/

/-- **The corestriction of the restriction in degree zero is the index of the subgroup.** -/
theorem cor0_res0 (x : H0 ρ) : cor0 H ρ (res0 H ρ x) = H.index • x := by
  obtain ⟨v, rfl⟩ := H0mk_surjective ρ x
  have hv : corInvariants H ρ (resInvariants H ρ v) = H.index • v := by
    refine Subtype.ext ?_
    rw [corInvariants_coe, resInvariants_coe, Submodule.coe_smul_of_tower]
    exact transferLeft_of_mem_invariants H ρ v.2
  rw [res0_H0mk, cor0_H0mk, hv, map_nsmul]

/-- **The corestriction of the restriction in degree minus one is the index of the subgroup.** -/
theorem corm1_resm1 (x : Hm1 ρ) : corm1 H ρ (resm1 H ρ x) = H.index • x := by
  obtain ⟨v, hv, rfl⟩ := exists_Hm1mk ρ x
  refine Subtype.ext ?_
  rw [corm1_coe, resm1_coe, Hm1mk_coe, resCoinvariants_mk, corCoinvariants_mk,
    Submodule.coe_smul_of_tower, Hm1mk_coe]
  exact mk_transferRight H ρ v

end Middle

end

end InverseGalois.CFT.Tate
