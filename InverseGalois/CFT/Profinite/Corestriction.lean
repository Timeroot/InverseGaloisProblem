/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Res

/-!
# Corestriction from a subgroup of finite index

Restriction takes a cochain on a topological group and reads it only on a subgroup.  Going the other
way is the trace: choose one element in each coset of the subgroup, and average a cochain of the
subgroup over the cosets, carrying each term back to the whole group by the chosen element.  Here
the cosets are the left cosets, the choice is a section of the projection onto them, and the
average is a product because the coefficients are written multiplicatively.

The whole construction turns on one element.  For a group element and a coset, the chosen
representative of the translated coset, inverted and multiplied by the element and by the
representative of the coset, lies in the subgroup; this is the element by which the group element
moves one representative to the next.  It obeys a cocycle rule of its own along a product of two
group elements, and that rule is exactly what makes the average of a cocycle a cocycle again.  The
same rule makes the average of a coboundary a coboundary, of the product of the chosen
representatives applied to the same coefficient, so the average descends to cohomology.

Smoothness needs a little care.  A cochain of the subgroup is constant on the cosets of a subgroup
open and normal in the subgroup, and the average is constant on the cosets of a subgroup open and
normal in the whole group provided one can be found inside the first and inside the subgroup.  That
is a genuine condition, recorded here as a property of the subgroup; it holds whenever the subgroup
is open in a compact group, the normal core of an open subgroup of finite index being open again.

The point of the construction is the composite.  Corestriction after restriction raises a class to
the index of the subgroup: the average of a restricted cocycle differs from the cocycle raised to
the number of cosets by the coboundary of the product of its values on the chosen representatives.
That is the standard device for killing the part of a cohomology class prime to the index, and for
reducing a question about a group to the same question about a subgroup.

## Main results

* `InverseGalois.CFT.transversalElt`: the element of the subgroup by which a group element carries
  one chosen representative to the next.
* `InverseGalois.CFT.transversalElt_mul`: **the cocycle rule for that element along a product.**
* `InverseGalois.CFT.corCochain₁`: the average of a one cochain of the subgroup over the cosets.
* `InverseGalois.CFT.isMulCocycle₁_corCochain₁`: **the average of a cocycle is a cocycle.**
* `InverseGalois.CFT.corCochain₁_coboundary`: the average of a coboundary is a coboundary.
* `InverseGalois.CFT.isSmooth₁_corCochain₁`: the average of a cochain constant on the cosets of a
  subgroup open and normal in the whole group is constant on the cosets of that same subgroup.
* `InverseGalois.CFT.HasOpenNormalCore`: the property that every open normal subgroup of the
  subgroup contains one that is open and normal in the whole group.
* `InverseGalois.CFT.hasOpenNormalCore_of_isOpen`: **an open subgroup of a compact group has that
  property.**
* `InverseGalois.CFT.corH1`: **corestriction in the first cohomology.**
* `InverseGalois.CFT.corH1_resH1`: **corestriction after restriction raises a class to the index of
  the subgroup.**
* `InverseGalois.CFT.corCochain₂`: the average of a two cochain of the subgroup over the cosets.
* `InverseGalois.CFT.isMulCocycle₂_corCochain₂`: **the average of a two cocycle is a two cocycle.**
* `InverseGalois.CFT.corCochain₂_coboundary₂`: the average of a coboundary is the coboundary of the
  average.
* `InverseGalois.CFT.isSmooth₂_corCochain₂_of_isSmooth₂`: the average of a smooth two cochain is
  smooth.
* `InverseGalois.CFT.corH2`: **corestriction in the second cohomology.**
* `InverseGalois.CFT.corAux₁`: the one cochain correcting the average of a restricted two cocycle.
* `InverseGalois.CFT.corCochain₂_comap₂`: the average of a restricted two cocycle is the cocycle
  raised to the number of cosets, times the coboundary of that correcting cochain.
* `InverseGalois.CFT.corH2_resH2`: **corestriction after restriction raises a class of the second
  cohomology to the index of the subgroup.**

## Tags

group cohomology, profinite group, corestriction, transfer, transversal, coset
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### The transversal element -/

section Transversal

variable {G : Type*} [Group G] (H : Subgroup G) (σ : G ⧸ H → G)
  (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x)

include hσ

/-- A group element carries the chosen representative of a coset into the coset of the chosen
representative of the translated coset, so the discrepancy lies in the subgroup. -/
theorem transversalMem (g : G) (x : G ⧸ H) : (σ (g • x))⁻¹ * g * σ x ∈ H := by
  have h2 : ((g * σ x : G) : G ⧸ H) = g • x := by
    conv_rhs => rw [← hσ x]
    rfl
  rw [mul_assoc]
  exact QuotientGroup.eq.1 ((hσ (g • x)).trans h2.symm)

/-- **The element of the subgroup by which a group element carries the chosen representative of a
coset to the chosen representative of the translated coset.** -/
def transversalElt (g : G) (x : G ⧸ H) : ↥H :=
  ⟨(σ (g • x))⁻¹ * g * σ x, transversalMem H σ hσ g x⟩

/-- The transversal element, read in the whole group. -/
theorem coe_transversalElt (g : G) (x : G ⧸ H) :
    (transversalElt H σ hσ g x : G) = (σ (g • x))⁻¹ * g * σ x := rfl

/-- The chosen representative of the translated coset, corrected by the transversal element, is the
group element applied to the chosen representative of the coset. -/
theorem mul_coe_transversalElt (g : G) (x : G ⧸ H) :
    σ (g • x) * (transversalElt H σ hσ g x : G) = g * σ x := by
  rw [coe_transversalElt, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

/-- **The transversal element of a product is the product of the transversal elements**, the first
one read at the coset already translated by the second factor. -/
theorem transversalElt_mul (g₁ g₂ : G) (x : G ⧸ H) :
    transversalElt H σ hσ (g₁ * g₂) x
      = transversalElt H σ hσ g₁ (g₂ • x) * transversalElt H σ hσ g₂ x := by
  ext
  simp only [coe_transversalElt, Subgroup.coe_mul, mul_smul]
  group

/-- Multiplying a group element on the right by a member of a normal subgroup contained in the
subgroup leaves the cosets alone and changes the transversal element by a conjugate of that
member. -/
theorem transversalElt_mul_right {N : Subgroup G} (hN : N.Normal) (hNH : N ≤ H) (g : G) {n : G}
    (hn : n ∈ N) (x : G ⧸ H) :
    (g * n) • x = g • x ∧ transversalElt H σ hσ (g * n) x
      = transversalElt H σ hσ g x * ⟨(σ x)⁻¹ * n * σ x, hNH (hN.conj_mem' n hn (σ x))⟩ := by
  have hx : (g * n) • x = g • x := by
    conv_lhs => rw [← hσ x]
    conv_rhs => rw [← hσ x]
    show ((g * n * σ x : G) : G ⧸ H) = ((g * σ x : G) : G ⧸ H)
    refine QuotientGroup.eq.2 ?_
    have : (g * n * σ x)⁻¹ * (g * σ x) = (σ x)⁻¹ * n⁻¹ * σ x := by group
    rw [this]
    exact hNH (hN.conj_mem' n⁻¹ (N.inv_mem hn) (σ x))
  refine ⟨hx, ?_⟩
  ext
  simp only [coe_transversalElt, Subgroup.coe_mul, hx]
  group

end Transversal

/-! ### The average of a cochain over the cosets -/

section Corestriction

variable {G : Type*} [Group G] (H : Subgroup G) (σ : G ⧸ H → G)
  (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x)
  {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- The subgroup acts on the coefficients the way the whole group does. -/
theorem subgroupSmul_eq (h : ↥H) (m : M) : h • m = (h : G) • m := rfl

include hσ

/-- **The corestriction of a one cochain of the subgroup**: the product over the cosets of its
values at the transversal elements, each carried back by the chosen representative. -/
def corCochain₁ [Fintype (G ⧸ H)] (u : ↥H → M) : G → M :=
  fun g => ∏ x : G ⧸ H, σ (g • x) • u (transversalElt H σ hσ g x)

/-- The corestriction of a one cochain, read at a group element. -/
theorem corCochain₁_apply [Fintype (G ⧸ H)] (u : ↥H → M) (g : G) :
    corCochain₁ H σ hσ u g = ∏ x : G ⧸ H, σ (g • x) • u (transversalElt H σ hσ g x) := rfl

/-- **The corestriction of a one cocycle is a one cocycle**, by the cocycle rule for the transversal
elements together with a change of the index of the product by a translation of the cosets. -/
theorem isMulCocycle₁_corCochain₁ [Fintype (G ⧸ H)] {u : ↥H → M} (hu : IsMulCocycle₁ u) :
    IsMulCocycle₁ (corCochain₁ H σ hσ u) := by
  intro g₁ g₂
  have hre : ∏ x : G ⧸ H, σ (g₁ • x) • u (transversalElt H σ hσ g₁ x)
      = ∏ x : G ⧸ H, σ (g₁ • (g₂ • x)) • u (transversalElt H σ hσ g₁ (g₂ • x)) :=
    (Fintype.prod_equiv (MulAction.toPerm g₂) _ _ fun _ => rfl).symm
  simp only [corCochain₁_apply]
  rw [hre, Finset.smul_prod', ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [mul_smul g₁ g₂ x, transversalElt_mul H σ hσ, hu, smul_mul']
  congr 1
  rw [subgroupSmul_eq, smul_smul, mul_coe_transversalElt, mul_smul]

/-- Corestriction is multiplicative in the cochain. -/
theorem corCochain₁_mul [Fintype (G ⧸ H)] (u v : ↥H → M) :
    corCochain₁ H σ hσ (u * v) = corCochain₁ H σ hσ u * corCochain₁ H σ hσ v := by
  funext g
  simp only [corCochain₁_apply, Pi.mul_apply, smul_mul']
  exact Finset.prod_mul_distrib

/-- **The corestriction of a coboundary is a coboundary**, of the product of the chosen
representatives applied to the same coefficient. -/
theorem corCochain₁_coboundary [Fintype (G ⧸ H)] (t : M) :
    corCochain₁ H σ hσ (fun h : ↥H => h • t / t)
      = fun g : G => g • (∏ x : G ⧸ H, σ x • t) / ∏ x : G ⧸ H, σ x • t := by
  funext g
  have hre : ∏ x : G ⧸ H, σ (g • x) • t = ∏ x : G ⧸ H, σ x • t :=
    Fintype.prod_equiv (MulAction.toPerm g) _ _ fun _ => rfl
  simp only [corCochain₁_apply, smul_div', Finset.prod_div_distrib, Finset.smul_prod', hre]
  congr 1
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [subgroupSmul_eq, smul_smul, mul_coe_transversalElt, mul_smul]

section Smooth

variable [TopologicalSpace G]

/-- **A cochain constant on the cosets of a subgroup open and normal in the whole group and
contained in the subgroup has a corestriction constant on the cosets of that same subgroup.** -/
theorem isSmooth₁_corCochain₁ [Fintype (G ⧸ H)] {N : Subgroup G} (hN : IsOpenNormal N)
    (hNH : N ≤ H) {u : ↥H → M} (hu : ∀ y n : ↥H, (n : G) ∈ N → u (y * n) = u y) :
    IsSmooth₁ (corCochain₁ H σ hσ u) := by
  refine ⟨N, hN, fun g n hn => ?_⟩
  simp only [corCochain₁_apply]
  refine Finset.prod_congr rfl fun x _ => ?_
  obtain ⟨hx, ht⟩ := transversalElt_mul_right H σ hσ hN.normal hNH g hn x
  rw [hx, ht, hu]
  exact hN.normal.conj_mem' n hn (σ x)

/-- A subgroup *has an open normal core* when every subgroup open and normal in it contains one that
is open and normal in the whole group.  This is what carries smoothness of a cochain of the subgroup
over to smoothness of its corestriction. -/
def HasOpenNormalCore : Prop :=
  ∀ N' : Subgroup ↥H, IsOpenNormal N' → ∃ N : Subgroup G, IsOpenNormal N ∧ N ≤ H ∧
    ∀ n : ↥H, (n : G) ∈ N → n ∈ N'

/-- **The corestriction of a smooth one cochain is smooth**, for a subgroup with an open normal
core. -/
theorem isSmooth₁_corCochain₁_of_isSmooth₁ [Fintype (G ⧸ H)] (hcore : HasOpenNormalCore H)
    {u : ↥H → M} (hu : IsSmooth₁ u) : IsSmooth₁ (corCochain₁ H σ hσ u) := by
  obtain ⟨N', hN', h⟩ := hu
  obtain ⟨N, hN, hNH, hmem⟩ := hcore N' hN'
  exact isSmooth₁_corCochain₁ H σ hσ hN hNH fun y n hn => h y n (hmem n hn)

end Smooth

end Corestriction

/-! ### Corestriction in cohomology -/

section Descent

variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) (σ : G ⧸ H → G)
  (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x)
  {M : Type*} [CommGroup M] [MulDistribMulAction G M] [Fintype (G ⧸ H)]

include hσ

/-- Corestriction on smooth one cocycles. -/
def corCocycle₁ (hcore : HasOpenNormalCore H) :
    smoothCocycle₁ ↥H M →* smoothCocycle₁ G M where
  toFun u := ⟨corCochain₁ H σ hσ u.1, isMulCocycle₁_corCochain₁ H σ hσ u.2.1,
    isSmooth₁_corCochain₁_of_isSmooth₁ H σ hσ hcore u.2.2⟩
  map_one' := by
    refine Subtype.ext (funext fun g => ?_)
    show ∏ x : G ⧸ H, σ (g • x) • (1 : M) = 1
    simp
  map_mul' u v := Subtype.ext (corCochain₁_mul H σ hσ u.1 v.1)

/-- **Corestriction in the first cohomology**, from a subgroup of finite index with an open normal
core. -/
def corH1 (hcore : HasOpenNormalCore H) : SmoothH1 ↥H M →* SmoothH1 G M :=
  QuotientGroup.map _ _ (corCocycle₁ H σ hσ hcore) <| by
    rintro ⟨u, hu, hus⟩ ⟨t, ht⟩
    refine Subgroup.mem_comap.2 ⟨∏ x : G ⧸ H, σ x • t, ?_⟩
    show (fun g : G => g • (∏ x : G ⧸ H, σ x • t) / ∏ x : G ⧸ H, σ x • t)
      = corCochain₁ H σ hσ u
    have ht' : (fun h : ↥H => h • t / t) = u := ht
    rw [← ht']
    exact (corCochain₁_coboundary H σ hσ t).symm

/-- **Corestriction in cohomology is computed on cocycles.** -/
theorem corH1_smoothH1Mk (hcore : HasOpenNormalCore H) {u : ↥H → M} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u) :
    corH1 H σ hσ hcore (smoothH1Mk u hu hs)
      = smoothH1Mk (corCochain₁ H σ hσ u) (isMulCocycle₁_corCochain₁ H σ hσ hu)
        (isSmooth₁_corCochain₁_of_isSmooth₁ H σ hσ hcore hs) := rfl

omit [TopologicalSpace G] in
/-- **The corestriction of a restricted cocycle is the cocycle raised to the number of cosets, times
the coboundary of the product of its values at the chosen representatives.** -/
theorem corCochain₁_comap₁ {u : G → M} (hu : IsMulCocycle₁ u) :
    corCochain₁ H σ hσ (comap₁ H.subtype u)
      = u ^ Fintype.card (G ⧸ H)
        * fun g : G => g • (∏ x : G ⧸ H, u (σ x)) / ∏ x : G ⧸ H, u (σ x) := by
  have hone : u 1 = 1 := by
    have h := hu 1 1
    rw [mul_one, one_smul] at h
    exact mul_eq_left.1 h.symm
  have hinv : ∀ s : G, s • u s⁻¹ = (u s)⁻¹ := by
    intro s
    have h := hu s s⁻¹
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  funext g
  have hterm : ∀ x : G ⧸ H,
      σ (g • x) • comap₁ H.subtype u (transversalElt H σ hσ g x)
        = g • u (σ x) * u g * (u (σ (g • x)))⁻¹ := by
    intro x
    rw [comap₁_apply]
    show σ (g • x) • u ((σ (g • x))⁻¹ * g * σ x) = _
    rw [mul_assoc, hu ((σ (g • x))⁻¹) (g * σ x), smul_mul', smul_smul, mul_inv_cancel, one_smul,
      hu g (σ x), hinv]
  have hre : ∏ x : G ⧸ H, (u (σ (g • x)))⁻¹ = (∏ x : G ⧸ H, u (σ x))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Fintype.prod_equiv (MulAction.toPerm g) _ _ fun _ => rfl
  rw [corCochain₁_apply, Finset.prod_congr rfl fun x (_ : x ∈ Finset.univ) => hterm x,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, hre, Finset.prod_const, ← Finset.smul_prod',
    Finset.card_univ]
  show _ = u g ^ Fintype.card (G ⧸ H) * (g • (∏ x : G ⧸ H, u (σ x)) / ∏ x : G ⧸ H, u (σ x))
  rw [div_eq_mul_inv]
  simp only [mul_comm, mul_assoc]

/-- **Corestriction after restriction raises a class of the first cohomology to the number of cosets
of the subgroup.** -/
theorem corH1_resH1 (hcore : HasOpenNormalCore H) (c : SmoothH1 G M) :
    corH1 H σ hσ hcore (resH1 H c) = c ^ Fintype.card (G ⧸ H) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective c
  rw [resH1_smoothH1Mk, corH1_smoothH1Mk]
  have hmk : (smoothH1Mk u hu hs) ^ Fintype.card (G ⧸ H)
      = QuotientGroup.mk ((⟨u, hu, hs⟩ : smoothCocycle₁ G M) ^ Fintype.card (G ⧸ H)) :=
    (map_pow (QuotientGroup.mk' ((smoothCoboundary₁ G M).subgroupOf (smoothCocycle₁ G M)))
      ⟨u, hu, hs⟩ _).symm
  rw [hmk]
  refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
  refine ⟨(∏ x : G ⧸ H, u (σ x))⁻¹, ?_⟩
  have hcoe : ((⟨u, hu, hs⟩ : smoothCocycle₁ G M) ^ Fintype.card (G ⧸ H) : G → M)
      = u ^ Fintype.card (G ⧸ H) := by
    simp
  show (fun g : G => g • (∏ x : G ⧸ H, u (σ x))⁻¹ / (∏ x : G ⧸ H, u (σ x))⁻¹)
    = (corCochain₁ H σ hσ (comap₁ H.subtype u))⁻¹
      * ((⟨u, hu, hs⟩ : smoothCocycle₁ G M) ^ Fintype.card (G ⧸ H) : G → M)
  rw [hcoe, corCochain₁_comap₁ H σ hσ hu]
  funext g
  show g • (∏ x : G ⧸ H, u (σ x))⁻¹ / (∏ x : G ⧸ H, u (σ x))⁻¹
    = (u g ^ Fintype.card (G ⧸ H)
        * (g • (∏ x : G ⧸ H, u (σ x)) / ∏ x : G ⧸ H, u (σ x)))⁻¹ * u g ^ Fintype.card (G ⧸ H)
  rw [smul_inv']
  have hgen : ∀ a b c : M, a⁻¹ / b⁻¹ = (c * (a / b))⁻¹ * c := by
    intro a b c
    rw [inv_div_inv, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, inv_div]
  exact hgen _ _ _

end Descent

/-! ### Open subgroups of a compact group -/

section Compact

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (H : Subgroup G)

/-- **An open subgroup of a compact group has an open normal core**: an open normal subgroup of it
is open in the whole group, its normal core is closed and of finite index, hence open, and it lies
inside the subgroup one started from. -/
theorem hasOpenNormalCore_of_isOpen (hH : IsOpen (H : Set G)) : HasOpenNormalCore H := by
  intro N' hN'
  have hKopen : IsOpen ((N'.map H.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hN'.isOpen
  haveI : Finite (G ⧸ (N'.map H.subtype : Subgroup G)) :=
    Subgroup.quotient_finite_of_isOpen _ hKopen
  haveI : (N'.map H.subtype : Subgroup G).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have hle : (N'.map H.subtype : Subgroup G) ≤ H := by
    rintro g hg
    obtain ⟨m, _, rfl⟩ := Subgroup.mem_map.1 hg
    exact m.2
  refine ⟨(N'.map H.subtype).normalCore, ⟨Subgroup.normalCore_normal _, ?_⟩,
    le_trans (Subgroup.normalCore_le _) hle, ?_⟩
  · exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
      ((N'.map H.subtype).normalCore_isClosed
        (⟨N'.map H.subtype, hKopen⟩ : OpenSubgroup G).isClosed)
  · intro n hn
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.1 (Subgroup.normalCore_le _ hn)
    rwa [show m = n from Subtype.ext hmn] at hm

end Compact


/-! ### The average of a two cochain over the cosets -/

section Two

variable {G : Type*} [Group G] (H : Subgroup G) (σ : G ⧸ H → G)
  (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x)
  {M : Type*} [CommGroup M] [MulDistribMulAction G M]

include hσ

/-- Multiplying a group element on the right by a member of a normal subgroup contained in the
subgroup leaves the cosets alone. -/
theorem smul_mul_right_of_mem {N : Subgroup G} (hN : N.Normal) (hNH : N ≤ H) (g : G) {n : G}
    (hn : n ∈ N) (x : G ⧸ H) : (g * n) • x = g • x :=
  (transversalElt_mul_right H σ hσ hN hNH g hn x).1

/-- **The corestriction of a two cochain of the subgroup**: the product over the cosets of its
values at the pairs of transversal elements, each carried back by the chosen representative. -/
def corCochain₂ [Fintype (G ⧸ H)] (a : ↥H × ↥H → M) : G × G → M :=
  fun p => ∏ x : G ⧸ H, σ ((p.1 * p.2) • x) •
    a (transversalElt H σ hσ p.1 (p.2 • x), transversalElt H σ hσ p.2 x)

/-- The corestriction of a two cochain, read at a pair of group elements. -/
theorem corCochain₂_apply [Fintype (G ⧸ H)] (a : ↥H × ↥H → M) (g₁ g₂ : G) :
    corCochain₂ H σ hσ a (g₁, g₂) = ∏ x : G ⧸ H, σ ((g₁ * g₂) • x) •
      a (transversalElt H σ hσ g₁ (g₂ • x), transversalElt H σ hσ g₂ x) := rfl

/-- **The corestriction of a two cocycle is a two cocycle.**  Written over the cosets translated so
that every term is carried back by the same representative, the four products in the cocycle
relation match term by term, and what is left at each coset is the cocycle relation for the three
transversal elements. -/
theorem isMulCocycle₂_corCochain₂ [Fintype (G ⧸ H)] {a : ↥H × ↥H → M} (ha : IsMulCocycle₂ a) :
    IsMulCocycle₂ (corCochain₂ H σ hσ a) := by
  intro g h j
  have e1 : corCochain₂ H σ hσ a (g * h, j)
      = ∏ x : G ⧸ H, σ ((g * h * j) • x) •
        a (transversalElt H σ hσ g (h • (j • x)) * transversalElt H σ hσ h (j • x),
          transversalElt H σ hσ j x) := by
    rw [corCochain₂_apply]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [transversalElt_mul H σ hσ]
  have e2 : corCochain₂ H σ hσ a (g, h)
      = ∏ x : G ⧸ H, σ ((g * h * j) • x) •
        a (transversalElt H σ hσ g (h • (j • x)), transversalElt H σ hσ h (j • x)) := by
    rw [corCochain₂_apply]
    refine (Fintype.prod_equiv (MulAction.toPerm j) _ _ fun x => ?_).symm
    rw [mul_smul (g * h) j x]
    rfl
  have e3 : g • corCochain₂ H σ hσ a (h, j)
      = ∏ x : G ⧸ H, σ ((g * h * j) • x) •
        (transversalElt H σ hσ g ((h * j) • x) •
          a (transversalElt H σ hσ h (j • x), transversalElt H σ hσ j x)) := by
    rw [corCochain₂_apply, Finset.smul_prod']
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [smul_smul, ← mul_coe_transversalElt H σ hσ g ((h * j) • x), ← mul_smul g (h * j) x,
      ← mul_assoc g h j, ← smul_smul, subgroupSmul_eq]
  have e4 : corCochain₂ H σ hσ a (g, h * j)
      = ∏ x : G ⧸ H, σ ((g * h * j) • x) •
        a (transversalElt H σ hσ g ((h * j) • x),
          transversalElt H σ hσ h (j • x) * transversalElt H σ hσ j x) := by
    rw [corCochain₂_apply, ← mul_assoc]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [transversalElt_mul H σ hσ]
  rw [e1, e2, e3, e4, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [← smul_mul', ← smul_mul']
  congr 1
  rw [mul_smul h j x]
  exact ha _ _ _

/-- Corestriction is multiplicative in the two cochain. -/
theorem corCochain₂_mul [Fintype (G ⧸ H)] (a b : ↥H × ↥H → M) :
    corCochain₂ H σ hσ (a * b) = corCochain₂ H σ hσ a * corCochain₂ H σ hσ b := by
  funext p
  obtain ⟨g₁, g₂⟩ := p
  simp only [corCochain₂_apply, Pi.mul_apply, smul_mul']
  exact Finset.prod_mul_distrib

/-- **The corestriction of a coboundary is the coboundary of the corestriction.**  This is what
makes the average descend from cocycles to classes in degree two. -/
theorem corCochain₂_coboundary₂ [Fintype (G ⧸ H)] (u : ↥H → M) :
    corCochain₂ H σ hσ (coboundary₂ u) = coboundary₂ (corCochain₁ H σ hσ u) := by
  funext p
  obtain ⟨g₁, g₂⟩ := p
  show corCochain₂ H σ hσ (coboundary₂ u) (g₁, g₂)
    = g₁ • corCochain₁ H σ hσ u g₂ / corCochain₁ H σ hσ u (g₁ * g₂) * corCochain₁ H σ hσ u g₁
  have e1 : g₁ • corCochain₁ H σ hσ u g₂
      = ∏ x : G ⧸ H, σ ((g₁ * g₂) • x) •
        (transversalElt H σ hσ g₁ (g₂ • x) • u (transversalElt H σ hσ g₂ x)) := by
    rw [corCochain₁_apply, Finset.smul_prod']
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [smul_smul, ← mul_coe_transversalElt H σ hσ g₁ (g₂ • x), ← mul_smul g₁ g₂ x,
      ← smul_smul, subgroupSmul_eq]
  have e3 : corCochain₁ H σ hσ u g₁
      = ∏ x : G ⧸ H, σ ((g₁ * g₂) • x) • u (transversalElt H σ hσ g₁ (g₂ • x)) := by
    rw [corCochain₁_apply]
    refine (Fintype.prod_equiv (MulAction.toPerm g₂) _ _ fun x => ?_).symm
    rw [mul_smul g₁ g₂ x]
    rfl
  rw [e1, e3, corCochain₁_apply, corCochain₂_apply, ← Finset.prod_div_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [← smul_div', ← smul_mul']
  congr 1
  show transversalElt H σ hσ g₁ (g₂ • x) • u (transversalElt H σ hσ g₂ x)
      / u (transversalElt H σ hσ g₁ (g₂ • x) * transversalElt H σ hσ g₂ x)
      * u (transversalElt H σ hσ g₁ (g₂ • x)) = _
  rw [← transversalElt_mul H σ hσ]

section Smooth

variable [TopologicalSpace G]

/-- A two cochain constant on the cosets of a subgroup open and normal in the whole group and
contained in the subgroup has a corestriction constant on the cosets of that same subgroup. -/
theorem isSmooth₂_corCochain₂ [Fintype (G ⧸ H)] {N : Subgroup G} (hN : IsOpenNormal N)
    (hNH : N ≤ H) {a : ↥H × ↥H → M}
    (ha : ∀ y z n m : ↥H, (n : G) ∈ N → (m : G) ∈ N → a (y * n, z * m) = a (y, z)) :
    IsSmooth₂ (corCochain₂ H σ hσ a) := by
  refine ⟨N, hN, fun g₁ g₂ n hn m hm => ?_⟩
  have hprod : (g₁ * n) * (g₂ * m) = (g₁ * g₂) * ((g₂⁻¹ * n * g₂) * m) := by group
  have hmemN : (g₂⁻¹ * n * g₂) * m ∈ N :=
    N.mul_mem (hN.normal.conj_mem' n hn g₂) hm
  have hcos : ∀ x : G ⧸ H, ((g₁ * n) * (g₂ * m)) • x = (g₁ * g₂) • x := by
    intro x
    rw [hprod]
    exact smul_mul_right_of_mem H σ hσ hN.normal hNH _ hmemN x
  rw [corCochain₂_apply, corCochain₂_apply]
  refine Finset.prod_congr rfl fun x _ => ?_
  obtain ⟨hx2, ht2⟩ := transversalElt_mul_right H σ hσ hN.normal hNH g₂ hm x
  obtain ⟨_, ht1⟩ := transversalElt_mul_right H σ hσ hN.normal hNH g₁ hn (g₂ • x)
  rw [hcos x, hx2, ht1, ht2, ha]
  · exact hN.normal.conj_mem' n hn (σ (g₂ • x))
  · exact hN.normal.conj_mem' m hm (σ x)

/-- **The corestriction of a smooth two cochain is smooth**, for a subgroup with an open normal
core. -/
theorem isSmooth₂_corCochain₂_of_isSmooth₂ [Fintype (G ⧸ H)] (hcore : HasOpenNormalCore H)
    {a : ↥H × ↥H → M} (ha : IsSmooth₂ a) : IsSmooth₂ (corCochain₂ H σ hσ a) := by
  obtain ⟨N', hN', h⟩ := ha
  obtain ⟨N, hN, hNH, hmem⟩ := hcore N' hN'
  exact isSmooth₂_corCochain₂ H σ hσ hN hNH
    fun y z n m hn hm => h y z n (hmem n hn) m (hmem m hm)

end Smooth

end Two


/-! ### Corestriction in the second cohomology -/

section Descent2

variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) (σ : G ⧸ H → G)
  (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x)
  {M : Type*} [CommGroup M] [MulDistribMulAction G M] [Fintype (G ⧸ H)]

include hσ

/-- Corestriction on smooth two cocycles. -/
def corCocycle₂ (hcore : HasOpenNormalCore H) :
    smoothCocycle₂ ↥H M →* smoothCocycle₂ G M where
  toFun a := ⟨corCochain₂ H σ hσ a.1, isMulCocycle₂_corCochain₂ H σ hσ a.2.1,
    isSmooth₂_corCochain₂_of_isSmooth₂ H σ hσ hcore a.2.2⟩
  map_one' := by
    refine Subtype.ext (funext fun p => ?_)
    obtain ⟨g₁, g₂⟩ := p
    show ∏ x : G ⧸ H, σ ((g₁ * g₂) • x) • (1 : M) = 1
    simp
  map_mul' a b := Subtype.ext (corCochain₂_mul H σ hσ a.1 b.1)

/-- **Corestriction in the second cohomology.** -/
def corH2 (hcore : HasOpenNormalCore H) : SmoothH2 ↥H M →* SmoothH2 G M :=
  QuotientGroup.map _ _ (corCocycle₂ H σ hσ hcore) <| by
    rintro ⟨a, ha, has⟩ ⟨u, hus, hcb⟩
    have hcb' : coboundary₂ u = a := hcb
    refine Subgroup.mem_comap.2 ⟨corCochain₁ H σ hσ u,
      isSmooth₁_corCochain₁_of_isSmooth₁ H σ hσ hcore hus, ?_⟩
    show coboundary₂ (corCochain₁ H σ hσ u) = corCochain₂ H σ hσ a
    rw [← hcb']
    exact (corCochain₂_coboundary₂ H σ hσ u).symm

/-- **Corestriction in the second cohomology is computed on cocycles.** -/
theorem corH2_smoothH2Mk (hcore : HasOpenNormalCore H) {a : ↥H × ↥H → M} (ha : IsMulCocycle₂ a)
    (has : IsSmooth₂ a) :
    corH2 H σ hσ hcore (smoothH2Mk a ha has)
      = smoothH2Mk (corCochain₂ H σ hσ a) (isMulCocycle₂_corCochain₂ H σ hσ ha)
        (isSmooth₂_corCochain₂_of_isSmooth₂ H σ hσ hcore has) := rfl

end Descent2


/-! ### Corestriction after restriction in degree two -/

section ResCor

variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) (σ : G ⧸ H → G)
  (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x)
  {M : Type*} [CommGroup M] [MulDistribMulAction G M] [Fintype (G ⧸ H)]

include hσ

/-- The one cochain correcting the corestriction of a restricted two cocycle: at a group element,
the values of the cocycle at the chosen representatives paired with the transversal elements,
divided by its values at the element paired with the chosen representatives. -/
def corAux₁ (a : G × G → M) : G → M :=
  fun g => (∏ x : G ⧸ H, a (σ (g • x), (transversalElt H σ hσ g x : G)))
    / ∏ x : G ⧸ H, a (g, σ x)

omit [MulDistribMulAction G M] in
/-- The correcting one cochain is constant on the cosets of a subgroup open and normal in the whole
group and contained in the subgroup, whenever the two cocycle is. -/
theorem isSmooth₁_corAux₁ {N : Subgroup G} (hN : IsOpenNormal N) (hNH : N ≤ H) {a : G × G → M}
    (hsm : ∀ x y : G, ∀ n ∈ N, ∀ m ∈ N, a (x * n, y * m) = a (x, y)) :
    IsSmooth₁ (corAux₁ H σ hσ a) := by
  refine ⟨N, hN, fun g n hn => ?_⟩
  show (∏ x : G ⧸ H, a (σ ((g * n) • x), (transversalElt H σ hσ (g * n) x : G)))
      / ∏ x : G ⧸ H, a (g * n, σ x)
    = (∏ x : G ⧸ H, a (σ (g • x), (transversalElt H σ hσ g x : G)))
      / ∏ x : G ⧸ H, a (g, σ x)
  congr 1
  · refine Finset.prod_congr rfl fun x _ => ?_
    obtain ⟨hx, ht⟩ := transversalElt_mul_right H σ hσ hN.normal hNH g hn x
    rw [hx, ht, Subgroup.coe_mul]
    have hone := hsm (σ (g • x)) (transversalElt H σ hσ g x : G) 1 N.one_mem
      ((σ x)⁻¹ * n * σ x) (hN.normal.conj_mem' n hn (σ x))
    rwa [mul_one] at hone
  · refine Finset.prod_congr rfl fun x _ => ?_
    have hone := hsm g (σ x) n hn 1 N.one_mem
    rwa [mul_one] at hone

omit [TopologicalSpace G] in
/-- **The corestriction of a restricted two cocycle is the cocycle raised to the number of cosets,
times the coboundary of the correcting one cochain.**  The three applications of the cocycle
relation that produce this are at the chosen representative against the two transversal elements,
at the first group element against the chosen representative and the second transversal element,
and at the two group elements against the chosen representative. -/
theorem corCochain₂_comap₂ {a : G × G → M} (ha : IsMulCocycle₂ a) :
    corCochain₂ H σ hσ (comap₂ H.subtype a)
      = a ^ Fintype.card (G ⧸ H) * coboundary₂ (corAux₁ H σ hσ a) := by
  funext p
  obtain ⟨g₁, g₂⟩ := p
  have hterm : ∀ x : G ⧸ H,
      σ ((g₁ * g₂) • x) • comap₂ H.subtype a
          (transversalElt H σ hσ g₁ (g₂ • x), transversalElt H σ hσ g₂ x)
        = (g₁ • a (σ (g₂ • x), (transversalElt H σ hσ g₂ x : G)))
          * a (g₁ * g₂, σ x) * a (g₁, g₂)
          * (g₁ • a (g₂, σ x))⁻¹ * (a (g₁, σ (g₂ • x)))⁻¹
          * a (σ ((g₁ * g₂) • x), (transversalElt H σ hσ g₁ (g₂ • x) : G))
          * (a (σ ((g₁ * g₂) • x), (transversalElt H σ hσ (g₁ * g₂) x : G)))⁻¹ := by
    intro x
    have hrA : σ ((g₁ * g₂) • x) * (transversalElt H σ hσ g₁ (g₂ • x) : G)
        = g₁ * σ (g₂ • x) := by
      rw [← mul_coe_transversalElt H σ hσ g₁ (g₂ • x), mul_smul g₁ g₂ x]
    have htB : σ (g₂ • x) * (transversalElt H σ hσ g₂ x : G) = g₂ * σ x :=
      mul_coe_transversalElt H σ hσ g₂ x
    have hAB : (transversalElt H σ hσ g₁ (g₂ • x) : G) * (transversalElt H σ hσ g₂ x : G)
        = (transversalElt H σ hσ (g₁ * g₂) x : G) := by
      rw [transversalElt_mul H σ hσ]
      rfl
    have h1 := ha (σ ((g₁ * g₂) • x)) (transversalElt H σ hσ g₁ (g₂ • x) : G)
      (transversalElt H σ hσ g₂ x : G)
    rw [hrA, hAB] at h1
    have h2 := ha g₁ (σ (g₂ • x)) (transversalElt H σ hσ g₂ x : G)
    rw [htB] at h2
    have h3 := ha g₁ g₂ (σ x)
    have k1 := eq_mul_inv_of_mul_eq h1.symm
    have k2 := eq_mul_inv_of_mul_eq h2
    have k3 := eq_mul_inv_of_mul_eq ((mul_comm _ _).trans h3.symm)
    show σ ((g₁ * g₂) • x) • a ((transversalElt H σ hσ g₁ (g₂ • x) : G),
      (transversalElt H σ hσ g₂ x : G)) = _
    rw [k1, k2, k3]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  have hC₁ : ∏ x : G ⧸ H, a (σ ((g₁ * g₂) • x), (transversalElt H σ hσ g₁ (g₂ • x) : G))
      = ∏ y : G ⧸ H, a (σ (g₁ • y), (transversalElt H σ hσ g₁ y : G)) := by
    refine Fintype.prod_equiv (MulAction.toPerm g₂) _ _ fun x => ?_
    rw [mul_smul g₁ g₂ x]
    rfl
  have hD₁ : ∏ x : G ⧸ H, a (g₁, σ (g₂ • x)) = ∏ y : G ⧸ H, a (g₁, σ y) :=
    Fintype.prod_equiv (MulAction.toPerm g₂) _ _ fun _ => rfl
  show corCochain₂ H σ hσ (comap₂ H.subtype a) (g₁, g₂)
    = a (g₁, g₂) ^ Fintype.card (G ⧸ H)
      * (g₁ • corAux₁ H σ hσ a g₂ / corAux₁ H σ hσ a (g₁ * g₂) * corAux₁ H σ hσ a g₁)
  rw [corCochain₂_apply, Finset.prod_congr rfl fun x (_ : x ∈ Finset.univ) => hterm x]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Finset.smul_prod',
    Finset.prod_const, Finset.card_univ, hC₁, hD₁]
  show _ = a (g₁, g₂) ^ Fintype.card (G ⧸ H)
    * (g₁ • ((∏ x : G ⧸ H, a (σ (g₂ • x), (transversalElt H σ hσ g₂ x : G)))
          / ∏ x : G ⧸ H, a (g₂, σ x))
      / ((∏ x : G ⧸ H, a (σ ((g₁ * g₂) • x), (transversalElt H σ hσ (g₁ * g₂) x : G)))
          / ∏ x : G ⧸ H, a (g₁ * g₂, σ x))
      * ((∏ x : G ⧸ H, a (σ (g₁ • x), (transversalElt H σ hσ g₁ x : G)))
          / ∏ x : G ⧸ H, a (g₁, σ x)))
  rw [smul_div']
  have hgen : ∀ p q r s t u v : M,
      p * q * r * s⁻¹ * t⁻¹ * u * v⁻¹ = r * (p / s / (v / q) * (u / t)) := by
    intro p q r s t u v
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  exact hgen _ _ _ _ _ _ _

omit [MulDistribMulAction G M] in
/-- **The correcting one cochain of a smooth two cocycle is smooth**, for a subgroup with an open
normal core. -/
theorem isSmooth₁_corAux₁_of_isSmooth₂ (hcore : HasOpenNormalCore H) {a : G × G → M}
    (hs : IsSmooth₂ a) : IsSmooth₁ (corAux₁ H σ hσ a) := by
  obtain ⟨N, hN, h⟩ := hs
  obtain ⟨N₁, hN₁, hN₁H, _⟩ := hcore ⊤ isOpenNormal_top
  exact isSmooth₁_corAux₁ H σ hσ (hN.inf hN₁) (le_trans inf_le_right hN₁H)
    fun x y n hn m hm => h x y n hn.1 m hm.1

/-- **Corestriction after restriction raises a class of the second cohomology to the index.** -/
theorem corH2_resH2 (hcore : HasOpenNormalCore H) (c : SmoothH2 G M) :
    corH2 H σ hσ hcore (resH2 H c) = c ^ Fintype.card (G ⧸ H) := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective c
  rw [resH2_smoothH2Mk, corH2_smoothH2Mk]
  have hmk : (smoothH2Mk a ha hs) ^ Fintype.card (G ⧸ H)
      = QuotientGroup.mk ((⟨a, ha, hs⟩ : smoothCocycle₂ G M) ^ Fintype.card (G ⧸ H)) :=
    (map_pow (QuotientGroup.mk' ((smoothCoboundary₂ G M).subgroupOf (smoothCocycle₂ G M)))
      ⟨a, ha, hs⟩ _).symm
  rw [hmk]
  refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
  refine ⟨(corAux₁ H σ hσ a)⁻¹, (isSmooth₁_corAux₁_of_isSmooth₂ H σ hσ hcore hs).inv, ?_⟩
  have hcoe : ((⟨a, ha, hs⟩ : smoothCocycle₂ G M) ^ Fintype.card (G ⧸ H) : G × G → M)
      = a ^ Fintype.card (G ⧸ H) := by
    simp
  show coboundary₂ (corAux₁ H σ hσ a)⁻¹
    = (corCochain₂ H σ hσ (comap₂ H.subtype a))⁻¹
      * ((⟨a, ha, hs⟩ : smoothCocycle₂ G M) ^ Fintype.card (G ⧸ H) : G × G → M)
  rw [hcoe, corCochain₂_comap₂ H σ hσ ha, coboundary₂_inv]
  have hgen : ∀ p q : G × G → M, q⁻¹ = (p * q)⁻¹ * p := by
    intro p q
    rw [mul_inv, mul_comm p⁻¹ q⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  exact hgen _ _

end ResCor

end InverseGalois.CFT
