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

end InverseGalois.CFT
