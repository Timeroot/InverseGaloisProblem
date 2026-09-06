/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.H1Conj
import InverseGalois.CFT.Profinite.InfRes
import InverseGalois.CFT.Profinite.Transgression
import InverseGalois.CFT.Profinite.Trivial

/-!
# The transgression as a class of the first cohomology of the quotient

The transgression of a two cocycle of a topological group along the kernel of a smooth surjection
onto a discrete group is a family of homomorphisms of the kernel into the coefficients, indexed by
the group, which is a cocycle for the conjugation action, factors through the quotient, and is
uniformly smooth.  Those four conditions are exactly what is needed to read the family as a smooth
one cocycle of the group with values in the first cohomology of the kernel, and the family is the
coboundary of a smooth homomorphism precisely when the class of that cocycle is trivial.

The passage is not quite formal: the kernel acts trivially on the coefficients, so its first
cohomology is the group of smooth homomorphisms and a class there is a cochain, but the trivialising
homomorphism produced on the kernel has to be extended to the whole group and the extension is
smooth only if the homomorphism kills an open normal subgroup **of the ambient group**.  An open
subgroup of a compact topological group contains one, its normal core being closed of finite index,
and that is the only hypothesis the passage needs beyond the ones already carried.

The statement obtained replaces the five conditions of a Hasse principle for the transgression by
the vanishing of a single cohomology class, which is the form in which the locally trivial classes
of a number field are produced.

## Main definitions

* `InverseGalois.CFT.HasOpenNormalBasis`: every open subgroup contains an open normal subgroup.
* `InverseGalois.CFT.IsTransgressionDatum`: **the conditions satisfied by a transgression.**
* `InverseGalois.CFT.transCochain`: a transgression, read as a cochain with values in the first
  cohomology of the subgroup.
* `InverseGalois.CFT.transClass`: **a transgression, read as a class of the first cohomology of the
  group with values in the first cohomology of the subgroup.**

## Main results

* `InverseGalois.CFT.hasOpenNormalBasis_of_compactSpace`: a compact topological group has a basis of
  open normal subgroups.
* `InverseGalois.CFT.isOpenNormal_ker_of_isSmoothHom`: the kernel of a smooth homomorphism onto a
  discrete group is open and normal.
* `InverseGalois.CFT.smoothH1Mk_eq_iff_of_trivial`: for a trivial action two one cocycles have the
  same class only if they are equal.
* `InverseGalois.CFT.transClass_eq_one_iff`: **a transgression is the coboundary of a smooth
  homomorphism exactly when its class vanishes.**
* `InverseGalois.CFT.exists_comapH2_eq_of_transClass`: **a locally trivial class of the second
  cohomology whose restriction to the kernel is trivial is inflated from the quotient**, as soon as
  every locally trivial transgression class vanishes.

## Tags

profinite group, Galois cohomology, transgression, inflation, Hasse principle, smooth cochain
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### An open normal subgroup inside an open subgroup -/

section Core

variable (G : Type*) [Group G] [TopologicalSpace G]

/-- A topological group *has a basis of open normal subgroups* when every open subgroup contains
one.  This is what lets a homomorphism which is smooth on an open subgroup be extended smoothly. -/
def HasOpenNormalBasis : Prop :=
  ∀ H : Subgroup G, IsOpen (H : Set G) → ∃ R : Subgroup G, IsOpenNormal R ∧ R ≤ H

/-- **A compact topological group has a basis of open normal subgroups.**  An open subgroup is
closed, hence of finite index, hence its normal core is closed of finite index and so open. -/
theorem hasOpenNormalBasis_of_compactSpace [IsTopologicalGroup G] [CompactSpace G] :
    HasOpenNormalBasis G := by
  intro H hH
  have hclopen : IsClopen (H : Set G) := ⟨(⟨H, hH⟩ : OpenSubgroup G).isClosed, hH⟩
  obtain ⟨R, hR⟩ :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hclopen H.one_mem
  exact ⟨(R : Subgroup G), ⟨R.isNormal', R.isOpen'⟩, hR⟩

end Core

/-! ### The kernel of a smooth homomorphism onto a discrete group -/

section Ker

variable {G Q : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [Group Q]
  [TopologicalSpace Q] [DiscreteTopology Q]

/-- **The kernel of a smooth homomorphism onto a discrete group is open and normal**, the trivial
subgroup of the target being open and normal there. -/
theorem isOpenNormal_ker_of_isSmoothHom {π : G →* Q} (hsm : IsSmoothHom π) :
    IsOpenNormal π.ker := by
  obtain ⟨R, hR, hle⟩ := hsm ⊥ isOpenNormal_bot
  have hle' : R ≤ π.ker := fun x hx => MonoidHom.mem_ker.2 (Subgroup.mem_bot.1 (hle hx))
  exact ⟨MonoidHom.normal_ker π, Subgroup.isOpen_mono hle' hR.isOpen⟩

end Ker

/-! ### A class of a trivial module is a cocycle -/

section TrivEq

variable {H : Type*} [Group H] [TopologicalSpace H] {M : Type*} [CommGroup M]
  [MulDistribMulAction H M] (htriv : ∀ (g : H) (m : M), g • m = m)

include htriv in
/-- **For a trivial action two one cocycles have the same class only if they are equal**, every
coboundary being trivial. -/
theorem smoothH1Mk_eq_iff_of_trivial {u v : H → M} (hu : IsMulCocycle₁ u) (hus : IsSmooth₁ u)
    (hv : IsMulCocycle₁ v) (hvs : IsSmooth₁ v) :
    smoothH1Mk u hu hus = smoothH1Mk v hv hvs ↔ u = v := by
  rw [smoothH1Mk_eq_iff]
  constructor
  · rintro ⟨s, hs⟩
    funext g
    have h := congrFun hs g
    rw [htriv, div_self'] at h
    exact div_eq_one.1 h.symm
  · rintro rfl
    exact ⟨1, by funext g; rw [htriv, div_self', div_self']⟩

end TrivEq

/-! ### The conditions satisfied by a transgression -/

section Datum

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- **The conditions satisfied by a transgression**: a family of maps of the ambient group into the
coefficients, indexed by the ambient group, which is uniformly smooth, is a homomorphism on the
subgroup in the second variable, is a one cocycle for the conjugation action in the first, and does
not change when the first variable is multiplied by an element of the subgroup. -/
structure IsTransgressionDatum (N : Subgroup G) (M : Type*) [CommGroup M]
    [MulDistribMulAction G M] (t : G → G → M) : Prop where
  /-- The family is constant on the cosets of an open normal subgroup, uniformly in the index. -/
  isSmooth : ∃ R : Subgroup G, IsOpenNormal R ∧ ∀ σ x : G, ∀ n ∈ R, t σ (x * n) = t σ x
  /-- Each member of the family is a homomorphism on the subgroup. -/
  map_mul : ∀ σ : G, ∀ x ∈ N, ∀ y ∈ N, t σ (x * y) = t σ x * t σ y
  /-- The family is a one cocycle for the conjugation action. -/
  cocycle : ∀ σ τ : G, ∀ x ∈ N, t (σ * τ) x = σ • t τ (σ⁻¹ * x * σ) * t σ x
  /-- The family depends only on the class of its index modulo the subgroup. -/
  smul_left : ∀ n ∈ N, ∀ σ : G, ∀ x ∈ N, t (n * σ) x = t σ x

variable {N : Subgroup G} {t : G → G → M}

/-- A member of a transgression is a smooth cochain on the subgroup. -/
theorem IsTransgressionDatum.isSmooth₁_apply (h : IsTransgressionDatum N M t) (σ : G) :
    IsSmooth₁ (fun x : ↥N => t σ (x : G)) := by
  obtain ⟨R, hR, hcon⟩ := h.isSmooth
  refine ⟨R.comap N.subtype, isOpenNormal_comap_subtype N hR, fun x n hn => ?_⟩
  exact hcon σ (x : G) (n : G) hn

/-- A member of a transgression is a one cocycle on the subgroup, the action there being
trivial. -/
theorem IsTransgressionDatum.isMulCocycle₁_apply (h : IsTransgressionDatum N M t)
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (σ : G) :
    IsMulCocycle₁ (fun x : ↥N => t σ (x : G)) := by
  intro x y
  have hx : (x : ↥N) • t σ (y : G) = t σ (y : G) := htriv (x : G) x.2 _
  show t σ ((x : G) * (y : G)) = (x : ↥N) • t σ (y : G) * t σ (x : G)
  rw [hx, h.map_mul σ (x : G) x.2 (y : G) y.2, mul_comm]

/-- **A transgression, read as a cochain of the ambient group with values in the first cohomology
of the subgroup.** -/
def transCochain (h : IsTransgressionDatum N M t) (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) :
    G → SmoothH1 ↥N M :=
  fun σ => smoothH1Mk (fun x : ↥N => t σ (x : G)) (h.isMulCocycle₁_apply htriv σ)
    (h.isSmooth₁_apply σ)

/-- The cochain of a transgression is computed by the class of each of its members. -/
theorem transCochain_apply (h : IsTransgressionDatum N M t)
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (σ : G) :
    transCochain h htriv σ = smoothH1Mk (fun x : ↥N => t σ (x : G))
      (h.isMulCocycle₁_apply htriv σ) (h.isSmooth₁_apply σ) := rfl

end Datum

/-! ### The class of a transgression -/

section Class

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
variable {N : Subgroup G} [hN : N.Normal]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- The conjugation action of the ambient group on the first cohomology of a normal subgroup. -/
instance conjSmoothH1Action : MulDistribMulAction G (SmoothH1 ↥N M) :=
  conjMulDistribMulAction hN

/-- The conjugation action is conjugation of classes. -/
theorem smul_eq_conjH1 (σ : G) (z : SmoothH1 ↥N M) : σ • z = conjH1 hN σ z := rfl

variable {t : G → G → M}

/-- **The cochain of a transgression is a one cocycle** for the conjugation action, which is the
cocycle condition on the transgression itself. -/
theorem isMulCocycle₁_transCochain (h : IsTransgressionDatum N M t)
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) : IsMulCocycle₁ (transCochain h htriv) := by
  intro σ τ
  rw [transCochain_apply, transCochain_apply, transCochain_apply, smul_eq_conjH1,
    conjH1_smoothH1Mk, ← smoothH1Mk_mul]
  exact smoothH1Mk_congr (funext fun x : ↥N => h.cocycle σ τ (x : G) x.2) _ _ _ _

omit [ContinuousMul G] in
/-- **The cochain of a transgression is smooth** when the subgroup is open, the transgression
depending only on the class of its index there. -/
theorem isSmooth₁_transCochain (h : IsTransgressionDatum N M t)
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (hop : IsOpen (N : Set G)) :
    IsSmooth₁ (transCochain h htriv) := by
  refine ⟨N, ⟨hN, hop⟩, fun σ n hn => ?_⟩
  rw [transCochain_apply, transCochain_apply]
  refine smoothH1Mk_congr (funext fun x => ?_) _ _ _ _
  have hc : σ * n = σ * n * σ⁻¹ * σ := by group
  rw [hc]
  exact h.smul_left (σ * n * σ⁻¹) (hN.conj_mem n hn σ) σ (x : G) x.2

/-- **A transgression, read as a class of the first cohomology of the ambient group with values in
the first cohomology of an open normal subgroup.** -/
def transClass (h : IsTransgressionDatum N M t) (htriv : ∀ n ∈ N, ∀ m : M, n • m = m)
    (hop : IsOpen (N : Set G)) : SmoothH1 G (SmoothH1 ↥N M) :=
  smoothH1Mk (transCochain h htriv) (isMulCocycle₁_transCochain h htriv)
    (isSmooth₁_transCochain h htriv hop)

/-- **The class of a transgression which is the coboundary of a smooth homomorphism vanishes**, the
restriction of that homomorphism to the subgroup being the cochain which trivialises it. -/
theorem transClass_eq_one (h : IsTransgressionDatum N M t)
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (hop : IsOpen (N : Set G)) {φ : G → M}
    (hφs : IsSmooth₁ fun x : ↥N => φ (x : G))
    (hφm : ∀ x ∈ N, ∀ y ∈ N, φ (x * y) = φ x * φ y)
    (hφ : ∀ σ : G, ∀ x ∈ N, t σ x = σ • φ (σ⁻¹ * x * σ) / φ x) :
    transClass h htriv hop = 1 := by
  have hc : IsMulCocycle₁ (fun x : ↥N => φ (x : G)) := by
    intro x y
    have hx : (x : ↥N) • φ (y : G) = φ (y : G) := htriv (x : G) x.2 _
    show φ ((x : G) * (y : G)) = (x : ↥N) • φ (y : G) * φ (x : G)
    rw [hx, hφm (x : G) x.2 (y : G) y.2, mul_comm]
  rw [transClass, smoothH1Mk_eq_one_iff]
  refine ⟨smoothH1Mk (fun x : ↥N => φ (x : G)) hc hφs, funext fun σ => ?_⟩
  rw [transCochain_apply, smul_eq_conjH1, conjH1_smoothH1Mk, div_eq_iff_eq_mul,
    ← smoothH1Mk_mul]
  refine smoothH1Mk_congr (funext fun x => ?_) _ _ _ _
  show σ • φ (σ⁻¹ * (x : G) * σ) = t σ (x : G) * φ (x : G)
  rw [hφ σ (x : G) x.2, div_mul_cancel]

/-- **A transgression whose class vanishes is the coboundary of a smooth homomorphism.**  A
trivialising class on the subgroup is a homomorphism there, and it is extended by the unit outside;
the extension is smooth because the homomorphism kills an open subgroup of the ambient group and
therefore an open normal one. -/
theorem exists_eq_smul_div_of_transClass_eq_one [IsTopologicalGroup G]
    (hbasis : HasOpenNormalBasis G) (h : IsTransgressionDatum N M t)
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (hop : IsOpen (N : Set G))
    (h1 : transClass h htriv hop = 1) :
    ∃ φ : G → M, IsSmooth₁ φ ∧ (∀ x ∈ N, ∀ y ∈ N, φ (x * y) = φ x * φ y) ∧
      ∀ σ : G, ∀ x ∈ N, t σ x = σ • φ (σ⁻¹ * x * σ) / φ x := by
  classical
  have htrivN : ∀ (x : ↥N) (m : M), x • m = m := fun x m => htriv (x : G) x.2 m
  rw [transClass, smoothH1Mk_eq_one_iff] at h1
  obtain ⟨z, hz⟩ := h1
  obtain ⟨ψ, hψ, hψs, rfl⟩ := smoothH1Mk_surjective z
  have hkey : ∀ (σ : G) (x : ↥N), t σ (x : G) * ψ x = σ • ψ (conjMemHom hN σ x) := by
    intro σ x
    have h2 := congrFun hz σ
    rw [transCochain_apply, smul_eq_conjH1, conjH1_smoothH1Mk, div_eq_iff_eq_mul,
      ← smoothH1Mk_mul, smoothH1Mk_eq_iff_of_trivial htrivN] at h2
    exact congrFun h2.symm x
  refine ⟨fun g => if hg : g ∈ N then ψ ⟨g, hg⟩ else 1, ?_, ?_, ?_⟩
  · obtain ⟨K, hK, hcon⟩ := hψs
    have hKopen : IsOpen ((K.map N.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.coe_map, Subgroup.coe_subtype]
      exact hop.isOpenMap_subtype_val _ hK.isOpen
    obtain ⟨R, hR, hRle⟩ := hbasis _ hKopen
    refine ⟨R, hR, fun g n hn => ?_⟩
    obtain ⟨y, hyK, hyn⟩ := hRle hn
    have hnN : n ∈ N := hyn ▸ y.2
    have hψn : ψ ⟨n, hnN⟩ = 1 := by
      have hy : (⟨n, hnN⟩ : ↥N) = y := Subtype.ext hyn.symm
      rw [hy]
      have h3 := hcon 1 y hyK
      rw [one_mul] at h3
      rw [h3, InverseGalois.CFT.map_one_of_isMulCocycle₁ hψ]
    by_cases hg : g ∈ N
    · have hgn : g * n ∈ N := N.mul_mem hg hnN
      simp only [dif_pos hg, dif_pos hgn]
      have hmul : (⟨g * n, hgn⟩ : ↥N) = (⟨g, hg⟩ : ↥N) * ⟨n, hnN⟩ := rfl
      rw [hmul, map_mul_of_isMulCocycle₁_of_trivial htrivN hψ, hψn, mul_one]
    · have hgn : g * n ∉ N := fun hc => hg (by simpa using N.mul_mem hc (N.inv_mem hnN))
      simp only [dif_neg hg, dif_neg hgn]
  · intro x hx y hy
    have hxy : x * y ∈ N := N.mul_mem hx hy
    simp only [dif_pos hx, dif_pos hy, dif_pos hxy]
    have hmul : (⟨x * y, hxy⟩ : ↥N) = (⟨x, hx⟩ : ↥N) * ⟨y, hy⟩ := rfl
    rw [hmul, map_mul_of_isMulCocycle₁_of_trivial htrivN hψ]
  · intro σ x hx
    have hcx : σ⁻¹ * x * σ ∈ N := by simpa using hN.conj_mem x hx σ⁻¹
    simp only [dif_pos hx, dif_pos hcx]
    have hcm : (⟨σ⁻¹ * x * σ, hcx⟩ : ↥N) = conjMemHom hN σ ⟨x, hx⟩ := rfl
    rw [hcm, ← hkey σ ⟨x, hx⟩, mul_div_cancel_right]

/-- **A transgression is the coboundary of a smooth homomorphism exactly when its class
vanishes.** -/
theorem transClass_eq_one_iff [IsTopologicalGroup G] (hbasis : HasOpenNormalBasis G)
    (h : IsTransgressionDatum N M t) (htriv : ∀ n ∈ N, ∀ m : M, n • m = m)
    (hop : IsOpen (N : Set G)) :
    transClass h htriv hop = 1 ↔ ∃ φ : G → M, IsSmooth₁ φ ∧
      (∀ x ∈ N, ∀ y ∈ N, φ (x * y) = φ x * φ y) ∧
      ∀ σ : G, ∀ x ∈ N, t σ x = σ • φ (σ⁻¹ * x * σ) / φ x :=
  ⟨exists_eq_smul_div_of_transClass_eq_one hbasis h htriv hop,
    fun ⟨_, hφs, hφm, hφ⟩ =>
      transClass_eq_one h htriv hop (isSmooth₁_comp (continuous_subtype N) hφs) hφm hφ⟩

end Class

/-! ### Inflation from the vanishing of the locally trivial transgression classes -/

section Package

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [CommGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable {π : G →* Q} (hπ : ∀ (g : G) (m : M), g • m = π g • m)

/-- **A locally trivial class of the second cohomology of a topological group whose restriction to
the kernel of a smooth surjection onto a discrete group is trivial is inflated from the quotient**,
as soon as every transgression class which is locally the coboundary of a smooth homomorphism
vanishes.  This is the Hasse principle of the previous file, with the five conditions on a
transgression replaced by the single class it defines in the first cohomology of the quotient with
values in the first cohomology of the kernel. -/
theorem exists_comapH2_eq_of_transClass (hbasis : HasOpenNormalBasis G) (hsm : IsSmoothHom π)
    (hsurj : Function.Surjective π) (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a)
    {b : G → M} (hbs : IsSmooth₁ b)
    (hb : ∀ x ∈ π.ker, ∀ y ∈ π.ker, a (x, y) = x • b y / b (x * y) * b x)
    {S : Set (Subgroup G)} (hmem : smoothH2Mk a ha has ∈ sha2 M S)
    (hsha : ∀ (t : G → G → M) (h : IsTransgressionDatum π.ker M t),
      (∀ D ∈ S, ∃ e : G → M, IsSmooth₁ (fun x : ↥(D ⊓ π.ker) => e x) ∧
        (∀ x ∈ D ⊓ π.ker, ∀ y ∈ D ⊓ π.ker, e (x * y) = e x * e y) ∧
        ∀ σ ∈ D, ∀ x ∈ D, x ∈ π.ker → t σ x = σ • e (σ⁻¹ * x * σ) / e x) →
      transClass h htriv (isOpenNormal_ker_of_isSmoothHom hsm).isOpen = 1) :
    ∃ x : SmoothH2 Q M, comapH2 π hπ hsm x = smoothH2Mk a ha has := by
  refine exists_comapH2_eq_of_mem_sha2 hπ hsm hsurj htriv ha has hbs hb hmem ?_
  intro t h1 h2 h3 h4 hloc
  exact exists_eq_smul_div_of_transClass_eq_one hbasis ⟨h1, h2, h3, h4⟩ htriv _
    (hsha t ⟨h1, h2, h3, h4⟩ hloc)

end Package

end InverseGalois.CFT
