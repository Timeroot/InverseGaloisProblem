/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Quotient
import InverseGalois.CFT.Profinite.TransgressionRestrict

/-!
# The transgression lives at the level of the quotient

A transgression takes the value one whenever its index lies in the subgroup: the cocycle condition
at the unit forces the member indexed by the unit to be trivial, and the family depends only on the
class of its index.  So the cochain the transgression defines is trivial on the subgroup, and since
the subgroup also acts trivially on the coefficients its class is inflated from the quotient.

Inflation is injective in the first cohomology, so the class of a transgression is a class of the
quotient and nothing is lost by asking for its vanishing there.  The quotient is discrete, and in
the arithmetic case finite, so the condition which the previous file expressed as the vanishing of a
group of classes of the ambient group becomes a condition on a group of classes of a finite group:
the classes of the first cohomology of the quotient whose localisation at every member of a family
of subgroups vanishes.

## Main definitions

* `InverseGalois.CFT.sha1Level`: **the classes of the first cohomology of the quotient by a level
  whose localisation at every member of a family of subgroups vanishes.**

## Main results

* `InverseGalois.CFT.IsTransgressionDatum.apply_eq_one_of_mem`: a transgression indexed by an
  element of the subgroup is trivial.
* `InverseGalois.CFT.exists_inflH1_transClass`: **the class of a transgression is inflated from the
  quotient.**
* `InverseGalois.CFT.transClass_eq_one_of_sha1Level`: a transgression whose localisations all
  vanish has trivial class as soon as the group of classes above is trivial.
* `InverseGalois.CFT.exists_comapH2_eq_of_sha1Level_eq_bot`: **a locally trivial class of the
  second cohomology whose restriction to the kernel is trivial is inflated from the quotient**, as
  soon as that group is trivial.

## Tags

profinite group, Galois cohomology, transgression, inflation, finite level, local-global principle
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### A transgression indexed by the subgroup is trivial -/

section Vanish

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]
variable {N : Subgroup G} {t : G → G → M}

/-- **A transgression indexed by the unit is trivial**, the cocycle condition there reading that its
value is its own square. -/
theorem IsTransgressionDatum.apply_one (h : IsTransgressionDatum N M t) {x : G} (hx : x ∈ N) :
    t 1 x = 1 := by
  have h1 := h.cocycle 1 1 x hx
  simp only [mul_one, one_mul, inv_one, one_smul] at h1
  exact left_eq_mul.1 h1

/-- **A transgression indexed by an element of the subgroup is trivial**, the family depending only
on the class of its index there. -/
theorem IsTransgressionDatum.apply_eq_one_of_mem (h : IsTransgressionDatum N M t) {n : G}
    (hn : n ∈ N) {x : G} (hx : x ∈ N) : t n x = 1 := by
  have h1 := h.smul_left n hn 1 x hx
  rw [mul_one] at h1
  rw [h1, h.apply_one hx]

/-- **The cochain of a transgression is trivial on the subgroup.** -/
theorem transCochain_eq_one_of_mem (h : IsTransgressionDatum N M t)
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) {n : G} (hn : n ∈ N) :
    transCochain h htriv n = 1 := by
  rw [transCochain_apply, smoothH1Mk_eq_one_iff]
  exact ⟨1, funext fun x => by rw [smul_one, div_one, h.apply_eq_one_of_mem hn x.2]⟩

end Vanish

/-! ### The class of a transgression is inflated -/

section Inflate

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]
variable {N : Subgroup G} [hN : N.Normal]

/-- **A normal subgroup acts trivially on its own first cohomology**, so the quotient acts there. -/
instance actsTrivially_smoothH1 : ActsTrivially N (SmoothH1 ↥N M) :=
  ⟨fun _ hn z => conjH1_eq_self_of_mem hN hn z⟩

variable [IsTopologicalGroup G] {t : G → G → M}

/-- **The class of a transgression is inflated from the quotient**, its cochain being trivial on the
subgroup and the subgroup acting trivially on the coefficients. -/
theorem exists_inflH1_transClass (h : IsTransgressionDatum N M t)
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (hop : IsOpen (N : Set G)) :
    ∃ x : SmoothH1 (G ⧸ N) (SmoothH1 ↥N M),
      inflH1 N (SmoothH1 ↥N M) hop x = transClass h htriv hop :=
  exists_inflH1_eq N (SmoothH1 ↥N M) hop (isMulCocycle₁_transCochain h htriv)
    (isSmooth₁_transCochain h htriv hop) 1
    fun n hn => by rw [smul_one, div_one, transCochain_eq_one_of_mem h htriv hn]

end Inflate

/-! ### The locally trivial classes at the level of the quotient -/

section Level

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]
variable {N : Subgroup G} [hN : N.Normal]

variable (M N) in
/-- **The classes of the first cohomology of the quotient by a level, with values in the first
cohomology of that level, whose localisation at every member of a family of subgroups vanishes.**
Localising means restricting the class to the subgroup and its coefficients to the part of the level
lying inside that subgroup; for the Galois group of a number field and the family of decomposition
subgroups this is the group a local-global principle in the first cohomology computes. -/
def sha1Level (hop : IsOpen (N : Set G)) (S : Set (Subgroup G)) :
    Subgroup (SmoothH1 (G ⧸ N) (SmoothH1 ↥N M)) :=
  ⨅ D ∈ S, ((resCoeffH1 N D).comp (inflH1 N (SmoothH1 ↥N M) hop)).ker

@[simp]
theorem mem_sha1Level {hop : IsOpen (N : Set G)} {S : Set (Subgroup G)}
    {x : SmoothH1 (G ⧸ N) (SmoothH1 ↥N M)} :
    x ∈ sha1Level M N hop S ↔
      ∀ D ∈ S, resCoeffH1 N D (inflH1 N (SmoothH1 ↥N M) hop x) = 1 := by
  simp [sha1Level, Subgroup.mem_iInf, MonoidHom.mem_ker]

variable {t : G → G → M}

/-- **A transgression all of whose localisations vanish has trivial class**, as soon as the locally
trivial classes at the level of the quotient are trivial.  The class of a transgression is inflated,
and inflation is injective in the first cohomology. -/
theorem transClass_eq_one_of_sha1Level (h : IsTransgressionDatum N M t)
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (hop : IsOpen (N : Set G)) {S : Set (Subgroup G)}
    (hsha : sha1Level M N hop S = ⊥)
    (hloc : ∀ D ∈ S, localTransClass h htriv hop D = 1) :
    transClass h htriv hop = 1 := by
  obtain ⟨x, hx⟩ := exists_inflH1_transClass h htriv hop
  have hmem : x ∈ sha1Level M N hop S := by
    refine mem_sha1Level.2 fun D hD => ?_
    rw [hx, resCoeffH1_transClass]
    exact hloc D hD
  rw [hsha, Subgroup.mem_bot] at hmem
  rw [← hx, hmem, map_one]

end Level

/-! ### The localisation, read at the level of the quotient -/

section LocaliseLevel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]
variable {N : Subgroup G} [hN : N.Normal] (D : Subgroup G)

/-- **The part of a level lying inside a subgroup acts trivially on the first cohomology of the
level**, so the quotient of the subgroup by it acts there. -/
instance actsTrivially_subgroupOf_smoothH1 :
    ActsTrivially (N.subgroupOf D) (SmoothH1 ↥N M) :=
  ⟨fun _ hn z => conjH1_eq_self_of_mem hN (Subgroup.mem_subgroupOf.1 hn) z⟩

variable (N) in
/-- The quotient of a subgroup by the part of a level lying inside it, mapped to the quotient by
the level. -/
def quotSubHom : ↥D ⧸ N.subgroupOf D →* G ⧸ N :=
  QuotientGroup.map (N.subgroupOf D) N D.subtype le_rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem quotSubHom_mk (x : ↥D) :
    quotSubHom N D (QuotientGroup.mk x) = QuotientGroup.mk (x : G) := rfl

/-- The two quotients act alike on the first cohomology of the level. -/
theorem quotSubHom_smul (g : ↥D ⧸ N.subgroupOf D) (z : SmoothH1 ↥N M) :
    g • z = quotSubHom N D g • z := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  rfl

/-- The projection of a subgroup onto the quotient by the part of a level lying inside it is a
smooth homomorphism, both quotients being discrete. -/
theorem isSmoothHom_quotSubHom (hop : IsOpen (N : Set G)) :
    IsSmoothHom (quotSubHom N D) := by
  haveI : DiscreteTopology (↥D ⧸ N.subgroupOf D) :=
    QuotientGroup.discreteTopology (isOpen_subgroupOf (N := N) (D := D) hop)
  exact isSmoothHom_of_continuous continuous_of_discreteTopology

variable (N) in
/-- **Restriction to a subgroup, read at the level of the quotient.** -/
def resQuotH1 (hop : IsOpen (N : Set G)) :
    SmoothH1 (G ⧸ N) (SmoothH1 ↥N M) →* SmoothH1 (↥D ⧸ N.subgroupOf D) (SmoothH1 ↥N M) :=
  comapH1 (quotSubHom N D) (quotSubHom_smul D) (isSmoothHom_quotSubHom D hop)

/-- Localising the coefficients is equivariant for the quotient of the subgroup. -/
theorem resSubH1_smul_quot (g : ↥D ⧸ N.subgroupOf D) (z : SmoothH1 ↥N M) :
    resSubH1 N D (g • z) = g • resSubH1 N D z := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  exact resSubH1_smul D x z

variable (N) in
/-- **Localisation of the coefficients, read at the level of the quotient.** -/
def coeffQuotH1 :
    SmoothH1 (↥D ⧸ N.subgroupOf D) (SmoothH1 ↥N M) →*
      SmoothH1 (↥D ⧸ N.subgroupOf D) (SmoothH1 ↥(N.subgroupOf D) M) :=
  coeffH1 (resSubH1 N D) (resSubH1_smul_quot D)

variable (N) in
/-- **The localisation at a subgroup, read at the level of the quotient**: restriction to the
quotient of the subgroup, followed by localisation of the coefficients. -/
def resCoeffQuotH1 (hop : IsOpen (N : Set G)) :
    SmoothH1 (G ⧸ N) (SmoothH1 ↥N M) →*
      SmoothH1 (↥D ⧸ N.subgroupOf D) (SmoothH1 ↥(N.subgroupOf D) M) :=
  (coeffQuotH1 N D).comp (resQuotH1 N D hop)

/-- **Localising an inflated class is inflating its localisation**, both being computed by the
same cochain on the subgroup. -/
theorem resCoeffH1_inflH1 (hop : IsOpen (N : Set G))
    (x : SmoothH1 (G ⧸ N) (SmoothH1 ↥N M)) :
    resCoeffH1 N D (inflH1 N (SmoothH1 ↥N M) hop x)
      = inflH1 (N.subgroupOf D) (SmoothH1 ↥(N.subgroupOf D) M)
          (isOpen_subgroupOf (N := N) (D := D) hop) (resCoeffQuotH1 N D hop x) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rfl

/-- **The localisation of an inflated class vanishes exactly when the localisation vanishes at the
level of the quotient**, inflation being injective in the first cohomology. -/
theorem resCoeffH1_inflH1_eq_one_iff (hop : IsOpen (N : Set G))
    (x : SmoothH1 (G ⧸ N) (SmoothH1 ↥N M)) :
    resCoeffH1 N D (inflH1 N (SmoothH1 ↥N M) hop x) = 1 ↔ resCoeffQuotH1 N D hop x = 1 := by
  rw [resCoeffH1_inflH1]
  constructor
  · intro h
    refine inflH1_injective (N.subgroupOf D) (SmoothH1 ↥(N.subgroupOf D) M)
      (isOpen_subgroupOf (N := N) (D := D) hop) ?_
    rw [h, map_one]
  · intro h
    rw [h, map_one]

/-- **The locally trivial classes at the level of the quotient, read entirely there**: the
localisations are the maps of the quotient by the level to the quotients of the subgroups by their
parts of it. -/
theorem mem_sha1Level_iff {hop : IsOpen (N : Set G)} {S : Set (Subgroup G)}
    {x : SmoothH1 (G ⧸ N) (SmoothH1 ↥N M)} :
    x ∈ sha1Level M N hop S ↔ ∀ D ∈ S, resCoeffQuotH1 N D hop x = 1 := by
  simp only [mem_sha1Level, resCoeffH1_inflH1_eq_one_iff]

/-- **The locally trivial classes at the level of the quotient are the intersection of the kernels
of the localisations there.** -/
theorem sha1Level_eq (hop : IsOpen (N : Set G)) (S : Set (Subgroup G)) :
    sha1Level M N hop S = ⨅ D ∈ S, (resCoeffQuotH1 N D hop).ker := by
  ext x
  rw [mem_sha1Level_iff]
  simp [Subgroup.mem_iInf, MonoidHom.mem_ker]

end LocaliseLevel

/-! ### Inflation from the vanishing of the locally trivial classes at the level -/

section Package

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [CommGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction Q M]
variable {π : G →* Q} (hπ : ∀ (g : G) (m : M), g • m = π g • m)

/-- **A locally trivial class of the second cohomology of a topological group whose restriction to
the kernel of a smooth surjection onto a discrete group is trivial is inflated from the quotient**,
as soon as the everywhere locally trivial classes of the first cohomology of the quotient, with
values in the first cohomology of the kernel, are trivial.  This is the previous file's statement
with the ambient group replaced by the quotient throughout: the transgression class is inflated, so
nothing is lost, and the condition is a condition on a group attached to the quotient alone. -/
theorem exists_comapH2_eq_of_sha1Level_eq_bot (hbasis : HasOpenNormalBasis G)
    (hsm : IsSmoothHom π) (hsurj : Function.Surjective π)
    (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a)
    {b : G → M} (hbs : IsSmooth₁ b)
    (hb : ∀ x ∈ π.ker, ∀ y ∈ π.ker, a (x, y) = x • b y / b (x * y) * b x)
    {S : Set (Subgroup G)} (hmem : smoothH2Mk a ha has ∈ sha2 M S)
    (hsha1 : sha1Level M π.ker (isOpenNormal_ker_of_isSmoothHom hsm).isOpen S = ⊥) :
    ∃ x : SmoothH2 Q M, comapH2 π hπ hsm x = smoothH2Mk a ha has := by
  refine exists_comapH2_eq_of_localTransClass hπ hbasis hsm hsurj htriv ha has hbs hb hmem ?_
  intro t h hloc
  exact transClass_eq_one_of_sha1Level h htriv _ hsha1 hloc

end Package

end InverseGalois.CFT
