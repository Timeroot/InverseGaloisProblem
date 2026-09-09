/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.TransgressionCocycle
import InverseGalois.CFT.Profinite.TransgressionInflate
import InverseGalois.CFT.Profinite.TwistRes

/-!
# The transgression class is natural in the coefficients

A homomorphism of the coefficients commuting with the action carries a transgression to a
transgression, simply by composing, and the transgression of a cocycle composed with the
homomorphism is the composition of the transgression.  In cohomology this says that the class of a
transgression is natural: pushing the coefficients forward twice, once inside the first cohomology
of the subgroup and once outside, carries the class of a transgression to the class of the pushed
forward transgression.

That naturality is what turns a vanishing statement about the coefficients into a descent statement.
The obstruction to inflating a class of the second cohomology from the quotient is the class of the
transgression of a normalised cocycle representing it, and that obstruction is everywhere locally
trivial when the class is.  So a homomorphism of the coefficients which kills the everywhere locally
trivial classes of the first cohomology with values in the first cohomology of the kernel carries
every everywhere locally trivial class of the second cohomology into the image of inflation — no
statement that the obstruction group itself vanishes is needed, only that the map of coefficients
annihilates it.

The passage from a class to a normalised cocycle is the first half of the correction pipeline of the
descent theorem, isolated here: a smooth cocycle whose restriction to the kernel is the coboundary
of a smooth cochain is cohomologous to one which is trivial at every pair whose first entry lies in
the kernel.

The obstruction attached to a class of the level is itself a class of the level: the map of the
coefficients commutes with inflation, and inflation is injective in the first cohomology, so
annihilating the obstruction over the whole group and annihilating it at the level are the same
demand.  That is what lets the demand be handed to a theorem about a finite group.

## Main definitions

* `InverseGalois.CFT.transMap`: a family of maps into the coefficients, composed with a homomorphism
  of the coefficients.
* `InverseGalois.CFT.coeffTransH1`: **the map of the first cohomology with values in the first
  cohomology of a normal subgroup induced by a homomorphism of the coefficients.**
* `InverseGalois.CFT.coeffQuotTransH1`: the same map, read at the level of the quotient.

## Main results

* `InverseGalois.CFT.IsTransgressionDatum.map`: a transgression composed with a homomorphism of the
  coefficients is a transgression.
* `InverseGalois.CFT.transClass_map`: **the class of a transgression is natural in the
  coefficients.**
* `InverseGalois.CFT.exists_eq_one_on_ker`: **a class of the second cohomology trivial along the
  kernel is the class of a cocycle vanishing there in the first variable.**
* `InverseGalois.CFT.exists_comapH2_eq_coeffH2_of_sha1Loc`: **a homomorphism of the coefficients
  killing the everywhere locally trivial obstructions carries an everywhere locally trivial class of
  the second cohomology into the image of inflation.**
* `InverseGalois.CFT.exists_comapH2_eq_coeffH2_of_sha1Level`: **the same, with the obstructions read
  at the level of the quotient.**
* `InverseGalois.CFT.coeffTransH1_inflH1`: **pushing the coefficients forward commutes with
  inflation from the level.**
* `InverseGalois.CFT.coeffTransH1_inflH1_eq_one_iff`: the obstruction attached to a class of the
  level is annihilated exactly when it is annihilated at the level.

## Tags

profinite group, Galois cohomology, transgression, inflation, functoriality, local-global principle
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### A family of maps composed with a homomorphism of the coefficients -/

section Push

variable {G : Type*} [Group G] {M M' : Type*} [CommGroup M] [CommGroup M'] (φ : M →* M')

/-- **A family of maps of a group into the coefficients, composed with a homomorphism of the
coefficients.** -/
def transMap (t : G → G → M) : G → G → M' := fun σ x => φ (t σ x)

omit [Group G] in
@[simp]
theorem transMap_apply (t : G → G → M) (σ x : G) : transMap φ t σ x = φ (t σ x) := rfl

/-- **The transgression of a cocycle composed with a homomorphism of the coefficients is the
composition of the transgression.** -/
theorem transMap_transgression (c : G × G → M) :
    transMap φ (transgression c) = transgression (coeffMap₂ φ c) := rfl

end Push

/-! ### A transgression pushed forward -/

section Datum

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M M' : Type*} [CommGroup M] [CommGroup M'] [MulDistribMulAction G M]
  [MulDistribMulAction G M']
variable {N : Subgroup G} {t : G → G → M}

/-- **A transgression composed with an equivariant homomorphism of the coefficients is a
transgression**, the four conditions being carried across by the homomorphism. -/
theorem IsTransgressionDatum.map (h : IsTransgressionDatum N M t) (φ : M →* M')
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    IsTransgressionDatum N M' (transMap φ t) where
  isSmooth := by
    obtain ⟨R, hR, hcon⟩ := h.isSmooth
    exact ⟨R, hR, fun σ x n hn => congrArg φ (hcon σ x n hn)⟩
  map_mul σ x hx y hy := by
    show φ (t σ (x * y)) = φ (t σ x) * φ (t σ y)
    rw [h.map_mul σ x hx y hy, _root_.map_mul]
  cocycle σ τ x hx := by
    show φ (t (σ * τ) x) = σ • φ (t τ (σ⁻¹ * x * σ)) * φ (t σ x)
    rw [h.cocycle σ τ x hx, _root_.map_mul, hφ]
  smul_left n hn σ x hx := congrArg φ (h.smul_left n hn σ x hx)

end Datum

/-! ### The map of the first cohomology of the subgroup induced on classes -/

section Coeff

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M M' : Type*} [CommGroup M] [CommGroup M'] [MulDistribMulAction G M]
  [MulDistribMulAction G M']
variable {N : Subgroup G} [hN : N.Normal]

/-- **A homomorphism of the coefficients commutes with the conjugation action of the ambient group
on the first cohomology of a normal subgroup**, conjugation being composition with conjugation on
the source and the action on the target. -/
theorem coeffH1_conj (φ : M →* M') (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (σ : G)
    (z : SmoothH1 ↥N M) :
    coeffH1 φ (fun (g : ↥N) m => hφ (g : G) m) (σ • z)
      = σ • coeffH1 φ (fun (g : ↥N) m => hφ (g : G) m) z := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  simp only [smul_eq_conjH1, conjH1_smoothH1Mk, coeffH1_smoothH1Mk]
  exact smoothH1Mk_congr (funext fun x => hφ σ (u (conjMemHom hN σ x))) _ _ _ _

variable (N) in
/-- **The map of the first cohomology with values in the first cohomology of a normal subgroup
induced by an equivariant homomorphism of the coefficients**, pushing the coefficients forward both
inside the first cohomology of the subgroup and outside it. -/
def coeffTransH1 (φ : M →* M') (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    SmoothH1 G (SmoothH1 ↥N M) →* SmoothH1 G (SmoothH1 ↥N M') :=
  coeffH1 (coeffH1 φ fun (g : ↥N) m => hφ (g : G) m) (coeffH1_conj φ hφ)

variable {t : G → G → M}

/-- **The class of a transgression is natural in the coefficients.** -/
theorem transClass_map (h : IsTransgressionDatum N M t) (φ : M →* M')
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (htriv : ∀ n ∈ N, ∀ m : M, n • m = m)
    (htriv' : ∀ n ∈ N, ∀ m : M', n • m = m) (hop : IsOpen (N : Set G)) :
    transClass (h.map φ hφ) htriv' hop = coeffTransH1 N φ hφ (transClass h htriv hop) := rfl

/-- **The transgression class of a cocycle pushed forward is the transgression class pushed
forward.** -/
theorem transgressionClass_coeffMap₂ (φ : M →* M')
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (htriv : ∀ n ∈ N, ∀ m : M, n • m = m)
    (htriv' : ∀ n ∈ N, ∀ m : M', n • m = m) (hop : IsOpen (N : Set G)) {c : G × G → M}
    (hc : IsMulCocycle₂ c) (hcs : IsSmooth₂ c) (h1 : ∀ n ∈ N, ∀ y : G, c (n, y) = 1)
    (h1' : ∀ n ∈ N, ∀ y : G, coeffMap₂ φ c (n, y) = 1) :
    transgressionClass htriv' hop (isMulCocycle₂_coeffMap₂ φ hφ hc) (hcs.coeffMap₂ φ) h1'
      = coeffTransH1 N φ hφ (transgressionClass htriv hop hc hcs h1) := rfl

end Coeff

/-! ### A cocycle trivial in the first variable along the kernel -/

section Normalise

variable {G Q M : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] [CommGroup M] [MulDistribMulAction G M]
variable {π : G →* Q}

/-- **A class of the second cohomology whose restriction to the kernel of a smooth surjection onto a
discrete group is the coboundary of a smooth cochain is the class of a smooth cocycle which is
trivial at every pair whose first entry lies in the kernel.**  This is the first half of the
correction pipeline of the descent theorem: two successive twists, by the trivialising cochain and
by a cochain read along a section of the kernel, and both of them are constant along an open normal
subgroup small enough for the data at hand. -/
theorem exists_eq_one_on_ker (hsm : IsSmoothHom π) (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a) {b : G → M} (hbs : IsSmooth₁ b)
    (hb : ∀ x ∈ π.ker, ∀ y ∈ π.ker, a (x, y) = x • b y / b (x * y) * b x) :
    ∃ (c : G × G → M) (hc : IsMulCocycle₂ c) (hcs : IsSmooth₂ c),
      smoothH2Mk c hc hcs = smoothH2Mk a ha has ∧ ∀ n ∈ π.ker, ∀ y : G, c (n, y) = 1 := by
  obtain ⟨K, hK, hKle⟩ : ∃ K : Subgroup G, IsOpenNormal K ∧ K ≤ π.ker := by
    obtain ⟨K, hK, hle⟩ := hsm ⊥ isOpenNormal_bot
    exact ⟨K, hK, fun x hx =>
      MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp (Subgroup.mem_comap.mp (hle hx)))⟩
  obtain ⟨s, hs, hsc, hs1⟩ := exists_cosetSection π.ker
  obtain ⟨R, hR, hRle, haR, hbR⟩ : ∃ R : Subgroup G, IsOpenNormal R ∧ R ≤ π.ker ∧
      (∀ x y : G, ∀ n ∈ R, ∀ m ∈ R, a (x * n, y * m) = a (x, y)) ∧
      (∀ g : G, ∀ n ∈ R, b (g * n) = b g) := by
    obtain ⟨N₁, hN₁, ha₁⟩ := has
    obtain ⟨N₂, hN₂, hb₁⟩ := hbs
    exact ⟨N₁ ⊓ N₂ ⊓ K, (hN₁.inf hN₂).inf hK, fun x hx => hKle hx.2,
      fun x y n hn m hm => ha₁ x y n hn.1.1 m hm.1.1, fun g n hn => hb₁ g n hn.1.2⟩
  obtain ⟨u₁, h₁, hi₁⟩ := exists_twist_eq_one_on_subgroup hb
  obtain ⟨u₂, h₂, hi₂⟩ :=
    exists_twist_eq_one_of_mem_left_of_section hs hsc hs1 (isMulCocycle₂_twist ha u₁) h₁
  rw [twist_twist] at h₂
  have hu₁R : ∀ g : G, ∀ n ∈ R, u₁ (g * n) = u₁ g := hi₁ R hRle hbR
  have hu₂R : ∀ g : G, ∀ n ∈ R, u₂ (g * n) = u₂ g :=
    hi₂ R hRle hR.normal fun x y n hn m hm =>
      twist_eq_of_mem hR.normal (fun n hn => htriv n (hRle hn)) haR hu₁R x y hn hm
  have hu₁₂R : ∀ g : G, ∀ n ∈ R, (u₁ * u₂) (g * n) = (u₁ * u₂) g := by
    intro g n hn
    simp only [Pi.mul_apply, hu₁R g n hn, hu₂R g n hn]
  exact ⟨twist a (u₁ * u₂), isMulCocycle₂_twist ha (u₁ * u₂),
    ⟨R, hR, fun x y n hn m hm =>
      twist_eq_of_mem hR.normal (fun n hn => htriv n (hRle hn)) haR hu₁₂R x y hn hm⟩,
    smoothH2Mk_twist ha has ⟨R, hR, hu₁₂R⟩ _, h₂⟩

end Normalise

/-! ### Inflation after a map of the coefficients -/

section Package

variable {G Q M M' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group Q]
  [TopologicalSpace Q] [DiscreteTopology Q] [CommGroup M] [CommGroup M']
  [MulDistribMulAction G M] [MulDistribMulAction G M'] [MulDistribMulAction Q M']
variable {π : G →* Q} (hπ' : ∀ (g : G) (m : M'), g • m = π g • m)

/-- **A homomorphism of the coefficients which kills the class of every everywhere locally trivial
transgression carries an everywhere locally trivial class of the second cohomology into the image of
inflation.**  The class is represented by a cocycle trivial in the first variable along the kernel;
its transgression is everywhere locally trivial, so the homomorphism kills its class; and the pushed
forward transgression class is the transgression class of any normalised cocycle representing the
pushed forward class, since the transgression class depends only on the cohomology class.  Nothing
is asked of the obstruction group itself, only that the map of coefficients annihilate the part of
it which is everywhere locally trivial. -/
theorem exists_comapH2_eq_coeffH2_of_localTransClass (hbasis : HasOpenNormalBasis G)
    (hsm : IsSmoothHom π) (hsurj : Function.Surjective π)
    (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m) (htriv' : ∀ n ∈ π.ker, ∀ m : M', n • m = m)
    (φ : M →* M') (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a) {b : G → M} (hbs : IsSmooth₁ b)
    (hb : ∀ x ∈ π.ker, ∀ y ∈ π.ker, a (x, y) = x • b y / b (x * y) * b x)
    {S : Set (Subgroup G)} (hmem : smoothH2Mk a ha has ∈ sha2 M S)
    (hkill : ∀ (t : G → G → M) (h : IsTransgressionDatum π.ker M t),
      (∀ D ∈ S, localTransClass h htriv (isOpenNormal_ker_of_isSmoothHom hsm).isOpen D = 1) →
        coeffTransH1 π.ker φ hφ
          (transClass h htriv (isOpenNormal_ker_of_isSmoothHom hsm).isOpen) = 1) :
    ∃ x : SmoothH2 Q M', comapH2 π hπ' hsm x = coeffH2 φ hφ (smoothH2Mk a ha has) := by
  have hop := (isOpenNormal_ker_of_isSmoothHom hsm).isOpen
  obtain ⟨c, hc, hcs, hccl, h1⟩ := exists_eq_one_on_ker hsm htriv ha has hbs hb
  have h1' : ∀ n ∈ π.ker, ∀ y : G, coeffMap₂ φ c (n, y) = 1 := by
    intro n hn y
    show φ (c (n, y)) = 1
    rw [h1 n hn y, _root_.map_one]
  have hmemc : smoothH2Mk c hc hcs ∈ sha2 M S := by rw [hccl]; exact hmem
  have hkey : coeffTransH1 π.ker φ hφ (transgressionClass htriv hop hc hcs h1) = 1 :=
    hkill _ (isTransgressionDatum_transgression htriv hc hcs h1) fun D hD =>
      localTransClass_transgression_eq_one htriv hop hc hcs h1
        ((smoothH2Mk_mem_sha2 hc hcs).1 hmemc D hD)
  rw [coeffH2_smoothH2Mk]
  refine exists_comapH2_eq_of_transgression hπ' hsm hsurj htriv'
    (isMulCocycle₂_coeffMap₂ φ hφ ha) (has.coeffMap₂ φ) (hbs.coeffMap₁ φ) ?_ ?_
  · intro x hx y hy
    show φ (a (x, y)) = x • φ (b y) / φ (b (x * y)) * φ (b x)
    rw [hb x hx y hy, _root_.map_mul, _root_.map_div, hφ]
  · intro d hd hds hdcl hd1
    refine exists_eq_smul_div_of_transClass_eq_one hbasis
      (isTransgressionDatum_transgression htriv' hd hds hd1) htriv' hop ?_
    have hcoh : smoothH2Mk d hd hds
        = smoothH2Mk (coeffMap₂ φ c) (isMulCocycle₂_coeffMap₂ φ hφ hc) (hcs.coeffMap₂ φ) := by
      rw [hdcl, ← coeffH2_smoothH2Mk φ hφ ha has, ← hccl, coeffH2_smoothH2Mk]
    show transgressionClass htriv' hop hd hds hd1 = 1
    rw [transgressionClass_congr htriv' hop hd hds hd1 (isMulCocycle₂_coeffMap₂ φ hφ hc)
        (hcs.coeffMap₂ φ) h1' hcoh,
      transgressionClass_coeffMap₂ φ hφ htriv htriv' hop hc hcs h1 h1']
    exact hkey

/-- **A homomorphism of the coefficients which kills the everywhere locally trivial obstructions
carries an everywhere locally trivial class of the second cohomology into the image of inflation.**
The class of a transgression whose localisations all vanish is one of those obstructions. -/
theorem exists_comapH2_eq_coeffH2_of_sha1Loc (hbasis : HasOpenNormalBasis G) (hsm : IsSmoothHom π)
    (hsurj : Function.Surjective π) (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m)
    (htriv' : ∀ n ∈ π.ker, ∀ m : M', n • m = m) (φ : M →* M')
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a) {b : G → M} (hbs : IsSmooth₁ b)
    (hb : ∀ x ∈ π.ker, ∀ y ∈ π.ker, a (x, y) = x • b y / b (x * y) * b x)
    {S : Set (Subgroup G)} (hmem : smoothH2Mk a ha has ∈ sha2 M S)
    (hkill : ∀ z ∈ sha1Loc M π.ker S, coeffTransH1 π.ker φ hφ z = 1) :
    ∃ x : SmoothH2 Q M', comapH2 π hπ' hsm x = coeffH2 φ hφ (smoothH2Mk a ha has) :=
  exists_comapH2_eq_coeffH2_of_localTransClass hπ' hbasis hsm hsurj htriv htriv' φ hφ ha has hbs hb
    hmem fun _ h hloc => hkill _ ((transClass_mem_sha1Loc_iff h htriv _).2 hloc)

/-- **A homomorphism of the coefficients which kills the everywhere locally trivial obstructions
read at the level of the quotient carries an everywhere locally trivial class of the second
cohomology into the image of inflation.**  The class of a transgression is inflated from the
quotient, and the class it is inflated from is everywhere locally trivial there as soon as all the
localisations vanish; so only the inflated obstructions have to be annihilated, and those form a
group attached to the quotient alone. -/
theorem exists_comapH2_eq_coeffH2_of_sha1Level (hbasis : HasOpenNormalBasis G)
    (hsm : IsSmoothHom π) (hsurj : Function.Surjective π)
    (htriv : ∀ n ∈ π.ker, ∀ m : M, n • m = m) (htriv' : ∀ n ∈ π.ker, ∀ m : M', n • m = m)
    (φ : M →* M') (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a) {b : G → M} (hbs : IsSmooth₁ b)
    (hb : ∀ x ∈ π.ker, ∀ y ∈ π.ker, a (x, y) = x • b y / b (x * y) * b x)
    {S : Set (Subgroup G)} (hmem : smoothH2Mk a ha has ∈ sha2 M S)
    (hkill : ∀ x ∈ sha1Level M π.ker (isOpenNormal_ker_of_isSmoothHom hsm).isOpen S,
      coeffTransH1 π.ker φ hφ
        (inflH1 π.ker (SmoothH1 ↥π.ker M) (isOpenNormal_ker_of_isSmoothHom hsm).isOpen x) = 1) :
    ∃ x : SmoothH2 Q M', comapH2 π hπ' hsm x = coeffH2 φ hφ (smoothH2Mk a ha has) := by
  have hop := (isOpenNormal_ker_of_isSmoothHom hsm).isOpen
  refine exists_comapH2_eq_coeffH2_of_localTransClass hπ' hbasis hsm hsurj htriv htriv' φ hφ
    ha has hbs hb hmem fun t h hloc => ?_
  obtain ⟨x, hx⟩ := exists_inflH1_transClass h htriv hop
  have hmemx : x ∈ sha1Level M π.ker hop S := by
    refine mem_sha1Level.2 fun D hD => ?_
    rw [hx, resCoeffH1_transClass]
    exact hloc D hD
  rw [← hx]
  exact hkill x hmemx

end Package

/-! ### The map of the coefficients at the level of the quotient -/

section Level

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M M' : Type*} [CommGroup M] [CommGroup M'] [MulDistribMulAction G M]
  [MulDistribMulAction G M']
variable {N : Subgroup G} [hN : N.Normal]
variable (φ : M →* M') (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)

/-- **A homomorphism of the coefficients commutes with the action of the quotient on the first
cohomology of a normal subgroup**, that action being the one the ambient group induces. -/
theorem coeffH1_quotient_smul (q : G ⧸ N) (z : SmoothH1 ↥N M) :
    coeffH1 φ (fun (g : ↥N) m => hφ (g : G) m) (q • z)
      = q • coeffH1 φ (fun (g : ↥N) m => hφ (g : G) m) z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [quotientMk_smul, quotientMk_smul]
  exact coeffH1_conj φ hφ g z

variable (N) in
/-- **The map of the first cohomology of the quotient with values in the first cohomology of a
normal subgroup induced by an equivariant homomorphism of the coefficients**, the same construction
as over the ambient group but read at the level. -/
def coeffQuotTransH1 :
    SmoothH1 (G ⧸ N) (SmoothH1 ↥N M) →* SmoothH1 (G ⧸ N) (SmoothH1 ↥N M') :=
  coeffH1 (coeffH1 φ fun (g : ↥N) m => hφ (g : G) m) (coeffH1_quotient_smul φ hφ)

variable (N) in
/-- **Pushing the coefficients forward commutes with inflation from the level**, so the obstruction
attached to a class inflated from the quotient is itself inflated from the quotient. -/
theorem coeffTransH1_inflH1 (hop : IsOpen (N : Set G))
    (x : SmoothH1 (G ⧸ N) (SmoothH1 ↥N M)) :
    coeffTransH1 N φ hφ (inflH1 N (SmoothH1 ↥N M) hop x)
      = inflH1 N (SmoothH1 ↥N M') hop (coeffQuotTransH1 N φ hφ x) :=
  (comapH1_coeffH1 (QuotientGroup.mk' N) (fun _ _ => rfl) (fun _ _ => rfl)
    (isSmoothHom_mk' N hop) _ (coeffH1_quotient_smul φ hφ) (coeffH1_conj φ hφ) x).symm

variable (N) in
/-- **The obstruction attached to a class of the level is trivial exactly when it is trivial at the
level**, inflation being injective in the first cohomology. -/
theorem coeffTransH1_inflH1_eq_one_iff (hop : IsOpen (N : Set G))
    (x : SmoothH1 (G ⧸ N) (SmoothH1 ↥N M)) :
    coeffTransH1 N φ hφ (inflH1 N (SmoothH1 ↥N M) hop x) = 1
      ↔ coeffQuotTransH1 N φ hφ x = 1 := by
  rw [coeffTransH1_inflH1 N φ hφ hop x, ← _root_.map_one (inflH1 N (SmoothH1 ↥N M') hop)]
  exact (inflH1_injective N (SmoothH1 ↥N M') hop).eq_iff

end Level

end InverseGalois.CFT
