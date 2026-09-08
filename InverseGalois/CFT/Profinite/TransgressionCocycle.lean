/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.TransgressionRestrict

/-!
# The transgression class of a cocycle trivial along a normal subgroup

The descent theorems of the previous files quantify over an abstract transgression: a family of maps
of the group into the coefficients satisfying four conditions.  The transgression of an honest two
cocycle which is trivial in the first variable along an open normal subgroup is such a family, and
the class it defines is therefore attached to the cocycle itself.

Two facts make that class usable.  The first is that it depends only on the cohomology class of the
cocycle: if two normalised cocycles are cohomologous, the cochain joining them is a homomorphism
along the subgroup, because the two cocycles are both trivial there, and the two transgressions
differ by exactly the coboundary of the class of that homomorphism.  The second is that the class is
everywhere locally trivial as soon as the class of the cocycle is: over a subgroup along which the
cocycle is a coboundary the transgression is the coboundary of the trivialising cochain, which on
the part of the normal subgroup lying inside is a smooth homomorphism.

Together they say that the transgression is a well defined map from the everywhere locally trivial
classes of the second cohomology to the everywhere locally trivial classes of the first cohomology
with values in the first cohomology of the subgroup — the obstruction to inflating, read as a class
rather than as a chosen list of properties of a chosen function.

## Main definitions

* `InverseGalois.CFT.transgressionClass`: **the class of the transgression of a smooth two cocycle
  trivial in the first variable along a normal subgroup.**

## Main results

* `InverseGalois.CFT.isTransgressionDatum_transgression`: the transgression of such a cocycle is a
  transgression in the abstract sense.
* `InverseGalois.CFT.transClass_eq_of_eq_smul_div`: two transgressions differing by the coboundary
  of a smooth homomorphism have the same class.
* `InverseGalois.CFT.transgressionClass_congr`: **the transgression class depends only on the
  cohomology class of the cocycle.**
* `InverseGalois.CFT.transgressionClass_mem_sha1Loc`: **the transgression class of an everywhere
  locally trivial class is everywhere locally trivial.**

## Tags

profinite group, Galois cohomology, transgression, inflation, local-global principle
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### The transgression of a normalised cocycle is a transgression -/

section Datum

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]
variable {N : Subgroup G} [N.Normal] {c : G × G → M}

/-- **The transgression of a smooth two cocycle which is trivial in the first variable along a
normal subgroup acting trivially satisfies the four conditions of a transgression.**  Smoothness is
inherited from the cocycle, the subgroup being normal so that conjugation preserves the open normal
subgroup along which the cocycle is constant. -/
theorem isTransgressionDatum_transgression (htriv : ∀ n ∈ N, ∀ m : M, n • m = m)
    (hc : IsMulCocycle₂ c) (hcs : IsSmooth₂ c) (h1 : ∀ n ∈ N, ∀ y : G, c (n, y) = 1) :
    IsTransgressionDatum N M (transgression c) where
  isSmooth := by
    obtain ⟨R, hR, hcR⟩ := hcs
    refine ⟨R, hR, fun σ x n hn => ?_⟩
    have hconj : σ⁻¹ * n * σ ∈ R := by simpa using hR.normal.conj_mem n hn σ⁻¹
    have h := hcR σ (σ⁻¹ * x * σ) 1 R.one_mem _ hconj
    rw [mul_one] at h
    rw [transgression_apply, transgression_apply,
      show σ⁻¹ * (x * n) * σ = σ⁻¹ * x * σ * (σ⁻¹ * n * σ) by group]
    exact h
  map_mul σ x hx y hy := transgression_mul_mem htriv hc h1 σ hx hy
  cocycle σ τ x hx := transgression_mul_left htriv hc h1 σ τ hx
  smul_left n hn σ x hx := transgression_smul_left htriv hc h1 hn σ hx

end Datum

/-! ### Two transgressions differing by a coboundary -/

section Congr

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]
variable {N : Subgroup G} [hN : N.Normal] {t t' : G → G → M}

/-- **Two transgressions which differ by the coboundary of a smooth homomorphism on the subgroup
have the same class.**  The homomorphism is a one cocycle of the subgroup for the trivial action,
and the pointwise quotient of the two transgressions is the coboundary of its class. -/
theorem transClass_eq_of_eq_smul_div (h : IsTransgressionDatum N M t)
    (h' : IsTransgressionDatum N M t') (htriv : ∀ n ∈ N, ∀ m : M, n • m = m)
    (hop : IsOpen (N : Set G)) {v : G → M} (hvs : IsSmooth₁ fun x : ↥N => v (x : G))
    (hvm : ∀ x ∈ N, ∀ y ∈ N, v (x * y) = v x * v y)
    (hv : ∀ σ : G, ∀ x ∈ N, t σ x = σ • v (σ⁻¹ * x * σ) / v x * t' σ x) :
    transClass h htriv hop = transClass h' htriv hop := by
  have hvc : IsMulCocycle₁ (fun x : ↥N => v (x : G)) := by
    intro x y
    have hx : (x : ↥N) • v (y : G) = v (y : G) := htriv (x : G) x.2 _
    show v ((x : G) * (y : G)) = (x : ↥N) • v (y : G) * v (x : G)
    rw [hx, hvm (x : G) x.2 (y : G) y.2, mul_comm]
  rw [transClass, transClass, smoothH1Mk_eq_iff]
  refine ⟨smoothH1Mk (fun x : ↥N => v (x : G)) hvc hvs, funext fun σ => ?_⟩
  rw [smul_eq_conjH1, conjH1_smoothH1Mk, transCochain_apply, transCochain_apply,
    div_eq_div_iff_mul_eq_mul, ← smoothH1Mk_mul, ← smoothH1Mk_mul]
  refine smoothH1Mk_congr (funext fun x => ?_) _ _ _ _
  show σ • v (σ⁻¹ * (x : G) * σ) * t' σ (x : G) = t σ (x : G) * v (x : G)
  rw [hv σ (x : G) x.2]
  apply Additive.ofMul.injective
  simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
  abel

end Congr

/-! ### The class of the transgression of a cocycle -/

section Class

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]
variable {N : Subgroup G} [hN : N.Normal]

/-- **The class of the transgression of a smooth two cocycle which is trivial in the first variable
along an open normal subgroup**, in the first cohomology of the group with values in the first
cohomology of that subgroup. -/
def transgressionClass (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (hop : IsOpen (N : Set G))
    {c : G × G → M} (hc : IsMulCocycle₂ c) (hcs : IsSmooth₂ c)
    (h1 : ∀ n ∈ N, ∀ y : G, c (n, y) = 1) : SmoothH1 G (SmoothH1 ↥N M) :=
  transClass (isTransgressionDatum_transgression htriv hc hcs h1) htriv hop

/-- **The transgression class depends only on the cohomology class of the cocycle.**  A cochain
joining two normalised cocycles is a homomorphism along the subgroup, both cocycles being trivial
there, and the two transgressions differ by the coboundary of the class of that homomorphism. -/
theorem transgressionClass_congr (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (hop : IsOpen (N : Set G))
    {c c' : G × G → M} (hc : IsMulCocycle₂ c) (hcs : IsSmooth₂ c)
    (h1 : ∀ n ∈ N, ∀ y : G, c (n, y) = 1) (hc' : IsMulCocycle₂ c') (hcs' : IsSmooth₂ c')
    (h1' : ∀ n ∈ N, ∀ y : G, c' (n, y) = 1)
    (heq : smoothH2Mk c hc hcs = smoothH2Mk c' hc' hcs') :
    transgressionClass htriv hop hc hcs h1 = transgressionClass htriv hop hc' hcs' h1' := by
  obtain ⟨v, hvs, hv⟩ := (smoothH2Mk_eq_iff hc hcs hc' hcs').1 heq
  have hvN : ∀ n ∈ N, ∀ y : G, v (n * y) = v y * v n := by
    intro n hn y
    have h : n • v y / v (n * y) * v n = c (n, y) / c' (n, y) := congrFun hv (n, y)
    rw [h1 n hn y, h1' n hn y, div_self', htriv n hn, div_mul_eq_mul_div, div_eq_one] at h
    exact h.symm
  have hvm : ∀ x ∈ N, ∀ y ∈ N, v (x * y) = v x * v y := fun x hx y _ => by
    rw [hvN x hx y, mul_comm]
  have hkey : ∀ σ : G, ∀ x ∈ N,
      transgression c σ x = σ • v (σ⁻¹ * x * σ) / v x * transgression c' σ x := by
    intro σ x hx
    have h : σ • v (σ⁻¹ * x * σ) / v (σ * (σ⁻¹ * x * σ)) * v σ
        = c (σ, σ⁻¹ * x * σ) / c' (σ, σ⁻¹ * x * σ) := congrFun hv (σ, σ⁻¹ * x * σ)
    rw [show σ * (σ⁻¹ * x * σ) = x * σ by group, hvN x hx σ] at h
    have hL : σ • v (σ⁻¹ * x * σ) / (v σ * v x) * v σ = σ • v (σ⁻¹ * x * σ) / v x := by
      apply Additive.ofMul.injective
      simp only [div_eq_mul_inv, mul_inv, ofMul_mul, ofMul_inv]
      abel
    rw [transgression_apply, transgression_apply]
    exact div_eq_iff_eq_mul.1 (h.symm.trans hL)
  exact transClass_eq_of_eq_smul_div _ _ htriv hop
    (isSmooth₁_comp (continuous_subtype N) hvs) hvm hkey

end Class

/-! ### The transgression class of a locally trivial class -/

section Local

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]
variable {N : Subgroup G} [hN : N.Normal]

/-- **Over a subgroup along which the cocycle is a coboundary the transgression class vanishes.**
The trivialising cochain is extended by the unit outside the subgroup; on the part of the normal
subgroup lying inside it is a smooth homomorphism, the cocycle being trivial along the normal
subgroup, and the transgression is its coboundary there. -/
theorem localTransClass_transgression_eq_one (htriv : ∀ n ∈ N, ∀ m : M, n • m = m)
    (hop : IsOpen (N : Set G)) {c : G × G → M} (hc : IsMulCocycle₂ c) (hcs : IsSmooth₂ c)
    (h1 : ∀ n ∈ N, ∀ y : G, c (n, y) = 1) {D : Subgroup G}
    (hD : ∃ d : ↥D → M, IsSmooth₁ d ∧ coboundary₂ d = comap₂ D.subtype c) :
    localTransClass (isTransgressionDatum_transgression htriv hc hcs h1) htriv hop D = 1 := by
  classical
  obtain ⟨d, hds, hd⟩ := hD
  obtain ⟨d', hd'mem⟩ : ∃ d' : G → M, ∀ g (hg : g ∈ D), d' g = d ⟨g, hg⟩ :=
    ⟨fun g => if hg : g ∈ D then d ⟨g, hg⟩ else 1, fun g hg => dif_pos hg⟩
  have hdcob : ∀ x ∈ D, ∀ y ∈ D, c (x, y) = x • d' y / d' (x * y) * d' x := by
    intro x hx y hy
    have h := congrFun hd (⟨x, hx⟩, ⟨y, hy⟩)
    rw [coboundary₂_apply] at h
    rw [hd'mem x hx, hd'mem y hy, hd'mem _ (D.mul_mem hx hy)]
    exact h.symm
  have hd'sm : IsSmooth₁ fun x : ↥(D ⊓ N) => d' (x : G) := by
    have heq : (fun x : ↥(D ⊓ N) => d' (x : G))
        = fun x : ↥(D ⊓ N) => d (Subgroup.inclusion (inf_le_left : D ⊓ N ≤ D) x) :=
      funext fun x => hd'mem _ x.2.1
    rw [heq]
    exact isSmooth₁_comp_inclusion (D ⊓ N) inf_le_left hds
  exact localTransClass_eq_one _ htriv hop D hd'sm
    (fun _ hx _ hy => map_mul_of_eq_coboundary htriv h1 hdcob hx.1 hx.2 hy.1)
    fun _ hσ _ hxD hxN => transgression_eq_smul_div_of_eq_coboundary htriv h1 hdcob hσ hxD hxN

/-- **The transgression class of an everywhere locally trivial class is everywhere locally
trivial.**  This is the obstruction to inflating, as a class of the first cohomology of the group
with values in the first cohomology of the subgroup which is trivial at every member of the
family. -/
theorem transgressionClass_mem_sha1Loc (htriv : ∀ n ∈ N, ∀ m : M, n • m = m)
    (hop : IsOpen (N : Set G)) {c : G × G → M} (hc : IsMulCocycle₂ c) (hcs : IsSmooth₂ c)
    (h1 : ∀ n ∈ N, ∀ y : G, c (n, y) = 1) {S : Set (Subgroup G)}
    (hmem : smoothH2Mk c hc hcs ∈ sha2 M S) :
    transgressionClass htriv hop hc hcs h1 ∈ sha1Loc M N S :=
  (transClass_mem_sha1Loc_iff _ htriv hop).2 fun D hD =>
    localTransClass_transgression_eq_one htriv hop hc hcs h1
      ((smoothH2Mk_mem_sha2 hc hcs).1 hmem D hD)

end Local

end InverseGalois.CFT
