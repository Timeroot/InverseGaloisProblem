/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Two-cocycles over a subgroup of index two

Let `G` be a group, `N` a normal subgroup with two cosets, and `M` an abelian group on which `G`
acts by automorphisms.  A two-cocycle of `G` with values in `M` whose restriction to `N` is a
coboundary is, provided the first cohomology of `N` vanishes, the product of a coboundary of `G`
with the very simple cocycle which takes a single `G`-invariant value `c` at the pairs of elements
outside `N` and the value one elsewhere.  That cocycle is the inflation to `G` of the standard
two-cocycle of the cyclic group of order two, so the statement is the inflation-restriction
sequence in degree two for a subgroup of index two, in the concrete language of cochains.

The trivialisation is obtained in three explicit steps, each correcting the cocycle by the
coboundary of a one-cochain: first the restriction to `N × N` is made trivial, then the value at a
pair whose first entry lies in `N`, then the value at a pair whose second entry lies in `N`.  Only
the third step uses the vanishing of the first cohomology of `N`.

In the other direction the inflated cocycle is a coboundary exactly when its value is a norm from
the invariants of `N`, which for a quadratic extension of fields is the classical description of
the relative Brauer group as the quotient of the base field by the group of norms.

## Main definitions

* `InverseGalois.CFT.coboundary₂`: the coboundary of a one-cochain, as a two-cochain.
* `InverseGalois.CFT.twist`: dividing a two-cochain by the coboundary of a one-cochain.
* `InverseGalois.CFT.indexTwoInflation`: the two-cochain taking the value `c` at a pair of
  elements both outside a subgroup and the value one elsewhere.

## Main results

* `InverseGalois.CFT.exists_twist_eq_indexTwoInflation`: a two-cocycle whose restriction to a
  normal subgroup with two cosets is a coboundary becomes, after correction by a coboundary, the
  inflation of a single `G`-invariant value.
* `InverseGalois.CFT.exists_smul_mul_eq_of_isMulCoboundary₂_indexTwoInflation`: an inflated
  cocycle which is a coboundary has its value a norm from the invariants of the subgroup.
* `InverseGalois.CFT.isMulCoboundary₂_indexTwoInflation`: conversely, the inflation of a norm from
  the invariants of the subgroup is a coboundary.

## Tags

group cohomology, two-cocycle, coboundary, inflation, restriction, index two
-/

open groupCohomology

namespace InverseGalois.CFT

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-! ### Coboundaries and twisting -/

/-- The coboundary of a one-cochain `u`, as a two-cochain.  A two-cochain is a multiplicative
two-coboundary exactly when it is of this form. -/
def coboundary₂ (u : G → M) : G × G → M := fun p => p.1 • u p.2 / u (p.1 * p.2) * u p.1

theorem coboundary₂_apply (u : G → M) (x y : G) :
    coboundary₂ u (x, y) = x • u y / u (x * y) * u x := rfl

theorem isMulCoboundary₂_iff {f : G × G → M} :
    IsMulCoboundary₂ f ↔ ∃ u : G → M, coboundary₂ u = f :=
  ⟨fun ⟨u, hu⟩ => ⟨u, funext fun p => hu p.1 p.2⟩,
    fun ⟨u, hu⟩ => ⟨u, fun x y => congrFun hu (x, y)⟩⟩

theorem coboundary₂_mul (u v : G → M) : coboundary₂ (u * v) = coboundary₂ u * coboundary₂ v := by
  funext p
  simp only [coboundary₂, Pi.mul_apply, smul_mul', div_eq_mul_inv, mul_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem coboundary₂_one : coboundary₂ (1 : G → M) = 1 := by
  funext p
  simp [coboundary₂]

theorem coboundary₂_inv (u : G → M) : coboundary₂ u⁻¹ = (coboundary₂ u)⁻¹ := by
  have h := coboundary₂_mul u u⁻¹
  rw [mul_inv_cancel, coboundary₂_one] at h
  rw [eq_comm, inv_eq_iff_mul_eq_one]
  exact h.symm

/-- The coboundary of the one-cochain attached to a single element of `M` is trivial. -/
theorem coboundary₂_smul_div (t : M) : coboundary₂ (fun g : G => g • t / t) = 1 := by
  funext p
  simp only [coboundary₂, Pi.one_apply, div_eq_mul_inv, smul_mul', smul_inv', smul_smul, mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem isMulCocycle₂_coboundary₂ (u : G → M) : IsMulCocycle₂ (coboundary₂ u) := by
  intro g h j
  simp only [coboundary₂, smul_mul', smul_inv', mul_smul, div_eq_mul_inv, mul_assoc g h j]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- Dividing a two-cochain by the coboundary of a one-cochain. -/
def twist (a : G × G → M) (u : G → M) : G × G → M := fun p => a p / coboundary₂ u p

theorem twist_apply (a : G × G → M) (u : G → M) (x y : G) :
    twist a u (x, y) = a (x, y) / (x • u y / u (x * y) * u x) := rfl

theorem twist_twist (a : G × G → M) (u v : G → M) : twist (twist a u) v = twist a (u * v) := by
  funext p
  simp [twist, coboundary₂_mul, div_div]

theorem eq_twist_mul_coboundary₂ (a : G × G → M) (u : G → M) (p : G × G) :
    a p = twist a u p * coboundary₂ u p := by
  simp [twist]

theorem isMulCocycle₂_twist {a : G × G → M} (ha : IsMulCocycle₂ a) (u : G → M) :
    IsMulCocycle₂ (twist a u) := by
  intro g h j
  have hb := isMulCocycle₂_coboundary₂ u g h j
  have hc := ha g h j
  simp only [twist, div_eq_mul_inv, smul_mul', smul_inv']
  rw [show a (g * h, j) * (coboundary₂ u (g * h, j))⁻¹ * (a (g, h) * (coboundary₂ u (g, h))⁻¹)
      = a (g * h, j) * a (g, h) * (coboundary₂ u (g * h, j) * coboundary₂ u (g, h))⁻¹ by
    simp [mul_comm, mul_left_comm, mul_assoc],
    show g • a (h, j) * (g • coboundary₂ u (h, j))⁻¹ *
        (a (g, h * j) * (coboundary₂ u (g, h * j))⁻¹)
      = g • a (h, j) * a (g, h * j) *
        (g • coboundary₂ u (h, j) * coboundary₂ u (g, h * j))⁻¹ by
    simp [mul_comm, mul_left_comm, mul_assoc], hc, hb]

/-! ### The inflated cocycle -/

open Classical in
/-- The two-cochain of `G` which takes the value `c` at a pair of elements both outside the
subgroup `N` and the value one elsewhere.  When `N` is normal with two cosets and `c` is
`G`-invariant this is the inflation of the standard two-cocycle of the cyclic group of order
two. -/
noncomputable def indexTwoInflation (N : Subgroup G) (c : M) : G × G → M :=
  fun p => if p.1 ∈ N ∨ p.2 ∈ N then 1 else c

variable {N : Subgroup G}

omit [MulDistribMulAction G M] in
theorem indexTwoInflation_of_mem_left {c : M} {x y : G} (hx : x ∈ N) :
    indexTwoInflation N c (x, y) = 1 := by
  simp [indexTwoInflation, hx]

omit [MulDistribMulAction G M] in
theorem indexTwoInflation_of_mem_right {c : M} {x y : G} (hy : y ∈ N) :
    indexTwoInflation N c (x, y) = 1 := by
  simp [indexTwoInflation, hy]

omit [MulDistribMulAction G M] in
theorem indexTwoInflation_of_not_mem {c : M} {x y : G} (hx : x ∉ N) (hy : y ∉ N) :
    indexTwoInflation N c (x, y) = c := by
  simp [indexTwoInflation, hx, hy]

/-! ### Cosets -/

variable {σ : G}

theorem mul_self_mem_of_two_cosets (hcov : ∀ g : G, g ∈ N ∨ g * σ⁻¹ ∈ N) (hσ : σ ∉ N) :
    σ * σ ∈ N := by
  rcases hcov (σ * σ) with h | h
  · exact h
  · rw [mul_inv_cancel_right] at h
    exact absurd h hσ

theorem mul_mem_of_not_mem_of_not_mem [N.Normal] (hcov : ∀ g : G, g ∈ N ∨ g * σ⁻¹ ∈ N)
    (hσ : σ ∉ N) {x y : G} (hx : x ∉ N) (hy : y ∉ N) : x * y ∈ N := by
  have hx' : x * σ⁻¹ ∈ N := (hcov x).resolve_left hx
  have hy' : y * σ⁻¹ ∈ N := (hcov y).resolve_left hy
  have hrw : x * y = x * σ⁻¹ * (σ * (y * σ⁻¹) * σ⁻¹) * (σ * σ) := by group
  rw [hrw]
  exact mul_mem (mul_mem hx' (‹N.Normal›.conj_mem _ hy' σ)) (mul_self_mem_of_two_cosets hcov hσ)

theorem not_mem_mul_of_mem_of_not_mem {n y : G} (hn : n ∈ N) (hy : y ∉ N) : n * y ∉ N := fun h =>
  hy (by simpa using mul_mem (inv_mem hn) h)

theorem not_mem_mul_of_not_mem_of_mem {x n : G} (hx : x ∉ N) (hn : n ∈ N) : x * n ∉ N := fun h =>
  hx (by simpa using mul_mem h (inv_mem hn))

/-! ### Normalising a cocycle -/

/-- If a two-cocycle is trivial at every pair whose first entry lies in `N`, then its value at a
pair whose first entry is the product of an element of `N` with `g` is the translate of its value
at `g`. -/
theorem smul_apply_of_mem_left {a : G × G → M} (ha : IsMulCocycle₂ a)
    (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) {n : G} (hn : n ∈ N) (g y : G) :
    a (n * g, y) = n • a (g, y) := by
  have h := ha n g y
  rwa [h1 n hn g, h1 n hn (g * y), mul_one, mul_one] at h

/-- The first normalisation: a two-cocycle whose restriction to `N` is a coboundary becomes, after
a twist, trivial on `N × N`. -/
theorem exists_twist_eq_one_on_subgroup {a : G × G → M}
    (hres : ∃ b : G → M, ∀ x ∈ N, ∀ y ∈ N, a (x, y) = x • b y / b (x * y) * b x) :
    ∃ u : G → M, ∀ x ∈ N, ∀ y ∈ N, twist a u (x, y) = 1 := by
  classical
  obtain ⟨b, hb⟩ := hres
  refine ⟨fun g => if g ∈ N then b g else 1, fun x hx y hy => ?_⟩
  have hxy : x * y ∈ N := mul_mem hx hy
  simp only [twist, coboundary₂, if_pos hx, if_pos hy, if_pos hxy]
  rw [← hb x hx y hy, div_self']

/-- The second normalisation: a two-cocycle trivial on `N × N` becomes, after a twist, trivial at
every pair whose first entry lies in `N`. -/
theorem exists_twist_eq_one_of_mem_left (hcov : ∀ g : G, g ∈ N ∨ g * σ⁻¹ ∈ N)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (h0 : ∀ x ∈ N, ∀ y ∈ N, a (x, y) = 1) :
    ∃ u : G → M, ∀ n ∈ N, ∀ y : G, twist a u (n, y) = 1 := by
  classical
  obtain ⟨u, huN, huout⟩ : ∃ u : G → M, (∀ g ∈ N, u g = 1) ∧
      (∀ g ∉ N, u g = (a (g * σ⁻¹, σ))⁻¹) :=
    ⟨fun g => if g ∈ N then 1 else (a (g * σ⁻¹, σ))⁻¹, fun g hg => if_pos hg,
      fun g hg => if_neg hg⟩
  refine ⟨u, fun n hn y => ?_⟩
  rw [twist_apply, huN n hn, mul_one]
  by_cases hy : y ∈ N
  · rw [huN y hy, huN _ (mul_mem hn hy), h0 n hn y hy, smul_one, div_one, div_self']
  · have hny : n * y ∉ N := not_mem_mul_of_mem_of_not_mem hn hy
    have hyσ : y * σ⁻¹ ∈ N := (hcov y).resolve_left hy
    have key : a (n * (y * σ⁻¹), σ) = n • a (y * σ⁻¹, σ) * a (n, y) := by
      have h := ha n (y * σ⁻¹) σ
      rwa [h0 n hn _ hyσ, mul_one, inv_mul_cancel_right] at h
    rw [huout y hy, huout _ hny, show n * y * σ⁻¹ = n * (y * σ⁻¹) by group, key, smul_inv',
      div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

/-- The third normalisation: a two-cocycle trivial at every pair whose first entry lies in `N`
becomes, after a twist, trivial also at every pair whose second entry lies in `N`.  This is the
step which consumes the vanishing of the first cohomology of `N`. -/
theorem exists_twist_eq_one_of_mem [N.Normal] (hσ : σ ∉ N)
    (hcov : ∀ g : G, g ∈ N ∨ g * σ⁻¹ ∈ N)
    (hH1 : ∀ f : G → M, (∀ x ∈ N, ∀ y ∈ N, f (x * y) = x • f y * f x) →
      ∃ t : M, ∀ x ∈ N, x • t / t = f x)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) :
    ∃ u : G → M, (∀ n ∈ N, ∀ y : G, twist a u (n, y) = 1) ∧
      (∀ x : G, ∀ n ∈ N, twist a u (x, n) = 1) := by
  classical
  have hFcoc : ∀ x ∈ N, ∀ y ∈ N,
      a (σ, σ⁻¹ * (x * y) * σ) = x • a (σ, σ⁻¹ * y * σ) * a (σ, σ⁻¹ * x * σ) := by
    intro x hx y hy
    have hp : σ⁻¹ * x * σ ∈ N := by simpa using ‹N.Normal›.conj_mem _ hx σ⁻¹
    have hmain := ha σ (σ⁻¹ * x * σ) (σ⁻¹ * y * σ)
    rw [h1 _ hp _, smul_one, one_mul] at hmain
    have hxσ : a (σ * (σ⁻¹ * x * σ), σ⁻¹ * y * σ) = x • a (σ, σ⁻¹ * y * σ) := by
      rw [show σ * (σ⁻¹ * x * σ) = x * σ by group]
      exact smul_apply_of_mem_left ha h1 hx σ _
    rw [hxσ] at hmain
    rw [show σ⁻¹ * (x * y) * σ = σ⁻¹ * x * σ * (σ⁻¹ * y * σ) by group]
    exact hmain.symm
  obtain ⟨t, ht⟩ := hH1 (fun m : G => a (σ, σ⁻¹ * m * σ)) hFcoc
  obtain ⟨u, huN, huout⟩ : ∃ u : G → M, (∀ g ∈ N, u g = 1) ∧
      (∀ g ∉ N, u g = (g * σ⁻¹) • t⁻¹) :=
    ⟨fun g => if g ∈ N then 1 else (g * σ⁻¹) • t⁻¹, fun g hg => if_pos hg, fun g hg => if_neg hg⟩
  have hone : ∀ n ∈ N, ∀ y : G, twist a u (n, y) = 1 := by
    intro n hn y
    rw [twist_apply, h1 n hn y, huN n hn, mul_one]
    by_cases hy : y ∈ N
    · rw [huN y hy, huN _ (mul_mem hn hy), smul_one, div_one, div_one]
    · have hny : n * y ∉ N := not_mem_mul_of_mem_of_not_mem hn hy
      rw [huout y hy, huout _ hny, show n * y * σ⁻¹ = n * (y * σ⁻¹) by group,
        mul_smul n (y * σ⁻¹) t⁻¹, div_self', div_one]
  have hσn : ∀ n ∈ N, twist a u (σ, n) = 1 := by
    intro n hn
    have hcn : σ * n * σ⁻¹ ∈ N := ‹N.Normal›.conj_mem _ hn σ
    have hσnN : σ * n ∉ N := not_mem_mul_of_not_mem_of_mem hσ hn
    have hval : (σ * n * σ⁻¹) • t / t = a (σ, n) := by
      have h := ht _ hcn
      rwa [show σ⁻¹ * (σ * n * σ⁻¹) * σ = n by group] at h
    have hinner : σ • u n / u (σ * n) * u σ = a (σ, n) := by
      rw [huN n hn, huout σ hσ, huout _ hσnN, smul_one, show σ * σ⁻¹ = (1 : G) by group,
        one_smul, smul_inv', one_div, inv_inv, ← hval, div_eq_mul_inv]
    rw [twist_apply, hinner, div_self']
  refine ⟨u, hone, fun x n hn => ?_⟩
  by_cases hx : x ∈ N
  · exact hone x hx n
  · have hxσ : x * σ⁻¹ ∈ N := (hcov x).resolve_left hx
    have hkey := smul_apply_of_mem_left (isMulCocycle₂_twist ha u) hone hxσ σ n
    rw [show x * σ⁻¹ * σ = x by group] at hkey
    rw [hkey, hσn n hn, smul_one]

/-- A two-cocycle trivial at every pair with an entry in `N` is the inflation of its value at the
pair `(σ, σ)`, and that value is `G`-invariant. -/
theorem eq_indexTwoInflation_of_eq_one [N.Normal] (hσ : σ ∉ N)
    (hcov : ∀ g : G, g ∈ N ∨ g * σ⁻¹ ∈ N)
    {a : G × G → M} (ha : IsMulCocycle₂ a) (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1)
    (h2 : ∀ x : G, ∀ n ∈ N, a (x, n) = 1) :
    (∀ g : G, g • a (σ, σ) = a (σ, σ)) ∧ a = indexTwoInflation N (a (σ, σ)) := by
  have hσσ : σ * σ ∈ N := mul_self_mem_of_two_cosets hcov hσ
  have hfixσ : σ • a (σ, σ) = a (σ, σ) := by
    have h := ha σ σ σ
    rw [h1 _ hσσ σ, h2 σ _ hσσ, one_mul, mul_one] at h
    exact h.symm
  have hmσ : ∀ m ∈ N, a (σ, m * σ) = (σ * m * σ⁻¹) • a (σ, σ) := by
    intro m hm
    have hcm : σ * m * σ⁻¹ ∈ N := ‹N.Normal›.conj_mem _ hm σ
    have h := ha σ m σ
    rw [h2 σ m hm, h1 m hm σ, mul_one, smul_one, one_mul] at h
    have h' := smul_apply_of_mem_left ha h1 hcm σ σ
    rw [show σ * m * σ⁻¹ * σ = σ * m by group] at h'
    rw [← h, h']
  have hfixN : ∀ m ∈ N, m • a (σ, σ) = a (σ, σ) := by
    intro m hm
    obtain ⟨n, hnN, hnm⟩ : ∃ n : G, n ∈ N ∧ σ * (σ * n * σ⁻¹) * σ⁻¹ = m := by
      refine ⟨σ⁻¹ * (σ⁻¹ * m * σ) * σ, ?_, by group⟩
      have h₁ : σ⁻¹ * m * σ ∈ N := by simpa using ‹N.Normal›.conj_mem _ hm σ⁻¹
      simpa using ‹N.Normal›.conj_mem _ h₁ σ⁻¹
    have h := ha σ σ n
    rw [h1 _ hσσ n, h2 σ n hnN, one_mul, smul_one, one_mul] at h
    have h' := hmσ _ (‹N.Normal›.conj_mem _ hnN σ)
    rw [show σ * n * σ⁻¹ * σ = σ * n by group, hnm] at h'
    rw [h'] at h
    exact h.symm
  have hfix : ∀ g : G, g • a (σ, σ) = a (σ, σ) := by
    intro g
    by_cases hg : g ∈ N
    · exact hfixN g hg
    · have hgσ : g * σ⁻¹ ∈ N := (hcov g).resolve_left hg
      rw [show g = g * σ⁻¹ * σ by group, mul_smul, hfixσ, hfixN _ hgσ]
  refine ⟨hfix, funext fun p => ?_⟩
  obtain ⟨x, y⟩ := p
  by_cases hx : x ∈ N
  · rw [h1 x hx y, indexTwoInflation_of_mem_left hx]
  · by_cases hy : y ∈ N
    · rw [h2 x y hy, indexTwoInflation_of_mem_right hy]
    · have hxσ : x * σ⁻¹ ∈ N := (hcov x).resolve_left hx
      have hyσ : y * σ⁻¹ ∈ N := (hcov y).resolve_left hy
      have hy' := hmσ _ hyσ
      rw [show y * σ⁻¹ * σ = y by group] at hy'
      have hx' := smul_apply_of_mem_left ha h1 hxσ σ y
      rw [show x * σ⁻¹ * σ = x by group] at hx'
      rw [indexTwoInflation_of_not_mem hx hy, hx', hy', hfix, hfix]

/-- A two-cocycle whose restriction to a normal subgroup with two cosets is a coboundary becomes,
after correction by a coboundary, the inflation of a single `G`-invariant value.  This is the
exactness of the inflation-restriction sequence in degree two, for a subgroup of index two. -/
theorem exists_twist_eq_indexTwoInflation [N.Normal] (hσ : σ ∉ N)
    (hcov : ∀ g : G, g ∈ N ∨ g * σ⁻¹ ∈ N)
    (hH1 : ∀ f : G → M, (∀ x ∈ N, ∀ y ∈ N, f (x * y) = x • f y * f x) →
      ∃ t : M, ∀ x ∈ N, x • t / t = f x)
    {a : G × G → M} (ha : IsMulCocycle₂ a)
    (hres : ∃ b : G → M, ∀ x ∈ N, ∀ y ∈ N, a (x, y) = x • b y / b (x * y) * b x) :
    ∃ (c : M) (u : G → M), (∀ g : G, g • c = c) ∧ twist a u = indexTwoInflation N c := by
  obtain ⟨u₁, h₁⟩ := exists_twist_eq_one_on_subgroup hres
  obtain ⟨u₂, h₂⟩ := exists_twist_eq_one_of_mem_left hcov (isMulCocycle₂_twist ha u₁) h₁
  obtain ⟨u₃, h₃, h₄⟩ := exists_twist_eq_one_of_mem hσ hcov hH1
    (isMulCocycle₂_twist (isMulCocycle₂_twist ha u₁) u₂) h₂
  rw [twist_twist, twist_twist] at h₃ h₄
  obtain ⟨hfix, heq⟩ := eq_indexTwoInflation_of_eq_one hσ hcov
    (isMulCocycle₂_twist ha (u₁ * (u₂ * u₃))) h₃ h₄
  exact ⟨_, u₁ * (u₂ * u₃), hfix, heq⟩

/-- The form of the previous statement as a factorisation of the cocycle itself. -/
theorem exists_eq_indexTwoInflation_mul_coboundary₂ [N.Normal] (hσ : σ ∉ N)
    (hcov : ∀ g : G, g ∈ N ∨ g * σ⁻¹ ∈ N)
    (hH1 : ∀ f : G → M, (∀ x ∈ N, ∀ y ∈ N, f (x * y) = x • f y * f x) →
      ∃ t : M, ∀ x ∈ N, x • t / t = f x)
    {a : G × G → M} (ha : IsMulCocycle₂ a)
    (hres : ∃ b : G → M, ∀ x ∈ N, ∀ y ∈ N, a (x, y) = x • b y / b (x * y) * b x) :
    ∃ (c : M) (u : G → M), (∀ g : G, g • c = c) ∧
      ∀ x y : G, a (x, y) = indexTwoInflation N c (x, y) * (x • u y / u (x * y) * u x) := by
  obtain ⟨c, u, hfix, heq⟩ := exists_twist_eq_indexTwoInflation hσ hcov hH1 ha hres
  refine ⟨c, u, hfix, fun x y => ?_⟩
  rw [← congrFun heq (x, y)]
  exact eq_twist_mul_coboundary₂ a u (x, y)

/-! ### Inflated cocycles and norms -/

/-- The inflation of a norm from the invariants of the subgroup is a coboundary. -/
theorem isMulCoboundary₂_indexTwoInflation [N.Normal] (hσ : σ ∉ N)
    (hcov : ∀ g : G, g ∈ N ∨ g * σ⁻¹ ∈ N) {f : M} (hf : ∀ n ∈ N, n • f = f) :
    IsMulCoboundary₂ (indexTwoInflation N (σ • f * f)) := by
  classical
  have hfσ : ∀ n ∈ N, n • (σ • f) = σ • f := by
    intro n hn
    have hc : σ⁻¹ * n * σ ∈ N := by simpa using ‹N.Normal›.conj_mem _ hn σ⁻¹
    rw [smul_smul, show n * σ = σ * (σ⁻¹ * n * σ) by group, mul_smul, hf _ hc]
  rw [isMulCoboundary₂_iff]
  obtain ⟨u, huN, huout⟩ : ∃ u : G → M, (∀ g ∈ N, u g = 1) ∧ (∀ g ∉ N, u g = f) :=
    ⟨fun g => if g ∈ N then 1 else f, fun g hg => if_pos hg, fun g hg => if_neg hg⟩
  refine ⟨u, funext fun p => ?_⟩
  obtain ⟨x, y⟩ := p
  rw [coboundary₂_apply]
  by_cases hx : x ∈ N
  · by_cases hy : y ∈ N
    · rw [huN x hx, huN y hy, huN _ (mul_mem hx hy), smul_one, div_one, mul_one,
        indexTwoInflation_of_mem_left hx]
    · rw [huN x hx, huout y hy, huout _ (not_mem_mul_of_mem_of_not_mem hx hy), hf x hx,
        div_self', one_mul, indexTwoInflation_of_mem_left hx]
  · by_cases hy : y ∈ N
    · rw [huout x hx, huN y hy, huout _ (not_mem_mul_of_not_mem_of_mem hx hy), smul_one,
        one_div, inv_mul_cancel, indexTwoInflation_of_mem_right hy]
    · have hxσ : x * σ⁻¹ ∈ N := (hcov x).resolve_left hx
      rw [huout x hx, huout y hy, huN _ (mul_mem_of_not_mem_of_not_mem hcov hσ hx hy),
        div_one, indexTwoInflation_of_not_mem hx hy]
      congr 1
      rw [show x = x * σ⁻¹ * σ by group, mul_smul, hfσ _ hxσ]

/-- An inflated cocycle which is a coboundary has its value a norm from the invariants of the
subgroup.  This is the injectivity of inflation in degree two, for a subgroup of index two. -/
theorem exists_smul_mul_eq_of_isMulCoboundary₂_indexTwoInflation [N.Normal] (hσ : σ ∉ N)
    (hcov : ∀ g : G, g ∈ N ∨ g * σ⁻¹ ∈ N)
    (hH1 : ∀ f : G → M, (∀ x ∈ N, ∀ y ∈ N, f (x * y) = x • f y * f x) →
      ∃ t : M, ∀ x ∈ N, x • t / t = f x)
    {c : M} (h : IsMulCoboundary₂ (indexTwoInflation N c)) :
    ∃ f : M, (∀ n ∈ N, n • f = f) ∧ σ • f * f = c := by
  rw [isMulCoboundary₂_iff] at h
  obtain ⟨u, hu⟩ := h
  have hcoc : ∀ x ∈ N, ∀ y ∈ N, u (x * y) = x • u y * u x := by
    intro x hx y hy
    have hp := congrFun hu (x, y)
    rw [coboundary₂_apply, indexTwoInflation_of_mem_left hx, div_mul_eq_mul_div,
      div_eq_one] at hp
    exact hp.symm
  obtain ⟨t, ht⟩ := hH1 u hcoc
  obtain ⟨v, hvcob, hvN⟩ : ∃ v : G → M, coboundary₂ v = indexTwoInflation N c ∧
      ∀ n ∈ N, v n = 1 := by
    refine ⟨u * (fun g : G => g • t / t)⁻¹, ?_, ?_⟩
    · rw [coboundary₂_mul, coboundary₂_inv, coboundary₂_smul_div, inv_one, mul_one, hu]
    · intro n hn
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [← ht n hn, mul_inv_cancel]
  have hleft : ∀ n ∈ N, ∀ y : G, v (n * y) = n • v y := by
    intro n hn y
    have hp := congrFun hvcob (n, y)
    rw [coboundary₂_apply, indexTwoInflation_of_mem_left hn, hvN n hn, mul_one,
      div_eq_one] at hp
    exact hp.symm
  have hright : ∀ x : G, ∀ n ∈ N, v (x * n) = v x := by
    intro x n hn
    have hp := congrFun hvcob (x, n)
    rw [coboundary₂_apply, indexTwoInflation_of_mem_right hn, hvN n hn, smul_one,
      div_mul_eq_mul_div, one_mul, div_eq_one] at hp
    exact hp.symm
  refine ⟨v σ, fun n hn => ?_, ?_⟩
  · have hc : σ⁻¹ * n * σ ∈ N := by simpa using ‹N.Normal›.conj_mem _ hn σ⁻¹
    rw [← hleft n hn σ, show n * σ = σ * (σ⁻¹ * n * σ) by group, hright σ _ hc]
  · have hp := congrFun hvcob (σ, σ)
    rw [coboundary₂_apply, indexTwoInflation_of_not_mem hσ hσ,
      hvN _ (mul_self_mem_of_two_cosets hcov hσ), div_one] at hp
    exact hp

end InverseGalois.CFT
