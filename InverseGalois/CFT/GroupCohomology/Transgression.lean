/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.InflationRestriction

/-!
# The transgression of a two-cocycle along a normal subgroup with trivial action

Let `N` be a normal subgroup of `G` acting trivially on a commutative group `M`.  A two-cocycle of
`G` which vanishes at every pair whose first entry lies in `N` carries, for each element `σ` of
`G`, the map on `N` sending `x` to the value of the cocycle at `(σ, σ⁻¹ x σ)`.  Because the action
of `N` is trivial this map is a homomorphism, it depends only on the coset of `σ`, and the family
of these homomorphisms satisfies the one-cocycle identity for the action of `G` on the
homomorphisms from `N` to `M` translating both the source and the target.  It is thus a
one-cocycle of the quotient with values in `Hom (N, M)`: the transgression.

The interest of this description is that the exactness of the inflation-restriction sequence in
degree two needs only the vanishing of the transgression, not the vanishing of the whole first
cohomology of `N`; and the transgression, being a one-cocycle of the quotient, is a finite object
even when `N` is enormous.  The last theorem records the resulting criterion, with the hypothesis
stated for every normalised representative of the class since the correction proceeds by twists.

## Main definitions

* `InverseGalois.CFT.transgression`: the map on the subgroup attached to an element of the group.

## Main results

* `InverseGalois.CFT.transgression_mul_mem`: the transgression is a homomorphism on the subgroup.
* `InverseGalois.CFT.transgression_conj`: it is invariant under conjugation by the subgroup.
* `InverseGalois.CFT.transgression_smul_left`: it depends only on the coset of its element.
* `InverseGalois.CFT.transgression_mul_left`: **the transgression satisfies the one-cocycle
  identity**, for the action translating both the source and the target.
* `InverseGalois.CFT.exists_twist_inflated_of_transgression_trivial`: **a two-cocycle whose
  restriction to a normal subgroup acting trivially is a coboundary and whose transgression is a
  coboundary is cohomologous to an inflated cocycle.**

## Tags

group cohomology, transgression, inflation, restriction, two-cocycle, normal subgroup
-/

namespace InverseGalois.CFT

open groupCohomology

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- **The transgression of a two-cochain at an element of the group**: the map sending an element
to the value of the cochain at the pair formed by the given element and the conjugate. -/
def transgression (a : G × G → M) (σ : G) : G → M := fun x => a (σ, σ⁻¹ * x * σ)

omit [CommGroup M] [MulDistribMulAction G M] in
theorem transgression_apply (a : G × G → M) (σ x : G) :
    transgression a σ x = a (σ, σ⁻¹ * x * σ) := rfl

section Trivial

variable {N : Subgroup G} [N.Normal] {a : G × G → M}

/-- **The transgression is a homomorphism on the subgroup**, as soon as the subgroup acts trivially
and the cocycle vanishes at every pair whose first entry lies in the subgroup. -/
theorem transgression_mul_mem (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (ha : IsMulCocycle₂ a)
    (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) (σ : G) {x y : G} (hx : x ∈ N) (hy : y ∈ N) :
    transgression a σ (x * y) = transgression a σ x * transgression a σ y := by
  have h := isMulCocycle₁_conj_of_eq_one ha h1 σ x hx y hy
  simp only at h
  rw [transgression_apply, transgression_apply, transgression_apply, h, htriv x hx, mul_comm]

/-- The transgression sends the identity to the identity. -/
theorem transgression_one (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (ha : IsMulCocycle₂ a)
    (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) (σ : G) : transgression a σ 1 = 1 := by
  have h := transgression_mul_mem htriv ha h1 σ N.one_mem N.one_mem
  rw [mul_one] at h
  refine mul_left_cancel (a := transgression a σ 1) ?_
  rw [mul_one, ← h]

/-- The transgression sends an inverse to the inverse. -/
theorem transgression_inv (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (ha : IsMulCocycle₂ a)
    (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) (σ : G) {x : G} (hx : x ∈ N) :
    transgression a σ x⁻¹ = (transgression a σ x)⁻¹ := by
  have h := transgression_mul_mem htriv ha h1 σ (N.inv_mem hx) hx
  rw [inv_mul_cancel, transgression_one htriv ha h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- **The transgression is invariant under conjugation by the subgroup.**  This is the triviality
of the inner action on the first cohomology of the subgroup, in the shape needed to view the
transgression as a one-cocycle of the quotient. -/
theorem transgression_conj (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (ha : IsMulCocycle₂ a)
    (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) (σ : G) {n x : G} (hn : n ∈ N) (hx : x ∈ N) :
    transgression a σ (n⁻¹ * x * n) = transgression a σ x := by
  rw [transgression_mul_mem htriv ha h1 σ (mul_mem (N.inv_mem hn) hx) hn,
    transgression_mul_mem htriv ha h1 σ (N.inv_mem hn) hx,
    transgression_inv htriv ha h1 σ hn]
  rw [mul_comm ((transgression a σ n)⁻¹) (transgression a σ x), mul_assoc, inv_mul_cancel, mul_one]

/-- **The transgression depends only on the coset of its element.** -/
theorem transgression_smul_left (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (ha : IsMulCocycle₂ a)
    (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) {n : G} (hn : n ∈ N) (σ : G) {x : G} (hx : x ∈ N) :
    transgression a (n * σ) x = transgression a σ x := by
  rw [transgression_apply, show (n * σ)⁻¹ * x * (n * σ) = σ⁻¹ * (n⁻¹ * x * n) * σ by group,
    smul_apply_of_mem_left ha h1 hn σ _, htriv n hn,
    ← transgression_apply a σ (n⁻¹ * x * n), transgression_conj htriv ha h1 σ hn hx]

/-- **The transgression satisfies the one-cocycle identity.**  The action on the homomorphisms from
the subgroup to the module translates the source by conjugation and the target by the action, and
the transgression of a product is the translate of the second transgression times the first. -/
theorem transgression_mul_left (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (ha : IsMulCocycle₂ a)
    (h1 : ∀ n ∈ N, ∀ y : G, a (n, y) = 1) (σ τ : G) {x : G} (hx : x ∈ N) :
    transgression a (σ * τ) x
      = σ • transgression a τ (σ⁻¹ * x * σ) * transgression a σ x := by
  rw [transgression_apply, transgression_apply, transgression_apply,
    transgression_mul ha h1 σ τ hx, htriv x hx, div_self', mul_one]

/-- **A two-cocycle whose restriction to a normal subgroup acting trivially is a coboundary and
whose transgression is a coboundary is cohomologous to an inflated cocycle.**  The transgression is
asked to be a coboundary for every normalised representative of the class, since the correction
proceeds by successive twists. -/
theorem exists_twist_inflated_of_transgression_trivial
    (htriv : ∀ n ∈ N, ∀ m : M, n • m = m) (ha : IsMulCocycle₂ a)
    (hres : ∃ b : G → M, ∀ x ∈ N, ∀ y ∈ N, a (x, y) = x • b y / b (x * y) * b x)
    (htr : ∀ c : G × G → M, IsMulCocycle₂ c → (∀ n ∈ N, ∀ y : G, c (n, y) = 1) →
      ∃ φ : G → M, (∀ x ∈ N, ∀ y ∈ N, φ (x * y) = φ x * φ y) ∧
        ∀ σ : G, ∀ x ∈ N, transgression c σ x = σ • φ (σ⁻¹ * x * σ) / φ x) :
    ∃ u : G → M,
      (∀ (x y n : G), n ∈ N → ∀ m : G, m ∈ N → twist a u (x * n, y * m) = twist a u (x, y)) ∧
      (∀ n : G, n ∈ N → ∀ x y : G, n • twist a u (x, y) = twist a u (x, y)) := by
  refine exists_twist_inflated_of_transgression ha hres fun c hc h1 => ?_
  obtain ⟨φ, hφ, hcls⟩ := htr c hc h1
  refine ⟨φ, fun x hx y hy => ?_, fun σ => ⟨1, fun x hx => ?_⟩⟩
  · rw [hφ x hx y hy, htriv x hx, mul_comm]
  · have h := hcls σ x hx
    rw [transgression_apply] at h
    rw [h, smul_one, div_one, mul_one]

end Trivial

end InverseGalois.CFT
