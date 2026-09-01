/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.IndexTwo

/-!
# Inflation in degree two is injective

Let `N` be a normal subgroup of `G` acting on a commutative group `M` whose first cohomology on `N`
vanishes.  A two cocycle of `G` inflated from the quotient, that is one whose value at a pair
depends only on the pair of cosets, is a coboundary on `G` exactly when it is a coboundary already
at the level of the quotient.  One direction is trivial, and this file proves the other.

The cochain trivialising the cocycle need not be inflated, but it can be corrected to be so.  The
inflation identity applied to a pair whose second entry lies in the subgroup says that the failure
of the cochain to be constant on a coset is measured by a single map on the subgroup, and that map
is a one cocycle.  The vanishing hypothesis writes it as a coboundary, and dividing the original
cochain by that coboundary produces a cochain with the same differential which is constant on
cosets.  Applying the inflation identity once more, on the other side, shows that the corrected
cochain automatically takes values fixed by the subgroup, so it really is the pullback of a cochain
on the quotient with values in the invariants.

## Main results

* `InverseGalois.CFT.exists_coboundary₂_inflated_of_cochain`: **a given cochain trivialising an
  inflated cocycle can be corrected to be constant on cosets and invariant under the subgroup**, as
  soon as the associated one cocycle on the subgroup is a coboundary there.
* `InverseGalois.CFT.exists_coboundary₂_inflated`: **a cochain trivialising an inflated cocycle can
  be chosen constant on cosets and invariant under the subgroup.**

## Tags

group cohomology, inflation, restriction, two cocycle, coboundary
-/

namespace InverseGalois.CFT

open groupCohomology

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

section Inflation

variable {N : Subgroup G} [N.Normal]

omit [CommGroup M] [MulDistribMulAction G M] in
/-- An inflated cochain is unchanged by multiplying the first entry on the left by an element of
the subgroup. -/
theorem apply_mul_left_of_inflated {a : G × G → M}
    (hinfl : ∀ (x y n : G), n ∈ N → ∀ m : G, m ∈ N → a (x * n, y * m) = a (x, y))
    {n : G} (hn : n ∈ N) (x y : G) : a (n * x, y) = a (x, y) := by
  have hconj : x⁻¹ * n * x ∈ N := by
    simpa using (Subgroup.Normal.conj_mem ‹N.Normal› n hn x⁻¹)
  have h := hinfl x y _ hconj 1 N.one_mem
  rwa [show x * (x⁻¹ * n * x) = n * x by group, mul_one] at h

omit [N.Normal] [CommGroup M] [MulDistribMulAction G M] in
/-- An inflated cochain is unchanged by multiplying the second entry on the right by an element of
the subgroup. -/
theorem apply_mul_right_of_inflated {a : G × G → M}
    (hinfl : ∀ (x y n : G), n ∈ N → ∀ m : G, m ∈ N → a (x * n, y * m) = a (x, y))
    {n : G} (hn : n ∈ N) (x y : G) : a (x, y * n) = a (x, y) := by
  have h := hinfl x y 1 N.one_mem n hn
  rwa [mul_one] at h

omit [N.Normal] in
/-- The failure of a trivialising cochain to be constant on a coset is the translate of a single
map on the subgroup. -/
theorem eq_smul_mul_of_inflated {a : G × G → M}
    (hinfl : ∀ (x y n : G), n ∈ N → ∀ m : G, m ∈ N → a (x * n, y * m) = a (x, y))
    {u : G → M} (hu : coboundary₂ u = a) (x : G) {n : G} (hn : n ∈ N) :
    u (x * n) = x • (u n / u 1) * u x := by
  have h1 : a (x, n) = a (x, 1) := by
    have h := apply_mul_right_of_inflated hinfl hn x 1
    rwa [one_mul] at h
  rw [← hu] at h1
  simp only [coboundary₂_apply, mul_one] at h1
  rw [div_mul_cancel] at h1
  rw [div_eq_mul_inv, smul_mul', smul_inv', ← h1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

omit [N.Normal] in
/-- The map measuring the failure of a trivialising cochain to be constant on a coset is a one
cocycle on the subgroup. -/
theorem isMulCocycle₁_div_one_of_inflated {a : G × G → M}
    (hinfl : ∀ (x y n : G), n ∈ N → ∀ m : G, m ∈ N → a (x * n, y * m) = a (x, y))
    {u : G → M} (hu : coboundary₂ u = a) (x : G) (_hx : x ∈ N) (y : G) (hy : y ∈ N) :
    u (x * y) / u 1 = x • (u y / u 1) * (u x / u 1) := by
  rw [eq_smul_mul_of_inflated hinfl hu x hy, mul_div_assoc]

/-- **A given cochain trivialising an inflated two cocycle can be corrected to be inflated itself**,
as soon as the map measuring its failure to be constant on a coset is a coboundary on the subgroup.
The corrected cochain is constant on the cosets of the subgroup and takes values fixed by it, so it
is the pullback of a cochain on the quotient with values in the invariants. -/
theorem exists_coboundary₂_inflated_of_cochain {a : G × G → M}
    (hinfl : ∀ (x y n : G), n ∈ N → ∀ m : G, m ∈ N → a (x * n, y * m) = a (x, y))
    {u : G → M} (hu : coboundary₂ u = a)
    (hH1 : ∃ t : M, ∀ x ∈ N, x • t / t = u x / u 1) :
    ∃ u' : G → M, (∀ g n : G, n ∈ N → u' (g * n) = u' g) ∧
      (∀ g n : G, n ∈ N → n • u' g = u' g) ∧ coboundary₂ u' = a := by
  obtain ⟨s, hs⟩ := hH1
  obtain ⟨u', hu'⟩ : ∃ u' : G → M, ∀ g : G, u' g = u g * (g • s / s)⁻¹ := ⟨_, fun _ => rfl⟩
  have hfun : u' = u * (fun g : G => g • s / s)⁻¹ := funext fun g => hu' g
  have hcb : coboundary₂ u' = a := by
    rw [hfun, coboundary₂_mul, coboundary₂_inv, coboundary₂_smul_div, inv_one, mul_one, hu]
  have hcoset : ∀ g n : G, n ∈ N → u' (g * n) = u' g := by
    intro g n hn
    have h := eq_smul_mul_of_inflated hinfl hu g hn
    have hsn : u n / u 1 = n • s / s := (hs n hn).symm
    rw [hu', hu', h, hsn]
    simp only [div_eq_mul_inv, smul_mul', smul_inv', mul_smul, mul_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine ⟨u', hcoset, ?_, hcb⟩
  intro g n hn
  have hng : u' (n * g) = u' g := by
    have hconj : g⁻¹ * n * g ∈ N := by
      simpa using (Subgroup.Normal.conj_mem ‹N.Normal› n hn g⁻¹)
    have h := hcoset g _ hconj
    rwa [show g * (g⁻¹ * n * g) = n * g by group] at h
  have hn1 : u' n = u' 1 := by
    have h := hcoset 1 n hn
    rwa [one_mul] at h
  have h1 : a (n, g) = a (1, g) := by
    have h := apply_mul_left_of_inflated hinfl hn 1 g
    rwa [mul_one] at h
  rw [← hcb] at h1
  simp only [coboundary₂_apply, one_smul, one_mul, hng, hn1, div_self'] at h1
  have h2 : n • u' g / u' g * u' 1 = 1 * u' 1 := by rw [h1, one_mul]
  exact div_eq_one.mp (mul_right_cancel h2)

/-- **A cochain trivialising an inflated two cocycle can be corrected to be inflated itself.**  The
corrected cochain is constant on the cosets of the subgroup and takes values fixed by it, so it is
the pullback of a cochain on the quotient with values in the invariants. -/
theorem exists_coboundary₂_inflated
    (hH1 : ∀ f : G → M, (∀ x ∈ N, ∀ y ∈ N, f (x * y) = x • f y * f x) →
      ∃ t : M, ∀ x ∈ N, x • t / t = f x)
    {a : G × G → M}
    (hinfl : ∀ (x y n : G), n ∈ N → ∀ m : G, m ∈ N → a (x * n, y * m) = a (x, y))
    (hcob : IsMulCoboundary₂ a) :
    ∃ u : G → M, (∀ g n : G, n ∈ N → u (g * n) = u g) ∧
      (∀ g n : G, n ∈ N → n • u g = u g) ∧ coboundary₂ u = a := by
  obtain ⟨u, hu⟩ := isMulCoboundary₂_iff.mp hcob
  exact exists_coboundary₂_inflated_of_cochain hinfl hu
    (hH1 (fun g => u g / u 1) (isMulCocycle₁_div_one_of_inflated hinfl hu))

end Inflation

end InverseGalois.CFT
