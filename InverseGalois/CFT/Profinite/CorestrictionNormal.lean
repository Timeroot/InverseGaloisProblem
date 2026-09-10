/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Corestriction

/-!
# Corestriction along a normal subgroup

The average of a cochain of a subgroup over the cosets is a cochain of the whole group.  When the
subgroup is normal the formula simplifies at the elements of the subgroup itself: such an element
fixes every coset, so the transversal element by which it carries one chosen representative to the
next is the conjugate of the element by that representative, and the average is the product over
the cosets of the value of the cochain at that conjugate, carried back by the representative.

That product is what makes the average usable for prescribing a cochain on a piece of the group.
Suppose one wants a cochain of the whole group taking assigned values on a subgroup, and one has a
cochain of the normal subgroup taking those values there.  The average takes, at an element of the
assigned subgroup, the product of the values of the given cochain at all the conjugates of that
element.  If the given cochain is trivial at every conjugate but one, the product collapses to a
single term and the assigned values are reproduced exactly, up to the representative of the coset
that survives.  The same collapse carries a bound on the values: if the surviving value is a power
of one coefficient, so is the average.

The other direction is what confines the average.  Reading the collapse as a contrapositive: if the
average is nontrivial at an element of the normal subgroup, the given cochain is nontrivial at one
of the conjugates of that element.  Applied to the elements of an inertia subgroup this says that
the average can only be ramified where the given cochain already was, at a conjugate place.

Finally, the collapse at the trivial coset asks that the chosen representative of the trivial coset
be the identity, which one can always arrange.

## Main results

* `InverseGalois.CFT.exists_section_one`: a section of the projection onto the cosets can be chosen
  to send the trivial coset to the identity.
* `InverseGalois.CFT.smul_quotient_eq_self_of_mem`: an element of a normal subgroup fixes every
  coset.
* `InverseGalois.CFT.coe_transversalElt_of_mem`: **at an element of a normal subgroup the
  transversal element is the conjugate by the chosen representative.**
* `InverseGalois.CFT.corCochain₁_eq_single`: **the average collapses to a single term when the
  cochain is trivial at all the other conjugates.**
* `InverseGalois.CFT.corCochain₁_eq_self_of_conj`: **the average reproduces the cochain at an
  element of the normal subgroup whose other conjugates it kills.**
* `InverseGalois.CFT.corCochain₁_mem_zpowers_of_single`: the collapse carries a bound by the powers
  of one coefficient.
* `InverseGalois.CFT.corCochain₁_eq_one_of_conj`: the average is trivial where the cochain kills all
  the conjugates.
* `InverseGalois.CFT.exists_ne_one_of_corCochain₁_ne_one`: **where the average is nontrivial the
  cochain is nontrivial at a conjugate.**

## Tags

group cohomology, corestriction, transfer, normal subgroup, conjugate, transversal
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### A section sending the trivial coset to the identity -/

section Section

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal]

/-- **A section of the projection onto the cosets may be chosen to send the trivial coset to the
identity**: correct an arbitrary section at that one coset. -/
theorem exists_section_one :
    ∃ s : G ⧸ H → G, (∀ x : G ⧸ H, (s x : G ⧸ H) = x) ∧ s 1 = 1 := by
  classical
  refine ⟨Function.update (fun x : G ⧸ H => x.out) 1 1, fun x => ?_, ?_⟩
  · by_cases hx : x = 1
    · subst hx
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hx]
      exact QuotientGroup.out_eq' x
  · rw [Function.update_self]

end Section

/-! ### The average at an element of the normal subgroup -/

section Normal

variable {G : Type*} [Group G] (H : Subgroup G) [hHn : H.Normal] (σ : G ⧸ H → G)
  (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x)
  {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- **An element of a normal subgroup fixes every coset of it.** -/
theorem smul_quotient_eq_self_of_mem {g : G} (hg : g ∈ H) (x : G ⧸ H) : g • x = x := by
  refine Quotient.inductionOn' x fun a => ?_
  show ((g * a : G) : G ⧸ H) = ((a : G) : G ⧸ H)
  have hga : g * a = a * (a⁻¹ * g * a) := by group
  rw [hga]
  exact QuotientGroup.mk_mul_of_mem a (hHn.conj_mem' g hg a)

include hσ

/-- **At an element of a normal subgroup the transversal element is the conjugate of that element by
the chosen representative of the coset.** -/
theorem coe_transversalElt_of_mem {g : G} (hg : g ∈ H) (x : G ⧸ H) :
    (transversalElt H σ hσ g x : G) = (σ x)⁻¹ * g * σ x := by
  rw [coe_transversalElt, smul_quotient_eq_self_of_mem H hg x]

/-- **The average of a cochain of a normal subgroup collapses to a single term** at an element of
the subgroup whose conjugates by all the other representatives the cochain sends to the identity. -/
theorem corCochain₁_eq_single [Fintype (G ⧸ H)] {u : ↥H → M} {g : G} (hg : g ∈ H) (x₀ : G ⧸ H)
    (y₀ : ↥H) (hy₀ : (y₀ : G) = (σ x₀)⁻¹ * g * σ x₀)
    (hvan : ∀ (x : G ⧸ H) (y : ↥H), x ≠ x₀ → (y : G) = (σ x)⁻¹ * g * σ x → u y = 1) :
    corCochain₁ H σ hσ u g = σ x₀ • u y₀ := by
  have hy : transversalElt H σ hσ g x₀ = y₀ :=
    Subtype.ext ((coe_transversalElt_of_mem H σ hσ hg x₀).trans hy₀.symm)
  have hsingle : ∏ x : G ⧸ H, σ (g • x) • u (transversalElt H σ hσ g x)
      = σ (g • x₀) • u (transversalElt H σ hσ g x₀) := by
    refine Finset.prod_eq_single x₀ (fun x _ hx => ?_) fun h => absurd (Finset.mem_univ x₀) h
    rw [hvan x _ hx (coe_transversalElt_of_mem H σ hσ hg x), smul_one]
  rw [corCochain₁_apply, hsingle, smul_quotient_eq_self_of_mem H hg x₀, hy]

/-- **The average of a cochain of a normal subgroup reproduces the cochain** at an element of the
subgroup whose conjugates by all the nontrivial representatives the cochain sends to the identity,
provided the trivial coset is represented by the identity. -/
theorem corCochain₁_eq_self_of_conj [Fintype (G ⧸ H)] (hσ1 : σ 1 = 1) {u : ↥H → M} {g : G}
    (hg : g ∈ H)
    (hvan : ∀ (x : G ⧸ H) (y : ↥H), x ≠ 1 → (y : G) = (σ x)⁻¹ * g * σ x → u y = 1) :
    corCochain₁ H σ hσ u g = u ⟨g, hg⟩ := by
  rw [corCochain₁_eq_single H σ hσ hg 1 ⟨g, hg⟩ (by simp [hσ1]) hvan, hσ1, one_smul]

/-- **A single surviving term keeps the average inside the powers of one coefficient**, carried back
by the representative of the coset that survives. -/
theorem corCochain₁_mem_zpowers_of_single [Fintype (G ⧸ H)] {u : ↥H → M} {g : G} (hg : g ∈ H)
    (x₀ : G ⧸ H) (w : M) (y₀ : ↥H) (hy₀ : (y₀ : G) = (σ x₀)⁻¹ * g * σ x₀)
    (hw : u y₀ ∈ Subgroup.zpowers w)
    (hvan : ∀ (x : G ⧸ H) (y : ↥H), x ≠ x₀ → (y : G) = (σ x)⁻¹ * g * σ x → u y = 1) :
    corCochain₁ H σ hσ u g ∈ Subgroup.zpowers (σ x₀ • w) := by
  obtain ⟨n, hn⟩ := hw
  refine ⟨n, ?_⟩
  show (σ x₀ • w) ^ n = corCochain₁ H σ hσ u g
  rw [← smul_zpow', show w ^ n = u y₀ from hn,
    corCochain₁_eq_single H σ hσ hg x₀ y₀ hy₀ hvan]

/-- **The average of a cochain of a normal subgroup is trivial** at an element of the subgroup all
of whose conjugates the cochain sends to the identity. -/
theorem corCochain₁_eq_one_of_conj [Fintype (G ⧸ H)] {u : ↥H → M} {g : G} (hg : g ∈ H)
    (hvan : ∀ (x : G ⧸ H) (y : ↥H), (y : G) = (σ x)⁻¹ * g * σ x → u y = 1) :
    corCochain₁ H σ hσ u g = 1 := by
  rw [corCochain₁_apply]
  refine Finset.prod_eq_one fun x _ => ?_
  rw [hvan x _ (coe_transversalElt_of_mem H σ hσ hg x), smul_one]

/-- **Where the average is nontrivial the cochain is nontrivial at a conjugate**: this is what
confines the ramification of the average to the places where the cochain was already ramified. -/
theorem exists_ne_one_of_corCochain₁_ne_one [Fintype (G ⧸ H)] {u : ↥H → M} {g : G} (hg : g ∈ H)
    (h : corCochain₁ H σ hσ u g ≠ 1) :
    ∃ (x : G ⧸ H) (y : ↥H), (y : G) = (σ x)⁻¹ * g * σ x ∧ u y ≠ 1 := by
  by_contra hc
  push_neg at hc
  exact h (corCochain₁_eq_one_of_conj H σ hσ hg fun x y hy => hc x y hy)

end Normal

end InverseGalois.CFT
