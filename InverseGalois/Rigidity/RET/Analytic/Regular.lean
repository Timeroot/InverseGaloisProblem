/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A transitive group commuting with a simply transitive one is a copy of it

A group acting simply transitively on a set is pinned down by a single point: every point is
`g • x₀` for exactly one `g`.  A permutation commuting with such an action is therefore determined
by the image of that one point, so permutations commuting with the action can be no more numerous
than the group; if they already move `x₀` everywhere, there are exactly as many, and the
correspondence is an isomorphism.

This is the abstract form of the identification of the monodromy group of a Galois cover with its
deck group: the deck group acts simply transitively on a fibre, monodromy commutes with it, and
monodromy is transitive when the cover is connected.  Reading the group element off the *inverse*
permutation turns the anti-isomorphism of the two regular representations into an isomorphism.

## Main results

* `Rigidity.RET.existsUnique_smul_eq` — a simply transitive action pins down the group element.
* `Rigidity.RET.commutingHom` — the homomorphism from a commuting group of permutations to the
  acting group.
* `Rigidity.RET.commutingEquiv` — a transitive group of permutations commuting with a simply
  transitive action is isomorphic to the acting group.
-/

noncomputable section

namespace Rigidity.RET

variable {G Ω : Type*} [Group G] [MulAction G Ω] {x₀ : Ω}

/-- **A simply transitive action pins down the group element**: every point is the translate of the
base point by exactly one element. -/
theorem existsUnique_smul_eq (hfree : ∀ g : G, g • x₀ = x₀ → g = 1)
    (htrans : ∀ y : Ω, ∃ g : G, g • x₀ = y) (y : Ω) : ∃! g : G, g • x₀ = y := by
  obtain ⟨g, hg⟩ := htrans y
  refine ⟨g, hg, fun g' hg' => ?_⟩
  have hcancel : (g⁻¹ * g') • x₀ = x₀ := by
    rw [mul_smul, hg', ← hg, ← mul_smul, inv_mul_cancel, one_smul]
  exact (inv_mul_eq_one.mp (hfree _ hcancel)).symm

/-- **The group element by which a commuting permutation moves the base point.**  It is read off
the inverse permutation, which is what makes the assignment multiplicative rather than
antimultiplicative. -/
def commutingHom (hfree : ∀ g : G, g • x₀ = x₀ → g = 1)
    (htrans : ∀ y : Ω, ∃ g : G, g • x₀ = y) (M : Subgroup (Equiv.Perm Ω))
    (hcomm : ∀ σ ∈ M, ∀ (g : G) (x : Ω), σ (g • x) = g • σ x) : M →* G where
  toFun σ := (htrans ((σ : Equiv.Perm Ω)⁻¹ x₀)).choose
  map_one' := by
    refine (existsUnique_smul_eq hfree htrans _).unique
      (htrans (((1 : M) : Equiv.Perm Ω)⁻¹ x₀)).choose_spec ?_
    show (1 : G) • x₀ = ((1 : M) : Equiv.Perm Ω)⁻¹ x₀
    simp
  map_mul' σ τ := by
    have hσ := (htrans ((σ : Equiv.Perm Ω)⁻¹ x₀)).choose_spec
    have hτ := (htrans ((τ : Equiv.Perm Ω)⁻¹ x₀)).choose_spec
    refine (existsUnique_smul_eq hfree htrans _).unique
      (htrans (((σ * τ : M) : Equiv.Perm Ω)⁻¹ x₀)).choose_spec ?_
    rw [mul_smul, hτ, ← hcomm _ (M.inv_mem τ.2), hσ, Subgroup.coe_mul, mul_inv_rev]
    rfl

theorem commutingHom_smul (hfree : ∀ g : G, g • x₀ = x₀ → g = 1)
    (htrans : ∀ y : Ω, ∃ g : G, g • x₀ = y) (M : Subgroup (Equiv.Perm Ω))
    (hcomm : ∀ σ ∈ M, ∀ (g : G) (x : Ω), σ (g • x) = g • σ x) (σ : M) :
    commutingHom hfree htrans M hcomm σ • x₀ = (σ : Equiv.Perm Ω)⁻¹ x₀ :=
  (htrans ((σ : Equiv.Perm Ω)⁻¹ x₀)).choose_spec

/-- **A transitive group of permutations commuting with a simply transitive action is a copy of the
acting group.** -/
def commutingEquiv (hfree : ∀ g : G, g • x₀ = x₀ → g = 1)
    (htrans : ∀ y : Ω, ∃ g : G, g • x₀ = y) (M : Subgroup (Equiv.Perm Ω))
    (hcomm : ∀ σ ∈ M, ∀ (g : G) (x : Ω), σ (g • x) = g • σ x)
    (hMtrans : ∀ y : Ω, ∃ σ ∈ M, σ x₀ = y) : M ≃* G := by
  refine MulEquiv.ofBijective (commutingHom hfree htrans M hcomm) ⟨?_, ?_⟩
  · -- a commuting permutation fixing the base point is the identity
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hbase : (σ : Equiv.Perm Ω)⁻¹ x₀ = x₀ := by
      have h := commutingHom_smul hfree htrans M hcomm σ
      rw [hσ, one_smul] at h
      exact h.symm
    refine Subtype.ext (Equiv.ext fun y => ?_)
    obtain ⟨g, rfl⟩ := htrans y
    have hfix : ((σ : Equiv.Perm Ω)⁻¹) (g • x₀) = g • x₀ := by
      rw [hcomm _ (M.inv_mem σ.2), hbase]
    have h : (σ : Equiv.Perm Ω) (((σ : Equiv.Perm Ω)⁻¹) (g • x₀)) = g • x₀ := by simp
    rw [hfix] at h
    exact h
  · -- transitivity supplies a preimage for every group element
    intro g
    obtain ⟨σ, hσM, hσ⟩ := hMtrans (g • x₀)
    refine ⟨⟨σ⁻¹, M.inv_mem hσM⟩, ?_⟩
    refine (existsUnique_smul_eq hfree htrans _).unique
      (commutingHom_smul hfree htrans M hcomm ⟨σ⁻¹, M.inv_mem hσM⟩) ?_
    show g • x₀ = ((⟨σ⁻¹, M.inv_mem hσM⟩ : M) : Equiv.Perm Ω)⁻¹ x₀
    rw [show ((⟨σ⁻¹, M.inv_mem hσM⟩ : M) : Equiv.Perm Ω) = σ⁻¹ from rfl, inv_inv, hσ]

end Rigidity.RET

end
