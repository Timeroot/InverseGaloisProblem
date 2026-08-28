/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.BlockDefect
import InverseGalois.CFT.Scholz.DyadicClassStep

/-!
# The residue correction on a cover, at the prime two

The residue correction of a solution presented as a quotient of a fixed cover asks that the
Frobenius defects of the solution be orthogonal to the exponent vectors already radical in the
constraint field.  At the prime two those vectors are governed by a family of blocks accounting for
the square roots of products of ramified primes, exactly as for a solution presented on its own, and
the defects are then the Scholz obstructions of the field the uncorrected solution cuts out of the
cover.

So the correction on a cover is available as soon as the obstructions of that cut field sum to zero
over each block — a condition on one subfield of the cover, with no reference to the correction that
is about to be performed.

## Main results

* `InverseGalois.CFT.exists_scholz_solution_lift_two_canonical`: **the residue correction on a
  cover, available whenever the Scholz obstructions of the field cut out by the uncorrected solution
  sum to zero over each block.**
* `InverseGalois.CFT.exists_scholz_solution_lift_two_blockDefect`: the same, with the sums read as
  the obstructions of the blocks.

## Tags

Scholz–Reichardt, residue correction, Scholz obstruction, block, cover, prime two
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The residue correction on a cover at the prime two, available whenever the Scholz obstructions
of the field cut out by the uncorrected solution sum to zero over each block of a family accounting
for the square roots of products of ramified primes.**  Every defect the correction has to be
orthogonal to comes from a square root of such a product inside the constraint field, and such a
square root lies in the field below the cover already, the cover being ramified away from two and
Frattini over it; so orthogonality is summing to zero over each block.  Each defect in turn is the
obstruction of the cut field, because it vanishes wherever the trivial defect is available. -/
theorem exists_scholz_solution_lift_two_canonical {N : ℕ} {Ĝ G H : Type} [Group Ĝ] [Group G]
    [Group H] [Finite Ĝ] {f : G →* H} {g : Ĝ →* G} {fg : Ĝ →* H} (hfg : ∀ x, fg x = f (g x))
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hZ : fg.ker ≤ Subgroup.center Ĝ) (hfr : fg.ker ≤ frattini Ĝ)
    (hcard : Nat.card ↥f.ker = 2) (s : ↥f.ker →* ↥fg.ker) (hs : ∀ z : ↥f.ker, g ↑(s z) = ↑z)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hschA : IsScholz 2 (N + 1) ↥A) (eA : Gal(↥A/ℚ) ≃* H)
    (T : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥T] [IsGalois ℚ ↥T] (hAT : A ≤ T)
    (hramT : IsScholzOver 2 (N + 1) ↥A ↥T) (ψ₀ : Gal(↥T/ℚ) ≃* Ĝ)
    (hcomp₀ : ∀ τ, fg (ψ₀ τ) = eA (galRestrictLE hAT τ)) (S : Finset ℕ)
    (hSprime : ∀ q ∈ S, q.Prime) (hAS : ∀ q ∈ ramifiedSet ↥A, q ∈ S)
    (hSsplit : ∀ q ∈ S, q ∉ ramifiedSet ↥A → SplitsCompletely ↥A q) (hS4 : ∀ q ∈ S, q % 4 = 1)
    {ι : Type*} {block : ι → Finset ℕ} (hspan : IsBlockSpanned A block)
    (hdefect : ∀ i, ∑ p : {q // q ∈ S},
      canonicalDefect ↥(cutField (g.comp ψ₀.toMonoidHom)) (p : ℕ) * blockVector S (block i) p = 0) :
    ∃ (E T' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAE : A ≤ E) (hET' : E ≤ T')
      (_ : NumberField ↥E) (_ : IsGalois ℚ ↥E) (_ : NumberField ↥T') (_ : IsGalois ℚ ↥T'),
      IsScholz 2 (N + 1) ↥E ∧ (∀ q ∈ S, IsSplitInertiaAt ↥E q) ∧
        ramifiedSet ↥T' ⊆ ramifiedSet ↥T ∪ ramifiedSet ↥E ∧ IsLevel 2 (N + 1) ↥T' ∧
        ∃ (ψ : Gal(↥E/ℚ) ≃* G) (Ψ : Gal(↥T'/ℚ) ≃* Ĝ),
          (∀ τ, f (ψ τ) = eA (galRestrictLE hAE τ)) ∧
          (∀ τ, ψ (galRestrictLE hET' τ) = g (Ψ τ)) ∧
          ∀ (W : Type) [Group W] (u : Ĝ →* W), (∀ z : ↥f.ker, u ↑(s z) = 1) →
            cutField (u.comp Ψ.toMonoidHom) = cutField (u.comp ψ₀.toMonoidHom) := by
  classical
  have hLsurj : Function.Surjective (g.comp ψ₀.toMonoidHom) := hg.comp ψ₀.surjective
  have h2A : (2 : ℕ) ∉ ramifiedSet ↥A := fun h => by
    have h4 := hS4 2 (hAS 2 h)
    norm_num at h4
  have h2T : (2 : ℕ) ∉ ramifiedSet ↥T := by
    intro h
    rcases hramT 2 h with h' | ⟨h', -⟩
    · exact h2A h'
    · have hdvd : (2 : ℕ) ∣ 2 ^ (N + 1) := dvd_pow_self 2 (Nat.succ_ne_zero N)
      have h2 : (2 : ℕ) ≡ 1 [MOD 2] := h'.of_dvd hdvd
      simp [Nat.ModEq] at h2
  have hfrT : (galRestrictLE hAT).ker ≤ frattini Gal(↥T/ℚ) :=
    ker_galRestrictLE_le_frattini_of_comp hAT hfr hcomp₀
  refine exists_scholz_solution_lift_of_forall_prod_eq_one Nat.prime_two hfg hf hg hZ hfr hcard s hs
    A hschA eA T hAT hramT ψ₀ hcomp₀ S hSprime hAS hSsplit ?_
  intro M _ _ hTM Θ hΘ ν hν hνinj t hinert hzero a ha
  have hLM : cutField (g.comp ψ₀.toMonoidHom) ≤ M := (cutField_le _).trans hTM
  have hΘ' : ∀ σ : Gal(↥M/ℚ),
      Θ σ = galEquivCutField (g.comp ψ₀.toMonoidHom) hLsurj (galRestrictLE hLM σ) := by
    intro σ
    have hstep : galRestrictLE hLM σ
        = galRestrictLE (cutField_le (g.comp ψ₀.toMonoidHom)) (galRestrictLE hTM σ) :=
      (galRestrictLE_galRestrictLE (cutField_le (g.comp ψ₀.toMonoidHom)) hTM σ).symm
    rw [hΘ σ, hstep, galEquivCutField_galRestrictLE]
    rfl
  have ht : ∀ p : {q // q ∈ S},
      t p = canonicalDefect ↥(cutField (g.comp ψ₀.toMonoidHom)) (p : ℕ) := fun p =>
    eq_canonicalDefect (hSprime p p.2) hLM (galEquivCutField (g.comp ψ₀.toMonoidHom) hLsurj) Θ hΘ'
      ν (t p) (hinert p) (hzero p)
  refine sum_mul_eq_zero_of_sq_mem_auxConstraintField A T hAT hfrT h2T hS4 (hspan S hSprime)
    (fun i => ?_) ha
  simp only [ht]
  exact hdefect i

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The residue correction on a cover at the prime two, with the sums read as the obstructions of
the blocks.** -/
theorem exists_scholz_solution_lift_two_blockDefect {N : ℕ} {Ĝ G H : Type} [Group Ĝ] [Group G]
    [Group H] [Finite Ĝ] {f : G →* H} {g : Ĝ →* G} {fg : Ĝ →* H} (hfg : ∀ x, fg x = f (g x))
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hZ : fg.ker ≤ Subgroup.center Ĝ) (hfr : fg.ker ≤ frattini Ĝ)
    (hcard : Nat.card ↥f.ker = 2) (s : ↥f.ker →* ↥fg.ker) (hs : ∀ z : ↥f.ker, g ↑(s z) = ↑z)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hschA : IsScholz 2 (N + 1) ↥A) (eA : Gal(↥A/ℚ) ≃* H)
    (T : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥T] [IsGalois ℚ ↥T] (hAT : A ≤ T)
    (hramT : IsScholzOver 2 (N + 1) ↥A ↥T) (ψ₀ : Gal(↥T/ℚ) ≃* Ĝ)
    (hcomp₀ : ∀ τ, fg (ψ₀ τ) = eA (galRestrictLE hAT τ)) (S : Finset ℕ)
    (hSprime : ∀ q ∈ S, q.Prime) (hAS : ∀ q ∈ ramifiedSet ↥A, q ∈ S)
    (hSsplit : ∀ q ∈ S, q ∉ ramifiedSet ↥A → SplitsCompletely ↥A q) (hS4 : ∀ q ∈ S, q % 4 = 1)
    {ι : Type*} {block : ι → Finset ℕ} (hspan : IsBlockSpanned A block)
    (hBS : ∀ i, block i ⊆ S)
    (hdefect : ∀ i, blockDefect ↥(cutField (g.comp ψ₀.toMonoidHom)) (block i) = 0) :
    ∃ (E T' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAE : A ≤ E) (hET' : E ≤ T')
      (_ : NumberField ↥E) (_ : IsGalois ℚ ↥E) (_ : NumberField ↥T') (_ : IsGalois ℚ ↥T'),
      IsScholz 2 (N + 1) ↥E ∧ (∀ q ∈ S, IsSplitInertiaAt ↥E q) ∧
        ramifiedSet ↥T' ⊆ ramifiedSet ↥T ∪ ramifiedSet ↥E ∧ IsLevel 2 (N + 1) ↥T' ∧
        ∃ (ψ : Gal(↥E/ℚ) ≃* G) (Ψ : Gal(↥T'/ℚ) ≃* Ĝ),
          (∀ τ, f (ψ τ) = eA (galRestrictLE hAE τ)) ∧
          (∀ τ, ψ (galRestrictLE hET' τ) = g (Ψ τ)) ∧
          ∀ (W : Type) [Group W] (u : Ĝ →* W), (∀ z : ↥f.ker, u ↑(s z) = 1) →
            cutField (u.comp Ψ.toMonoidHom) = cutField (u.comp ψ₀.toMonoidHom) :=
  exists_scholz_solution_lift_two_canonical hfg hf hg hZ hfr hcard s hs A hschA eA T hAT hramT ψ₀
    hcomp₀ S hSprime hAS hSsplit hS4 hspan fun i => by
      rw [sum_blockVector_eq_blockDefect (hBS i)]
      exact hdefect i

end InverseGalois.CFT
