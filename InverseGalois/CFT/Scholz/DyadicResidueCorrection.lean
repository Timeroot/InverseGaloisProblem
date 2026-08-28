/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.DyadicSocle
import InverseGalois.CFT.Scholz.ResidueCorrection

/-!
# The residue correction at the prime two

At an odd prime the exponent vectors whose radicand is already a root in the constraint field are
all zero, so the correcting character is available for every configuration of Frobenius defects.
At the prime two they are not, and the correction is available exactly for the defects orthogonal
to them.

The square roots of products of ramified primes lying in the constraint field already lie in the
field below the solution, so if those are accounted for by a family of blocks of ramified primes
then it is enough that the Frobenius defects sum to zero over each block.  That is the shape in
which the vanishing is arranged, by collapsing a redundant family of blocks.

## Main results

* `InverseGalois.CFT.exists_scholz_solution_two`: **a solution of a central Frattini embedding
  problem with kernel of order two, whose Frobenius defects sum to zero over each block of a family
  accounting for the square roots of products of ramified primes, is corrected to a Scholz field
  over the one below.**
* `InverseGalois.CFT.isScholzRealizable_of_solution_two`: the same statement, read as a Scholz
  realization at the given level.

## Tags

Scholz–Reichardt, embedding problem, residue correction, prime two, block
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-- **A solution of a central Frattini embedding problem with kernel of order two, whose Frobenius
defects sum to zero over each block of a family accounting for the square roots of products of
ramified primes, is corrected to a Scholz field over the one below.**  A square root of such a
product lying in the constraint field lies in the solution, because the cyclotomic layer of the
constraint field is ramified only at two while the solution is not; and it lies in the field below,
because the automorphisms fixing that field lie in the Frattini subgroup.  So the blocks account for
every exponent vector obstructing the correction, and summing to zero over each block is
orthogonality to all of them.

The defects are read at a prescribed finite set of primes, congruent to one modulo four, containing
the ramified ones and split completely below elsewhere; the correction then also gives residue
degree one at every prime of that set. -/
theorem exists_scholz_solution_two {N : ℕ} {G H : Type} [Group G] [Group H] [Finite G]
    {f : G →* H} (hf : Function.Surjective f) (hZ : f.ker ≤ Subgroup.center G)
    (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = 2)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hschA : IsScholz 2 (N + 2) ↥A) (eA : Gal(↥A/ℚ) ≃* H)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] [IsGalois ℚ ↥L] (hAL : A ≤ L)
    (hramL : IsScholzOver 2 (N + 2) ↥A ↥L) (ψ₀ : Gal(↥L/ℚ) ≃* G)
    (hcomp₀ : ∀ τ, f (ψ₀ τ) = eA (galRestrictLE hAL τ)) (S : Finset ℕ)
    (hSprime : ∀ q ∈ S, q.Prime) (hAS : ∀ q ∈ ramifiedSet ↥A, q ∈ S)
    (hSsplit : ∀ q ∈ S, q ∉ ramifiedSet ↥A → SplitsCompletely ↥A q) (hS4 : ∀ q ∈ S, q % 4 = 1)
    {ι : Type*} {block : ι → Finset ℕ} (hspan : IsBlockSpanned A block)
    (hdefect : ∀ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥M] [IsGalois ℚ ↥M]
      (hLM : L ≤ M) (Θ : Gal(↥M/ℚ) →* G), (∀ σ, Θ σ = ψ₀ (galRestrictLE hLM σ)) →
      ∀ ν : Multiplicative (ZMod 2) →* G, (∀ x, ν x ∈ f.ker) → Function.Injective ν →
      ∀ t : {q // q ∈ S} → ZMod 2,
      (∀ q : {q // q ∈ S}, ∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ * ν (Multiplicative.ofAdd (t q)) ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) →
      (∀ q : {q // q ∈ S}, (∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) → t q = 0) →
      ∀ i, ∑ p, t p * blockVector S (block i) p = 0) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAE : A ≤ E) (_ : NumberField ↥E),
      IsGalois ℚ ↥E ∧ IsScholz 2 (N + 1) ↥E ∧ (∀ q ∈ S, IsSplitInertiaAt ↥E q) ∧
        ∃ ψ : Gal(↥E/ℚ) ≃* G, ∀ τ, f (ψ τ) = eA (galRestrictLE hAE τ) := by
  have h2A : (2 : ℕ) ∉ ramifiedSet ↥A := fun h => by
    have h4 := hS4 2 (hAS 2 h)
    norm_num at h4
  have h2L : (2 : ℕ) ∉ ramifiedSet ↥L := by
    intro h
    rcases hramL 2 h with h' | ⟨h', -⟩
    · exact h2A h'
    · have hdvd : (4 : ℕ) ∣ 2 ^ (N + 2) := ⟨2 ^ N, by ring⟩
      have h4 : (2 : ℕ) ≡ 1 [MOD 4] := h'.of_dvd hdvd
      simp [Nat.ModEq] at h4
  -- the automorphisms fixing the field below lie in the Frattini subgroup
  have hfrL : (galRestrictLE hAL).ker ≤ frattini Gal(↥L/ℚ) := by
    intro σ hσ
    have hker : ψ₀ σ ∈ f.ker := by
      rw [MonoidHom.mem_ker, hcomp₀ σ, MonoidHom.mem_ker.mp hσ, map_one]
    have hcomap : frattini G ≤ (frattini Gal(↥L/ℚ)).comap ψ₀.symm.toMonoidHom :=
      frattini_le_comap_frattini_of_surjective ψ₀.symm.surjective
    simpa using hcomap (hfr hker)
  refine exists_scholz_solution_of_forall_prod_eq_one Nat.prime_two hf hZ hfr hcard A
    hschA eA L hAL hramL ψ₀ hcomp₀ S hSprime hAS hSsplit ?_
  intro M _ _ hLM Θ hΘ ν hν hνinj t hinert hzero a ha
  exact sum_mul_eq_zero_of_sq_mem_auxConstraintField A L hAL hfrL h2L hS4 (hspan _ hSprime)
    (hdefect M hLM Θ hΘ ν hν hνinj t hinert hzero) ha

/-- **A solution of a central Frattini embedding problem with kernel of order two, whose Frobenius
defects sum to zero over each block of a family accounting for the square roots of products of
ramified primes, gives a Scholz realization at the given level.** -/
theorem isScholzRealizable_of_solution_two {N : ℕ} {G H : Type} [Group G] [Group H] [Finite G]
    {f : G →* H} (hf : Function.Surjective f) (hZ : f.ker ≤ Subgroup.center G)
    (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = 2)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hschA : IsScholz 2 (N + 2) ↥A) (eA : Gal(↥A/ℚ) ≃* H)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] [IsGalois ℚ ↥L] (hAL : A ≤ L)
    (hramL : IsScholzOver 2 (N + 2) ↥A ↥L) (ψ₀ : Gal(↥L/ℚ) ≃* G)
    (hcomp₀ : ∀ τ, f (ψ₀ τ) = eA (galRestrictLE hAL τ))
    {ι : Type*} {block : ι → Finset ℕ} (hspan : IsBlockSpanned A block)
    (hdefect : ∀ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥M] [IsGalois ℚ ↥M]
      (hLM : L ≤ M) (Θ : Gal(↥M/ℚ) →* G), (∀ σ, Θ σ = ψ₀ (galRestrictLE hLM σ)) →
      ∀ ν : Multiplicative (ZMod 2) →* G, (∀ x, ν x ∈ f.ker) → Function.Injective ν →
      ∀ t : {q // q ∈ (finite_ramifiedSet ↥A).toFinset} → ZMod 2,
      (∀ q : {q // q ∈ (finite_ramifiedSet ↥A).toFinset}, ∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ * ν (Multiplicative.ofAdd (t q)) ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) →
      (∀ q : {q // q ∈ (finite_ramifiedSet ↥A).toFinset}, (∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) → t q = 0) →
      ∀ i, ∑ p, t p * blockVector (finite_ramifiedSet ↥A).toFinset (block i) p = 0) :
    IsScholzRealizable G 2 (N + 1) := by
  have hS4 : ∀ p ∈ (finite_ramifiedSet ↥A).toFinset, p % 4 = 1 := by
    intro p hp
    have hdvd : (4 : ℕ) ∣ 2 ^ (N + 2) := ⟨2 ^ N, by ring⟩
    have hmod : p ≡ 1 [MOD 4] := (hschA.1 p ((Set.Finite.mem_toFinset _).mp hp)).of_dvd hdvd
    simpa [Nat.ModEq] using hmod
  obtain ⟨E, -, hNF, hGal, hsch, -, ψ, -⟩ :=
    exists_scholz_solution_two hf hZ hfr hcard A hschA eA L hAL hramL ψ₀ hcomp₀
      (finite_ramifiedSet ↥A).toFinset (fun q hq => ((Set.Finite.mem_toFinset _).mp hq).1)
      (fun q hq => (Set.Finite.mem_toFinset _).mpr hq)
      (fun q hq hq' => absurd ((Set.Finite.mem_toFinset _).mp hq) hq') hS4 hspan hdefect
  haveI := hNF
  haveI := hGal
  exact isScholzRealizable_of_isGalois ↥E hsch ψ

end InverseGalois.CFT
