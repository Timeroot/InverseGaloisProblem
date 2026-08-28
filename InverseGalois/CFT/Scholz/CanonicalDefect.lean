/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.DyadicResidueCorrection
import InverseGalois.CFT.Scholz.SplitInertiaAt

/-!
# The canonical Frobenius defect of a solution

A solution of a central embedding problem with kernel of order two carries, at each prime ramified
in the field below, a defect: the amount by which the image of an arithmetic Frobenius misses the
image of the inertia group.  The defect is only pinned down once the trivial one is preferred
whenever it is available, and then it is not a piece of data at all but a property of the prime and
of the field the solution lives over: it vanishes exactly when the prime has split inertia there.

That is the **Scholz obstruction** of the prime.  It is read off from the field alone — not from the
larger field the solution is examined inside, nor from the identification of the kernel with the
group of order two — so it survives any base change, and the condition the residue correction asks
for becomes a condition on the field and the family of blocks only.

## Main definitions

* `InverseGalois.CFT.canonicalDefect`: the Scholz obstruction of a prime in a number field.

## Main results

* `InverseGalois.CFT.eq_canonicalDefect`: **a defect that vanishes wherever the trivial defect is
  available is the canonical one.**
* `InverseGalois.CFT.exists_scholz_solution_two_canonical` and
  `InverseGalois.CFT.isScholzRealizable_of_solution_two_canonical`: **the residue correction, with
  the orthogonality condition read on the canonical defect.**

## Tags

Scholz–Reichardt, embedding problem, residue correction, Scholz obstruction, prime two
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

open scoped Classical in
/-- **The Scholz obstruction of a rational prime in a number field**: zero when the prime has split
inertia there, and one otherwise.  It is the defect an arithmetic Frobenius above the prime has
against the inertia group, seen through a solution of a central embedding problem with kernel of
order two over the field. -/
noncomputable def canonicalDefect (K : Type*) [Field K] [NumberField K] (q : ℕ) : ZMod 2 :=
  if IsSplitInertiaAt K q then 0 else 1

theorem canonicalDefect_eq_zero {K : Type*} [Field K] [NumberField K] {q : ℕ}
    (h : IsSplitInertiaAt K q) : canonicalDefect K q = 0 := by
  classical
  simp [canonicalDefect, h]

theorem canonicalDefect_eq_one {K : Type*} [Field K] [NumberField K] {q : ℕ}
    (h : ¬ IsSplitInertiaAt K q) : canonicalDefect K q = 1 := by
  classical
  simp [canonicalDefect, h]

theorem canonicalDefect_eq_zero_iff {K : Type*} [Field K] [NumberField K] {q : ℕ} :
    canonicalDefect K q = 0 ↔ IsSplitInertiaAt K q := by
  refine ⟨fun h => ?_, canonicalDefect_eq_zero⟩
  by_contra hc
  rw [canonicalDefect_eq_one hc] at h
  exact one_ne_zero h

/-! ### The defect of a solution is the canonical one -/

section Solution

variable {L M : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L] [IsGalois ℚ ↥L]
  [NumberField ↥M] [IsGalois ℚ ↥M] {G : Type*} [Group G]

/-- **A defect that vanishes wherever the trivial defect is available is the canonical one.**  If
the prime has split inertia below then the trivial defect is available, so the defect vanishes; and
if the defect vanishes then the trivial defect is the one recorded, so the prime has split inertia
below. -/
theorem eq_canonicalDefect {q : ℕ} (hq : q.Prime) (hLM : L ≤ M) (ψ₀ : Gal(↥L/ℚ) ≃* G)
    (Θ : Gal(↥M/ℚ) →* G) (hΘ : ∀ σ, Θ σ = ψ₀ (galRestrictLE hLM σ))
    (ν : Multiplicative (ZMod 2) →* G) (x : ZMod 2)
    (hinert : ∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime, ∃ _ : P.LiesOver (Ideal.span {(q : ℤ)}),
      ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
        Θ σ * ν (Multiplicative.ofAdd x) ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ)
    (hzero : (∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime, ∃ _ : P.LiesOver (Ideal.span {(q : ℤ)}),
        ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P → Θ σ ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) →
      x = 0) :
    x = canonicalDefect ↥L q := by
  by_cases h : IsSplitInertiaAt ↥L q
  · rw [canonicalDefect_eq_zero h]
    exact hzero ((exists_forall_mem_map_inertia_iff hLM ψ₀ Θ hΘ hq).mpr h)
  · rw [canonicalDefect_eq_one h]
    have hx : x ≠ 0 := by
      intro hx0
      refine h ((exists_forall_mem_map_inertia_iff hLM ψ₀ Θ hΘ hq).mp ?_)
      obtain ⟨P, hPp, hPo, hP⟩ := hinert
      refine ⟨P, hPp, hPo, fun σ hσ => ?_⟩
      have := hP σ hσ
      rw [hx0] at this
      simpa using this
    have hbit : ∀ y : ZMod 2, y ≠ 0 → y = 1 := by decide
    exact hbit x hx

end Solution

/-! ### The residue correction on the canonical defect -/

/-- **A solution of a central Frattini embedding problem with kernel of order two whose canonical
defects sum to zero over each block of a family accounting for the square roots of products of
ramified primes is corrected to a Scholz field over the one below.**  Every defect a solution can
carry is the canonical one, so the orthogonality the correction asks for is a condition on the field
and the family of blocks alone.  The defects are read at a prescribed finite set of primes,
congruent to one modulo four, containing the ramified ones and split completely below elsewhere; the
correction then also gives residue degree one at every prime of that set. -/
theorem exists_scholz_solution_two_canonical {N : ℕ} {G H : Type} [Group G] [Group H] [Finite G]
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
    (hdefect : ∀ i, ∑ p : {q // q ∈ S},
      canonicalDefect ↥L (p : ℕ) * blockVector S (block i) p = 0) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAE : A ≤ E) (_ : NumberField ↥E),
      IsGalois ℚ ↥E ∧ IsScholz 2 (N + 1) ↥E ∧ (∀ q ∈ S, IsSplitInertiaAt ↥E q) ∧
        ∃ ψ : Gal(↥E/ℚ) ≃* G, ∀ τ, f (ψ τ) = eA (galRestrictLE hAE τ) := by
  refine exists_scholz_solution_two hf hZ hfr hcard A hschA eA L hAL hramL ψ₀ hcomp₀ S hSprime
    hAS hSsplit hS4 hspan ?_
  intro M _ _ hLM Θ hΘ ν _ _ t hinert hzero i
  have ht : ∀ p : {q // q ∈ S}, t p = canonicalDefect ↥L (p : ℕ) := fun p =>
    eq_canonicalDefect (hSprime p p.2) hLM ψ₀ Θ hΘ ν (t p) (hinert p) (hzero p)
  simp only [ht]
  exact hdefect i

/-- **A solution of a central Frattini embedding problem with kernel of order two whose canonical
defects sum to zero over each block of a family accounting for the square roots of products of
ramified primes gives a Scholz realization at the given level.** -/
theorem isScholzRealizable_of_solution_two_canonical {N : ℕ} {G H : Type} [Group G] [Group H]
    [Finite G] {f : G →* H} (hf : Function.Surjective f) (hZ : f.ker ≤ Subgroup.center G)
    (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = 2)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hschA : IsScholz 2 (N + 2) ↥A) (eA : Gal(↥A/ℚ) ≃* H)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] [IsGalois ℚ ↥L] (hAL : A ≤ L)
    (hramL : IsScholzOver 2 (N + 2) ↥A ↥L) (ψ₀ : Gal(↥L/ℚ) ≃* G)
    (hcomp₀ : ∀ τ, f (ψ₀ τ) = eA (galRestrictLE hAL τ))
    {ι : Type*} {block : ι → Finset ℕ} (hspan : IsBlockSpanned A block)
    (hdefect : ∀ i, ∑ p : {q // q ∈ (finite_ramifiedSet ↥A).toFinset},
      canonicalDefect ↥L (p : ℕ) *
        blockVector (finite_ramifiedSet ↥A).toFinset (block i) p = 0) :
    IsScholzRealizable G 2 (N + 1) := by
  have hS4 : ∀ p ∈ (finite_ramifiedSet ↥A).toFinset, p % 4 = 1 := by
    intro p hp
    have hdvd : (4 : ℕ) ∣ 2 ^ (N + 2) := ⟨2 ^ N, by ring⟩
    have hmod : p ≡ 1 [MOD 4] := (hschA.1 p ((Set.Finite.mem_toFinset _).mp hp)).of_dvd hdvd
    simpa [Nat.ModEq] using hmod
  obtain ⟨E, -, hNF, hGal, hsch, -, ψ, -⟩ := exists_scholz_solution_two_canonical hf hZ hfr hcard A
    hschA eA L hAL hramL ψ₀ hcomp₀ (finite_ramifiedSet ↥A).toFinset
    (fun q hq => ((Set.Finite.mem_toFinset _).mp hq).1)
    (fun q hq => (Set.Finite.mem_toFinset _).mpr hq)
    (fun q hq hq' => absurd ((Set.Finite.mem_toFinset _).mp hq) hq') hS4 hspan hdefect
  haveI := hNF
  haveI := hGal
  exact isScholzRealizable_of_isGalois ↥E hsch ψ

end InverseGalois.CFT
