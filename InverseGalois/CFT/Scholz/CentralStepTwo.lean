/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.RestrictLE
import InverseGalois.CFT.Scholz.ProperSolutionTwo

/-!
# The central step of order two, over the rationals

A central Frattini embedding problem with kernel of odd prime order `ℓ` is solved over the `ℓ`-th
cyclotomic base and the solution is then descended along a subgroup of index prime to `ℓ`.  For a
kernel of order two the cyclotomic base is the rational field itself, so the solution is already
defined over the rationals and no descent step is needed: the field produced by the local-global
criterion is Galois over the rationals and the restriction homomorphism it comes with is the
restriction of automorphisms.

## Main results

* `InverseGalois.CFT.exists_surjective_hom_of_isScholz_two`: **a central Frattini embedding problem
  with kernel of order two posed over a field of two-power degree satisfying Serre's condition one
  level higher is solved over a Galois extension of the rationals.**
* `InverseGalois.CFT.exists_surjective_hom_of_centralStep_two`: **the same conclusion under exactly
  the hypotheses of the central step of the Scholz-Reichardt induction**, where the field realises
  the quotient.

## Tags

embedding problem, Scholz condition, central extension, two-group
-/

namespace InverseGalois.CFT

open IntermediateField NumberField InverseGalois.NumberTheory

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem with kernel of order two posed over a field of two-power
degree satisfying Serre's condition one level higher is solved over a Galois extension of the
rationals.**  The local-global criterion over the rationals produces the solution field directly,
and the homomorphism onto the Galois group of `A` that comes with it is the restriction of
automorphisms because it acts as the original automorphism inside the ambient field. -/
theorem exists_surjective_hom_of_isScholz_two
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = 2)
    {t : H → G} (ht : ∀ h, f (t h) = h) {M : ℕ}
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥A] [NumberField ↥A]
    (hG : IsPGroup 2 Gal(↥A/ℚ)) (hsch : IsScholz 2 (M + 1) ↥A)
    (hdvd : Nat.card Gal(↥A/ℚ) ∣ 2 ^ M)
    {π₀ : Gal(↥A/ℚ) →* H} (hπ₀ : Function.Surjective π₀) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAE : A ≤ E), NumberField ↥E ∧
      IsGalois ℚ ↥E ∧ ∃ ψ : Gal(↥E/ℚ) →* G, Function.Surjective ψ ∧
        ∀ τ, f (ψ τ) = π₀ (galRestrictLE hAE τ) := by
  obtain ⟨E, hAE, hNF, hGal, ρ, -, hρcoe, φ, hφsurj, hφ⟩ :=
    hasProperSolution_two hZ hfr hcard ht A hG hsch hdvd hπ₀
  haveI := hNF
  haveI := hGal
  refine ⟨E, hAE, inferInstance, inferInstance, φ, hφsurj, fun τ => ?_⟩
  rw [hφ τ]
  refine congrArg π₀ (AlgEquiv.ext fun x => Subtype.ext ?_)
  rw [coe_galRestrictLE hAE]
  exact hρcoe τ (x : AlgebraicClosure ℚ) x.2 (hAE x.2)

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The central step of the Scholz-Reichardt induction at the prime two produces a solution field
over the rationals.**  Starting from a field realising the quotient and satisfying Serre's condition
one level above the order of that quotient, a central Frattini embedding problem with kernel of
order two is solved by a Galois extension of the rationals containing that field. -/
theorem exists_surjective_hom_of_centralStep_two {N : ℕ}
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H} (hf : Function.Surjective f)
    (hpg : IsPGroup 2 G) (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = 2) (hHdvd : Nat.card H ∣ 2 ^ N)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥A] [NumberField ↥A]
    (hsch : IsScholz 2 (N + 1) ↥A) (e : Gal(↥A/ℚ) ≃* H) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAE : A ≤ E), NumberField ↥E ∧
      IsGalois ℚ ↥E ∧ ∃ ψ : Gal(↥E/ℚ) →* G, Function.Surjective ψ ∧
        ∀ τ, f (ψ τ) = e (galRestrictLE hAE τ) := by
  have hG : IsPGroup 2 Gal(↥A/ℚ) := (hpg.of_surjective f hf).of_equiv e.symm
  have hdvd : Nat.card Gal(↥A/ℚ) ∣ 2 ^ N := by
    rw [Nat.card_congr e.toEquiv]
    exact hHdvd
  exact exists_surjective_hom_of_isScholz_two hZ hfr hcard
    (t := Function.surjInv hf) (fun h => Function.surjInv_eq hf h) A hG hsch hdvd
    (π₀ := e.toMonoidHom) e.surjective

end InverseGalois.CFT
