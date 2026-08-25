/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.Splitting
import InverseGalois.CFT.RestrictLE
import InverseGalois.CFT.Scholz.BaseDescent
import InverseGalois.CFT.Scholz.ProperSolution

/-!
# The central step of the Scholz-Reichardt induction, over the rationals

A central Frattini embedding problem with kernel of odd prime order `ℓ` posed over a field `A`
satisfying Serre's condition is solved in two moves.  First the base is enlarged to the `ℓ`-th
cyclotomic field, where the roots of unity the local-global criterion needs are available, and the
problem is solved over the compositum.  Then the solution is descended: the automorphisms fixing the
cyclotomic field form a subgroup of index `ℓ - 1`, which is coprime to the order of the kernel, so
the group-theoretic descent along a subgroup of coprime index returns a solution over the rationals.

The field produced by the first move is Galois only over the cyclotomic field, so the second move is
applied to its normal closure over the rationals.

## Main results

* `InverseGalois.CFT.splitsCompletely_cycSubfield_of_isLevel`: a field whose ramified primes are
  congruent to one modulo a positive power of `ℓ` has all of them split completely in the `ℓ`-th
  cyclotomic field.
* `InverseGalois.CFT.exists_surjective_hom_of_isScholz`: **a central Frattini embedding problem with
  kernel of odd prime order `ℓ` posed over a field of `ℓ`-power degree satisfying Serre's condition
  one level higher is solved over a Galois extension of the rationals**, provided the primes
  ramifying in that field split completely in the `ℓ`-th cyclotomic field.
* `InverseGalois.CFT.exists_surjective_hom_of_centralStep`: **the same conclusion under exactly the
  hypotheses of the central step of the Scholz-Reichardt induction**, where the field realises the
  quotient and Serre's condition supplies the splitting behaviour by itself.

## Tags

embedding problem, Scholz condition, cyclotomic base change, descent
-/

namespace InverseGalois.CFT

open IntermediateField Module NumberField InverseGalois.NumberTheory

variable {ℓ : ℕ} [NeZero ℓ]

/-- **A field whose ramified primes are congruent to one modulo a positive power of `ℓ` has all of
them split completely in the `ℓ`-th cyclotomic field.**  Such a prime is congruent to one modulo
`ℓ` itself, hence differs from `ℓ`, and the cyclotomic splitting law applies. -/
theorem splitsCompletely_cycSubfield_of_isLevel {n : ℕ} (hℓ : ℓ.Prime) (hn : n ≠ 0)
    {E : Type*} [Field E] [NumberField E] (h : IsLevel ℓ n E) :
    ∀ p ∈ ramifiedSet E, SplitsCompletely ↥(cycSubfield ℓ) p := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp.1⟩
  have hmod : p ≡ 1 [MOD ℓ] := (h p hp).of_dvd (dvd_pow_self ℓ hn)
  have hdvd : ¬ p ∣ ℓ := by
    intro hd
    have hpl : p = ℓ := (Nat.prime_dvd_prime_iff_eq hp.1 hℓ).mp hd
    rw [hpl] at hmod
    have h1 : ℓ ∣ ℓ - 1 := (Nat.modEq_iff_dvd' hℓ.one_le).mp hmod.symm
    have h2 := Nat.le_of_dvd (Nat.sub_pos_of_lt hℓ.one_lt) h1
    have h3 := hℓ.one_lt
    omega
  exact splitsCompletely_of_modEq ℓ ↥(cycSubfield ℓ) p hdvd hmod

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem with kernel of odd prime order `ℓ` posed over a field of
`ℓ`-power degree satisfying Serre's condition one level higher is solved over a Galois extension of
the rationals**, provided the primes ramifying in that field split completely in the `ℓ`-th
cyclotomic field.  The solution is obtained over the compositum with the cyclotomic field and then
descended along a subgroup of index prime to `ℓ`. -/
theorem exists_surjective_hom_of_isScholz (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H} (hf : Function.Surjective f)
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = ℓ) {t : H → G} (ht : ∀ h, f (t h) = h) {M : ℕ}
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥A] [NumberField ↥A]
    (hG : IsPGroup ℓ Gal(↥A/ℚ)) (hsch : IsScholz ℓ (M + 1) ↥A)
    (hdvd : Nat.card Gal(↥A/ℚ) ∣ ℓ ^ M)
    (hsplit : ∀ p ∈ ramifiedSet ↥A, SplitsCompletely ↥(cycSubfield ℓ) p)
    {π₀ : Gal(↥A/ℚ) →* H} (hπ₀ : Function.Surjective π₀) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAE : A ≤ E), NumberField ↥E ∧
      IsGalois ℚ ↥E ∧ ∃ ψ : Gal(↥E/ℚ) →* G, Function.Surjective ψ ∧
        ∀ τ, f (ψ τ) = π₀ (galRestrictLE hAE τ) := by
  have hcop : Nat.Coprime (finrank ℚ ↥A) (Nat.totient ℓ) := by
    rw [← IsGalois.card_aut_eq_finrank ℚ ↥A]
    exact Nat.Coprime.coprime_dvd_left hdvd (coprime_pow_totient hℓ M)
  have hπ : Function.Surjective (π₀.comp (galEquivCycBase ℓ A hcop).toMonoidHom) :=
    hπ₀.comp (galEquivCycBase ℓ A hcop).surjective
  obtain ⟨N, hKN, hNFN, hGalN, ρ, -, hρcoe, φ, hφsurj, hφ⟩ :=
    hasProperSolution_cycBaseChange hℓ hodd hZ hfr hcard ht A hG hsch hdvd hsplit hπ
  haveI := hNFN
  haveI := hGalN
  haveI : FiniteDimensional ℚ ↥(N.restrictScalars ℚ) := inferInstanceAs (FiniteDimensional ℚ ↥N)
  set E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    normalClosure ℚ ↥(N.restrictScalars ℚ) (AlgebraicClosure ℚ) with hEdef
  have hNE : N.restrictScalars ℚ ≤ E := IntermediateField.le_normalClosure _
  haveI : FiniteDimensional ℚ ↥E := by
    rw [hEdef]; exact normalClosure.is_finiteDimensional ℚ ↥(N.restrictScalars ℚ) _
  haveI : Normal ℚ ↥E := by
    rw [hEdef]; exact normalClosure.normal ℚ ↥(N.restrictScalars ℚ) _
  haveI : IsGalois ℚ ↥E := ⟨⟩
  haveI : NumberField ↥E := ⟨⟩
  have hAE : A ≤ E := fun _ hx => hNE (hKN ((le_sup_left : A ≤ A ⊔ cycSubfield ℓ) hx))
  have hQE : cycSubfield ℓ ≤ E := fun _ hx =>
    hNE (hKN ((le_sup_right : cycSubfield ℓ ≤ A ⊔ cycSubfield ℓ) hx))
  have hNEover : N ≤ extendScalars hQE := fun _ hx => hNE hx
  have hcop2 : Nat.Coprime (finrank ℚ ↥(cycSubfield ℓ)) (Nat.card ↥f.ker) := by
    rw [hcard, finrank_cycSubfield]
    simpa using (coprime_pow_totient hℓ 1).symm
  letI : Algebra ↥(cycSubfield ℓ) ↥E :=
    inferInstanceAs (Algebra ↥(cycSubfield ℓ) ↥(extendScalars hQE))
  haveI : IsScalarTower ℚ ↥(cycSubfield ℓ) ↥E :=
    inferInstanceAs (IsScalarTower ℚ ↥(cycSubfield ℓ) ↥(extendScalars hQE))
  have hstep : ∀ u : Gal(↥E/↥(cycSubfield ℓ)),
      f (φ (galRestrictLE hNEover u)) = π₀ (galRestrictLE hAE (galRestrictScalars ℚ u)) := by
    intro u
    rw [hφ (galRestrictLE hNEover u)]
    refine congrArg π₀ (AlgEquiv.ext fun x => Subtype.ext ?_)
    show ((galRestrictBase A (cycSubfield ℓ) (ρ (galRestrictLE hNEover u)) x : ↥A) :
      AlgebraicClosure ℚ) = _
    rw [coe_galRestrictBase, coe_galRestrictLE hAE,
      hρcoe (galRestrictLE hNEover u) (x : AlgebraicClosure ℚ) _
        (hKN ((le_sup_left : A ≤ A ⊔ cycSubfield ℓ) x.2)),
      coe_galRestrictLE hNEover]
    rfl
  obtain ⟨ψ, hψsurj, hψ⟩ :=
    exists_surjective_hom_of_coprime_finrank (F := ℚ) (k := ↥(cycSubfield ℓ)) (E := ↥E)
      hf hZ hfr hcop2 (π := π₀.comp (galRestrictLE hAE))
      (hπ₀.comp (galRestrictLE_surjective hAE)) (φ.comp (galRestrictLE hNEover)) hstep
  exact ⟨E, hAE, inferInstance, inferInstance, ψ, hψsurj, hψ⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The central step of the Scholz-Reichardt induction produces a solution field over the
rationals.**  Starting from a field realising the quotient and satisfying Serre's condition one
level above the order of that quotient, a central Frattini embedding problem with kernel of odd
prime order `ℓ` is solved by a Galois extension of the rationals containing that field.  The
splitting behaviour needed over the cyclotomic field is part of Serre's condition. -/
theorem exists_surjective_hom_of_centralStep (hℓ : ℓ.Prime) (hodd : Odd ℓ) {N : ℕ}
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H} (hf : Function.Surjective f)
    (hpg : IsPGroup ℓ G) (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = ℓ) (hHdvd : Nat.card H ∣ ℓ ^ N)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥A] [NumberField ↥A]
    (hsch : IsScholz ℓ (N + 1) ↥A) (e : Gal(↥A/ℚ) ≃* H) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAE : A ≤ E), NumberField ↥E ∧
      IsGalois ℚ ↥E ∧ ∃ ψ : Gal(↥E/ℚ) →* G, Function.Surjective ψ ∧
        ∀ τ, f (ψ τ) = e (galRestrictLE hAE τ) := by
  have hG : IsPGroup ℓ Gal(↥A/ℚ) := (hpg.of_surjective f hf).of_equiv e.symm
  have hdvd : Nat.card Gal(↥A/ℚ) ∣ ℓ ^ N := by
    rw [Nat.card_congr e.toEquiv]
    exact hHdvd
  exact exists_surjective_hom_of_isScholz hℓ hodd hf hZ hfr hcard
    (t := Function.surjInv hf) (fun h => Function.surjInv_eq hf h) A hG hsch hdvd
    (splitsCompletely_cycSubfield_of_isLevel hℓ (Nat.succ_ne_zero N) hsch.isLevel)
    (π₀ := e.toMonoidHom) e.surjective

end InverseGalois.CFT
