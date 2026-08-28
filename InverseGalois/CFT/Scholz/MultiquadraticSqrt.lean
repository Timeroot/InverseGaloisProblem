/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Multiquadratic
import InverseGalois.CFT.PrimeProductSquare
import InverseGalois.CFT.Scholz.BlockGenerators
import InverseGalois.CFT.Scholz.MultiquadraticBase

/-!
# The multiquadratic base, with its square roots matched to the generators

The multiquadratic base of the dyadic induction carries a square root of each of the `d` distinct
primes it ramifies at.  Those square roots are independent: a product of a nonempty subfamily of
them is irrational, because its square is a squarefree product of primes.  So every pattern of
signs is realized by an automorphism, and the joint sign character is onto; the Galois group has
order `2 ^ d`, the same as the group of sign patterns, so the character is an isomorphism.

Transporting the coordinates of the free object of rank `d` and `2`-class one back along it
identifies the Galois group with that free object in such a way that the `k`-th distinguished
generator changes the sign of the `k`-th square root and of no other.  That is the form in which
the base enters the induction on the `2`-class.

## Main results

* `InverseGalois.CFT.exists_galEquiv_sqrtSign_gen`: **square roots of distinct primes identify the
  Galois group of a field of degree `2 ^ d` with the free object of rank `d` and `2`-class one,
  matching the square roots to the distinguished generators.**
* `InverseGalois.CFT.exists_scholz_freePClass_one_sqrt`: **the base of the dyadic
  Scholz–Reichardt induction**, with that identification.

## Tags

Scholz–Reichardt, multiquadratic field, square root, sign character, free object
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Matching the square roots to the generators -/

/-- **Square roots of distinct primes identify the Galois group with the free object of `2`-class
one, matching the square roots to the distinguished generators.**  A product of a nonempty
subfamily of the square roots is irrational, since its square is a squarefree product of primes, so
every sign pattern is realized by an automorphism; the group of sign patterns has the same order as
the Galois group, so the joint sign character is an isomorphism, and reading the coordinates of the
free object back along it matches the `k`-th generator to the `k`-th square root. -/
theorem exists_galEquiv_sqrtSign_gen {d : ℕ} (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField ↥K] [IsGalois ℚ ↥K] {q : Fin d → ℕ} (hqinj : Function.Injective q)
    (hqp : ∀ i, (q i).Prime) {v : Fin d → ↥K}
    (hvsq : ∀ i, v i ^ 2 = algebraMap ℚ ↥K ((q i : ℕ) : ℚ))
    (hcard : Nat.card Gal(↥K/ℚ) = 2 ^ d) :
    ∃ e : Gal(↥K/ℚ) ≃* FreePClass 2 d 1,
      ∀ k i, sqrtSign (v i) (e.symm (FreePClass.gen 2 d 1 k)) = if i = k then 1 else 0 := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hv : ∀ i, v i ≠ 0 := by
    intro i hzero
    have h0 : algebraMap ℚ ↥K ((q i : ℕ) : ℚ) = 0 := by
      rw [← hvsq i, hzero, zero_pow (by norm_num : 2 ≠ 0)]
    have hq0 : ((q i : ℕ) : ℚ) = 0 := (map_eq_zero_iff _ (algebraMap ℚ ↥K).injective).mp h0
    exact (hqp i).ne_zero (by exact_mod_cast hq0)
  set χ : Gal(↥K/ℚ) →* Multiplicative (Fin d → ZMod 2) := sqrtSignHom v hv hvsq with hχ
  have hsurj : Function.Surjective χ := by
    intro x
    have hside : ∀ S : Finset (Fin d), (∏ i ∈ S, v i) ∈ (⊥ : IntermediateField ℚ ↥K) →
        ∑ i ∈ S, Multiplicative.toAdd x i = 0 := by
      intro S hS
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hS
      have hsq : algebraMap ℚ ↥K (c ^ 2) = algebraMap ℚ ↥K (∏ i ∈ S, ((q i : ℕ) : ℚ)) := by
        rw [map_pow, hc, ← Finset.prod_pow, map_prod]
        exact Finset.prod_congr rfl fun i _ => hvsq i
      have hc2 : c ^ 2 = ∏ i ∈ S, ((q i : ℕ) : ℚ) := (algebraMap ℚ ↥K).injective hsq
      have hprod : ((∏ p ∈ S.image q, p : ℕ) : ℚ) = ∏ i ∈ S, ((q i : ℕ) : ℚ) := by
        rw [Nat.cast_prod]
        exact Finset.prod_image fun x _ y _ h => hqinj h
      have himg : S.image q = (∅ : Finset ℕ) := by
        refine eq_of_rat_sq_eq_prod_mul_prod (c := c) (fun p hp => ?_)
          (fun p hp => absurd hp (Finset.notMem_empty p)) ?_
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
          exact hqp i
        · rw [Finset.prod_empty, mul_one, hprod]
          exact hc2
      rw [Finset.image_eq_empty.mp himg, Finset.sum_empty]
    obtain ⟨σ, -, hσ⟩ :=
      exists_fixingSubgroup_map_eq_signZMod_mul (⊥ : IntermediateField ℚ ↥K) hvsq hv
        (Multiplicative.toAdd x) hside
    exact ⟨σ, congrArg Multiplicative.ofAdd
      (funext fun i => sqrtSign_eq_of_apply_eq (hv i) (hvsq i) (hσ i))⟩
  have hcard2 : Nat.card (Multiplicative (Fin d → ZMod 2)) = 2 ^ d :=
    (Nat.card_congr (FreePClass.coordEquiv 2 d).toEquiv).symm.trans (FreePClass.card_one 2 d)
  have hbij : Function.Bijective χ :=
    (Nat.bijective_iff_surjective_and_card χ).mpr ⟨hsurj, by rw [hcard, hcard2]⟩
  refine ⟨(MulEquiv.ofBijective χ hbij).trans (FreePClass.coordEquiv 2 d).symm, fun k i => ?_⟩
  have hkey : χ (((MulEquiv.ofBijective χ hbij).trans (FreePClass.coordEquiv 2 d).symm).symm
      (FreePClass.gen 2 d 1 k)) = Multiplicative.ofAdd (Pi.single k (1 : ZMod 2)) := by
    simp only [MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
    show (MulEquiv.ofBijective χ hbij) ((MulEquiv.ofBijective χ hbij).symm
      (FreePClass.coordEquiv 2 d (FreePClass.gen 2 d 1 k))) = _
    rw [MulEquiv.apply_symm_apply]
    exact FreePClass.coord_gen 2 d k
  have hfun : (fun j => sqrtSign (v j)
      (((MulEquiv.ofBijective χ hbij).trans (FreePClass.coordEquiv 2 d).symm).symm
        (FreePClass.gen 2 d 1 k))) = Pi.single k (1 : ZMod 2) :=
    congrArg Multiplicative.toAdd hkey
  rw [congrFun hfun i, Pi.single_apply]

/-! ### The base of the induction -/

/-- **The base of the dyadic Scholz–Reichardt induction.**  A field satisfying Serre's condition,
ramified at exactly `d` distinct primes, carrying a square root of each of them, and with its
Galois group identified with the free object of rank `d` and `2`-class one so that the `k`-th
distinguished generator changes the sign of the `k`-th square root alone. -/
theorem exists_scholz_freePClass_one_sqrt {N : ℕ} (hN : 2 ≤ N) (d : ℕ) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥K) (_ : IsGalois ℚ ↥K)
      (q : Fin d → ℕ) (v : Fin d → ↥K) (e : Gal(↥K/ℚ) ≃* FreePClass 2 d 1),
      Function.Injective q ∧ (∀ i, (q i).Prime) ∧ IsScholz 2 N ↥K ∧
        ramifiedSet ↥K = Set.range q ∧
        (∀ i, v i ^ 2 = algebraMap ℚ ↥K ((q i : ℕ) : ℚ)) ∧
        ∀ k i, sqrtSign (v i) (e.symm (FreePClass.gen 2 d 1 k)) = if i = k then 1 else 0 := by
  obtain ⟨K, hNF, hGal, q, v, hqinj, hqp, hsch, hram, hcard, -, hvsq⟩ :=
    exists_scholz_ramifiedSet_eq_range hN d
  haveI := hNF
  haveI := hGal
  obtain ⟨e, he⟩ := exists_galEquiv_sqrtSign_gen K hqinj hqp hvsq hcard
  exact ⟨K, hNF, hGal, q, v, e, hqinj, hqp, hsch, hram, hvsq, he⟩

end InverseGalois.CFT
