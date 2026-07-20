/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Polynomial.DedekindProof

/-!
# Dedekind-type facts for Xⁿ - X - 1

This file develops polynomial infrastructure for `Xⁿ - X - 1` and proves general
cycle-type consequences of Dedekind's theorem. It also contains an elementary lemma
turning a squarefree root count into factorization type `{2}`.

## Structure

The file is organized in layers:

1. **Polynomial infrastructure**: Integer and mod-p versions of `Xⁿ - X - 1`,
   with basic properties (monicity, degree, maps between rings).

2. **Dedekind's theorem**: A formulation relating mod-p factorization to Galois
   group cycle types, stated via `Equiv.Perm.cycleType`.

3. **Factorization analysis**: An elementary reduction from a root count over a finite
   field to factorization type `{2}`.

## Background

**Dedekind's Theorem**: Let `f ∈ ℤ[X]` be monic of degree `n` and let `p` be a prime
such that `f mod p` is squarefree (equivalently, `p ∤ disc(f)`). If the factorization
of `f mod p` into irreducibles over `𝔽_p` has degree types `(d₁, d₂, ..., dₖ)`, then
the Galois group of `f` over `ℚ` (viewed as a subgroup of `Sₙ` via the action on roots)
contains a permutation of cycle type `(d₁, d₂, ..., dₖ)`.

## References

* Dedekind, R. "Über Zusammenhang zwischen der Theorie der Ideale und der Theorie
  der höheren Kongruenzen", 1878.
* Selmer, E. S. "On the irreducibility of certain trinomials", 1956.
* Osada, H. "The Galois groups of the polynomials Xⁿ + aXˡ + b", 1987.
-/

open Polynomial UniqueFactorizationMonoid

noncomputable section

/-!
## Section 1: Polynomial Infrastructure
-/

/-- The polynomial `Xⁿ - X - 1` over `ℚ`. -/
def xnSubXSubOne' (n : ℕ) : ℚ[X] := X ^ n - X - C 1

/-- The polynomial `Xⁿ - X - 1` over `ℤ`, the "integral model". -/
def xnSubXSubOneZ (n : ℕ) : ℤ[X] := X ^ n - X - C 1

/-- The polynomial `Xⁿ - X - 1` over `ZMod p`, the "mod-p reduction". -/
def xnSubXSubOne_modp (n p : ℕ) : (ZMod p)[X] := X ^ n - X - C 1

/-- The ℚ-polynomial is the image of the ℤ-polynomial under the canonical map. -/
lemma xnSubXSubOne'_eq_map (n : ℕ) :
    xnSubXSubOne' n = (xnSubXSubOneZ n).map (Int.castRingHom ℚ) := by
  simp [xnSubXSubOne', xnSubXSubOneZ, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_one, Polynomial.map_X]

/-- The mod-p polynomial is the image of the ℤ-polynomial under reduction. -/
lemma xnSubXSubOne_modp_eq_map (n p : ℕ) :
    xnSubXSubOne_modp n p = (xnSubXSubOneZ n).map (Int.castRingHom (ZMod p)) := by
  simp [xnSubXSubOne_modp, xnSubXSubOneZ, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_one, Polynomial.map_X]

/-
The integral polynomial `Xⁿ - X - 1` is monic for `n ≥ 2`.
-/
lemma xnSubXSubOneZ_monic (n : ℕ) (hn : 2 ≤ n) : (xnSubXSubOneZ n).Monic := by
  unfold xnSubXSubOneZ
  erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
  · rw [Polynomial.coeff_one, Polynomial.coeff_X, if_neg, if_neg] <;> linarith
  · bv_omega

/-
The degree of `Xⁿ - X - 1` over ℤ equals `n` for `n ≥ 2`.
-/
lemma xnSubXSubOneZ_natDegree (n : ℕ) (hn : 2 ≤ n) :
    (xnSubXSubOneZ n).natDegree = n := by
  erw [Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
    norm_num [Polynomial.natDegree_X_pow, hn]
  linarith

/-
The degree of `Xⁿ - X - 1` over `ZMod p` equals `n` for `n ≥ 2` and `p` prime.
-/
lemma xnSubXSubOne_modp_natDegree (n p : ℕ) (hn : 2 ≤ n) [hp : Fact (Nat.Prime p)] :
    (xnSubXSubOne_modp n p).natDegree = n := by
  rw [xnSubXSubOne_modp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
  all_goals linarith

/-!
## Section 2: Dedekind's Theorem

We state Dedekind's theorem in a form relating the mod-p factorization pattern
to the cycle type of an element in the Galois group.

The cycle type is represented as `Equiv.Perm.cycleType`, which gives a `Multiset ℕ`
of cycle lengths (all ≥ 2; fixed points are excluded).

The factorization pattern is the multiset of degrees of irreducible factors of `f mod p`,
restricted to those of degree ≥ 2 (since degree-1 factors correspond to fixed points
of the Frobenius).
-/

-- factorizationType is imported from DedekindProof

/-- **Dedekind's Theorem** (cycle type version):
Let `f ∈ ℤ[X]` be monic with `f` irreducible over `ℚ`. Let `p` be a prime
such that `f mod p` is squarefree (i.e., separable) over `𝔽_p`.
Then there exists `σ ∈ Gal(f/ℚ)` whose image under `galActionHom` has
cycle type equal to the factorization type of `f mod p`.

The proof requires constructing the Frobenius automorphism at an unramified prime
above `p` in the ring of integers of the splitting field, and showing its cycle type
on roots matches the mod-p factorization. This involves:
- The ring of integers `𝒪_K` of the splitting field `K`
- Prime decomposition `(p) = 𝔭₁^{e₁} ⋯ 𝔭ᵣ^{eᵣ}` in `𝒪_K`
- The Frobenius element `Frob(𝔭/p)` for unramified `𝔭 | p`
- The bijection between roots of `f` in `K` and roots of `f mod p` in the residue field
-/
theorem dedekind_theorem (f : ℤ[X]) (hf_monic : f.Monic)
    (hf_irr : Irreducible (f.map (Int.castRingHom ℚ)))
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (h_sep : Squarefree (f.map (Int.castRingHom (ZMod p)))) :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      (@Polynomial.Gal.galActionHom _ _ (f.map (Int.castRingHom ℚ)) ℂ _ _
        ⟨IsAlgClosed.splits _⟩ σ).cycleType =
      factorizationType (f.map (Int.castRingHom (ZMod p))) :=
  dedekind_theorem' f hf_monic hf_irr h_sep

/-!
### Corollaries of Dedekind's theorem

We derive two specialized corollaries: one for producing transpositions (swaps)
and one for producing `(n-1)`-cycles. These follow from the general theorem by
analyzing the cycle type.
-/

/-
A permutation with cycle type `{2}` is a transposition.
-/
lemma cycleType_eq_two_isSwap {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Equiv.Perm α} (h : σ.cycleType = {2}) : σ.IsSwap := by
  exact Equiv.Perm.isSwap_iff_cycleType.mpr h

/-
A permutation with cycle type `{d}` for `d ≥ 2` is a cycle with support size `d`.
-/
lemma cycleType_singleton_isCycle {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Equiv.Perm α} {d : ℕ} (_hd : d ≥ 2) (h : σ.cycleType = {d}) :
    σ.IsCycle ∧ σ.support.card = d := by
  obtain ⟨c, hc⟩ : ∃ c : Equiv.Perm α, c.IsCycle ∧ c.cycleType = {d} ∧ σ = c := by
    have := Equiv.Perm.card_cycleType_eq_one.mp (by
      simp_all only [ge_iff_le, Multiset.card_singleton] : σ.cycleType.card = 1)
    simp_all only [ge_iff_le, ↓existsAndEq, and_self]
  have := hc.1.cycleType
  simp_all only [ge_iff_le, Multiset.singleton_inj, and_self]

/-- If `f mod p` has factorization type `{2}` (exactly one quadratic irreducible factor,
rest linear), then `Gal(f)` contains a transposition. -/
theorem dedekind_swap (f : ℤ[X]) (hf_monic : f.Monic)
    (hf_irr : Irreducible (f.map (Int.castRingHom ℚ)))
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (h_sep : Squarefree (f.map (Int.castRingHom (ZMod p))))
    (h_type : factorizationType (f.map (Int.castRingHom (ZMod p))) = {2}) :
    ∃ σ ∈ (@Polynomial.Gal.galActionHom _ _ (f.map (Int.castRingHom ℚ)) ℂ _ _
      ⟨IsAlgClosed.splits _⟩).range,
      Equiv.Perm.IsSwap σ := by
  obtain ⟨σ, hσ⟩ := dedekind_theorem f hf_monic hf_irr p h_sep
  exact ⟨_, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, cycleType_eq_two_isSwap (by rw [hσ, h_type])⟩

/-- If `f mod p` has factorization type `{d}` with `d ≥ 2`, then `Gal(f)` contains
a cycle of support size `d`. -/
theorem dedekind_cycle (f : ℤ[X]) (hf_monic : f.Monic)
    (hf_irr : Irreducible (f.map (Int.castRingHom ℚ)))
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (h_sep : Squarefree (f.map (Int.castRingHom (ZMod p))))
    (d : ℕ) (hd : d ≥ 2)
    (h_type : factorizationType (f.map (Int.castRingHom (ZMod p))) = {d}) :
    ∃ σ ∈ (@Polynomial.Gal.galActionHom _ _ (f.map (Int.castRingHom ℚ)) ℂ _ _
      ⟨IsAlgClosed.splits _⟩).range,
      Equiv.Perm.IsCycle σ ∧ σ.support.card = d := by
  obtain ⟨σ, hσ⟩ := dedekind_theorem f hf_monic hf_irr p h_sep
  exact ⟨_, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, cycleType_singleton_isCycle hd (by rw [hσ, h_type])⟩

/-!
## Section 3: Factorization Analysis of Xⁿ - X - 1

We state the specific factorization properties needed for the two main results.

### For the transposition

For `n ≥ 3`, there exists a prime `p` such that `Xⁿ - X - 1 mod p` is squarefree
and has exactly one quadratic irreducible factor (with the remaining factors linear).

### For the (n-1)-cycle

For `n ≥ 3`, there exists a prime `p` such that `Xⁿ - X - 1 mod p` factors as
`(X - a) · g(X)` where `g` is irreducible of degree `n - 1` over `𝔽_p`.
-/

/-
**Elementary reduction lemma.**  Over any field `F`, if `g` is squarefree of degree
`≥ 3` and has exactly `natDegree g - 2` distinct roots in `F`, then its factorization
type is `{2}` (one irreducible quadratic factor, the remaining factors linear).

This converts a root-counting statement into a statement about the multiset of
irreducible-factor degrees.
Since `g` is squarefree its normalized factors are distinct irreducibles; the degree-`1`
factors are in bijection with the roots, so exactly `natDegree g - 2` factors are linear
and the remaining factors contribute total degree `2`.  As every non-linear factor has
degree `≥ 2`, there must be exactly one such factor, of degree `2`.
-/
lemma factorizationType_eq_two_of_squarefree_card_roots
    {F : Type*} [Field F] [DecidableEq F] (g : F[X])
    (hsq : Squarefree g) (hdeg : 3 ≤ g.natDegree)
    (hroots : g.roots.toFinset.card = g.natDegree - 2) :
    factorizationType g = {2} := by
  unfold factorizationType
  have h_linear_factors : Multiset.card (Multiset.filter (fun x => x = 1)
      (Multiset.map Polynomial.natDegree (normalizedFactors g))) = g.roots.toFinset.card := by
    have h_linear_factors : Multiset.toFinset (Multiset.filter (fun q => q.natDegree = 1)
        (normalizedFactors g)) = g.roots.toFinset.image (fun a => Polynomial.X - Polynomial.C a) := by
      ext q
      simp [Finset.mem_image]
      constructor <;> intro hq
      all_goals generalize_proofs at *
      · obtain ⟨a, ha⟩ : ∃ a : F, q = Polynomial.X - Polynomial.C a := by
          have h_linear : q.Monic := by
            have := hq.1
            rw [normalizedFactors] at this
            rw [Multiset.mem_map] at this
            obtain ⟨q, hq, rfl⟩ := this
            simp [normalize_apply]
            simp [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
            simp [normUnit]
            split_ifs <;> simp_all
          rw [Polynomial.Monic.def, Polynomial.leadingCoeff,
            Polynomial.natDegree_eq_of_degree_eq_some
              (Polynomial.degree_eq_natDegree <| by aesop)] at h_linear
          rw [Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hq.2)] at h_linear ⊢
          by_cases h : q.coeff 1 = 0 <;> simp_all [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
          · exact absurd h (by
              rw [← hq.2, Polynomial.coeff_natDegree]
              aesop)
          · exact ⟨-q.coeff 0, by simp⟩
        generalize_proofs at *
        use a
        generalize_proofs at *
        simp_all
        refine ⟨by aesop_cat, ?_⟩
        simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
          (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq) (by simp)
      · obtain ⟨a, ⟨hg, ha⟩, rfl⟩ := hq
        have h_factor : X - C a ∣ g := Polynomial.dvd_iff_isRoot.mpr ha
        have h_irred : Irreducible (X - C a) := Polynomial.irreducible_X_sub_C a
        have h_normalized : normalize (X - C a) = X - C a := by
          simp [normalize]
        have h_factor_in_normalizedFactors : X - C a ∈ normalizedFactors g := by
          grind only [mem_normalizedFactors_iff']
        exact ⟨h_factor_in_normalizedFactors, Polynomial.natDegree_X_sub_C a⟩
    have h_linear_factors_card : Multiset.card (Multiset.filter (fun q => q.natDegree = 1)
        (normalizedFactors g)) =
        Finset.card (g.roots.toFinset.image (fun a => Polynomial.X - Polynomial.C a)) := by
      rw [← h_linear_factors, Multiset.toFinset_card_of_nodup]
      refine' Multiset.Nodup.filter _ _
      rw [Multiset.nodup_iff_ne_cons_cons]
      intro a t h
      have := hsq
      simp_all [Squarefree]
      have := h ▸ UniqueFactorizationMonoid.prod_normalizedFactors (show g ≠ 0 from by aesop_cat)
      simp_all [Multiset.prod_cons]
      obtain ⟨u, hu⟩ := this.symm
      have := hsq a ?_
      · have := UniqueFactorizationMonoid.irreducible_of_normalized_factor a
          (h.symm ▸ Multiset.mem_cons_self _ _)
        simp_all [irreducible_iff]
      · refine ⟨t.prod * ↑u⁻¹, ?_⟩
        simpa [mul_assoc, mul_comm, mul_left_comm] using congr_arg (fun x : F[X] => x * ↑u⁻¹) hu
    rw [Finset.card_image_of_injective _
      fun x y hxy => by simpa using congr_arg (fun p => p.coeff 0) hxy] at h_linear_factors_card
    simp_all [Multiset.filter_map]
  have h_sum_degrees :
      Multiset.sum (Multiset.map Polynomial.natDegree (normalizedFactors g)) = g.natDegree := by
    have h_sum_degrees : Polynomial.natDegree (Multiset.prod (normalizedFactors g)) =
        Multiset.sum (Multiset.map Polynomial.natDegree (normalizedFactors g)) := by
      rw [Polynomial.natDegree_multiset_prod]
      intro h
      have := UniqueFactorizationMonoid.irreducible_of_normalized_factor 0 h
      simp_all
    rw [← h_sum_degrees, ← Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated <|
        UniqueFactorizationMonoid.prod_normalizedFactors <| show g ≠ 0 from by aesop_cat)]
  have h_sum_degrees_ge_two :
      Multiset.sum (Multiset.filter (fun x => x ≥ 2)
        (Multiset.map Polynomial.natDegree (normalizedFactors g))) = 2 := by
    have h_sum_degrees_ge_two :
        Multiset.sum (Multiset.filter (fun x => x ≥ 2)
            (Multiset.map Polynomial.natDegree (normalizedFactors g))) +
          Multiset.sum (Multiset.filter (fun x => x = 1)
            (Multiset.map Polynomial.natDegree (normalizedFactors g))) = g.natDegree := by
      rw [← h_sum_degrees, ← Multiset.sum_add]
      congr with x
      by_cases hx : x ≥ 2 <;> by_cases hx' : x = 1 <;> simp [hx, hx']
      interval_cases x <;> simp_all
      rw [Multiset.count_eq_zero.mpr]
      simp [Polynomial.natDegree_eq_zero_iff_degree_le_zero]
      intro x hx
      have := UniqueFactorizationMonoid.irreducible_of_normalized_factor x hx
      exact Polynomial.degree_pos_of_irreducible this
    simp_all [Multiset.filter_eq']
    omega
  have h_card_ge_two : ∀ {m : Multiset ℕ}, (∀ x ∈ m, x ≥ 2) → Multiset.sum m = 2 → m = {2} := by
    intros m hm hm'
    induction m using Multiset.induction <;> simp_all
    induction ‹Multiset ℕ› using Multiset.induction <;> simp_all +arith +decide
    omega
  exact h_card_ge_two (fun x hx => by
    simp_all only [ge_iff_le, Multiset.mem_filter, Multiset.mem_map,
      implies_true, Multiset.mem_singleton, le_refl, Multiset.sum_singleton])
    h_sum_degrees_ge_two

/-!
## Scope -/

end
