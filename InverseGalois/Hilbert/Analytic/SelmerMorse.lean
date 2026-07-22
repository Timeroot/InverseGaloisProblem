/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The Selmer polynomials `Xⁿ - X - 1` are Morse

This file develops the elementary algebraic core of the "Morse polynomial" approach to
the Galois group of the Selmer trinomials `Xⁿ - X - 1`, following Serre,
*Topics in Galois Theory*, §4.4.

A polynomial is *Morse* if, modulo every maximal ideal, its roots collide in at most one
pair.  The key elementary computation is that `Xⁿ - X - 1` and its derivative
`n·Xⁿ⁻¹ - 1` have **at most one common root** over any field, and that no root has
multiplicity `≥ 3`.  These are the "clean identities" behind the transposition/swap
input to Dedekind/Frobenius arguments.

## Main results

* `selmer_derivative_common_root_unique`: over any field, `Xⁿ - X - 1` and its derivative
  have at most one common root.
* `selmer_rootMultiplicity_le_two`: over any field, every root of `Xⁿ - X - 1` has
  multiplicity at most `2`. -/

open Polynomial

namespace SelmerMorse

/-- The Selmer trinomial `Xⁿ - X - 1` over a commutative ring `F`. -/
noncomputable def selmerPoly (F : Type*) [CommRing F] (n : ℕ) : F[X] := X ^ n - X - 1

/-
The derivative of `Xⁿ - X - 1` is `n·Xⁿ⁻¹ - 1`.
-/
lemma derivative_selmerPoly {F : Type*} [CommRing F] (n : ℕ) :
    derivative (selmerPoly F n) = (n : F[X]) * X ^ (n - 1) - 1 := by
  unfold selmerPoly
  cases n <;> simp [Polynomial.derivative_pow]

/-
**Serre's Morse condition (uniqueness of the singular point).**  Over any integral
domain `F`, the polynomial `Xⁿ - X - 1` and its derivative have at most one common root:
if `a` and `b` are both roots of `Xⁿ - X - 1` and of its derivative, then `a = b`.

This is the elementary identity underlying the "one collision" property of Selmer
polynomials.  The proof: at a common root `α`, `n·αⁿ⁻¹ = 1` and `αⁿ = α + 1`; multiplying
the first by `α` gives `n·(α + 1) = α`, i.e. `(n - 1)·α = -n`, a relation forcing `α` to be
determined independently of the choice of root (using that `F` is a domain).
-/
lemma selmer_derivative_common_root_unique {F : Type*} [CommRing F] [IsDomain F] (n : ℕ)
    {a b : F}
    (ha : (selmerPoly F n).IsRoot a) (ha' : (derivative (selmerPoly F n)).IsRoot a)
    (hb : (selmerPoly F n).IsRoot b) (hb' : (derivative (selmerPoly F n)).IsRoot b) :
    a = b := by
  unfold selmerPoly at *
  rcases n with (_ | _ | n) <;> simp_all [Polynomial.derivative_pow]
  grind +qlia

/-
**No triple roots.**  Over any integral domain `F`, every root of `Xⁿ - X - 1` has
multiplicity at most `2`.  Equivalently, `Xⁿ - X - 1`, its derivative and its second
derivative have no common root.  Together with `selmer_derivative_common_root_unique` this
says that `Xⁿ - X - 1` has at most one repeated root, and that root is exactly a double
root.
-/
lemma selmer_rootMultiplicity_le_two {F : Type*} [CommRing F] [IsDomain F] (n : ℕ) (a : F) :
    (selmerPoly F n).rootMultiplicity a ≤ 2 := by
  by_contra h_contradiction
  have h_div : (Polynomial.X - Polynomial.C a)^3 ∣ selmerPoly F n :=
    dvd_trans (pow_dvd_pow _ (not_le.mp h_contradiction)) (Polynomial.pow_rootMultiplicity_dvd _ _)
  have h_root :
      Polynomial.eval a (selmerPoly F n) = 0 ∧ Polynomial.eval a (derivative (selmerPoly F n)) = 0 ∧
        Polynomial.eval a (derivative (derivative (selmerPoly F n))) = 0 := by
    obtain ⟨q, hq⟩ := h_div
    simp_all [pow_succ, mul_assoc]
  simp_all [selmerPoly, Polynomial.derivative_pow]
  rcases n with (_ | _ | n) <;> simp_all [sub_eq_iff_eq_add]
  obtain h | h | h := h_root.2.2 <;> simp_all [pow_succ', add_eq_zero_iff_eq_neg]
  obtain ⟨p, hp⟩ := h_div
  replace hp := congr_arg (Polynomial.eval a) hp
  simp_all [mul_assoc]

/-
**The field/domain-level Morse property.**  Over any integral domain `F`, the trinomial
`Xⁿ - X - 1` has at most one repeated root, and that root is at most a double root.
Concretely, the number of roots counted with multiplicity exceeds the number of distinct
roots by at most `1`.

This is the clean elementary identity behind the fact that Selmer polynomials are *Morse*
(Serre, §4.4): reducing the roots of `Xⁿ - X - 1` from a domain to a residue field can
collide at most one pair.  It follows from `selmer_derivative_common_root_unique` (at most
one root has multiplicity `≥ 2`) and `selmer_rootMultiplicity_le_two` (no root has
multiplicity `≥ 3`).
-/
lemma selmer_ncard_roots_field {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F] (n : ℕ) :
    (selmerPoly F n).roots.card ≤ (selmerPoly F n).roots.toFinset.card + 1 := by
  -- By `selmer_derivative_common_root_unique`, at most one root has multiplicity `≥ 2`.
  have h_at_most_one_repeated :
      Finset.card (Finset.filter (fun a ↦ 2 ≤ (selmerPoly F n).roots.count a)
        (selmerPoly F n).roots.toFinset) ≤ 1 := by
    rw [Finset.card_le_one_iff]
    simp at *
    intro a b h₁ h₂ h₃ h₄ h₅ h₆
    have hda := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
      (show 1 < rootMultiplicity a (selmerPoly F n) from h₃)
    have hdb := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
      (show 1 < rootMultiplicity b (selmerPoly F n) from h₆)
    simp only [Function.iterate_one] at hda hdb
    exact selmer_derivative_common_root_unique n h₂ hda h₅ hdb
  have h_sum_le_one :
      ∑ a ∈ (selmerPoly F n).roots.toFinset, ((selmerPoly F n).roots.count a - 1) ≤
        Finset.card (Finset.filter (fun a ↦ 2 ≤ (selmerPoly F n).roots.count a)
          (selmerPoly F n).roots.toFinset) := by
    rw [Finset.card_filter]
    gcongr with a ha
    have := selmer_rootMultiplicity_le_two n a
    simp_all [Polynomial.count_roots]
    grind
  have h_count_sum_eq_card :
      ∑ a ∈ (selmerPoly F n).roots.toFinset, (selmerPoly F n).roots.count a =
        (selmerPoly F n).roots.card := by
    rw [← Multiset.toFinset_sum_count_eq]
  have h_sum_eq_card :
      ∑ a ∈ (selmerPoly F n).roots.toFinset, ((selmerPoly F n).roots.count a - 1) +
          ∑ a ∈ (selmerPoly F n).roots.toFinset, 1 = (selmerPoly F n).roots.card := by
    have hcongr : ∀ x ∈ (selmerPoly F n).roots.toFinset,
        (selmerPoly F n).roots.count x - 1 + 1 = (selmerPoly F n).roots.count x :=
      fun x hx ↦ tsub_add_cancel_of_le <| Nat.succ_le_of_lt <|
        Multiset.count_pos.mpr <| Multiset.mem_toFinset.mp hx
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hcongr]
    simp_all [count_roots]
  norm_num at *
  linarith

/-
The image of `Xⁿ - X - 1` under a base-change map is again `Xⁿ - X - 1`.
-/
lemma selmerPoly_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) :
    (selmerPoly R n).map (algebraMap R S) = selmerPoly S n := by
  unfold selmerPoly
  simp

/-
`Xⁿ - X - 1` is never the zero polynomial over a nontrivial commutative ring
(its constant coefficient is `-1`).
-/
lemma selmerPoly_ne_zero {F : Type*} [CommRing F] [Nontrivial F] (n : ℕ) :
    selmerPoly F n ≠ 0 := by
  by_contra h_zero_poly
  have h_contra : ∀ x : F, x^n - x - 1 = 0 :=
    fun x ↦ by simpa [selmerPoly] using congr_arg (Polynomial.eval x) h_zero_poly
  have := h_contra 0
  have := h_contra 1
  rcases n with (_ | _ | n) <;> simp_all
  exact absurd (h_contra 1) one_ne_zero

/-
**Counting collisions.**  Let `S` be an `R`-algebra domain and `D` an `S`-algebra
domain (compatibly an `R`-algebra).  For any `q : R[X]` whose image in `D` is nonzero, the
number of *distinct* roots of `q` in `S` is at most the number of roots of the image of `q`
in `D`, counted with multiplicity.

The reason: the distinct roots `a₁, …, aₘ` of `q` in `S` give a factor
`∏ᵢ (X - aᵢ) ∣ q` in `S[X]`; mapping to `D` yields `∏ᵢ (X - φ(aᵢ)) ∣ q_D`, whose root
multiset `{φ(a₁), …, φ(aₘ)}` therefore embeds in `q_D.roots`.
-/
lemma ncard_rootSet_le_roots_card
    {R S D : Type*} [CommRing R] [CommRing S] [IsDomain S] [CommRing D] [IsDomain D]
    [Algebra R S] [Algebra S D] [Algebra R D] [IsScalarTower R S D]
    (q : R[X]) (hne : (q.map (algebraMap R D)) ≠ 0) :
    (q.rootSet S).ncard ≤ (q.map (algebraMap R D)).roots.card := by
  -- Let `s` be the set of distinct roots of `q` in `S`.
  set s := (Polynomial.rootSet q S).toFinset with hs_def
  -- The product `∏ a ∈ s, (X - C a)` divides `q_S` in `S[X]`.
  have h_div : (∏ a ∈ s, (Polynomial.X - Polynomial.C a)) ∣ (Polynomial.map (algebraMap R S) q) := by
    have h_div_prod : ∀ {m : Multiset S},
        (∀ a ∈ m, Polynomial.IsRoot (Polynomial.map (algebraMap R S) q) a) → Multiset.Nodup m →
          (m.map (fun a ↦ Polynomial.X - Polynomial.C a)).prod ∣ (Polynomial.map (algebraMap R S) q) := by
      intro m hm hm_nodup
      induction' m using Multiset.induction with a m ih
      · simp
      · obtain ⟨p, hp⟩ := ih (fun x hx ↦ hm x (Multiset.mem_cons_of_mem hx))
          (Multiset.nodup_cons.mp hm_nodup |>.2)
        simp_all
        rw [mul_comm]
        refine mul_dvd_mul_left _ ?_
        apply Polynomial.dvd_iff_isRoot.mpr
        replace hp := congr_arg (Polynomial.eval a) hp
        simp_all [Polynomial.eval_multiset_prod]
        refine hm.1.resolve_left ?_
        rintro ⟨b, hb, h⟩
        apply hm_nodup.1
        simpa [sub_eq_zero.mp h] using hb
    convert h_div_prod _ _ <;> simp_all
    · grind only [aeval_eq_zero_of_mem_rootSet]
    · exact Finset.nodup _
  -- Applying the algebra map `φ : S → D` to the divisibility relation gives
  -- `∏ a ∈ s, (X - C (φ a))` divides `q_D` in `D[X]`.
  have h_div_D : (∏ a ∈ s, (Polynomial.X - Polynomial.C (algebraMap S D a))) ∣ (Polynomial.map (algebraMap R D) q) := by
    convert Polynomial.map_dvd (algebraMap S D) h_div using 1
    · simp [Polynomial.map_prod]
    · simp [Polynomial.map_map, IsScalarTower.algebraMap_eq R S D]
  -- The roots of `∏ a ∈ s, (X - C (φ a))` are exactly `{φ a | a ∈ s}`.
  have h_roots : (Polynomial.map (algebraMap R D) q).roots ≥ Multiset.map (fun a ↦ algebraMap S D a) s.val := by
    have h_roots_eq :
        Polynomial.roots (∏ a ∈ s, (Polynomial.X - Polynomial.C (algebraMap S D a))) =
          Multiset.map (fun a ↦ algebraMap S D a) s.val := by
      rw [Polynomial.roots_prod]
      · rw [Multiset.bind_congr fun x hx ↦ by rw [Polynomial.roots_X_sub_C]]
        simp_all only [ne_eq, Multiset.bind_singleton, s]
      · exact Finset.prod_ne_zero_iff.mpr fun x hx ↦ Polynomial.X_sub_C_ne_zero _
    rw [ge_iff_le, ← h_roots_eq]
    exact Polynomial.roots.le_of_dvd hne h_div_D
  refine le_trans ?_ (Multiset.card_le_card h_roots)
  rw [Set.ncard_eq_toFinset_card _]
  simp_all only [ne_eq, ge_iff_le, Set.toFinite_toFinset, Set.toFinset_card, Multiset.card_map,
    Finset.card_val, le_refl, s]

/-
**The Selmer polynomials are Morse.**  For any `R`-algebra domain `S` over which
`Xⁿ - X - 1` splits, and any prime ideal `p` of `S`, the roots of `Xⁿ - X - 1` in `S`
collide, on reduction modulo `p`, in at most one pair.  This is exactly the hypothesis
`(f.rootSet S).ncard ≤ (f.rootSet (S ⧸ p)).ncard + 1` required by Mathlib's Morse
polynomial results
(`Polynomial.Splits.toPermHom_apply_eq_one_or_isSwap_of_ncard_le_of_mem_inertia`,
`Polynomial.Splits.surjective_toPermHom_of_iSup_inertia_eq_top`).
-/
theorem selmerPoly_isMorse
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDomain S]
    (n : ℕ) (p : Ideal S) [p.IsPrime] :
    ((selmerPoly R n).rootSet S).ncard ≤ ((selmerPoly R n).rootSet (S ⧸ p)).ncard + 1 := by
  -- Let `D := S ⧸ p`.
  set D := S ⧸ p
  -- By `ncard_rootSet_le_roots_card` (with the domains S and D),
  -- `(q.rootSet S).ncard ≤ (q.map (algebraMap R D)).roots.card`.
  have h1 : (Polynomial.rootSet (selmerPoly R n) S).ncard ≤
      (Polynomial.map (algebraMap R D) (selmerPoly R n)).roots.card := by
    apply ncard_rootSet_le_roots_card
    rw [selmerPoly_map]
    apply selmerPoly_ne_zero
  refine h1.trans ?_
  convert selmer_ncard_roots_field (F := S ⧸ p) n using 1
  · rw [selmerPoly_map]
  · classical
    rw [Polynomial.rootSet_def, Set.ncard_coe_finset, Polynomial.aroots_def, selmerPoly_map]

end SelmerMorse
