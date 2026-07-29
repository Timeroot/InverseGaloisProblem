/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Resolvent.ResolventFamily

/-!
# The alternating-orbit linear resolvent

The alternating-group analogue of `ResolventFamily.fullResolventProduct`: the product

  `∏_{σ ∈ Aₙ} (Y − w_σ)`,   `w_σ = ∑ᵢ i · x_(σ i)`,

over the `Aₙ`-orbit of the generic linear form, of degree `|Aₙ| = n!/2`.  This is the
degree-`n!/2` resolvent whose descent to `ℚ(T)` (once the family's discriminant is a square, so
that the `Aₙ`-invariant coefficients — living in `ℚ[e₁,…,eₙ][δ]` — become rational) is the `G`
consumed by `IsInverseGalois.of_regular_family` in the alternating construction.

The `Aₙ`-invariant *descent* to `ℚ(T)` and the geometric-monodromy (absolute irreducibility)
statement are the remaining hard steps; this file establishes the family-independent algebra of
the orbit product itself (monic, degree `n!/2`, functorial in ring maps, and root-containment),
reusing `ResolventFamily.genForm`.
-/

open Polynomial

noncomputable section

namespace AlternatingResolvent

open ResolventFamily

/-- The `Aₙ`-orbit linear resolvent product `∏_{σ ∈ Aₙ} (Y − w_σ)`. -/
def altResolventProduct {A : Type*} [CommRing A] (n : ℕ) (x : Fin n → A) : Polynomial A :=
  ∏ σ : alternatingGroup (Fin n),
    (Polynomial.X - Polynomial.C (genForm n x (σ : Equiv.Perm (Fin n))))

/-- The `Aₙ`-orbit resolvent product is monic (a product of monic linear factors). -/
theorem altResolventProduct_monic {A : Type*} [CommRing A] (n : ℕ) (x : Fin n → A) :
    (altResolventProduct n x).Monic := by
  unfold altResolventProduct
  exact monic_prod_of_monic _ _ (fun σ _ ↦ monic_X_sub_C _)

/-- The `Aₙ`-orbit resolvent product has degree `n!/2 = |Aₙ|` (for `n ≥ 2`). -/
theorem altResolventProduct_natDegree {A : Type*} [CommRing A] [Nontrivial A] (n : ℕ)
    (hn : 2 ≤ n) (x : Fin n → A) :
    (altResolventProduct n x).natDegree = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  unfold altResolventProduct
  rw [natDegree_prod_of_monic _ _ (fun σ _ ↦ monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [card_alternatingGroup, Fintype.card_fin]

/-- The `Aₙ`-orbit resolvent product commutes with ring homomorphisms. -/
theorem altResolventProduct_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (n : ℕ) (x : Fin n → A) :
    (altResolventProduct n x).map φ = altResolventProduct n (fun i ↦ φ (x i)) := by
  unfold altResolventProduct
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro σ _
  rw [Polynomial.map_sub, map_X, map_C, genForm_map]

/-- The linear form `w₁ = ∑ᵢ i · xᵢ` (at the identity permutation, which lies in `Aₙ`) is a root
of the `Aₙ`-orbit resolvent product — the root-containment witness. -/
theorem altResolventProduct_isRoot_genForm_one {A : Type*} [CommRing A] (n : ℕ) (x : Fin n → A) :
    (altResolventProduct n x).IsRoot (genForm n x 1) := by
  unfold altResolventProduct IsRoot
  rw [eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : alternatingGroup (Fin n)))
  simp only [OneMemClass.coe_one, eval_sub, eval_X, eval_C, sub_self]

end AlternatingResolvent

end
