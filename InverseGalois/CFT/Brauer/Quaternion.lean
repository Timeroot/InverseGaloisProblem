import Mathlib
import InverseGalois.CFT.Brauer.CyclicAlgebra

/-!
# The Hamilton quaternions as a nontrivial Brauer class

The cyclic-algebra machinery of `InverseGalois.CFT.Brauer.CyclicAlgebra` turns a unit which is not
a norm into a central simple algebra which is not a matrix algebra.  This file feeds it the two
classical examples.

Over `ℝ` the relevant extension is `ℂ / ℝ`, whose norm is `z ↦ ‖z‖ ^ 2`; the unit `-1` is
therefore not a norm, and the resulting cyclic algebra `(ℂ / ℝ, conj, -1)` is the algebra of
Hamilton quaternions.  Over `ℚ` the extension is `ℚ(i)`, realised as the intermediate field
`ℚ⟮Complex.I⟯` of `ℂ`; the norm of `x` is `‖x‖ ^ 2` again, computed by pairing the two complex
embeddings of `ℚ(i)`, so `-1` is not a norm there either and the rational quaternion algebra is
not a matrix algebra.

In both cases the algebra produced has dimension `4` over the base field, so the only matrix
algebra it could possibly be isomorphic to is the algebra of `2 × 2` matrices; the statements
below rule out matrices of every size at once.

## Main results

* `InverseGalois.CFT.exists_csa_not_matrix`: the packaging of the cyclic-algebra criterion used
  here, recording also the dimension of the algebra and excluding matrices of every size.
* `InverseGalois.CFT.norm_real_complex_nonneg`,
  `InverseGalois.CFT.not_isNorm_neg_one_real`: `-1` is not a norm from `ℂ` to `ℝ`.
* `InverseGalois.CFT.exists_csa_real`: a central simple `ℝ`-algebra of dimension `4`, split by
  `ℂ`, which is not a matrix algebra over `ℝ`.
* `InverseGalois.CFT.minpoly_rat_I`, `InverseGalois.CFT.finrank_rat_I`: `ℚ⟮Complex.I⟯` is a
  quadratic extension of `ℚ` with minimal polynomial `X ^ 2 + 1`.
* `InverseGalois.CFT.coe_norm_rat_I`, `InverseGalois.CFT.norm_rat_I_nonneg`,
  `InverseGalois.CFT.not_isNorm_neg_one_rat`: the norm of `ℚ⟮Complex.I⟯ / ℚ` is the squared
  absolute value, so `-1` is not a norm.
* `InverseGalois.CFT.exists_csa_rat`: a central simple `ℚ`-algebra of dimension `4`, split by
  `ℚ(i)`, which is not a matrix algebra over `ℚ`.

## Tags

Brauer group, quaternion algebra, cyclic algebra, norm
-/

open Module Polynomial IntermediateField

namespace InverseGalois.CFT

/-! ### The criterion, with dimensions -/

/-- **A unit which is not a norm produces a genuine quaternion-style algebra.**  For a finite
cyclic Galois extension `L / K` and a unit `a` of `K` which is not a norm from `L`, there is a
central simple `K`-algebra `A` split by `L`, of dimension `[L : K] ^ 2` over `K`, which is not
isomorphic to a matrix algebra over `K` of any size. -/
theorem exists_csa_not_matrix {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] {a : Kˣ}
    (ha : ¬ ∃ b : Lˣ, Algebra.norm K (b : L) = (a : K)) :
    ∃ A : CSA.{0, 0} K, (⟦A⟧ : BrauerGroup K) ∈ BrauerGroup.relative K L ∧
      finrank K (A : Type) = finrank K L ^ 2 ∧
      ∀ n : ℕ, ¬ Nonempty ((A : Type) ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨σ₀, hσ₀⟩ := exists_generator_of_isCyclic (K := K) (L := L)
  have hdim : finrank K ((CrossedProduct.csa (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) :
      CSA.{0, 0} K) : Type) = finrank K L ^ 2 := by
    show finrank K (CrossedProduct (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)) = finrank K L ^ 2
    rw [CrossedProduct.finrank_eq]
    exact congrArg (· ^ 2) (IsGalois.card_aut_eq_finrank K L)
  refine ⟨_, mk_cyclicAlgebra_mem_relative hσ₀ a, hdim, ?_⟩
  rintro n ⟨e⟩
  have hn : n ^ 2 = finrank K L ^ 2 := by
    rw [← hdim, e.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp [sq]
  have hn' : n = finrank K L := Nat.pow_left_injective (by norm_num) hn
  subst hn'
  exact ha ((nonempty_algEquivMatrix_cyclicAlgebra_iff hσ₀ a).mp ⟨e⟩)

/-! ### The real quaternions -/

/-- `ℂ` is a quadratic extension of `ℝ`. -/
instance isQuadraticExtension_real_complex : Algebra.IsQuadraticExtension ℝ ℂ where
  finrank_eq_two' := Complex.finrank_real_complex

/-- The norm of `ℂ / ℝ` takes nonnegative values: it is the squared absolute value. -/
theorem norm_real_complex_nonneg (z : ℂ) : 0 ≤ Algebra.norm ℝ z := by
  rw [Algebra.norm_complex_apply]
  exact Complex.normSq_nonneg z

/-- **`-1` is not a norm from `ℂ` to `ℝ`.** -/
theorem not_isNorm_neg_one_real : ¬ ∃ b : ℂˣ, Algebra.norm ℝ (b : ℂ) = (-1 : ℝ) := by
  rintro ⟨b, hb⟩
  have h := norm_real_complex_nonneg (b : ℂ)
  rw [hb] at h
  norm_num at h

/-- **The Hamilton quaternions are a nontrivial Brauer class over `ℝ`.**  There is a central
simple `ℝ`-algebra of dimension `4`, split by `ℂ`, which is not isomorphic to a matrix algebra
over `ℝ` of any size. -/
theorem exists_csa_real :
    ∃ A : CSA.{0, 0} ℝ, (⟦A⟧ : BrauerGroup ℝ) ∈ BrauerGroup.relative ℝ ℂ ∧
      finrank ℝ (A : Type) = 4 ∧
      ∀ n : ℕ, ¬ Nonempty ((A : Type) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ) := by
  have ha : ¬ ∃ b : ℂˣ, Algebra.norm ℝ (b : ℂ) = ((-1 : ℝˣ) : ℝ) := by
    simpa using not_isNorm_neg_one_real
  obtain ⟨A, hrel, hdim, hmat⟩ := exists_csa_not_matrix (K := ℝ) (L := ℂ) ha
  refine ⟨A, hrel, ?_, hmat⟩
  rw [hdim, Complex.finrank_real_complex]
  norm_num

/-! ### The field `ℚ(i)` -/

/-- The minimal polynomial of `Complex.I` over `ℚ` is `X ^ 2 + 1`. -/
theorem minpoly_rat_I : minpoly ℚ Complex.I = X ^ 2 + 1 := by
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · have h : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
      simp [h]
    · intro q hq
      rw [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hq
      nlinarith [sq_nonneg q]
  · simp [Complex.I_sq]
  · monicity!

/-- The minimal polynomial of `Complex.I` over `ℚ` has degree `2`. -/
theorem natDegree_minpoly_rat_I : (minpoly ℚ Complex.I).natDegree = 2 := by
  rw [minpoly_rat_I]
  compute_degree!

/-- `ℚ(i)` is a finite extension of `ℚ`. -/
instance finiteDimensional_rat_I : FiniteDimensional ℚ ℚ⟮Complex.I⟯ :=
  IntermediateField.adjoin.finiteDimensional Complex.isIntegral_rat_I

/-- `ℚ(i)` has degree `2` over `ℚ`. -/
theorem finrank_rat_I : finrank ℚ ℚ⟮Complex.I⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank Complex.isIntegral_rat_I, natDegree_minpoly_rat_I]

/-- `ℚ(i)` is a quadratic extension of `ℚ`; in particular it is Galois with cyclic group. -/
instance isQuadraticExtension_rat_I : Algebra.IsQuadraticExtension ℚ ℚ⟮Complex.I⟯ where
  finrank_eq_two' := finrank_rat_I

/-- Complex conjugation, read as a `ℚ`-algebra map. -/
noncomputable def conjRat : ℂ →ₐ[ℚ] ℂ := (Complex.conjAe.restrictScalars ℚ).toAlgHom

/-- **The norm of `ℚ(i) / ℚ` is the squared absolute value.**  The two complex embeddings of
`ℚ(i)` are the inclusion and its conjugate, so the norm of `x` is `x * conj x`. -/
theorem coe_norm_rat_I (x : ℚ⟮Complex.I⟯) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = Complex.normSq (x : ℂ) := by
  classical
  set ι : ℚ⟮Complex.I⟯ →ₐ[ℚ] ℂ := ℚ⟮Complex.I⟯.val with hι
  set κ : ℚ⟮Complex.I⟯ →ₐ[ℚ] ℂ := conjRat.comp ι with hκ
  have hα : (Complex.I : ℂ) ∈ ℚ⟮Complex.I⟯ := IntermediateField.mem_adjoin_simple_self ℚ Complex.I
  have hne : ι ≠ κ := by
    intro h
    have hI := congrArg (fun f => f (⟨Complex.I, hα⟩ : ℚ⟮Complex.I⟯)) h
    simp only [hκ, hι, AlgHom.coe_comp, Function.comp_apply, conjRat] at hI
    norm_num [Complex.ext_iff] at hI
  have hcard : Fintype.card (ℚ⟮Complex.I⟯ →ₐ[ℚ] ℂ) = 2 := by
    rw [AlgHom.card]
    exact finrank_rat_I
  have huniv : (Finset.univ : Finset (ℚ⟮Complex.I⟯ →ₐ[ℚ] ℂ)) = {ι, κ} := by
    refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  have key := Algebra.norm_eq_prod_embeddings (L := ℚ⟮Complex.I⟯) ℚ ℂ x
  rw [huniv, Finset.prod_pair hne] at key
  have h2 : ι x * κ x = ((Complex.normSq (x : ℂ) : ℝ) : ℂ) := by
    rw [hκ]
    simpa [hι, conjRat] using Complex.mul_conj (x : ℂ)
  rw [h2] at key
  have h3 : ((Algebra.norm ℚ x : ℚ) : ℂ) = ((Complex.normSq (x : ℂ) : ℝ) : ℂ) := by
    rw [← key]
    norm_num
  exact_mod_cast h3

/-- The norm of `ℚ(i) / ℚ` takes nonnegative values. -/
theorem norm_rat_I_nonneg (x : ℚ⟮Complex.I⟯) : 0 ≤ Algebra.norm ℚ x := by
  have h : (0 : ℝ) ≤ ((Algebra.norm ℚ x : ℚ) : ℝ) := (coe_norm_rat_I x) ▸ Complex.normSq_nonneg _
  exact_mod_cast h

/-- **`-1` is not a norm from `ℚ(i)` to `ℚ`.** -/
theorem not_isNorm_neg_one_rat :
    ¬ ∃ b : (ℚ⟮Complex.I⟯)ˣ, Algebra.norm ℚ (b : ℚ⟮Complex.I⟯) = (-1 : ℚ) := by
  rintro ⟨b, hb⟩
  have h := norm_rat_I_nonneg (b : ℚ⟮Complex.I⟯)
  rw [hb] at h
  norm_num at h

/-- **The rational quaternions are a nontrivial Brauer class over `ℚ`.**  There is a central
simple `ℚ`-algebra of dimension `4`, split by `ℚ(i)`, which is not isomorphic to a matrix algebra
over `ℚ` of any size. -/
theorem exists_csa_rat :
    ∃ A : CSA.{0, 0} ℚ, (⟦A⟧ : BrauerGroup ℚ) ∈ BrauerGroup.relative ℚ ℚ⟮Complex.I⟯ ∧
      finrank ℚ (A : Type) = 4 ∧
      ∀ n : ℕ, ¬ Nonempty ((A : Type) ≃ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ) := by
  have ha : ¬ ∃ b : (ℚ⟮Complex.I⟯)ˣ,
      Algebra.norm ℚ (b : ℚ⟮Complex.I⟯) = ((-1 : ℚˣ) : ℚ) := by
    simpa using not_isNorm_neg_one_rat
  obtain ⟨A, hrel, hdim, hmat⟩ := exists_csa_not_matrix (K := ℚ) (L := ℚ⟮Complex.I⟯) ha
  refine ⟨A, hrel, ?_, hmat⟩
  rw [hdim, finrank_rat_I]
  norm_num

end InverseGalois.CFT
