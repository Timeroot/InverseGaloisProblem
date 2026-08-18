/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Transfer.FactorScheme
import InverseGalois.Rigidity.RET.Transfer.Nullstellensatz
import InverseGalois.Rigidity.RET.Transfer.WeightedDegree

/-!
# Irreducibility of a two-variable polynomial descends to the algebraically closed base

Let `F` be a polynomial in two variables `X` and `Y`, monic in `Y`, whose coefficients are
polynomial expressions in parameters `σ` with coefficients in an algebraically closed field `k`,
and whose weights `j + D * i` are bounded by `D * (its degree in Y)`.  Suppose the parameters are
given values `x` in an algebraically closed extension field `K`, and that the resulting polynomial
over `K` admits no factorization into two monic factors of positive degree.

Then the parameters can be given values `y` in `k` itself, in such a way that every polynomial
identity satisfied by `x` is still satisfied by `y`, and the resulting polynomial over `k` still
admits no factorization into two monic factors of positive degree.

The proof combines three ingredients.  The degree bound turns the factorizations of prescribed
degrees into a *finite* system of polynomial equations; the coordinate ring of that system is
integral over the parameters, so the parameter values admitting a factorization are exactly the
zeros of an ideal of the parameter ring; and a point of the parameter space avoiding finitely many
such ideals specializes, by the Nullstellensatz, to a point over `k` avoiding them as well.

## Main results

* `Rigidity.RET.Transfer.exists_specialization_no_monic_factor` — the descent.
* `Rigidity.RET.Transfer.irreducible_map_ratFunc_iff` — having no monic factor of positive degree
  is irreducibility over the function field of the line.
* `Rigidity.RET.Transfer.exists_specialization_irreducible` — the descent, in that language.
-/

open Polynomial

open scoped Polynomial.Bivariate

namespace Rigidity.RET.Transfer

variable {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
variable {σ : Type*} [Finite σ]

/-- **A polynomial in two variables with no monic factor of positive degree over an extension of
the parameters has none after a specialization of the parameters to the algebraically closed
base.**

The specialized point retains every polynomial identity of the original one, so any further
property of the original expressed by identities is retained as well. -/
theorem exists_specialization_no_monic_factor {D : ℕ}
    (F : (MvPolynomial σ k)[X][Y]) (hFm : F.Monic)
    (hFd : ∀ i, F.coeff i ≠ 0 → (F.coeff i).natDegree + D * i ≤ D * F.natDegree)
    (x : σ → K)
    (hirr : ∀ G H : K[X][Y], G.Monic → H.Monic → 0 < G.natDegree → 0 < H.natDegree →
      F.map (mapRingHom (MvPolynomial.aeval x).toRingHom) ≠ G * H) :
    ∃ y : σ → k,
      (∀ p : MvPolynomial σ k, MvPolynomial.aeval x p = 0 → MvPolynomial.aeval y p = 0) ∧
      ∀ G H : k[X][Y], G.Monic → H.Monic → 0 < G.natDegree → 0 < H.natDegree →
        F.map (mapRingHom (MvPolynomial.aeval y).toRingHom) ≠ G * H := by
  classical
  -- for each pair of positive degrees, an eliminated equation which does not vanish at `x`
  have key : ∀ m l : ℕ, 0 < m → 0 < l →
      ∃ q ∈ factorIdeal (D * F.natDegree) m l F, MvPolynomial.aeval x q ≠ 0 := by
    intro m l hm hl
    by_contra hcon
    push_neg at hcon
    have hle : factorIdeal (D * F.natDegree) m l F ≤
        RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] K).toRingHom := by
      intro q hq
      simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hcon q hq
    obtain ⟨G, H, hG, hH, hGd, hHd, hGH⟩ :=
      exists_factorization_of_factorIdeal_le_ker (D * F.natDegree) m l F hFm _ hle
    exact hirr G H hG hH (by rw [hGd]; exact hm) (by rw [hHd]; exact hl) hGH
  choose! q hqmem hqne using key
  -- the finitely many inequations to be preserved by the specialization
  obtain ⟨y, hy, hyQ⟩ := exists_specialization (K := K) x
    (fun p : Fin (F.natDegree + 1) × Fin (F.natDegree + 1) =>
      if 0 < (p.1 : ℕ) ∧ 0 < (p.2 : ℕ) then q p.1 p.2 else 1)
    (by
      intro p
      dsimp only
      split_ifs with h
      · exact hqne _ _ h.1 h.2
      · simp)
  refine ⟨y, hy, ?_⟩
  rintro G H hG hH hGpos hHpos hGH
  -- the two factors have complementary degrees
  have hmapdeg : (F.map (mapRingHom
      (MvPolynomial.aeval y : MvPolynomial σ k →ₐ[k] k).toRingHom)).natDegree = F.natDegree :=
    hFm.natDegree_map _
  have hn : G.natDegree + H.natDegree = F.natDegree := by
    rw [← hmapdeg, hGH, hG.natDegree_mul hH]
  -- the weight bound is inherited by the specialization, hence by each factor
  have hbound : ∀ i, ((G * H).coeff i) ≠ 0 →
      ((G * H).coeff i).natDegree + D * i ≤ D * (G.natDegree + H.natDegree) := by
    intro i hi
    rw [hn]
    rw [← hGH] at hi ⊢
    rw [coeff_map, coe_mapRingHom] at hi ⊢
    have hFi : F.coeff i ≠ 0 := fun hz => hi (by rw [hz, Polynomial.map_zero])
    exact le_trans (Nat.add_le_add_right natDegree_map_le _) (hFd i hFi)
  have hbound' : ∀ i, ((H * G).coeff i) ≠ 0 →
      ((H * G).coeff i).natDegree + D * i ≤ D * (H.natDegree + G.natDegree) := by
    intro i hi
    rw [mul_comm H G, add_comm H.natDegree]
    exact hbound i (by rwa [mul_comm G H])
  have hGE : ∀ i, (G.coeff i).natDegree ≤ D * F.natDegree := by
    intro i
    by_cases hi : G.coeff i = 0
    · simp [hi]
    · calc (G.coeff i).natDegree ≤ (G.coeff i).natDegree + D * i := Nat.le_add_right _ _
        _ ≤ D * G.natDegree := natDegree_coeff_le_of_monic_mul D hG hH hbound i hi
        _ ≤ D * F.natDegree := Nat.mul_le_mul_left D (by omega)
  have hHE : ∀ i, (H.coeff i).natDegree ≤ D * F.natDegree := by
    intro i
    by_cases hi : H.coeff i = 0
    · simp [hi]
    · calc (H.coeff i).natDegree ≤ (H.coeff i).natDegree + D * i := Nat.le_add_right _ _
        _ ≤ D * H.natDegree := natDegree_coeff_le_of_monic_mul D hH hG hbound' i hi
        _ ≤ D * F.natDegree := Nat.mul_le_mul_left D (by omega)
  -- so the eliminated equation for this pair of degrees vanishes at `y`, which it must not
  have hker := factorIdeal_le_ker (D * F.natDegree) G.natDegree H.natDegree F
    (MvPolynomial.aeval y : MvPolynomial σ k →ₐ[k] k).toRingHom hG hH rfl rfl hGE hHE hGH
  have hGlt : G.natDegree < F.natDegree + 1 := by omega
  have hHlt : H.natDegree < F.natDegree + 1 := by omega
  have hzero : MvPolynomial.aeval y (q G.natDegree H.natDegree) = 0 := by
    have := hker (hqmem G.natDegree H.natDegree hGpos hHpos)
    simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this
  refine hyQ (⟨G.natDegree, hGlt⟩, ⟨H.natDegree, hHlt⟩) ?_
  dsimp only
  rw [if_pos ⟨hGpos, hHpos⟩]
  exact hzero

/-! ## From monic factors to irreducibility over the function field

A monic polynomial in two variables is irreducible over the function field of the line exactly when
it admits no factorization into two monic factors of positive degree — Gauss's lemma, plus the
observation that a factorization of a monic polynomial can always be normalized to a monic one. -/

/-- **A monic two-variable polynomial is irreducible over the function field of the line exactly
when it has no monic factor of positive degree.** -/
theorem irreducible_map_ratFunc_iff {F : Type*} [Field F] {f : F[X][Y]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) :
    Irreducible (f.map (algebraMap (F[X]) (RatFunc F))) ↔
      ∀ G H : F[X][Y], G.Monic → H.Monic → 0 < G.natDegree → 0 < H.natDegree → f ≠ G * H := by
  rw [← hf.irreducible_iff_irreducible_map_fraction_map (K := RatFunc F),
    hf.irreducible_iff_natDegree]
  constructor
  · rintro ⟨-, h⟩ G H hG hH hGpos hHpos hGH
    rcases h G H hG hH hGH.symm with h0 | h0 <;> omega
  · refine fun h => ⟨fun h1 => ?_, fun G H hG hH hGH => ?_⟩
    · rw [h1, natDegree_one] at hdeg
      exact absurd hdeg (lt_irrefl 0)
    · by_contra hcon
      push_neg at hcon
      exact h G H hG hH (Nat.pos_of_ne_zero hcon.1) (Nat.pos_of_ne_zero hcon.2) hGH.symm

/-- **Irreducibility over the function field of the line descends to the algebraically closed
base**, together with every polynomial identity satisfied by the parameters. -/
theorem exists_specialization_irreducible {D : ℕ}
    (F : (MvPolynomial σ k)[X][Y]) (hFm : F.Monic) (hFpos : 0 < F.natDegree)
    (hFd : ∀ i, F.coeff i ≠ 0 → (F.coeff i).natDegree + D * i ≤ D * F.natDegree)
    (x : σ → K)
    (hirr : Irreducible (((F.map (mapRingHom
      (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] K).toRingHom))).map
        (algebraMap (K[X]) (RatFunc K)))) :
    ∃ y : σ → k,
      (∀ p : MvPolynomial σ k, MvPolynomial.aeval x p = 0 → MvPolynomial.aeval y p = 0) ∧
      Irreducible (((F.map (mapRingHom
        (MvPolynomial.aeval y : MvPolynomial σ k →ₐ[k] k).toRingHom))).map
          (algebraMap (k[X]) (RatFunc k))) := by
  have hmx : (F.map (mapRingHom
      (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] K).toRingHom)).Monic := hFm.map _
  have hdx : (F.map (mapRingHom
      (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] K).toRingHom)).natDegree = F.natDegree :=
    hFm.natDegree_map _
  obtain ⟨y, hy, hfac⟩ :=
    exists_specialization_no_monic_factor (D := D) F hFm hFd x
      ((irreducible_map_ratFunc_iff hmx (by omega)).1 hirr)
  have hmy : (F.map (mapRingHom
      (MvPolynomial.aeval y : MvPolynomial σ k →ₐ[k] k).toRingHom)).Monic := hFm.map _
  have hdy : (F.map (mapRingHom
      (MvPolynomial.aeval y : MvPolynomial σ k →ₐ[k] k).toRingHom)).natDegree = F.natDegree :=
    hFm.natDegree_map _
  exact ⟨y, hy, (irreducible_map_ratFunc_iff hmy (by omega)).2 hfac⟩

end Rigidity.RET.Transfer
