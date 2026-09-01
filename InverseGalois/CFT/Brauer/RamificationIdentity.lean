/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.ResidueDegree
import InverseGalois.CFT.Brauer.DivisionValueGroup
import InverseGalois.CFT.Brauer.DivisionCompact

/-!
# The fundamental identity of a finite extension of a local field

Let `K` be a nonarchimedean local field and `L` a finite extension of degree `n`.  The absolute
value of an element of `L` is the `n`-th root of the absolute value of its norm to `K`, so the
absolute values of the nonzero elements of `L` are the integer powers of a fixed number below one
and `L` has a uniformizer `ϖ`.  Write `e` for the number of steps of the value group of `L` that
make up one step of the value group of `K`, and `f` for the degree of the residue extension.

The products of a lift of a basis of the residue field with the powers of `ϖ` below the `e`-th
form a basis of `L`.  They are independent because the absolute value of a combination of the lifts
is the absolute value of a scalar: the terms of a relation then have pairwise different absolute
values and cannot cancel.  They generate because an element can be corrected by such a combination
so that its absolute value drops by one step of the value group, and a subspace is closed for the
absolute value.

## Main results

* `InverseGalois.CFT.exists_isDivisionUniformizer_of_field`: **a finite extension of a local field
  has a uniformizer.**
* `InverseGalois.CFT.ramification_mul_finrank_divisionResidue`: **the ramification index times the
  residue degree is the degree of the extension.**

## Tags

local field, ramification index, residue degree, fundamental identity, uniformizer
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u

open Module

namespace InverseGalois.CFT

/-! ### Sums of terms with different absolute values -/

section Ultrametric

variable {K D : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

/-- Adding something smaller does not change an absolute value. -/
theorem divisionNorm_add_eq_left {a b : D} (h : divisionNorm K D b < divisionNorm K D a) :
    divisionNorm K D (a + b) = divisionNorm K D a := by
  refine le_antisymm ((divisionNorm_isNonarchimedean a b).trans (max_le le_rfl h.le)) ?_
  have hsub : a = a + b + -b := (add_neg_cancel_right a b).symm
  have hle := divisionNorm_isNonarchimedean (K := K) (D := D) (a + b) (-b)
  rw [← hsub, divisionNorm_neg] at hle
  rcases le_total (divisionNorm K D (a + b)) (divisionNorm K D b) with hm | hm
  · rw [max_eq_right hm] at hle
    exact absurd (lt_of_le_of_lt hle h) (lt_irrefl _)
  · rwa [max_eq_left hm] at hle

/-- A sum of terms of absolute value below a bound stays below that bound. -/
theorem divisionNorm_sum_lt {ι : Type*} (s : Finset ι) (t : ι → D) {c : ℝ} (hc : 0 < c) :
    (∀ i ∈ s, divisionNorm K D (t i) < c) → divisionNorm K D (∑ i ∈ s, t i) < c := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _; simpa [divisionNorm_zero] using hc
  | @insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha]
      exact lt_of_le_of_lt (divisionNorm_isNonarchimedean _ _)
        (max_lt (h a (Finset.mem_insert_self a s))
          (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **A sum of nonzero terms with pairwise different absolute values is nonzero**: the largest term
dominates the others, so the absolute value of the sum is the absolute value of that term. -/
theorem sum_ne_zero_of_divisionNorm_pairwise_ne {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (t : ι → D) (hne : ∀ i ∈ s, t i ≠ 0)
    (hinj : ∀ i ∈ s, ∀ i' ∈ s, divisionNorm K D (t i) = divisionNorm K D (t i') → i = i') :
    ∑ i ∈ s, t i ≠ 0 := by
  classical
  obtain ⟨i₀, hi₀s, hmax⟩ := Finset.exists_max_image s (fun i => divisionNorm K D (t i)) hs
  have hrest : divisionNorm K D (∑ i ∈ s.erase i₀, t i) < divisionNorm K D (t i₀) := by
    refine divisionNorm_sum_lt _ _ (divisionNorm_pos (hne i₀ hi₀s)) fun i hi => ?_
    have hmem : i ∈ s := Finset.mem_of_mem_erase hi
    refine lt_of_le_of_ne (hmax i hmem) fun heq => ?_
    exact (Finset.ne_of_mem_erase hi) (hinj i hmem i₀ hi₀s heq)
  have hsplit : ∑ i ∈ s, t i = t i₀ + ∑ i ∈ s.erase i₀, t i :=
    (Finset.add_sum_erase s t hi₀s).symm
  rw [hsplit]
  intro hzero
  have := divisionNorm_add_eq_left hrest
  rw [hzero, divisionNorm_zero] at this
  exact (hne i₀ hi₀s) (divisionNorm_eq_zero_iff.1 this.symm)

end Ultrametric

/-! ### The value group of a finite extension -/

section ValueGroup

variable {K L : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]

omit [IsUltrametricDist K] [ProperSpace K] in
variable (K L) in
/-- The absolute value of an element of a finite extension is the root of index the degree of the
absolute value of its norm. -/
theorem divisionNorm_pow_finrank (x : L) :
    divisionNorm K L x ^ finrank K L = ‖Algebra.norm K x‖ := by
  have hN : ((finrank K L : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Module.finrank_pos (R := K) (M := L)).ne'
  rw [divisionNorm, ← Real.rpow_natCast (‖Algebra.norm K x‖ ^ (1 / finrank K L : ℝ)) (finrank K L),
    ← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hN, Real.rpow_one]

omit [IsUltrametricDist K] [ProperSpace K] in
/-- **The absolute values of the nonzero elements of a finite extension of a local field are the
integer powers of the root of index the degree of the absolute value of a uniformizer.** -/
theorem exists_divisionNorm_eq_zpow {π : K} (hπ : IsNormUniformizer π) {x : L} (hx : x ≠ 0) :
    ∃ i : ℤ, divisionNorm K L x = (‖π‖ ^ ((finrank K L : ℝ)⁻¹)) ^ i := by
  have hp : 0 < ‖π‖ := hπ.norm_pos
  have hN0 : finrank K L ≠ 0 := (Module.finrank_pos (R := K) (M := L)).ne'
  have hN : ((finrank K L : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN0
  set ρ : ℝ := ‖π‖ ^ ((finrank K L : ℝ)⁻¹) with hρdef
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hp _
  have hρpow : ρ ^ (finrank K L) = ‖π‖ := by
    rw [hρdef, ← Real.rpow_natCast (‖π‖ ^ ((finrank K L : ℝ)⁻¹)) (finrank K L),
      ← Real.rpow_mul hp.le, inv_mul_cancel₀ hN, Real.rpow_one]
  obtain ⟨j, hj⟩ := hπ.exists_zpow (algebraNorm_ne_zero (K := K) hx)
  refine ⟨j, ?_⟩
  have hpow : (ρ ^ j) ^ (finrank K L) = ‖Algebra.norm K x‖ := by
    rw [← zpow_natCast (ρ ^ j) (finrank K L), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρpow,
      hj]
  exact (pow_left_inj₀ (divisionNorm_nonneg x) (zpow_pos hρpos _).le hN0).1
    ((divisionNorm_pow_finrank K L x).trans hpow.symm)

omit [IsUltrametricDist K] [ProperSpace K] in
variable (K L) in
/-- **A finite extension of a nonarchimedean local field has a uniformizer.**  The absolute values
of the nonzero elements are the integer powers of a fixed number less than one, and the exponents
that occur and are positive have a least element. -/
theorem exists_isDivisionUniformizer_of_field {π : K} (hπ : IsNormUniformizer π) :
    ∃ ϖ : L, IsDivisionUniformizer K L ϖ := by
  have hp : 0 < ‖π‖ := hπ.norm_pos
  have hN1 : 1 ≤ finrank K L := Module.finrank_pos (R := K) (M := L)
  have hN : ((finrank K L : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set ρ : ℝ := ‖π‖ ^ ((finrank K L : ℝ)⁻¹) with hρdef
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hp _
  have hρ1 : ρ < 1 := Real.rpow_lt_one hp.le hπ.norm_lt_one (by positivity)
  have hρpow : ρ ^ (finrank K L) = ‖π‖ := by
    rw [hρdef, ← Real.rpow_natCast (‖π‖ ^ ((finrank K L : ℝ)⁻¹)) (finrank K L),
      ← Real.rpow_mul hp.le, inv_mul_cancel₀ hN, Real.rpow_one]
  set S : Set ℕ := {j | ∃ x : L, x ≠ 0 ∧ divisionNorm K L x = ρ ^ ((j : ℤ) + 1)} with hSdef
  have hSne : S.Nonempty := by
    refine ⟨finrank K L - 1, algebraMap K L π, ?_, ?_⟩
    · exact fun h => hπ.ne_zero ((algebraMap K L).injective (h.trans (map_zero _).symm))
    · have hcast : ((finrank K L - 1 : ℕ) : ℤ) + 1 = ((finrank K L : ℕ) : ℤ) := by omega
      rw [divisionNorm_algebraMap, hcast, zpow_natCast, hρpow]
  obtain ⟨ϖ, hϖ0, hϖ⟩ := Nat.sInf_mem hSne
  refine ⟨ϖ, hϖ0, ?_, ?_⟩
  · rw [hϖ]
    exact zpow_lt_one₀ hρpos hρ1 (by positivity)
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [hϖ, divisionNorm_zero]
      exact (zpow_pos hρpos _).le
    · obtain ⟨i, hi⟩ := exists_divisionNorm_eq_zpow hπ hx0
      rw [← hρdef] at hi
      rw [hi] at hx ⊢
      rw [hϖ]
      have hipos : 0 < i := by
        by_contra hcon
        push_neg at hcon
        have h1 : ρ ^ (0 : ℤ) ≤ ρ ^ i := zpow_le_zpow_right_of_le_one₀ hρpos hρ1.le hcon
        rw [zpow_zero] at h1
        exact absurd hx (not_lt.2 h1)
      have hmem : (i - 1).toNat ∈ S := ⟨x, hx0, by rw [hi]; congr 1; omega⟩
      have hle : ((sInf S : ℕ) : ℤ) + 1 ≤ i := by
        have := Nat.sInf_le hmem
        omega
      exact zpow_le_zpow_right_of_le_one₀ hρpos hρ1.le hle

end ValueGroup

/-! ### The fundamental identity -/

section Fundamental

variable {K L : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]

attribute [local instance] residueBaseField residueBaseAlgebra

omit [IsUltrametricDist K] [ProperSpace K] [FiniteDimensional K L] in
/-- The absolute value of a nonzero scalar is a whole number of periods of the value group. -/
theorem exists_norm_eq_zpow_mul {π : K} (hπ : IsNormUniformizer π) {ϖ : L} {e : ℕ}
    (hee : divisionNorm K L ϖ ^ e = ‖π‖) {d : K} (hd : d ≠ 0) :
    ∃ k : ℤ, ‖d‖ = divisionNorm K L ϖ ^ ((e : ℤ) * k) := by
  obtain ⟨k, hk⟩ := hπ.exists_zpow hd
  refine ⟨k, ?_⟩
  rw [hk, ← hee, ← zpow_natCast (divisionNorm K L ϖ) e, ← zpow_mul]

/-- **Lifts of a basis of the residue field, multiplied by the powers of a uniformizer below the
ramification index, are independent over the base field.**  The absolute value of a combination of
the lifts is the absolute value of a scalar, so the terms of a relation have pairwise different
absolute values and the largest of them cannot be cancelled. -/
theorem linearIndependent_mul_pow {ϖ : L} (hϖ : IsDivisionUniformizer K L ϖ) {π : K}
    (hπ : IsNormUniformizer π) {e : ℕ} (hee : divisionNorm K L ϖ ^ e = ‖π‖) {f : ℕ}
    (y : Fin f → divisionIntegers K L)
    (hyind : LinearIndependent (DivisionResidue K K)
      fun j => ((y j : divisionIntegers K L) : DivisionResidue K L)) :
    LinearIndependent K
      fun p : Fin e × Fin f => ((y p.2 : divisionIntegers K L) : L) * ϖ ^ (p.1 : ℕ) := by
  classical
  have hρpos : 0 < divisionNorm K L ϖ := hϖ.norm_pos
  have hρ1 : divisionNorm K L ϖ < 1 := hϖ.norm_lt_one
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hind0 : LinearIndependent K fun j => ((y j : divisionIntegers K L) : L) :=
    linearIndependent_of_linearIndependent_divisionResidue y hyind
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hzzero : ∀ i : Fin e, (∑ j, g (i, j) • ((y j : divisionIntegers K L) : L)) = 0 := by
    by_contra hcon
    push_neg at hcon
    set t : Fin e → L :=
      fun i => (∑ j, g (i, j) • ((y j : divisionIntegers K L) : L)) * ϖ ^ (i : ℕ) with htdef
    have hsum : ∑ i : Fin e, t i = 0 := by
      rw [← hg, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [htdef, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _
    set S : Finset (Fin e) :=
      Finset.univ.filter fun i => (∑ j, g (i, j) • ((y j : divisionIntegers K L) : L)) ≠ 0
      with hSdef
    have hmemS : ∀ i : Fin e,
        i ∈ S ↔ (∑ j, g (i, j) • ((y j : divisionIntegers K L) : L)) ≠ 0 := by
      intro i; simp [hSdef]
    obtain ⟨i₁, hi₁⟩ := hcon
    have hSne : S.Nonempty := ⟨i₁, (hmemS i₁).2 hi₁⟩
    have htne : ∀ i ∈ S, t i ≠ 0 := by
      intro i hi
      simp only [htdef]
      exact mul_ne_zero ((hmemS i).1 hi) (pow_ne_zero _ hϖ0)
    have hkey : ∀ i ∈ S, ∃ k : ℤ,
        divisionNorm K L (t i) = divisionNorm K L ϖ ^ ((e : ℤ) * k + ((i : ℕ) : ℤ)) := by
      intro i hi
      have hex : ∃ j : Fin f, g (i, j) ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact (hmemS i).1 hi (by simp [hall])
      obtain ⟨j₀, hj₀⟩ := hex
      obtain ⟨d, hd0, hd⟩ := exists_divisionNorm_sum_eq y hyind (fun j => g (i, j)) hj₀
      obtain ⟨k, hk⟩ := exists_norm_eq_zpow_mul hπ hee hd0
      refine ⟨k, ?_⟩
      simp only [htdef, divisionNorm_mul, divisionNorm_pow, hd, hk]
      rw [← zpow_natCast (divisionNorm K L ϖ) (i : ℕ), ← zpow_add₀ hρpos.ne']
    have hinj : ∀ i ∈ S, ∀ i' ∈ S,
        divisionNorm K L (t i) = divisionNorm K L (t i') → i = i' := by
      intro i hi i' hi' heq
      obtain ⟨k, hk⟩ := hkey i hi
      obtain ⟨k', hk'⟩ := hkey i' hi'
      rw [hk, hk'] at heq
      have hexp : (e : ℤ) * k + ((i : ℕ) : ℤ) = (e : ℤ) * k' + ((i' : ℕ) : ℤ) :=
        (zpow_right_strictAnti₀ hρpos hρ1).injective heq
      have hcast : ((i : ℕ) : ℤ) = ((i' : ℕ) : ℤ) := by
        have h1 : (((i : ℕ) : ℤ) + (e : ℤ) * k) % (e : ℤ) = ((i : ℕ) : ℤ) := by
          rw [Int.add_mul_emod_self_left]
          exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt)
        have h2 : (((i' : ℕ) : ℤ) + (e : ℤ) * k') % (e : ℤ) = ((i' : ℕ) : ℤ) := by
          rw [Int.add_mul_emod_self_left]
          exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i'.isLt)
        rw [← h1, ← h2]
        congr 1
        linarith
      exact Fin.ext (by exact_mod_cast hcast)
    refine sum_ne_zero_of_divisionNorm_pairwise_ne hSne t htne hinj ?_
    rw [← hsum]
    refine Finset.sum_subset (Finset.subset_univ S) ?_
    intro i _ hi
    have : (∑ j, g (i, j) • ((y j : divisionIntegers K L) : L)) = 0 := by
      by_contra hcon'
      exact hi ((hmemS i).2 hcon')
    simp only [htdef, this, zero_mul]
  intro p
  exact Fintype.linearIndependent_iff.1 hind0 (fun j => g (p.1, j)) (hzzero p.1) p.2

/-- **Lifts of a basis of the residue field, multiplied by the powers of a uniformizer below the
ramification index, generate the extension over the base field.**  Correcting an element by such a
combination makes its absolute value drop by one step of the value group, and the span is closed
for the absolute value. -/
theorem span_mul_pow_eq_top {ϖ : L} (hϖ : IsDivisionUniformizer K L ϖ) {π : K}
    (hπ : IsNormUniformizer π) {e : ℕ} (he : 0 < e) (hee : divisionNorm K L ϖ ^ e = ‖π‖) {f : ℕ}
    (b : Basis (Fin f) (DivisionResidue K K) (DivisionResidue K L))
    (y : Fin f → divisionIntegers K L)
    (hy : ∀ j, ((y j : divisionIntegers K L) : DivisionResidue K L) = b j) :
    Submodule.span K
        (Set.range fun p : Fin e × Fin f =>
          ((y p.2 : divisionIntegers K L) : L) * ϖ ^ (p.1 : ℕ)) = ⊤ := by
  classical
  set w : Fin e × Fin f → L :=
    fun p => ((y p.2 : divisionIntegers K L) : L) * ϖ ^ (p.1 : ℕ) with hwdef
  set V : Submodule K L := Submodule.span K (Set.range w) with hVdef
  have hρpos : 0 < divisionNorm K L ϖ := hϖ.norm_pos
  have hρ1 : divisionNorm K L ϖ < 1 := hϖ.norm_lt_one
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hepos : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  -- one step of approximation
  have hstep : ∀ x : L, ∃ v ∈ V,
      divisionNorm K L (x - v) ≤ divisionNorm K L ϖ * divisionNorm K L x := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, V.zero_mem, by simp [divisionNorm_zero]⟩
    obtain ⟨m, hm⟩ := hϖ.exists_zpow hx
    have hi0 : 0 ≤ m % (e : ℤ) := Int.emod_nonneg m (by omega)
    have hie : m % (e : ℤ) < (e : ℤ) := Int.emod_lt_of_pos m hepos
    have hms : (e : ℤ) * (m / (e : ℤ)) + m % (e : ℤ) = m := Int.mul_ediv_add_emod m (e : ℤ)
    have hitn : (m % (e : ℤ)).toNat < e := by omega
    set i : ℤ := m % (e : ℤ) with hidef
    set s : ℤ := m / (e : ℤ) with hsdef
    set c : L := ϖ ^ i * algebraMap K L (π ^ s) with hcdef
    have hc0 : c ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ hϖ0) fun h =>
        (zpow_ne_zero s hπ0) ((map_eq_zero_iff _ (algebraMap K L).injective).1 h)
    have hcn : divisionNorm K L c = divisionNorm K L ϖ ^ m := by
      rw [hcdef, divisionNorm_mul, divisionNorm_zpow, divisionNorm_algebraMap, norm_zpow, ← hee,
        ← zpow_natCast (divisionNorm K L ϖ) e, ← zpow_mul, ← zpow_add₀ hρpos.ne']
      congr 1
      linarith
    have hu1 : divisionNorm K L (x / c) = 1 := by
      rw [div_eq_mul_inv, divisionNorm_mul, divisionNorm_inv, hm, hcn]
      exact mul_inv_cancel₀ (zpow_ne_zero m hρpos.ne')
    set U : divisionIntegers K L := ⟨x / c, mem_divisionIntegers.2 hu1.le⟩ with hUdef
    obtain ⟨C, hC⟩ : ∃ C : Fin f → divisionIntegers K K, ∀ j,
        ((C j : divisionIntegers K K) : DivisionResidue K K)
          = b.repr ((U : divisionIntegers K L) : DivisionResidue K L) j := by
      choose C hC using fun j =>
        (divisionResidueCon K K).mk'_surjective
          (b.repr ((U : divisionIntegers K L) : DivisionResidue K L) j)
      exact ⟨C, hC⟩
    set v0 : divisionIntegers K L := ∑ j, divisionIntegersBase L (C j) * y j with hv0def
    have hres : ((v0 : divisionIntegers K L) : DivisionResidue K L)
        = ((U : divisionIntegers K L) : DivisionResidue K L) := by
      have h1 : ((v0 : divisionIntegers K L) : DivisionResidue K L)
          = ∑ j, ((C j : divisionIntegers K K) : DivisionResidue K K) •
              ((y j : divisionIntegers K L) : DivisionResidue K L) := by
        show (divisionResidueCon K L).mk' (∑ j, divisionIntegersBase L (C j) * y j) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [residueBaseAlgebra_smul_def, divisionResidueBase_coe, map_mul]
        simp only [RingCon.coe_mk']
      rw [h1]
      conv_rhs => rw [← b.sum_repr ((U : divisionIntegers K L) : DivisionResidue K L)]
      exact Finset.sum_congr rfl fun j _ => by rw [hC j, hy j]
    have hlt : divisionNorm K L (((U : divisionIntegers K L) : L)
        - ((v0 : divisionIntegers K L) : L)) < 1 := divisionResidue_eq_iff.1 hres.symm
    have hle : divisionNorm K L (((U : divisionIntegers K L) : L)
        - ((v0 : divisionIntegers K L) : L)) ≤ divisionNorm K L ϖ := hϖ.le_norm _ hlt
    refine ⟨c * ((v0 : divisionIntegers K L) : L), ?_, ?_⟩
    · have hϖi : ϖ ^ i = ϖ ^ i.toNat := by
        conv_lhs => rw [← Int.toNat_of_nonneg hi0]
        rw [zpow_natCast]
      have heq : c * ((v0 : divisionIntegers K L) : L)
          = ∑ j, ((π ^ s) * ((C j : divisionIntegers K K) : K)) •
              w (⟨i.toNat, hitn⟩, j) := by
        simp only [hwdef, Algebra.smul_def, map_mul, hv0def]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hcdef, coe_divisionIntegersBase, hϖi]
        push_cast
        ring
      rw [heq]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))
    · have hxc : x = c * ((U : divisionIntegers K L) : L) := by
        rw [hUdef]
        field_simp
      have hfac : x - c * ((v0 : divisionIntegers K L) : L)
          = c * (((U : divisionIntegers K L) : L) - ((v0 : divisionIntegers K L) : L)) := by
        rw [mul_sub, ← hxc]
      rw [hfac, divisionNorm_mul, hcn, hm]
      calc divisionNorm K L ϖ ^ m * divisionNorm K L (((U : divisionIntegers K L) : L)
              - ((v0 : divisionIntegers K L) : L))
            ≤ divisionNorm K L ϖ ^ m * divisionNorm K L ϖ :=
              mul_le_mul_of_nonneg_left hle (zpow_nonneg hρpos.le m)
        _ = divisionNorm K L ϖ * divisionNorm K L ϖ ^ m := by ring
  -- iterating the approximation
  have hiter : ∀ (k : ℕ) (x : L), ∃ v ∈ V,
      divisionNorm K L (x - v) ≤ divisionNorm K L ϖ ^ k * divisionNorm K L x := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, V.zero_mem, by simp⟩
    | succ n ih =>
        intro x
        obtain ⟨v, hv, hvle⟩ := ih x
        obtain ⟨v', hv', hv'le⟩ := hstep (x - v)
        refine ⟨v + v', V.add_mem hv hv', ?_⟩
        have hrw : x - (v + v') = x - v - v' := by ring
        rw [hrw]
        calc divisionNorm K L (x - v - v')
              ≤ divisionNorm K L ϖ * divisionNorm K L (x - v) := hv'le
          _ ≤ divisionNorm K L ϖ * (divisionNorm K L ϖ ^ n * divisionNorm K L x) :=
              mul_le_mul_of_nonneg_left hvle hρpos.le
          _ = divisionNorm K L ϖ ^ (n + 1) * divisionNorm K L x := by ring
  rw [eq_top_iff]
  intro x _
  refine mem_of_forall_exists_divisionNorm_sub_lt K L V fun ε hε => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, V.zero_mem, by simpa [divisionNorm_zero] using hε⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, divisionNorm K L ϖ ^ k < ε / divisionNorm K L x :=
    exists_pow_lt_of_lt_one (div_pos hε (divisionNorm_pos hx)) hρ1
  obtain ⟨v, hv, hvle⟩ := hiter k x
  refine ⟨v, hv, lt_of_le_of_lt hvle ?_⟩
  rwa [← lt_div_iff₀ (divisionNorm_pos hx)]

variable (K L) in
/-- **The fundamental identity of a finite extension of a local field**: the ramification index
times the residue degree is the degree of the extension.  Lifts of a basis of the residue field,
multiplied by the powers of a uniformizer below the ramification index, form a basis. -/
theorem ramification_mul_finrank_divisionResidue {π : K} (hπ : IsNormUniformizer π) {ϖ : L}
    (hϖ : IsDivisionUniformizer K L ϖ) {e : ℕ} (he : 0 < e)
    (hee : divisionNorm K L ϖ ^ e = ‖π‖) :
    e * finrank (DivisionResidue K K) (DivisionResidue K L) = finrank K L := by
  classical
  set f : ℕ := finrank (DivisionResidue K K) (DivisionResidue K L) with hfdef
  set b := Module.finBasis (DivisionResidue K K) (DivisionResidue K L) with hb
  choose y hy using fun j => (divisionResidueCon K L).mk'_surjective (b j)
  have hy' : ∀ j, ((y j : divisionIntegers K L) : DivisionResidue K L) = b j := hy
  have hyind : LinearIndependent (DivisionResidue K K)
      fun j => ((y j : divisionIntegers K L) : DivisionResidue K L) := by
    have hyb : (fun j => ((y j : divisionIntegers K L) : DivisionResidue K L)) = b := funext hy'
    rw [hyb]
    exact b.linearIndependent
  have hindep := linearIndependent_mul_pow hϖ hπ hee y hyind
  have hspan := span_mul_pow_eq_top hϖ hπ he hee b y hy'
  have hbasis : Basis (Fin e × Fin f) K L := Basis.mk hindep (le_of_eq hspan.symm)
  rw [Module.finrank_eq_card_basis hbasis, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

end Fundamental

end InverseGalois.CFT
