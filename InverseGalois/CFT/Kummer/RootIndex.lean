/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The index of the stabilizer of a radical

Let `M / K` be a finite Galois extension and let `x` be an element of `M` whose `p`-th power lies
in the base field.  The subgroup of the Galois group fixing `x` has index at most `p`, since `x`
generates a subextension of degree at most `p`: the polynomial `X ^ p - a` is monic and kills `x`,
so the minimal polynomial has degree at most `p`, and the degree of a subextension is the index of
the subgroup fixing it.

If moreover the Galois group is a `p`-group and the radicand is not already a `p`-th power in the
base field, the index is exactly `p`.  Indeed the index divides the order of the group, so it is a
power of `p`, and it is neither `1` — else `x` would be fixed by everything and so lie in the base
field, making its radicand a `p`-th power there — nor a higher power, by the bound above.

## Main results

* `InverseGalois.CFT.fixingSubgroup_adjoin_simple_eq_stabilizer`: the subgroup fixing a simple
  subextension is the stabilizer of the generator.
* `InverseGalois.CFT.index_stabilizer_le`: **the stabilizer of a `p`-th root has index at most
  `p`.**
* `InverseGalois.CFT.index_stabilizer_eq`: **for a Galois group of `p`-power order, the stabilizer
  of a `p`-th root of a non-`p`-th-power has index exactly `p`.**

## Tags

Galois theory, radical, stabilizer, index, Kummer theory
-/

namespace InverseGalois.CFT

open MulAction IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  {p : ℕ}

omit [FiniteDimensional K M] [IsGalois K M] in
/-- The subgroup fixing a simple subextension is the stabilizer of its generator. -/
theorem fixingSubgroup_adjoin_simple_eq_stabilizer (x : M) :
    (K⟮x⟯ : IntermediateField K M).fixingSubgroup = stabilizer Gal(M/K) x := by
  ext σ
  simp only [IntermediateField.mem_fixingSubgroup_iff, mem_stabilizer_iff]
  constructor
  · intro h
    exact h x (IntermediateField.mem_adjoin_simple_self K x)
  · intro h y hy
    have hzs : Subgroup.zpowers σ ≤ stabilizer Gal(M/K) x := by
      rw [Subgroup.zpowers_le]
      exact h
    have hle : Subgroup.zpowers σ ≤ (K⟮x⟯ : IntermediateField K M).fixingSubgroup := by
      rw [← IntermediateField.le_iff_le, IntermediateField.adjoin_simple_le_iff]
      exact fun τ => hzs τ.2
    exact hle (Subgroup.mem_zpowers σ) ⟨y, hy⟩

/-- **The stabilizer of a `p`-th root has index at most `p`**, that index being the degree of the
subextension the root generates, and the minimal polynomial of the root dividing `X ^ p - a`. -/
theorem index_stabilizer_le (hp : p ≠ 0) {a : K} {x : M} (hx : x ^ p = algebraMap K M a) :
    (stabilizer Gal(M/K) x).index ≤ p := by
  rw [← fixingSubgroup_adjoin_simple_eq_stabilizer,
    ← IntermediateField.finrank_eq_fixingSubgroup_index]
  have hint : IsIntegral K x := IsIntegral.of_finite K x
  rw [IntermediateField.adjoin.finrank hint]
  have hmonic : (Polynomial.X ^ p - Polynomial.C a).Monic := Polynomial.monic_X_pow_sub_C a hp
  have hroot : Polynomial.aeval x (Polynomial.X ^ p - Polynomial.C a) = 0 := by
    simp [hx]
  have hmin := minpoly.min K x hmonic hroot
  have hdeg : (Polynomial.X ^ p - Polynomial.C a : Polynomial K).natDegree = p :=
    Polynomial.natDegree_X_pow_sub_C
  exact (Polynomial.natDegree_le_natDegree hmin).trans_eq hdeg

/-- The stabilizer of a `p`-th root of an element which is not a `p`-th power in the base field is
a proper subgroup: an element fixed by the whole Galois group lies in the base field. -/
theorem stabilizer_ne_top (hp : p ≠ 0) {a : Kˣ} {x : M}
    (hx : x ^ p = algebraMap K M (a : K)) (hnot : ∀ y : Kˣ, a ≠ y ^ p) :
    stabilizer Gal(M/K) x ≠ ⊤ := by
  intro htop
  have hfix : ∀ σ : Gal(M/K), σ x = x := fun σ =>
    mem_stabilizer_iff.mp (by rw [htop]; exact Subgroup.mem_top σ)
  obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hfix
  have hyne : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    have : (a : K) = 0 := by
      have := hx
      rw [← hy, zero_pow hp] at this
      exact (map_eq_zero _).mp this.symm
    exact (Units.ne_zero a) this
  refine hnot (Units.mk0 y hyne) (Units.ext ?_)
  have : algebraMap K M ((y : K) ^ p) = algebraMap K M (a : K) := by
    rw [map_pow, hy, hx]
  exact ((algebraMap K M).injective this).symm

/-- **For a Galois group of `p`-power order, the stabilizer of a `p`-th root of an element which is
not already a `p`-th power in the base field has index exactly `p`.**  The index is a power of `p`
at most `p`, and it is not `1`. -/
theorem index_stabilizer_eq (hp : p.Prime) {s : ℕ} (hcard : Nat.card Gal(M/K) = p ^ s)
    {a : Kˣ} {x : M} (hx : x ^ p = algebraMap K M (a : K)) (hnot : ∀ y : Kˣ, a ≠ y ^ p) :
    (stabilizer Gal(M/K) x).index = p := by
  have hdvd : (stabilizer Gal(M/K) x).index ∣ p ^ s := by
    rw [← hcard]
    exact Subgroup.index_dvd_card _
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hle : (stabilizer Gal(M/K) x).index ≤ p := index_stabilizer_le hp.ne_zero hx
  have hne : (stabilizer Gal(M/K) x).index ≠ 1 := by
    intro h1
    exact stabilizer_ne_top hp.ne_zero hx hnot (Subgroup.index_eq_one.mp h1)
  match k, hkeq with
  | 0, hkeq => exact absurd (by simpa using hkeq) hne
  | 1, hkeq => simpa using hkeq
  | (k + 2), hkeq =>
    exfalso
    rw [hkeq] at hle
    have hlt : p ^ 1 < p ^ (k + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    rw [pow_one] at hlt
    omega

end InverseGalois.CFT
