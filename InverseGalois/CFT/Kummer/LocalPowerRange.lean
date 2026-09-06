/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LocalPower

/-!
# A radical whose local `p`-th power comes from below

Let `M / K` be a Galois extension of number fields whose base contains a primitive `p`-th root of
unity and let `w` be a place of `M`, finite or infinite.  The criterion for the decomposition group
at `w` to fix a radical is usually stated for a radicand lying in `K`; what the proof of that
criterion really uses is weaker, and weaker is what an infinite extension needs.

In one direction, an element of `M` fixed by the decomposition group at `w` has an image in the
completion at `w` which **comes from the completion of `K` below**: that is the description of the
completion below as the fixed field of the decomposition group, read through the action of the
decomposition group on the completion.

In the other direction, an element of `M` whose image in the completion at `w` has the **same `p`-th
power as an element coming from the completion below** is itself fixed by the decomposition group:
the two differ by a `p`-th root of unity, which already lies in `K`, so the image comes from below
as well.  Here the radicand is not required to lie in `K`; only the local `p`-th root is.

Freeing the radicand is what lets a Kummer argument be run for an element of a compositum rather
than of the base: the base supplies the roots of unity and the local root, and the compositum
supplies the radicand.

## Main results

* `InverseGalois.CFT.exists_algebraMap_eq_toAdicCompletion_of_forall_stabilizer_smul_eq`: **an
  element fixed by the decomposition group at a prime has an image in the completion coming from
  the completion below.**
* `InverseGalois.CFT.forall_stabilizer_smul_eq_of_pow_eq_pow`: **an element whose image in the
  completion at a prime has the same `p`-th power as an element from the completion below is fixed
  by the decomposition group there.**
* `InverseGalois.CFT.exists_algebraMap_eq_of_forall_stabilizer_smul_eq_infinite`: **the same first
  statement at an archimedean place.**
* `InverseGalois.CFT.forall_stabilizer_smul_eq_of_pow_eq_pow_infinite`: **the same second statement
  at an archimedean place.**

## Tags

number field, completion, decomposition group, Kummer theory, local power
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### The finite places -/

section FinitePlace

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (w : HeightOneSpectrum (𝓞 M)) {p : ℕ}

/-- **An element fixed by the decomposition group at a prime has an image in the completion coming
from the completion below**, the completion below being the fixed field of the decomposition group
acting on the completion. -/
theorem exists_algebraMap_eq_toAdicCompletion_of_forall_stabilizer_smul_eq {b : M}
    (h : ∀ σ : ↥(stabilizer Gal(M/K) w), (σ : Gal(M/K)) b = b) :
    ∃ c : (primeUnder (𝓞 K) w).adicCompletion K,
      algebraMap ((primeUnder (𝓞 K) w).adicCompletion K) (w.adicCompletion M) c
        = toAdicCompletion w b := by
  refine (mem_range_algebraMap_iff_forall_stabilizer_smul_eq K w (toAdicCompletion w b)).mp ?_
  intro σ
  rw [stabilizer_smul_toAdicCompletion, h σ]

/-- **An element whose image in the completion at a prime has the same `p`-th power as an element
of the completion below is fixed by the decomposition group there**, the base field containing the
`p`-th roots of unity.  The two elements differ by a `p`-th root of unity, which lies in the base
field, so the image comes from the completion below and is therefore fixed. -/
theorem forall_stabilizer_smul_eq_of_pow_eq_pow {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0)
    {b : M} {δ : (primeUnder (𝓞 K) w).adicCompletion K}
    (hd : (algebraMap ((primeUnder (𝓞 K) w).adicCompletion K) (w.adicCompletion M) δ) ^ p
      = (toAdicCompletion w b) ^ p) :
    ∀ σ : ↥(stabilizer Gal(M/K) w), (σ : Gal(M/K)) b = b := by
  haveI : NeZero p := ⟨hp⟩
  have hinjM : Function.Injective (toAdicCompletion w (K := M)) :=
    (toAdicCompletion w (K := M)).injective
  intro σ
  refine hinjM ?_
  rw [← stabilizer_smul_toAdicCompletion]
  revert σ
  rw [mem_range_algebraMap_iff_forall_stabilizer_smul_eq K w (toAdicCompletion w b)]
  rcases eq_or_ne b 0 with rfl | hb
  · exact ⟨0, by rw [map_zero, map_zero]⟩
  have hbne : toAdicCompletion w b ≠ 0 := fun h => hb (hinjM (by simpa using h))
  have hu : (algebraMap ((primeUnder (𝓞 K) w).adicCompletion K) (w.adicCompletion M) δ
      / toAdicCompletion w b) ^ p = 1 := by
    rw [div_pow, hd, div_self (pow_ne_zero p hbne)]
  have hzM : IsPrimitiveRoot (algebraMap K (w.adicCompletion M) ζ) p :=
    hζ.map_of_injective (algebraMap K (w.adicCompletion M)).injective
  obtain ⟨j, -, hj⟩ := hzM.eq_pow_of_pow_eq_one hu
  have hz0 : algebraMap K (w.adicCompletion M) ζ ≠ 0 := by
    intro h0
    have hone := hzM.pow_eq_one
    rw [h0, zero_pow hp] at hone
    exact zero_ne_one hone
  refine ⟨δ * algebraMap K ((primeUnder (𝓞 K) w).adicCompletion K) (ζ ^ j)⁻¹, ?_⟩
  have hmap : algebraMap ((primeUnder (𝓞 K) w).adicCompletion K) (w.adicCompletion M)
      (algebraMap K ((primeUnder (𝓞 K) w).adicCompletion K) (ζ ^ j)⁻¹)
      = ((algebraMap K (w.adicCompletion M) ζ) ^ j)⁻¹ := by
    rw [← IsScalarTower.algebraMap_apply K ((primeUnder (𝓞 K) w).adicCompletion K)
      (w.adicCompletion M), map_inv₀, map_pow]
  have hj' : algebraMap ((primeUnder (𝓞 K) w).adicCompletion K) (w.adicCompletion M) δ
      = (algebraMap K (w.adicCompletion M) ζ) ^ j * toAdicCompletion w b :=
    ((eq_div_iff hbne).mp hj).symm
  rw [map_mul, hmap, hj', mul_right_comm, mul_inv_cancel₀ (pow_ne_zero j hz0), one_mul]

end FinitePlace

/-! ### The infinite places -/

section InfinitePlaceRange

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (w : InfinitePlace M) {p : ℕ}

/-- **An element fixed by the decomposition group at an archimedean place has an image in the
completion coming from the completion below.** -/
theorem exists_algebraMap_eq_of_forall_stabilizer_smul_eq_infinite {b : M}
    (h : ∀ σ : ↥(stabilizer Gal(M/K) w), (σ : Gal(M/K)) b = b) :
    ∃ c : (w.comap (algebraMap K M)).Completion,
      algebraMap ((w.comap (algebraMap K M)).Completion) w.Completion c
        = algebraMap M w.Completion b := by
  refine (mem_range_algebraMap_iff_forall_stabilizer_smul_eq_infinite K w
    (algebraMap M w.Completion b)).mp ?_
  intro σ
  rw [stabilizer_smul_algebraMap_infinitePlace, h σ]

/-- **An element whose image in the completion at an archimedean place has the same `p`-th power as
an element of the completion below is fixed by the decomposition group there**, the base field
containing the `p`-th roots of unity. -/
theorem forall_stabilizer_smul_eq_of_pow_eq_pow_infinite {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hp : p ≠ 0) {b : M} {δ : (w.comap (algebraMap K M)).Completion}
    (hd : (algebraMap ((w.comap (algebraMap K M)).Completion) w.Completion δ) ^ p
      = (algebraMap M w.Completion b) ^ p) :
    ∀ σ : ↥(stabilizer Gal(M/K) w), (σ : Gal(M/K)) b = b := by
  haveI : NeZero p := ⟨hp⟩
  have hinjM : Function.Injective (algebraMap M w.Completion) :=
    (algebraMap M w.Completion).injective
  intro σ
  refine hinjM ?_
  rw [← stabilizer_smul_algebraMap_infinitePlace]
  revert σ
  rw [mem_range_algebraMap_iff_forall_stabilizer_smul_eq_infinite K w
    (algebraMap M w.Completion b)]
  rcases eq_or_ne b 0 with rfl | hb
  · exact ⟨0, by rw [map_zero, map_zero]⟩
  have hbne : algebraMap M w.Completion b ≠ 0 := fun h => hb (hinjM (by simpa using h))
  have hu : (algebraMap ((w.comap (algebraMap K M)).Completion) w.Completion δ
      / algebraMap M w.Completion b) ^ p = 1 := by
    rw [div_pow, hd, div_self (pow_ne_zero p hbne)]
  have hzM : IsPrimitiveRoot (algebraMap K w.Completion ζ) p :=
    hζ.map_of_injective (algebraMap K w.Completion).injective
  obtain ⟨j, -, hj⟩ := hzM.eq_pow_of_pow_eq_one hu
  have hz0 : algebraMap K w.Completion ζ ≠ 0 := by
    intro h0
    have hone := hzM.pow_eq_one
    rw [h0, zero_pow hp] at hone
    exact zero_ne_one hone
  refine ⟨δ * algebraMap K ((w.comap (algebraMap K M)).Completion) (ζ ^ j)⁻¹, ?_⟩
  have hmap : algebraMap ((w.comap (algebraMap K M)).Completion) w.Completion
      (algebraMap K ((w.comap (algebraMap K M)).Completion) (ζ ^ j)⁻¹)
      = ((algebraMap K w.Completion ζ) ^ j)⁻¹ := by
    rw [← IsScalarTower.algebraMap_apply K ((w.comap (algebraMap K M)).Completion) w.Completion,
      map_inv₀, map_pow]
  have hj' : algebraMap ((w.comap (algebraMap K M)).Completion) w.Completion δ
      = (algebraMap K w.Completion ζ) ^ j * algebraMap M w.Completion b :=
    ((eq_div_iff hbne).mp hj).symm
  rw [map_mul, hmap, hj', mul_right_comm, mul_inv_cancel₀ (pow_ne_zero j hz0), one_mul]

end InfinitePlaceRange

end InverseGalois.CFT
