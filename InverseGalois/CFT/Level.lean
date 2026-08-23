import Mathlib
import InverseGalois.NumberTheory.SplitDensity

/-!
# Ramification in a tower of number fields, and the level of an extension

A rational prime that ramifies in a number field ramifies in every number field above it, so the
set of ramified primes only grows in a tower.  Scholz and Reichardt's construction of `ℓ`-power
extensions of `ℚ` is organised around the *level* of an extension: the extension has level `n` for
the prime `ℓ` when every ramified prime is congruent to one modulo `ℓ ^ n`.  The level is what the
induction on the order of the group carries along, and the two facts recorded here — that the level
condition weakens as `n` decreases, and that it is inherited by subfields — are what make the
induction go.

## Main results

* `InverseGalois.CFT.ramifiedSet_subset`: a prime ramified in a subfield is ramified above it.
* `InverseGalois.CFT.IsLevel`: the level condition.
* `InverseGalois.CFT.IsLevel.mono`: a field of level `n` has level `m` for every `m ≤ n`.
* `InverseGalois.CFT.IsLevel.of_tower`: the level condition passes to subfields.
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-- The extension of a nonzero ideal along an injective map is nonzero. -/
private theorem map_ne_bot_of_injective {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : Function.Injective (algebraMap R S)) {I : Ideal R} (hI : I ≠ ⊥) :
    I.map (algebraMap R S) ≠ ⊥ := by
  obtain ⟨x, hxI, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  intro hmap
  refine hx (h ?_)
  have hmem : algebraMap R S x ∈ I.map (algebraMap R S) := Ideal.mem_map_of_mem _ hxI
  rw [hmap, Ideal.mem_bot] at hmem
  rw [hmem, map_zero]

variable (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]

/-- **Ramification propagates upward.**  A rational prime that ramifies in a number field ramifies
in every number field containing it. -/
theorem ramifiedSet_subset : ramifiedSet E ⊆ ramifiedSet M := by
  rintro p ⟨hp, P, ⟨hPprime, hPover⟩, hPe⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hPprime
  haveI := hPover
  -- the prime below `P` is nonzero, hence so is `P`
  have hspan : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hP0 : P ≠ ⊥ := by
    intro h
    refine hspan ?_
    rw [hPover.over, h, Ideal.under,
      Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP0 hPprime
  -- choose a prime of `𝓞 M` above `P`
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) P
  haveI := hQmax
  haveI := hQover
  haveI : Q.IsPrime := hQmax.isPrime
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q P (Ideal.span {(p : ℤ)})
  refine ⟨hp, Q, ⟨inferInstance, inferInstance⟩, ?_⟩
  -- the ramification index above `p` factors through `P`
  have hle : P.map (algebraMap (𝓞 E) (𝓞 M)) ≤ Q :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq hQover.over)
  have hg0 : P.map (algebraMap (𝓞 E) (𝓞 M)) ≠ ⊥ :=
    map_ne_bot_of_injective (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 M)) hP0
  have hfg : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 M)) ≠ ⊥ :=
    map_ne_bot_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 M)) hspan
  have htower := Ideal.ramificationIdx_algebra_tower (R := ℤ) (S := 𝓞 E) (T := 𝓞 M)
    (p := Ideal.span {(p : ℤ)}) (P := P) (Q := Q) hg0 hfg hle
  rw [htower]
  intro hone
  exact hPe (Nat.eq_one_of_mul_eq_one_right hone)

variable {E M}

/-- An extension of `ℚ` **has level `n` at `ℓ`** when every rational prime ramified in it is
congruent to one modulo `ℓ ^ n`. -/
def IsLevel (ℓ n : ℕ) (E : Type*) [Field E] [NumberField E] : Prop :=
  ∀ q ∈ ramifiedSet E, q ≡ 1 [MOD ℓ ^ n]

/-- The level condition weakens as the exponent decreases. -/
theorem IsLevel.mono {ℓ n m : ℕ} (h : IsLevel ℓ n E) (hmn : m ≤ n) : IsLevel ℓ m E := fun q hq =>
  (h q hq).of_dvd (pow_dvd_pow ℓ hmn)

/-- The level condition is inherited by subfields. -/
theorem IsLevel.of_tower {ℓ n : ℕ} (h : IsLevel ℓ n M) : IsLevel ℓ n E := fun q hq =>
  h q (ramifiedSet_subset E M hq)

end InverseGalois.CFT
