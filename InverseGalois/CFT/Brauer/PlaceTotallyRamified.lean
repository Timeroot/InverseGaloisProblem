/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceCyclic
import InverseGalois.CFT.Brauer.PlaceExponent
import InverseGalois.CFT.Local.RatResidueDegree
import InverseGalois.CFT.Units.FrobeniusPlace
import InverseGalois.CFT.Units.RatFundamentalClass

/-!
# The decomposition group at a totally ramified place

At a prime whose inertia subgroup is the whole Galois group there is nothing left for the
decomposition group to be: inertia is contained in the decomposition group, so the latter is the
whole group as well, its index is one, and the completion of the extension at that prime has the
same degree over the completion of the base as the extension itself.  In particular a generator of
the local Galois group restricts to a generator of the global one, with no correcting power.

This is the shape in which the local data of a cyclic algebra is read at the single ramified place
of an auxiliary cyclic field: the coefficient of the localised algebra is the image of the global
coefficient and the local generator is the image of the global generator, so the invariant there is
computed by a symbol over the completion with no bookkeeping in between.

The last section identifies the place of the rationals below a place of a number field containing
a rational prime: it is the place attached to that prime, and conversely a place lying above the
place attached to a prime lies over the ideal that prime generates.

## Main results

* `InverseGalois.CFT.stabilizer_eq_top_of_inertia_eq_top`: **the decomposition group of a totally
  ramified prime is the whole Galois group.**
* `InverseGalois.CFT.index_stabilizer_eq_one_of_inertia_eq_top`: the decomposition group of a
  totally ramified place has index one.
* `InverseGalois.CFT.finrank_adicCompletion_eq_of_inertia_eq_top`: **the local degree at a totally
  ramified place is the degree of the extension.**
* `InverseGalois.CFT.exists_restrictScalars_eq_of_inertia_eq_top`: **at a totally ramified place the
  Galois group of the completions has a generator restricting to a prescribed generator of the
  Galois group of the extension.**
* `InverseGalois.CFT.primeUnder_eq_ratPlace` and
  `InverseGalois.CFT.liesOver_span_of_primeUnder_eq_ratPlace`: the place of the rationals below a
  place above a rational prime is the place attached to that prime.

## Tags

decomposition group, inertia subgroup, totally ramified, local degree, cyclic algebra, class field
theory
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField

open scoped Pointwise

/-! ### The decomposition group of a totally ramified prime -/

section Stabilizer

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- **The decomposition group of a totally ramified prime is the whole Galois group.**  The inertia
subgroup is contained in the decomposition group, and it is already everything. -/
theorem stabilizer_eq_top_of_inertia_eq_top (P : Ideal (𝓞 K))
    (h : Ideal.inertia Gal(K/k) P = ⊤) : stabilizer Gal(K/k) P = ⊤ := by
  have hle := Ideal.inertia_le_stabilizer (M := Gal(K/k)) P
  rw [h] at hle
  exact eq_top_iff.mpr hle

omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- **The decomposition group of a totally ramified place is the whole Galois group.** -/
theorem stabilizer_place_eq_top_of_inertia_eq_top (w : HeightOneSpectrum (𝓞 K))
    (h : Ideal.inertia Gal(K/k) w.asIdeal = ⊤) : stabilizer Gal(K/k) w = ⊤ := by
  rw [stabilizer_eq_stabilizer_asIdeal]
  exact stabilizer_eq_top_of_inertia_eq_top w.asIdeal h

omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- **The decomposition group of a totally ramified place has index one.** -/
theorem index_stabilizer_eq_one_of_inertia_eq_top (w : HeightOneSpectrum (𝓞 K))
    (h : Ideal.inertia Gal(K/k) w.asIdeal = ⊤) : (stabilizer Gal(K/k) w).index = 1 := by
  rw [stabilizer_place_eq_top_of_inertia_eq_top w h, Subgroup.index_top]

variable (k) in
/-- **The local degree at a totally ramified place is the degree of the extension.**  The index of
the decomposition group times the local degree is the degree, and that index is one. -/
theorem finrank_adicCompletion_eq_of_inertia_eq_top (w : HeightOneSpectrum (𝓞 K))
    (h : Ideal.inertia Gal(K/k) w.asIdeal = ⊤) :
    finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
      = Nat.card Gal(K/k) := by
  have hkey := index_mul_finrank_adicCompletion k w
  rwa [index_stabilizer_eq_one_of_inertia_eq_top w h, one_mul] at hkey

variable (k) in
/-- **At a totally ramified place the Galois group of the completions has a generator restricting
to a prescribed generator of the Galois group of the extension.**  In general the restriction is
the power of the generator by the index of the decomposition group, and that index is one. -/
theorem exists_restrictScalars_eq_of_inertia_eq_top (w : HeightOneSpectrum (𝓞 K))
    (h : Ideal.inertia Gal(K/k) w.asIdeal = ⊤) {σ₀ : Gal(K/k)}
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) :
    ∃ σ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K,
      (∀ x : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K,
          x ∈ Subgroup.zpowers σ) ∧
        (localDecompositionEquiv k w σ).restrictScalars k = σ₀ := by
  obtain ⟨σ, hσ, hres⟩ := exists_forall_mem_zpowers_restrictScalars_eq k w hσ₀
  exact ⟨σ, hσ, by rwa [index_stabilizer_eq_one_of_inertia_eq_top w h, pow_one] at hres⟩

end Stabilizer

/-! ### The place of the rationals below a place above a rational prime -/

section Rat

variable {K : Type} [Field K] [NumberField K] {q : ℕ}

omit [NumberField K] in
/-- A rational prime lies in every prime of the ring of integers above it. -/
theorem natCast_mem_of_liesOver_span (P : Ideal (𝓞 K))
    [P.LiesOver (Ideal.span {(q : ℤ)})] : ((q : ℕ) : 𝓞 K) ∈ P := by
  have hz : (q : ℤ) ∈ Ideal.span {(q : ℤ)} := Ideal.subset_span rfl
  rw [Ideal.LiesOver.over (p := Ideal.span {(q : ℤ)}) (P := P)] at hz
  simpa using hz

/-- **The place of the rationals below a place above a rational prime is the place attached to that
prime.**  Both contain the prime, and a finite place of the rationals is determined by the rational
prime it contains. -/
theorem primeUnder_eq_ratPlace (hq : q.Prime) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver (Ideal.span {(q : ℤ)})] :
    primeUnder (𝓞 ℚ) w = ratPlace q hq := by
  refine heightOneSpectrum_rat_eq_of_natCast_mem hq ?_ (natCast_mem_ratPlace q hq)
  rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
  exact natCast_mem_of_liesOver_span (q := q) w.asIdeal

/-- **A place lying above the place attached to a rational prime lies over the ideal that prime
generates.**  The prime belongs to the place below, hence to the place itself. -/
theorem liesOver_span_of_primeUnder_eq_ratPlace (hq : q.Prime) (w : HeightOneSpectrum (𝓞 K))
    (hw : primeUnder (𝓞 ℚ) w = ratPlace q hq) : w.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) := by
  refine liesOver_span_of_natCast_mem hq w ?_
  have hmem : ((q : ℕ) : 𝓞 ℚ) ∈ (primeUnder (𝓞 ℚ) w).asIdeal := by
    rw [hw]
    exact natCast_mem_ratPlace q hq
  rwa [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem

end Rat

end InverseGalois.CFT
