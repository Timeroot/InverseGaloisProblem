import Mathlib
import InverseGalois.CFT.SplitCompositum
import InverseGalois.CFT.TameRamification
import InverseGalois.CFT.UnramifiedCompositum

/-!
# Serre's condition `(S_N)` for the Scholz–Reichardt construction

Scholz and Reichardt build `ℓ`-power extensions of `ℚ` by induction on the order of the group, and
the induction hypothesis is a normalisation of the ramification: every ramified rational prime is
congruent to one modulo `ℓ ^ N`, and its residue degree is one, so that the decomposition group at
a ramified prime coincides with the inertia group there.  Following Serre, we call this condition
`(S_N)`.

The level half of the condition already behaves well under compositum.  The residue-degree half
does not: for `p = 3`, the fields `ℚ(√3)` and `ℚ(√(-3))` both have residue degree one at `3`,
while their compositum contains `ℚ(i)`, in which `3` is inert.  What is true, and what the
Scholz–Reichardt induction actually uses, is that the residue degree stays equal to one in a
compositum whose second factor the prime splits completely in; that is the content of
`InverseGalois.CFT.inertiaDeg_eq_one_of_sup`.

## Main definitions

* `InverseGalois.CFT.IsSplitInertia`: every ramified prime has residue degree one.
* `InverseGalois.CFT.IsScholz`: Serre's condition `(S_N)`.

## Main results

* `InverseGalois.CFT.IsScholz.mono`: the condition weakens as the exponent decreases.
* `InverseGalois.CFT.IsScholz.of_ringEquiv`: the condition is an isomorphism invariant.
* `InverseGalois.CFT.isSplitInertia_of_tower`: residue degree one is inherited by subfields.
* `InverseGalois.CFT.IsScholz.of_tower`: **the condition `(S_N)` is inherited by subfields.**
* `InverseGalois.CFT.isSplitInertia_of_finrank_prime`: a Galois extension of `ℚ` of prime degree
  has residue degree one at every ramified prime.
* `InverseGalois.CFT.isSplitInertia_of_sup`: **residue degree one passes to a compositum** in
  which each factor's ramified primes split completely in the other factor.
* `InverseGalois.CFT.IsScholz.of_sup_eq_top`: the same for the full condition `(S_N)`.
-/

open NumberField InverseGalois.NumberTheory

set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

/-- A number field has **split inertia** when every ramified rational prime has residue degree one,
that is, when the decomposition group at a ramified prime is its inertia group. -/
def IsSplitInertia (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ p ∈ ramifiedSet K, ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
    (Ideal.span {(p : ℤ)}).inertiaDeg P = 1

/-- **Serre's condition `(S_N)`.**  An extension of `ℚ` satisfies it, for the prime `ℓ`, when every
ramified rational prime is congruent to one modulo `ℓ ^ N` and has residue degree one. -/
def IsScholz (ℓ N : ℕ) (K : Type*) [Field K] [NumberField K] : Prop :=
  IsLevel ℓ N K ∧ IsSplitInertia K

variable {E : Type*} [Field E] [NumberField E]

/-- The condition `(S_N)` contains the level condition. -/
theorem IsScholz.isLevel {ℓ N : ℕ} (h : IsScholz ℓ N E) : IsLevel ℓ N E := h.1

/-- The condition `(S_N)` contains the residue-degree condition. -/
theorem IsScholz.isSplitInertia {ℓ N : ℕ} (h : IsScholz ℓ N E) : IsSplitInertia E := h.2

/-- The condition `(S_N)` weakens as the exponent decreases. -/
theorem IsScholz.mono {ℓ N M : ℕ} (h : IsScholz ℓ N E) (hMN : M ≤ N) : IsScholz ℓ M E :=
  ⟨h.1.mono hMN, h.2⟩

/-- Split inertia is an isomorphism invariant. -/
theorem isSplitInertia_of_ringEquiv {F : Type*} [Field F] [NumberField F] (e : E ≃+* F)
    (h : IsSplitInertia E) : IsSplitInertia F := by
  intro p hp P hPprime hPover
  haveI := hPprime
  haveI := isMaximal_span_prime hp.1
  have hp' : p ∈ ramifiedSet E := by rwa [ramifiedSet_eq_of_ringEquiv e]
  set f := mapAlgEquivInt e with hf
  set Q : Ideal (𝓞 E) := Ideal.comap (f : 𝓞 E →+* 𝓞 F) P with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQo : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    have hunder : Q.under ℤ = P.under ℤ := by
      rw [Ideal.under, Ideal.under, hQ, Ideal.comap_comap]
      congr 1
      exact Subsingleton.elim _ _
    rw [hunder]
    exact hPover.over
  have hdeg := Ideal.inertiaDeg_comap_eq (Ideal.span {(p : ℤ)}) f P
  rw [← hdeg]
  exact h p hp' Q hQp hQo

/-- The level condition is an isomorphism invariant. -/
theorem IsLevel.of_ringEquiv {F : Type*} [Field F] [NumberField F] {ℓ N : ℕ} (e : E ≃+* F)
    (h : IsLevel ℓ N E) : IsLevel ℓ N F :=
  fun q hq => h q (by rwa [ramifiedSet_eq_of_ringEquiv e])

/-- Serre's condition `(S_N)` is an isomorphism invariant. -/
theorem IsScholz.of_ringEquiv {F : Type*} [Field F] [NumberField F] {ℓ N : ℕ} (e : E ≃+* F)
    (h : IsScholz ℓ N E) : IsScholz ℓ N F :=
  ⟨h.1.of_ringEquiv e, isSplitInertia_of_ringEquiv e h.2⟩

section Tower

variable {M : Type*} [Field M] [NumberField M] [Algebra E M]

/-- **Split inertia is inherited by subfields.**  A prime ramified below is ramified above, and the
residue degree above it factors through the intermediate field, so a residue degree equal to one at
the top forces one at every stage. -/
theorem isSplitInertia_of_tower (h : IsSplitInertia M) : IsSplitInertia E := by
  intro p hp P hPprime hPover
  haveI := hPprime
  haveI := hPover
  have hprime : p.Prime := hp.1
  haveI := isMaximal_span_prime hprime
  have hspan : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hprime.ne_zero
  have hP0 : P ≠ ⊥ := by
    intro hb
    refine hspan ?_
    rw [hPover.over, hb, Ideal.under,
      Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP0 hPprime
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) P
  haveI := hQmax
  haveI := hQover
  haveI : Q.IsPrime := hQmax.isPrime
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q P (Ideal.span {(p : ℤ)})
  have hone := h p (ramifiedSet_subset E M hp) Q inferInstance inferInstance
  rw [Ideal.inertiaDeg_algebra_tower (R := ℤ) (S := 𝓞 E) (T := 𝓞 M)
    (Ideal.span {(p : ℤ)}) P Q] at hone
  exact Nat.eq_one_of_mul_eq_one_right hone

/-- **Serre's condition `(S_N)` is inherited by subfields.**  Both halves of the condition only
constrain the ramified primes, and a subfield has fewer of them. -/
theorem IsScholz.of_tower {ℓ N : ℕ} (h : IsScholz ℓ N M) : IsScholz ℓ N E :=
  ⟨h.1.of_tower, isSplitInertia_of_tower h.2⟩

end Tower

/-- **A Galois extension of `ℚ` of prime degree has split inertia.**  A ramified prime has
ramification index different from one at some prime above it, hence at every prime above it, and
the product of the ramification index with the residue degree is the order of a subgroup of a
group of prime order. -/
theorem isSplitInertia_of_finrank_prime [IsGalois ℚ E] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdeg : Module.finrank ℚ E = ℓ) : IsSplitInertia E := by
  rintro p ⟨hp, Q, ⟨hQprime, hQover⟩, hQe⟩ P hPprime hPover
  haveI := hQprime
  haveI := hQover
  haveI := hPprime
  haveI := hPover
  -- the ramification index does not depend on the chosen prime above `p`
  have hPe : Ideal.ramificationIdx (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) P ≠ 1 := by
    rw [Ideal.ramificationIdx_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q Gal(E/ℚ)]
    exact hQe
  -- the product of the two invariants is the order of a decomposition subgroup
  have hdvd : Ideal.ramificationIdx (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) P *
      (Ideal.span {(p : ℤ)}).inertiaDeg P ∣ ℓ := by
    rw [← card_stabilizer_eq_mul E hp P, ← hdeg, ← IsGalois.card_aut_eq_finrank ℚ E]
    exact Subgroup.card_subgroup_dvd_card _
  have hprod := (Nat.Prime.eq_one_or_self_of_dvd hℓ _ hdvd).resolve_left fun h =>
    hPe (Nat.eq_one_of_mul_eq_one_right h)
  have he := (Nat.Prime.eq_one_or_self_of_dvd hℓ _ ⟨_, hprod.symm⟩).resolve_left hPe
  rw [he] at hprod
  exact Nat.eq_of_mul_eq_mul_left hℓ.pos (hprod.trans (mul_one ℓ).symm)

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N]

/-- **Split inertia passes to a compositum** in which each factor's ramified primes split
completely in the other factor. -/
theorem isSplitInertia_of_sup (A B : IntermediateField ℚ N) [Normal ℚ ↥A] [Normal ℚ ↥B]
    (hAB : A ⊔ B = ⊤) (hA : IsSplitInertia ↥A) (hB : IsSplitInertia ↥B)
    (hAsplit : ∀ p ∈ ramifiedSet ↥A, SplitsCompletely ↥B p)
    (hBsplit : ∀ p ∈ ramifiedSet ↥B, SplitsCompletely ↥A p) :
    IsSplitInertia N := by
  haveI : NumberField ↥A := ⟨⟩
  haveI : NumberField ↥B := ⟨⟩
  intro p hp P hPprime hPover
  haveI := hPprime
  haveI := hPover
  have hprime : p.Prime := hp.1
  haveI hAo : (P.under (𝓞 ↥A)).LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨by rw [Ideal.under_under]; exact hPover.over⟩
  haveI hBo : (P.under (𝓞 ↥B)).LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨by rw [Ideal.under_under]; exact hPover.over⟩
  -- the prime is ramified in one of the two factors
  have hmem : p ∈ ramifiedSet ↥A ∪ ramifiedSet ↥B := by
    rw [← ramifiedSet_sup A B, hAB]
    rwa [ramifiedSet_eq_of_ringEquiv (IntermediateField.topEquiv (F := ℚ) (E := N)).toRingEquiv]
  rcases hmem with h | h
  · exact inertiaDeg_eq_one_of_sup A B hAB hprime P (hAsplit p h)
      (hA p h _ inferInstance hAo)
  · exact inertiaDeg_eq_one_of_sup B A (sup_comm A B ▸ hAB) hprime P (hBsplit p h)
      (hB p h _ inferInstance hBo)

/-- **Serre's condition `(S_N)` passes to a compositum** in which each factor's ramified primes
split completely in the other factor. -/
theorem IsScholz.of_sup_eq_top {ℓ M : ℕ} (A B : IntermediateField ℚ N) [Normal ℚ ↥A] [Normal ℚ ↥B]
    (hAB : A ⊔ B = ⊤) (hA : IsScholz ℓ M ↥A) (hB : IsScholz ℓ M ↥B)
    (hAsplit : ∀ p ∈ ramifiedSet ↥A, SplitsCompletely ↥B p)
    (hBsplit : ∀ p ∈ ramifiedSet ↥B, SplitsCompletely ↥A p) :
    IsScholz ℓ M N := by
  haveI : NumberField ↥A := ⟨⟩
  haveI : NumberField ↥B := ⟨⟩
  refine ⟨fun q hq => ?_, isSplitInertia_of_sup A B hAB hA.2 hB.2 hAsplit hBsplit⟩
  have hlevel := IsLevel.sup hA.1 hB.1
  rw [hAB] at hlevel
  refine hlevel q ?_
  rwa [ramifiedSet_eq_of_ringEquiv (IntermediateField.topEquiv (F := ℚ) (E := N)).toRingEquiv]

end InverseGalois.CFT
