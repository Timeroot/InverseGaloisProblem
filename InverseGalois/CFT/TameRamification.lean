import Mathlib
import InverseGalois.CFT.Decomposition
import InverseGalois.CFT.InertiaAbelian
import InverseGalois.CFT.InertiaRestrict
import InverseGalois.CFT.Cyclotomic.InertiaOrder
import InverseGalois.CFT.ScalarSemidirect

/-!
# Tame ramification in a number field

A number field is tamely ramified when the residue characteristic never divides the ramification
index, so that the inertia subgroups have order prime to the residue characteristic.  Since the
order of the inertia subgroup at a prime of a Galois number field is exactly the ramification
index, tameness can equally be read off the Galois group, and in that form it visibly passes to a
compositum: the inertia subgroup of a compositum embeds into the product of the two inertia
subgroups, so a prime dividing its order divides one of theirs.

The other source of tame extensions recorded here is the cyclotomic one: the ramification index of
`p` in `ℚ(ζₙ)` is `φ (p ^ k)` for `p ^ k` the exact power of `p` dividing `n`, and when `n` is
squarefree this is `1` or `p - 1`, neither of which `p` divides.

## Main results

* `InverseGalois.CFT.IsTamelyRamified`: the tameness condition.
* `InverseGalois.CFT.isTamelyRamified_of_ringEquiv`: tameness is an isomorphism invariant.
* `InverseGalois.CFT.not_dvd_card_inertia_of_tame` and
  `InverseGalois.CFT.isTamelyRamified_of_not_dvd_card_inertia`: for a Galois number field,
  tameness says exactly that no residue characteristic divides the order of its inertia subgroup.
* `InverseGalois.CFT.isTamelyRamified_sup`: **a compositum of two tamely ramified normal
  subfields is tamely ramified.**
* `InverseGalois.CFT.isTamelyRamified_cyclotomic`: **`ℚ(ζₙ)` is tamely ramified when `n` is
  squarefree.**
-/

open NumberField

namespace InverseGalois.CFT

/-- A number field is **tamely ramified** when no rational prime divides the ramification index of
any prime of its ring of integers lying above it. -/
def IsTamelyRamified (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ p : ℕ, p.Prime → ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
    ¬ p ∣ Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P

section Transport

variable {E F : Type*} [Field E] [NumberField E] [Field F] [NumberField F]

/-- A ring isomorphism of number fields, restricted to the rings of integers and regarded as an
isomorphism of `ℤ`-algebras. -/
noncomputable def mapAlgEquivInt (e : E ≃+* F) : 𝓞 E ≃ₐ[ℤ] 𝓞 F :=
  { RingOfIntegers.mapRingEquiv e with
    commutes' := fun _ => by simp }

/-- **Tameness is an isomorphism invariant.**  Contracting a prime along an isomorphism of rings
of integers preserves both the rational prime below it and the ramification index. -/
theorem isTamelyRamified_of_ringEquiv (e : E ≃+* F) (h : IsTamelyRamified E) :
    IsTamelyRamified F := by
  intro p hp P hPp hPo
  haveI := hPp
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
    exact hPo.over
  have hidx := Ideal.ramificationIdx_comap_eq (Ideal.span {(p : ℤ)}) f P
  rw [← hidx]
  exact h p hp Q hQp hQo

end Transport

section Inertia

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **Tameness bounds the inertia subgroup.**  Its order is the ramification index, so the residue
characteristic does not divide it. -/
theorem not_dvd_card_inertia_of_tame (h : IsTamelyRamified K) (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 K)) [P.IsPrime] [hPo : P.LiesOver (Ideal.span {(p : ℤ)})] :
    ¬ p ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP := ne_bot_of_liesOver p P
  rw [card_inertia_eq_ramificationIdx P hP, ← hPo.over]
  exact h p hp P inferInstance inferInstance

/-- **Inertia of order prime to the residue characteristic means tameness.**  The converse of
`InverseGalois.CFT.not_dvd_card_inertia_of_tame`. -/
theorem isTamelyRamified_of_not_dvd_card_inertia
    (h : ∀ p : ℕ, p.Prime → ∀ P : Ideal (𝓞 K), ∀ _ : P.IsPrime,
      ∀ _ : P.LiesOver (Ideal.span {(p : ℤ)}), ¬ p ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P)) :
    IsTamelyRamified K := by
  intro p hp P hPp hPo
  haveI := hPp
  haveI := hPo
  haveI : Fact p.Prime := ⟨hp⟩
  have hP := ne_bot_of_liesOver p P
  have hnd := h p hp P hPp hPo
  rwa [card_inertia_eq_ramificationIdx P hP, ← hPo.over] at hnd

end Inertia

section Compositum

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N]

/-- **A compositum of tamely ramified fields is tamely ramified.**  A Galois element in the inertia
subgroup of the compositum restricts to the inertia subgroups of the two factors, and it is trivial
as soon as both restrictions are, so the order of the inertia subgroup of the compositum divides
the product of the two orders. -/
theorem isTamelyRamified_sup (A B : IntermediateField ℚ N) [Normal ℚ ↥A] [Normal ℚ ↥B]
    (hAB : A ⊔ B = ⊤) (hA : IsTamelyRamified ↥A) (hB : IsTamelyRamified ↥B) :
    IsTamelyRamified N := by
  haveI : NumberField ↥A := ⟨⟩
  haveI : NumberField ↥B := ⟨⟩
  haveI : IsGalois ℚ ↥A := ⟨⟩
  haveI : IsGalois ℚ ↥B := ⟨⟩
  refine isTamelyRamified_of_not_dvd_card_inertia fun p hp P hPp hPo => ?_
  haveI := hPp
  haveI := hPo
  haveI : (P.under (𝓞 ↥A)).LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    rw [Ideal.under_under]
    exact hPo.over
  haveI : (P.under (𝓞 ↥B)).LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    rw [Ideal.under_under]
    exact hPo.over
  exact not_dvd_card_inertia A B hAB P hp
    (not_dvd_card_inertia_of_tame hA p hp _) (not_dvd_card_inertia_of_tame hB p hp _)

end Compositum

section Cyclotomic

/-- **A squarefree cyclotomic field is tamely ramified.**  The ramification index of `p` is `1` or
`p - 1`, and `p` divides neither. -/
theorem isTamelyRamified_cyclotomic (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (hn : Squarefree n) : IsTamelyRamified K := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  refine isTamelyRamified_of_not_dvd_card_inertia fun p hp P hPp hPo => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hPp
  haveI := hPo
  rw [card_inertia_eq_totient n K p P]
  have hle : n.factorization p ≤ 1 := hn.natFactorization_le_one p
  interval_cases h : n.factorization p
  · simp [hp.one_lt.ne']
  · rw [pow_one, Nat.totient_prime hp]
    exact not_dvd_sub_one hp

end Cyclotomic

end InverseGalois.CFT
