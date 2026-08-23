import Mathlib

/-!
# Inertia under restriction to a subfield

Let `N` be a number field, let `A` be an intermediate field of `N / ℚ` which is normal over `ℚ`,
and let `P` be a prime of `𝓞 N`.  Membership of `σ : Gal(N/ℚ)` in the inertia group of `P` is the
condition `σ • x - x ∈ P` for every `x : 𝓞 N`, a condition that does not refer to the base field.
Consequently, restricting `σ` to `A` sends the inertia group of `P` into the inertia group of the
prime of `𝓞 A` lying under `P`: for `x : 𝓞 A` the element `σ • x - x` lands in `P ∩ 𝓞 A`.

This has an immediate consequence for a pair of normal subextensions `A` and `B` whose compositum
is all of `N`.  An automorphism of `N` restricting trivially to both `A` and `B` is the identity,
so an element of prime order `p` of the inertia group of `P` restricts to an element of order `p`
of the inertia group of `P ∩ 𝓞 A` or of the inertia group of `P ∩ 𝓞 B`.  Hence a prime `p`
dividing the order of the inertia group upstairs already divides the order of one of the two
inertia groups downstairs.

## Main results

* `InverseGalois.CFT.algebraMap_smul_restrictNormal`: restricting an automorphism to a normal
  subextension is compatible with the inclusion of rings of integers.
* `InverseGalois.CFT.restrictNormal_mem_inertia`: restriction to a normal subextension maps the
  inertia group of `P` into the inertia group of the prime below `P`.
* `InverseGalois.CFT.eq_one_of_restrictNormal_eq_one`: an automorphism restricting trivially to two
  subextensions generating `N` is the identity.
* `InverseGalois.CFT.dvd_card_inertia_under_or`: a prime dividing the order of the inertia group of
  `P` divides the order of one of the two inertia groups below it.
* `InverseGalois.CFT.not_dvd_card_inertia`: the contrapositive form of the previous statement.
-/

open NumberField

namespace InverseGalois.CFT

variable {N : Type*} [Field N] [NumberField N]

/-- Restricting an automorphism of `N` to a normal subextension `A` is compatible with the
inclusion of `𝓞 A` into `𝓞 N`. -/
theorem algebraMap_smul_restrictNormal (A : IntermediateField ℚ N) [Normal ℚ ↥A] (σ : Gal(N/ℚ))
    (x : 𝓞 ↥A) :
    algebraMap (𝓞 ↥A) (𝓞 N) (σ.restrictNormal ↥A • x) = σ • algebraMap (𝓞 ↥A) (𝓞 N) x := by
  apply RingOfIntegers.ext
  show algebraMap (↥A) N ((σ.restrictNormal ↥A • x : 𝓞 ↥A) : ↥A) = σ (algebraMap (↥A) N (x : ↥A))
  rw [← AlgEquiv.restrictNormal_commutes σ ↥A (x : ↥A)]
  rfl

/-- **Restriction sends inertia into inertia.**  If `σ` lies in the inertia group of a prime `P`
of `𝓞 N`, then its restriction to a normal subextension `A` lies in the inertia group of the prime
of `𝓞 A` lying under `P`. -/
theorem restrictNormal_mem_inertia (A : IntermediateField ℚ N) [Normal ℚ ↥A] (P : Ideal (𝓞 N))
    {σ : Gal(N/ℚ)} (hσ : σ ∈ Ideal.inertia Gal(N/ℚ) P) :
    σ.restrictNormal ↥A ∈ Ideal.inertia Gal(↥A/ℚ) (P.under (𝓞 ↥A)) := by
  intro x
  show algebraMap (𝓞 ↥A) (𝓞 N) _ ∈ P
  rw [map_sub, algebraMap_smul_restrictNormal]
  exact hσ _

/-- An automorphism of `N` whose restriction to a normal subextension `A` is trivial fixes `A`
pointwise. -/
theorem mem_fixingSubgroup_of_restrictNormal_eq_one {A : IntermediateField ℚ N} [Normal ℚ ↥A]
    {σ : Gal(N/ℚ)} (h : σ.restrictNormal ↥A = 1) : σ ∈ A.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hcom := AlgEquiv.restrictNormal_commutes σ ↥A ⟨x, hx⟩
  rw [h] at hcom
  simpa using hcom.symm

/-- An automorphism of `N` restricting trivially to two normal subextensions whose compositum is
all of `N` is the identity. -/
theorem eq_one_of_restrictNormal_eq_one {A B : IntermediateField ℚ N} [Normal ℚ ↥A] [Normal ℚ ↥B]
    (hAB : A ⊔ B = ⊤) {σ : Gal(N/ℚ)} (hA : σ.restrictNormal ↥A = 1)
    (hB : σ.restrictNormal ↥B = 1) : σ = 1 := by
  have hmem : σ ∈ (⊤ : IntermediateField ℚ N).fixingSubgroup := by
    rw [← hAB, IntermediateField.fixingSubgroup_sup]
    exact ⟨mem_fixingSubgroup_of_restrictNormal_eq_one hA,
      mem_fixingSubgroup_of_restrictNormal_eq_one hB⟩
  rw [IntermediateField.fixingSubgroup_top] at hmem
  simpa using hmem

/-- **No new `p`-torsion in the inertia of a compositum.**  If `A` and `B` are normal
subextensions of `N / ℚ` whose compositum is all of `N`, then a prime dividing the order of the
inertia group of a prime `P` of `𝓞 N` divides the order of the inertia group of `P ∩ 𝓞 A` or of
the inertia group of `P ∩ 𝓞 B`. -/
theorem dvd_card_inertia_under_or (A B : IntermediateField ℚ N) [Normal ℚ ↥A] [Normal ℚ ↥B]
    (hAB : A ⊔ B = ⊤) (P : Ideal (𝓞 N)) {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card (Ideal.inertia Gal(N/ℚ) P)) :
    p ∣ Nat.card (Ideal.inertia Gal(↥A/ℚ) (P.under (𝓞 ↥A))) ∨
      p ∣ Nat.card (Ideal.inertia Gal(↥B/ℚ) (P.under (𝓞 ↥B))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' (G := Ideal.inertia Gal(N/ℚ) P) p h
  have hord : orderOf (τ : Gal(N/ℚ)) = p := (Subgroup.orderOf_coe τ).trans hτ
  have hne : ¬ ((τ : Gal(N/ℚ)).restrictNormal ↥A = 1 ∧ (τ : Gal(N/ℚ)).restrictNormal ↥B = 1) := by
    rintro ⟨h1, h2⟩
    rw [eq_one_of_restrictNormal_eq_one hAB h1 h2, orderOf_one] at hord
    exact hp.ne_one hord.symm
  -- the order of a restriction divides `p`, hence is `1` or `p`
  have key : ∀ (E : IntermediateField ℚ N) (_ : Normal ℚ ↥E),
      (τ : Gal(N/ℚ)).restrictNormal ↥E ≠ 1 →
        p ∣ Nat.card (Ideal.inertia Gal(↥E/ℚ) (P.under (𝓞 ↥E))) := by
    intro E _ hE
    have hdvd : orderOf ((τ : Gal(N/ℚ)).restrictNormal ↥E) ∣ p :=
      hord ▸ orderOf_map_dvd (AlgEquiv.restrictNormalHom ↥E) (τ : Gal(N/ℚ))
    have heq : orderOf ((τ : Gal(N/ℚ)).restrictNormal ↥E) = p :=
      (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left fun hone => hE (orderOf_eq_one_iff.mp hone)
    exact heq ▸ Subgroup.orderOf_dvd_natCard _ (restrictNormal_mem_inertia E P τ.2)
  by_cases hA : (τ : Gal(N/ℚ)).restrictNormal ↥A = 1
  · exact Or.inr (key B ‹_› fun hB => hne ⟨hA, hB⟩)
  · exact Or.inl (key A ‹_› hA)

/-- **No new `p`-torsion in the inertia of a compositum**, in contrapositive form.  If a prime `p`
divides neither of the orders of the inertia groups of `P ∩ 𝓞 A` and `P ∩ 𝓞 B`, it does not
divide the order of the inertia group of `P`. -/
theorem not_dvd_card_inertia (A B : IntermediateField ℚ N) [Normal ℚ ↥A] [Normal ℚ ↥B]
    (hAB : A ⊔ B = ⊤) (P : Ideal (𝓞 N)) {p : ℕ} (hp : p.Prime)
    (hA : ¬ p ∣ Nat.card (Ideal.inertia Gal(↥A/ℚ) (P.under (𝓞 ↥A))))
    (hB : ¬ p ∣ Nat.card (Ideal.inertia Gal(↥B/ℚ) (P.under (𝓞 ↥B)))) :
    ¬ p ∣ Nat.card (Ideal.inertia Gal(N/ℚ) P) := fun h =>
  (dvd_card_inertia_under_or A B hAB P hp h).elim hA hB

end InverseGalois.CFT
