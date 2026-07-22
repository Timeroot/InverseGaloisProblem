/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Polynomial.GaloisGroupTools
import InverseGalois.Polynomial.QuinticDiscriminant
import InverseGalois.Resolvent.QuinticGroupTheory
import InverseGalois.Resolvent.PentagonalSum

/-!
# Abstract Galois-Theoretic Tools for Polynomials

This file develops general infrastructure for computing Galois groups of polynomials,
with three main components:

## 1. Discriminant and the Alternating Group (§DiscriminantAlternating)

If the discriminant Δ(f) = ∏_{i<j}(rⱼ−rᵢ)² of a separable polynomial is a perfect square
in the base field, then every Galois automorphism acts as an *even* permutation of the roots.
Consequently |Gal(f)| divides n!/2.

## 2. Complex Conjugation (§ComplexConjugation)

For an irreducible polynomial f ∈ ℚ[X] that has a non-real complex root, complex
conjugation restricts to a non-trivial automorphism of the splitting field, proving
2 ∣ |Gal(f)|.

## 3. Resolvent Theory for Quintics (§QuinticResolvent)

For an irreducible quintic f = X⁵ + pX + q over a field K (char ≠ 2,3,5), the
*sextic resolvent* R₆(y) is a degree-6 polynomial whose roots are specific expressions
in the roots of f. When Δ(f) is a perfect square, R₆ factors as a product of two cubics
(the *resolvent cubics*). A rational root of R₆ (or of a resolvent cubic) witnesses
the Galois group being contained in the Frobenius group F₂₀ = AGL(1,5) ≅ ℤ₅ ⋊ ℤ₄,
giving |Gal(f)| ∣ 20. -/

open Polynomial IntermediateField Finset

noncomputable section

/-!
## § 1. Discriminant and the Alternating Group

### Setup

Given a separable polynomial `f` of degree `n` over a field `K`, let `L` be its
splitting field and `r : Fin n ≃ rootSet f L` an enumeration of its roots.
Define the *discriminant element*

  δ(f) = ∏_{i < j} (rⱼ − rᵢ)

and the *discriminant*

  Δ(f) = δ(f)² = ∏_{i < j} (rⱼ − rᵢ)².

Every σ ∈ Gal(L/K) permutes the roots by some π ∈ Sₙ, and

  σ(δ) = sign(π) · δ.

When Δ(f) = d² for some d ∈ K, the element δ lies in K (up to sign), hence
is fixed by every σ. This forces sign(π) = 1 for all σ, i.e. the Galois group
embeds into Aₙ.
-/

section DiscriminantAlternating

variable {K : Type*} [Field K] [CharZero K]

/-- The discriminant element δ = ∏_{i<j}(vⱼ − vᵢ) for a sequence of field elements. -/
def discElem {L : Type*} [Field L] {n : ℕ} (v : Fin n → L) : L :=
  ∏ i : Fin n, ∏ j ∈ Ioi i, (v j - v i)

/-- The discriminant Δ = δ². -/
def discSq {L : Type*} [Field L] {n : ℕ} (v : Fin n → L) : L :=
  discElem v ^ 2

/-
**Discriminant–Alternating Theorem** (see `gal_le_alternating_of_disc_sq` below).

Let `f ∈ K[X]` be separable of degree `n` with splitting field `L`, and let
`v : Fin n → L` enumerate the roots. If the discriminant `Δ(f)` is the
square of an element of `K` (i.e. `∃ d : K, Δ(f) = (algebraMap K L d)²`), then
every Galois automorphism acts as an even permutation of the roots.

Equivalently, the image of the Galois action homomorphism
`Gal(f) →* Perm(rootSet f L)` lands inside the alternating group.

A Galois automorphism permutes roots of f.
-/
omit [CharZero K] in
lemma gal_perm_roots {n : ℕ} (f : K[X]) (hf_ne : f ≠ 0)
    (v : Fin n ≃ f.rootSet f.SplittingField)
    (σ : f.Gal) : ∃ π : Equiv.Perm (Fin n),
      ∀ i, σ (v i : f.SplittingField) = v (π i) := by
  have h_perm : ∀ i : Fin n, σ (v i) ∈ f.rootSet f.SplittingField := by
    intro i
    have h_root : Polynomial.eval₂ (algebraMap K f.SplittingField) (v i : f.SplittingField) f = 0 :=
      Polynomial.mem_rootSet.mp (v i |>.2) |>.2
    have h_eval : f.eval₂ (algebraMap K f.SplittingField) (σ (v i)) = 0 := by
      convert congr_arg (σ : f.SplittingField → f.SplittingField) h_root using 1
      · simp [eval₂_eq_sum_range]
        exact Finset.sum_congr rfl fun _ _ => by erw [σ.commutes]
      · exact Eq.symm (map_zero σ)
    exact Polynomial.mem_rootSet.mpr ⟨hf_ne, h_eval⟩
  have hinj : Function.Injective (fun i => v.symm ⟨σ (v i), h_perm i⟩) :=
    fun i j hij => by simpa [v.injective.eq_iff] using hij
  exact ⟨Equiv.ofBijective _ ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, fun i => by simp⟩

/-- discElem composed with a permutation picks up the sign. -/
lemma discElem_perm {L : Type*} [Field L] {n : ℕ}
    (v : Fin n → L) (π : Equiv.Perm (Fin n)) :
    discElem (v ∘ π) = ↑↑(Equiv.Perm.sign π) * discElem v := by
  exact prod_sub_perm_eq_sign_mul v π

/-
A Galois automorphism maps discElem to discElem ∘ π.
-/
omit [CharZero K] in
lemma gal_map_discElem {n : ℕ} (f : K[X])
    (v : Fin n ≃ f.rootSet f.SplittingField)
    (σ : f.Gal) (π : Equiv.Perm (Fin n))
    (hπ : ∀ i, σ (v i : f.SplittingField) = v (π i)) :
    σ (discElem (fun i => (v i : f.SplittingField))) =
    discElem (fun i => (v (π i) : f.SplittingField)) := by
  unfold discElem
  aesop

/-
If discElem = ±d for d ∈ K, then σ fixes discElem.
-/
omit [CharZero K] in
lemma gal_fixes_discElem {n : ℕ} (f : K[X])
    (v : Fin n ≃ f.rootSet f.SplittingField)
    (σ : f.Gal) (d : K)
    (h_val : discElem (fun i => (v i : f.SplittingField)) = algebraMap K _ d ∨
             discElem (fun i => (v i : f.SplittingField)) = -(algebraMap K _ d)) :
    σ (discElem (fun i => (v i : f.SplittingField))) =
    discElem (fun i => (v i : f.SplittingField)) := by
  cases' h_val with h h
  · rw [h, σ.commutes]
  · rw [h, map_neg, σ.commutes]

theorem gal_le_alternating_of_disc_sq
    {n : ℕ} (f : K[X]) (hf_ne : f ≠ 0)
    (v : Fin n ≃ f.rootSet f.SplittingField)
    (h_sq : ∃ d : K, discSq (fun i => (v i : f.SplittingField)) =
      (algebraMap K f.SplittingField d) ^ 2)
    (h_ne : discElem (fun i => (v i : f.SplittingField)) ≠ 0) :
    ∀ σ : f.Gal, ∃ π : Equiv.Perm (Fin n),
      (∀ i, σ (v i : f.SplittingField) = v (π i)) ∧ Equiv.Perm.sign π = 1 := by
  intro σ
  obtain ⟨π, hπ⟩ := gal_perm_roots f hf_ne v σ
  have h_sign : (Equiv.Perm.sign π : f.SplittingField) *
      discElem (fun i => (v i : f.SplittingField)) =
      discElem (fun i => (v i : f.SplittingField)) := by
    obtain ⟨d, hd⟩ := h_sq
    have h_sign_eq := gal_map_discElem f v σ π hπ
    convert h_sign_eq.symm using 1
    · exact (discElem_perm (fun i => (v i : f.SplittingField)) π).symm
    · rw [gal_fixes_discElem f v σ d]
      exact eq_or_eq_neg_of_sq_eq_sq _ _ hd
  cases' Int.units_eq_one_or (Equiv.Perm.sign π) with h h <;> simp_all
  · exact ⟨π, fun i => rfl, h⟩
  · grind +ring

/-- Under the hypotheses of `gal_le_alternating_of_disc_sq`, the Galois group
embeds (injectively) into the alternating group `Aₙ`. -/
theorem exists_gal_embeds_alternating
    {n : ℕ} (f : K[X])
    (hf_ne : f ≠ 0)
    (v : Fin n ≃ f.rootSet f.SplittingField)
    (h_sq : ∃ d : K, discSq (fun i => (v i : f.SplittingField)) =
      (algebraMap K f.SplittingField d) ^ 2)
    (h_ne : discElem (fun i => (v i : f.SplittingField)) ≠ 0) :
    ∃ g' : f.Gal →* alternatingGroup (Fin n), Function.Injective g' := by
  obtain ⟨g, hg⟩ : ∃ g : f.Gal →* Equiv.Perm (Fin n),
      Function.Injective g ∧ ∀ σ : f.Gal, Equiv.Perm.sign (g σ) = 1 := by
    have := gal_le_alternating_of_disc_sq f hf_ne v h_sq h_ne
    choose g hg₁ hg₂ using this
    refine ⟨MonoidHom.mk' g ?_, ?_, hg₂⟩
    all_goals norm_num [Function.Injective, Equiv.Perm.ext_iff]
    · intro σ τ i
      have h_eq : σ (τ (v i : f.SplittingField)) = v (g (σ * τ) i) := hg₁ (σ * τ) i
      exact v.injective (Subtype.ext <| by aesop)
    · intro σ τ h_eq
      ext x
      obtain ⟨i, hi⟩ := v.surjective ⟨x, by assumption⟩
      grind
  exact ⟨MonoidHom.codRestrict g _ fun σ => hg.2 σ, fun σ τ h => hg.1 <| by simpa using h⟩

/-
**Corollary.** Under the hypotheses of `gal_le_alternating_of_disc_sq`,
the order of the Galois group divides `n! / 2`.
-/
theorem card_gal_dvd_half_factorial_of_disc_sq
    {n : ℕ} (f : K[X])
    (hf_ne : f ≠ 0)
    (v : Fin n ≃ f.rootSet f.SplittingField)
    (h_sq : ∃ d : K, discSq (fun i => (v i : f.SplittingField)) =
      (algebraMap K f.SplittingField d) ^ 2)
    (h_ne : discElem (fun i => (v i : f.SplittingField)) ≠ 0) :
    Nat.card f.Gal ∣ n.factorial / 2 := by
  have h_gal_le_alt : (Nat.card f.Gal) ∣ (Fintype.card (alternatingGroup (Fin n))) := by
    obtain ⟨g', hg'⟩ := exists_gal_embeds_alternating f hf_ne v h_sq h_ne
    have := Subgroup.card_dvd_of_injective g' hg'
    aesop
  rcases n with (_ | _ | n) <;> simp_all
  have := Subgroup.card_mul_index (alternatingGroup (Fin (n + 2)))
  simp_all [Fintype.card_perm]
  refine h_gal_le_alt.trans (Nat.dvd_div_of_mul_dvd ⟨1, ?_⟩)
  linarith

end DiscriminantAlternating

/-!
## § 2. Complex Conjugation

For `f ∈ ℚ[X]` irreducible, the splitting field `L` of `f` embeds into `ℂ`.
Complex conjugation `conj : ℂ → ℂ` restricts to a `ℚ`-algebra automorphism of (the
image of) `L` inside `ℂ`. When `f` has a non-real root, this automorphism is
non-trivial, hence has order 2, proving `2 ∣ |Gal(f)|`.
-/

section ComplexConjugation

/-
If an irreducible polynomial `f ∈ ℚ[X]` has a root `z ∈ ℂ` with `z ∉ ℝ`,
then the Galois group of `f` has even order. -/
theorem two_dvd_card_gal_of_nonreal_root
    (f : ℚ[X]) (hf : Irreducible f)
    (z : ℂ) (hz_root : Polynomial.aeval z f = 0) (hz_nonreal : z.im ≠ 0) :
    2 ∣ Nat.card f.Gal := by
  -- Embed SplittingField f ↪ₐ[ℚ] ℂ via algebra homomorphism ι.
  have ι : f.SplittingField →ₐ[ℚ] ℂ := IsAlgClosed.lift
  -- Every complex root of `f` lies in the image of `ι` (since `f` splits there).
  have h_range : ∀ w : ℂ, f.eval₂ (algebraMap ℚ ℂ) w = 0 → w ∈ ι.range := by
    have := Polynomial.SplittingField.splits f
    rw [Polynomial.splits_iff_exists_multiset] at this
    obtain ⟨m, hm⟩ := this
    replace hm := congr_arg (Polynomial.map (ι : f.SplittingField →+* ℂ)) hm
    simp_all [Polynomial.map_multiset_prod]
    intro w hw
    replace hm := congr_arg (Polynomial.eval w) hm
    simp_all [Polynomial.eval_multiset_prod]
    simp_all [Polynomial.map_map, aeval_def]
    exact hm.elim (fun h => absurd h hf.ne_zero) fun ⟨a, ha, h⟩ => ⟨a, by linear_combination -h⟩
  -- Build conjugation first as an algebra endomorphism of the splitting field, then promote
  -- it to a Galois automorphism.
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ : f.SplittingField →ₐ[ℚ] f.SplittingField,
      ∀ x : f.SplittingField, ι (σ x) = starRingEnd ℂ (ι x) := by
    have h_conj : ∀ x : f.SplittingField, starRingEnd ℂ (ι x) ∈ ι.range := by
      intro x
      have h_roots : ∀ y ∈ f.rootSet f.SplittingField, starRingEnd ℂ (ι y) ∈ ι.range := by
        intro y hy
        have h_root : f.eval₂ (algebraMap ℚ ℂ) (ι y) = 0 := by
          rw [Polynomial.mem_rootSet] at hy
          simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range] using congr_arg (fun x => ι x) hy.2
        refine h_range _ ?_
        simpa [Polynomial.eval₂_eq_sum_range, Complex.ext_iff] using congr_arg Star.star h_root
      have h_adjoin : ∀ y ∈ Algebra.adjoin ℚ (f.rootSet f.SplittingField),
          starRingEnd ℂ (ι y) ∈ ι.range := by
        intro y hy
        refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hy
        · exact h_roots
        · exact fun r => ⟨r, by simp⟩
        · simp at *
          exact fun x y hx hy z hz w hw => ⟨z + w, by simp [hz, hw]⟩
        · simp at *
          exact fun x y hx hy z hz w hw => ⟨z * w, by simp [hz, hw]⟩
      have h_top : Algebra.adjoin ℚ (f.rootSet f.SplittingField) = ⊤ := by
        grind only [SplittingField.adjoin_rootSet]
      aesop
    choose σ hσ using h_conj
    refine ⟨{ toFun := σ, map_zero' := ?_, map_one' := ?_, map_add' := ?_,
                map_mul' := ?_, commutes' := ?_ }, hσ⟩ <;> simp_all
    · apply ι.injective
      aesop
    · intro x y
      apply ι.injective
      aesop
    · apply ι.injective
      aesop
    · intro x y
      apply ι.injective
      aesop
    · intro r
      have := hσ r
      simp_all [Complex.ext_iff]
      apply ι.injective
      simpa [Complex.ext_iff] using hσ r
  obtain ⟨σ, hσ⟩ : ∃ σ : f.Gal, ∀ x : f.SplittingField, ι (σ x) = starRingEnd ℂ (ι x) :=
    ⟨AlgEquiv.ofBijective σ₀ σ₀.bijective, hσ₀⟩
  -- Since `z` is a root of `f` and `z ∉ ℝ`, we have `σ z ≠ z`.
  have hσ_ne_id : σ ≠ 1 := by
    -- Since `z` is a root of `f` and `z ∉ ℝ`, there exists `x ∈ SplittingField f` with `ι x = z`.
    obtain ⟨x, hx⟩ : ∃ x : f.SplittingField, ι x = z := by
      have hz : f.eval₂ (algebraMap ℚ ℂ) z = 0 := by
        simpa [Polynomial.aeval_def] using hz_root
      exact h_range z hz
    intro h
    specialize hσ x
    simp_all [Complex.ext_iff]
    apply hz_nonreal
    linarith!
  -- Since σ is not the identity, its order must be 2.
  have hσ_order : orderOf σ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · ext x
      apply ι.injective
      erw [hσ, hσ]
      norm_num
      rfl
    · assumption
  rw [← hσ_order, orderOf_dvd_iff_pow_eq_one]
  simp [pow_card_eq_one]

end ComplexConjugation

/-!
## § 3. Resolvent Theory for Quintics

### The Sextic Resolvent

For a quintic `f(x) = x⁵ + px + q` with roots `θ₁, …, θ₅`, consider the
*Lagrange resolvent expressions*

  Φₖ = θ₁θ_{σᵏ(2)} + θ_{σᵏ(2)}θ_{σᵏ(3)} + θ_{σᵏ(3)}θ_{σᵏ(4)}
       + θ_{σᵏ(4)}θ_{σᵏ(5)} + θ_{σᵏ(5)}θ₁

where σ = (1 2 3 4 5) is a 5-cycle. There are 12 = |S₅|/|⟨σ⟩| such expressions,
coming in 6 pairs `{Φ, −Φ}`, giving rise to the *sextic resolvent*

  R₆(y) = ∏ᵢ (y − Φᵢ²)

which is a degree-6 polynomial whose coefficients lie in K (since they are
symmetric functions of the roots).

### The Key Structural Theorem

The stabilizer of any single Φₖ in S₅ is the *Frobenius group*
F₂₀ = AGL(1, 𝔽₅) = ℤ₅ ⋊ ℤ₄, the unique transitive subgroup of S₅ of order 20.

Therefore: **R₆ has a root in K ⟺ Gal(f) ⊆ F₂₀ (up to conjugacy in S₅)**.

When Gal(f) ⊆ F₂₀, we get |Gal(f)| ∣ 20.

### Factorization over K(√Δ)

When the discriminant Δ is a perfect square in K, the sextic resolvent R₆
factors over K into two cubics. A root of either cubic is a root of R₆,
so it suffices to find a rational root of a cubic (which can be checked by
the rational root theorem or direct substitution).
-/


section QuinticResolvent

variable {K : Type*} [Field K] [CharZero K]

/--
The sextic resolvent of the quintic `X⁵ + p·X + q`.

For a quintic f(x) = x⁵ + px + q with roots θ₁, …, θ₅, define the *pentagonal*
resolvent expression:

  Ψ = θ₁θ₂ + θ₂θ₃ + θ₃θ₄ + θ₄θ₅ + θ₅θ₁

The stabilizer of Ψ in S₅ is the dihedral group D₅ (order 10), giving 12 orbit
elements that pair as {Ψᵢ, −Ψᵢ} into 6 pairs. The sextic resolvent is

  R₆(t) = ∏ᵢ₌₁⁶ (t − Ψᵢ²)

a degree-6 polynomial with coefficients in K. The stabilizer of each Ψᵢ² is
the Frobenius group F₂₀ = N_{S₅}(D₅) = AGL(1,5) of order 20.

Explicit factored form:
  R₆(t) = (t − p)⁴ · (t² − 6pt + 25p²) − 3125q⁴ · t

Expanded:
  R₆(t) = t⁶ − 10pt⁵ + 55p²t⁴ − 140p³t³ + 175p⁴t²
           − (106p⁵ + 3125q⁴)t + 25p⁶
-/
def sexticResolvent (p q : K) : K[X] :=
  Polynomial.X ^ 6 - Polynomial.C (10 * p) * Polynomial.X ^ 5
    + Polynomial.C (55 * p ^ 2) * Polynomial.X ^ 4
    - Polynomial.C (140 * p ^ 3) * Polynomial.X ^ 3
    + Polynomial.C (175 * p ^ 4) * Polynomial.X ^ 2
    - Polynomial.C (106 * p ^ 5 + 3125 * q ^ 4) * Polynomial.X
    + Polynomial.C (25 * p ^ 6)

/-

The natDegree of X⁵ + C(p)·X + C(q) is 5 when p ≠ 0. -/
omit [CharZero K] in
lemma natDegree_X5_pXq (p q : K) (hp : p ≠ 0) :
    (Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q : K[X]).natDegree = 5 := by
  rw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num [hp]

/-
|Gal(f)| is the cardinality of a subgroup of Perm(rootSet f L)
-/
lemma card_gal_dvd_natDegree_factorial {K : Type*} [Field K] [CharZero K]
    (f : K[X]) (hf_irr : Irreducible f) :
    Nat.card f.Gal ∣ f.natDegree.factorial := by
  have hFact : Fact (Polynomial.map (algebraMap K f.SplittingField) f).Splits :=
    ⟨Polynomial.SplittingField.splits f⟩
  have h_card_roots : Nat.card (f.rootSet f.SplittingField) = f.natDegree := by
    rw [Nat.card_eq_fintype_card]
    grind only [Polynomial.card_rootSet_eq_natDegree, SplittingField.splits, Irreducible.separable]
  have h_card_le : Nat.card f.Gal ∣ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) := by
    rw [Nat.card_congr (Equiv.ofInjective _ (Polynomial.Gal.galActionHom_injective f f.SplittingField))]
    exact Subgroup.card_subgroup_dvd_card
      (MonoidHom.range (Polynomial.Gal.galActionHom f f.SplittingField))
  rw [Nat.card_perm, h_card_roots] at h_card_le
  exact h_card_le

/-
**Core resolvent bound**: When R₆ has a root y₀ ∈ K, the Galois group
    order is at most 20. -/
lemma card_gal_le_20_of_resolvent_root_core
    (p q : K) (hp : p ≠ 0)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (hf_irr : Irreducible f)
    (y₀ : K) (hy₀ : (sexticResolvent p q).IsRoot y₀) :
    Nat.card f.Gal ≤ 20 := by
  -- Denote the roots of `f` by `v`.
  have v : Fin 5 ≃ f.rootSet f.SplittingField := Fintype.equivOfCardEq (by
    have h_card_roots : Fintype.card (f.rootSet f.SplittingField) = f.natDegree := by
      grind only [Polynomial.card_rootSet_eq_natDegree, SplittingField.splits, Irreducible.separable]
    rw [h_card_roots, hf, Polynomial.natDegree_add_C,
      Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> aesop)
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Equiv.Perm (Fin 5),
      algebraMap K f.SplittingField y₀ = pentagonalSum (fun i => (v (σ₀ i) : f.SplittingField)) ^ 2 := by
    have := sexticResolvent_roots_are_pentagonalSums p q f hf v (algebraMap K f.SplittingField y₀) ?_ <;> aesop
  have h_image : ∀ τ : f.Gal, ∃ π : Equiv.Perm (Fin 5),
      (∀ i, τ (v i : f.SplittingField) = v (π i)) ∧ IsAffineLinearMod5 (σ₀⁻¹ * π * σ₀) := by
    intro τ
    obtain ⟨π, hπ⟩ := gal_perm_roots f hf_irr.ne_zero v τ
    use π
    have h_eq : pentagonalSum (fun i => (v (π (σ₀ i)) : f.SplittingField)) ^ 2 =
        pentagonalSum (fun i => (v (σ₀ i) : f.SplittingField)) ^ 2 := by
      have h_eq : τ (pentagonalSum (fun i => (v (σ₀ i) : f.SplittingField)) ^ 2) =
          pentagonalSum (fun i => (v (σ₀ i) : f.SplittingField)) ^ 2 := by
        rw [← hσ₀, τ.commutes]
      convert h_eq using 1
      simp [pentagonalSum, hπ]
    have h_affine : IsAffineLinearMod5 (σ₀⁻¹ * π * σ₀) := by
      have := pentagonalSum_sq_eq_iff_F20_coset p q f hf hf_irr v (σ₀) (π * σ₀)
      simp_all [mul_assoc]
    exact ⟨hπ, h_affine⟩
  choose π hπ₁ hπ₂ using h_image
  have h_image : Function.Injective (fun τ : f.Gal => σ₀⁻¹ * π τ * σ₀) := by
    intro τ₁ τ₂ h_eq
    ext x
    obtain ⟨i, hi⟩ := v.surjective ⟨x, by assumption⟩
    replace h_eq := Equiv.congr_fun h_eq (σ₀⁻¹ i)
    simp_all [mul_assoc]
    grind
  have h_image : Nat.card (Set.range (fun τ : f.Gal => σ₀⁻¹ * π τ * σ₀)) ≤
      Nat.card (F20_finset : Finset (Equiv.Perm (Fin 5))) := by
    apply Nat.card_mono
    · exact Finset.finite_toSet _
    · exact Set.range_subset_iff.mpr fun τ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ₂ τ⟩
  rw [Nat.card_range_of_injective ‹_›] at h_image
  aesop

/-- Key resolvent lemma: if R₆ has a root in K and f = X⁵+pX+q is irreducible,
    then |Gal(f)| ≠ 60 and |Gal(f)| ≠ 120.

    This follows immediately from `card_gal_le_20_of_resolvent_root_core`,
    since 60 > 20 and 120 > 20. -/
lemma gal_ne_60_120_of_resolvent_root
    (p q : K) (hp : p ≠ 0)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (hf_irr : Irreducible f)
    (y₀ : K) (hy₀ : (sexticResolvent p q).IsRoot y₀) :
    Nat.card f.Gal ≠ 60 ∧ Nat.card f.Gal ≠ 120 := by
  have h := card_gal_le_20_of_resolvent_root_core p q hp f hf hf_irr y₀ hy₀
  exact ⟨by omega, by omega⟩

/-
**Resolvent Root Theorem for Quintics.**

If `f = X⁵ + p·X + q ∈ K[X]` is irreducible with `p ≠ 0` and the sextic resolvent
`R₆` has a root in `K`, then `|Gal(f)| ∣ 20`.
-/
set_option maxHeartbeats 800000 in
theorem card_gal_dvd_20_of_resolvent_root
    (p q : K) (hp : p ≠ 0)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (hf_irr : Irreducible f)
    (y₀ : K) (hy₀ : (sexticResolvent p q).IsRoot y₀) :
    Nat.card f.Gal ∣ 20 := by
  -- Step 1: 5 | |Gal| (from irreducibility and degree 5)
  have hf_deg : f.natDegree = 5 := hf ▸ natDegree_X5_pXq p q hp
  have h5 : 5 ∣ Nat.card f.Gal := hf_deg ▸ natDegree_dvd_card hf_irr
  -- Step 2: |Gal| | 120 = 5!
  have h120 : Nat.card f.Gal ∣ 120 := by
    have := card_gal_dvd_natDegree_factorial f hf_irr
    rw [hf_deg] at this
    norm_num [Nat.factorial] at this ⊢
    exact this
  -- Step 3: |Gal| ≠ 60 and |Gal| ≠ 120 (from resolvent root)
  have ⟨hne60, hne120⟩ := gal_ne_60_120_of_resolvent_root p q hp f hf hf_irr y₀ hy₀
  -- Step 4: |Gal| is the order of a subgroup of S₅, so it can't be 15, 30, or 40
  -- The Galois group injects (via `galActionHom`) as a subgroup of `Perm(rootSet f L)`, and
  -- the roots are in bijection with `Fin 5`, so `Perm(rootSet f L) ≃* Perm(Fin 5)`.
  have h_sub : ∃ H : Subgroup (Equiv.Perm (f.rootSet f.SplittingField)),
      Nat.card H = Nat.card f.Gal := by
    obtain ⟨σ, hσ⟩ : ∃ σ : f.Gal →* Equiv.Perm (f.rootSet f.SplittingField),
        Function.Injective σ := by
      have : Fact (Polynomial.map (algebraMap K f.SplittingField) f).Splits :=
        ⟨Polynomial.SplittingField.splits f⟩
      exact ⟨Polynomial.Gal.galActionHom f f.SplittingField,
        Polynomial.Gal.galActionHom_injective f f.SplittingField⟩
    exact ⟨σ.range, (Nat.card_congr (Equiv.ofInjective _ hσ)).symm⟩
  have h_iso : Nonempty (Equiv.Perm (f.rootSet f.SplittingField) ≃* Equiv.Perm (Fin 5)) := by
    refine ⟨?_⟩
    refine' { Equiv.permCongr (Fintype.equivOfCardEq _) with .. }
    all_goals norm_num [Equiv.Perm.ext_iff]
    rw [← hf_deg, Polynomial.card_rootSet_eq_natDegree]
    · exact hf_irr.separable
    · exact Polynomial.SplittingField.splits _
  have hne15 : Nat.card f.Gal ≠ 15 := by
    intro h15
    obtain ⟨H, hH⟩ := h_sub
    obtain ⟨iso⟩ := h_iso
    have h_card_iso : Nat.card (↥(H.map iso.toMonoidHom)) = Nat.card f.Gal := by
      rw [← hH, Nat.card_congr]
      symm
      refine Equiv.ofBijective (fun x => ⟨iso x, Subgroup.mem_map_of_mem _ x.2⟩)
        ⟨fun x y hxy => ?_, fun x => ?_⟩ <;> aesop
    exact Perm_Fin5_no_subgroup_order_15 _ (h_card_iso.trans h15)
  have hne30 : Nat.card f.Gal ≠ 30 := by
    have := card_gal_le_20_of_resolvent_root_core p q hp f hf hf_irr y₀ hy₀
    interval_cases Nat.card f.Gal <;> trivial
  have hne40 : Nat.card f.Gal ≠ 40 := by
    intro h
    obtain ⟨H, hH⟩ := h_sub
    obtain ⟨e⟩ := h_iso
    refine Perm_Fin5_no_subgroup_order_40 (H.map e.toMonoidHom) ?_
    rw [← h, ← hH, Nat.card_congr]
    symm
    refine Equiv.ofBijective (fun x => ⟨e x, Subgroup.mem_map_of_mem _ x.2⟩)
      ⟨fun x y hxy => ?_, fun x => ?_⟩ <;> aesop
  -- Step 5: Conclude |Gal| | 20
  have hpos : 0 < Nat.card f.Gal := Nat.card_pos
  exact dvd_20_of_constraints _ hpos h5 h120 hne60 hne120 hne15 hne30 hne40

end QuinticResolvent

/-!
## § 4. Combination Theorems

Putting the above together, we get convenient "pipeline" lemmas for determining
quintic Galois groups.
-/

section Pipeline

/--
**Quintic Galois group divides 60.**

If `f ∈ K[X]` is an irreducible separable quintic whose discriminant is a perfect square
in K, then `|Gal(f)| ∣ 60 = 5!/2`.
-/
theorem quintic_gal_dvd_60_of_disc_sq
    {K : Type*} [Field K] [CharZero K]
    (f : K[X]) (hf_irr : Irreducible f)
    (v : Fin 5 ≃ f.rootSet f.SplittingField)
    (h_sq : ∃ d : K, discSq (fun i => (v i : f.SplittingField)) =
      (algebraMap K f.SplittingField d) ^ 2)
    (h_ne : discElem (fun i => (v i : f.SplittingField)) ≠ 0) :
    Nat.card f.Gal ∣ 60 := by
  have := card_gal_dvd_half_factorial_of_disc_sq f hf_irr.ne_zero v h_sq h_ne
  norm_num [Nat.factorial] at this ⊢
  exact this

/--
**Quintic with resolvent root has |Gal| ∣ 20.**
-/
theorem quintic_gal_dvd_20_of_disc_sq_and_resolvent
    {K : Type*} [Field K] [CharZero K]
    (p q : K) (hp : p ≠ 0)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (hf_irr : Irreducible f)
    (y₀ : K) (hy₀ : (sexticResolvent p q).IsRoot y₀) :
    Nat.card f.Gal ∣ 20 :=
  card_gal_dvd_20_of_resolvent_root p q hp f hf hf_irr y₀ hy₀

end Pipeline

end
