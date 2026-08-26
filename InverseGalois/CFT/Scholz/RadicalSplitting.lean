/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.FrobeniusSplitting
import InverseGalois.CFT.Scholz.RadicalTower

/-!
# The power residue criterion for splitting in a radical field

Let `ℓ` be a prime, let `v` be an integer and let `q` be a prime congruent to one modulo `ℓ` and
prime to `v`.  If `v` is an `ℓ`-th power modulo `q`, then `q` splits completely in the field
obtained by adjoining to the rationals the `ℓ`-th roots of unity together with the `ℓ`-th roots of
`v`.

The proof is a direct computation with the two conditions defining a totally split prime at a
prime `Q` of the ring of integers above `q`: that inertia is trivial and that the arithmetic
Frobenius is trivial.  Both are statements about a single automorphism `σ`, and both give the same
information at each of the generators `α` of the field, whose `ℓ`-th power is an integer `c` prime
to `q` and satisfying `c ^ ((q - 1) / ℓ) ≡ 1` modulo `q`.  For inertia the information is
`σ α ≡ α`; for Frobenius it is `σ α ≡ α ^ q`, and `α ^ q = α · c ^ ((q - 1) / ℓ) ≡ α`, so it is
again `σ α ≡ α`.  Now `σ α` is `α` times an `ℓ`-th root of unity `ξ`, so `(ξ - 1) α ∈ Q`; the
generator `α` is not in `Q` because its `ℓ`-th power is prime to `q`, so `ξ ≡ 1`, and distinct
`ℓ`-th roots of unity stay distinct modulo `Q` because `ξ - 1` divides `ℓ` and `q ≠ ℓ`.  Hence `σ`
fixes every generator and is the identity.

## Main results

* `InverseGalois.CFT.eq_one_of_pow_eq_one_of_sub_mem`: an `ℓ`-th root of unity congruent to one
  modulo a prime above a rational prime different from `ℓ` is one.
* `InverseGalois.CFT.eq_one_of_forall_radicalGens_fixed`: an automorphism of a radical field fixing
  every generator is the identity.
* `InverseGalois.CFT.splitsCompletely_radicalField`: **a prime congruent to one modulo `ℓ` modulo
  which an integer is an `ℓ`-th power splits completely in the radical field of that integer.**

## Tags

radical extension, power residue, splitting completely, Frobenius, inertia
-/

open NumberField Polynomial IntermediateField InverseGalois.NumberTheory

namespace InverseGalois.CFT

attribute [local instance] Int.ideal_span_isMaximal_of_prime

/-! ### Roots of unity modulo a prime -/

/-- **An `ℓ`-th root of unity congruent to one modulo a prime above a rational prime other than
`ℓ`** is equal to one.  A nontrivial `ℓ`-th root of unity `ξ` is primitive, so `ξ - 1` divides `ℓ`;
were `ξ - 1` in the prime, `ℓ` would lie in it too, forcing the rational prime underneath to be
`ℓ`. -/
theorem eq_one_of_pow_eq_one_of_sub_mem {K : Type*} [Field K] [NumberField K] {ℓ q : ℕ}
    (hℓ : ℓ.Prime) (hq : q.Prime) (hne : q ≠ ℓ) {Q : Ideal (𝓞 K)} [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(q : ℤ)})] {ξ : 𝓞 K} (hpow : ξ ^ ℓ = 1) (hsub : ξ - 1 ∈ Q) :
    ξ = 1 := by
  by_contra hne1
  have hord : orderOf ξ ∣ ℓ := orderOf_dvd_of_pow_eq_one hpow
  have hordne : orderOf ξ ≠ 1 := fun h => hne1 (orderOf_eq_one_iff.mp h)
  have hordeq : orderOf ξ = ℓ := (hℓ.eq_one_or_self_of_dvd _ hord).resolve_left hordne
  have hprim : IsPrimitiveRoot ξ ℓ := hordeq ▸ IsPrimitiveRoot.orderOf ξ
  obtain ⟨z, -, hz⟩ := hprim.self_sub_one_pow_dvd_order (k := 1) hℓ.one_lt
  have hlQ : ((ℓ : ℕ) : 𝓞 K) ∈ Q := by
    rw [hz, pow_one]
    exact Ideal.mul_mem_left _ _ hsub
  have hunder : Ideal.span {(q : ℤ)} = Q.under ℤ := Ideal.LiesOver.over
  have hmem : (ℓ : ℤ) ∈ Ideal.span {(q : ℤ)} := by
    rw [hunder]
    show algebraMap ℤ (𝓞 K) (ℓ : ℤ) ∈ Q
    simpa using hlQ
  rw [Ideal.mem_span_singleton] at hmem
  exact hne ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp (by exact_mod_cast hmem))

/-! ### Automorphisms fixing the generators -/

variable {ℓ : ℕ} {S : Finset ℚ}

/-- **An automorphism of a radical field fixing every generator is the identity**, the generators
generating the field. -/
theorem eq_one_of_forall_radicalGens_fixed {σ : Gal(↥(radicalField ℓ S)/ℚ)}
    (h : ∀ α ∈ radicalGens ℓ S, σ α = α) : σ = 1 := by
  refine AlgEquiv.ext fun x => ?_
  show σ x = x
  have hx : x ∈ IntermediateField.adjoin ℚ (radicalGens ℓ S) := by
    rw [adjoin_radicalGens]
    exact IntermediateField.mem_top
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => exact h y hy
  | algebraMap r => exact σ.commutes r
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | inv y _ hy => rw [map_inv₀, hy]
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]

/-- Every generator of a radical field has `ℓ`-th power one of the prescribed rational numbers. -/
theorem exists_mem_pow_eq_of_mem_radicalGens {α : ↥(radicalField ℓ S)}
    (hα : α ∈ radicalGens ℓ S) :
    ∃ c ∈ insert (1 : ℚ) S, α ^ ℓ = algebraMap ℚ ↥(radicalField ℓ S) c := by
  have hα' : (α : AlgebraicClosure ℚ) ∈ (radicalPoly ℓ S).rootSet (AlgebraicClosure ℚ) := hα
  rw [mem_rootSet] at hα'
  obtain ⟨-, hzero⟩ := hα'
  rw [radicalPoly, map_prod] at hzero
  obtain ⟨c, hc, hc0⟩ := Finset.prod_eq_zero_iff.mp hzero
  simp only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at hc0
  exact ⟨c, hc, Subtype.ext (by push_cast; exact hc0)⟩

/-- A generator of a radical field whose `ℓ`-th power is an integer is itself an algebraic
integer. -/
theorem exists_ringOfIntegers_pow_eq (hℓ : ℓ ≠ 0) {c : ℤ} {α : ↥(radicalField ℓ S)}
    (hα : α ^ ℓ = (c : ↥(radicalField ℓ S))) :
    ∃ β : 𝓞 ↥(radicalField ℓ S), (β : ↥(radicalField ℓ S)) = α ∧
      β ^ ℓ = (c : 𝓞 ↥(radicalField ℓ S)) := by
  refine ⟨⟨α, ⟨X ^ ℓ - C c, monic_X_pow_sub_C c hℓ, ?_⟩⟩, rfl, ?_⟩
  · rw [eval₂_sub, eval₂_X_pow, eval₂_C, eq_intCast, hα, sub_self]
  · apply RingOfIntegers.ext
    show (α : ↥(radicalField ℓ S)) ^ ℓ = (c : ↥(radicalField ℓ S))
    exact hα

/-! ### The power residue criterion -/

variable {q : ℕ} {v : ℤ}

/-- The `ℓ`-th power of a generator of the radical field of an integer `v` is an integer prime to
`q` which is an `ℓ`-th power modulo `q`, provided `v` is one. -/
theorem exists_intCast_pow_eq_of_mem_radicalGens (hq : q.Prime)
    (hqv : ¬ (q : ℤ) ∣ v) (hvpow : (v : ZMod q) ^ ((q - 1) / ℓ) = 1)
    {α : ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))} (hα : α ∈ radicalGens ℓ {(v : ℚ)}) :
    ∃ c : ℤ, ¬ (q : ℤ) ∣ c ∧ (q : ℤ) ∣ c ^ ((q - 1) / ℓ) - 1 ∧
      α ^ ℓ = (c : ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : 2 ≤ q := hq.two_le
  obtain ⟨c, hc, hcα⟩ := exists_mem_pow_eq_of_mem_radicalGens hα
  rw [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl
  · refine ⟨1, fun h => ?_, by simp, by simpa using hcα⟩
    have := Int.le_of_dvd one_pos h
    omega
  · refine ⟨v, hqv, ?_, by simpa using hcα⟩
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ?_
    push_cast [hvpow]
    ring

/-- **A prime congruent to one modulo `ℓ` modulo which an integer is an `ℓ`-th power splits
completely in the radical field of that integer.**  At a prime `Q` above it, both the triviality of
inertia and the triviality of the Frobenius say that the automorphism in question moves each
generator by an `ℓ`-th root of unity congruent to one modulo `Q`, hence fixes it. -/
theorem splitsCompletely_radicalField (hℓ : ℓ.Prime) (hq : q.Prime) (hdvd : ℓ ∣ q - 1)
    (hqv : ¬ (q : ℤ) ∣ v) (hvpow : (v : ZMod q) ^ ((q - 1) / ℓ) = 1) :
    SplitsCompletely ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ)) q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : 2 ≤ q := hq.two_le
  have hl2 : 2 ≤ ℓ := hℓ.two_le
  have hqℓ : q ≠ ℓ := by
    rintro rfl
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (R := ℤ) (S := 𝓞 ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))) (Ideal.span {(q : ℤ)})
  haveI := hQmax
  haveI := hQover
  haveI : Q.IsPrime := hQmax.isPrime
  have hQne : Q ≠ ⊥ := ne_bot_of_liesOver q Q
  haveI : Finite (𝓞 ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ)) ⧸ Q) :=
    finite_quotient_of_ne_bot Q hQne
  have hQint : ∀ z : ℤ, ((z : 𝓞 ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))) ∈ Q) ↔ (q : ℤ) ∣ z := by
    intro z
    have h1 : ((z : 𝓞 ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))) ∈ Q) ↔ z ∈ Q.under ℤ := by
      simp [Ideal.under, Ideal.mem_comap]
    rw [h1, ← Ideal.over_def Q (Ideal.span {(q : ℤ)}), Ideal.mem_span_singleton]
  -- The key step: an automorphism moving no generator modulo `Q` is the identity.
  have hgen : ∀ σ : Gal(↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))/ℚ),
      (∀ β : 𝓞 ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ)),
        (β : ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))) ∈ radicalGens ℓ {(v : ℚ)} →
          σ • β - β ∈ Q) → σ = 1 := by
    intro σ hσ
    refine eq_one_of_forall_radicalGens_fixed fun α hα => ?_
    obtain ⟨c, hqc, -, hcα⟩ := exists_intCast_pow_eq_of_mem_radicalGens hq hqv hvpow hα
    obtain ⟨β, hβ, hβpow⟩ := exists_ringOfIntegers_pow_eq hℓ.ne_zero hcα
    have hβQ : β ∉ Q := by
      intro hmem
      exact hqc ((hQint c).mp (hβpow ▸ Ideal.pow_mem_of_mem Q hmem ℓ hℓ.pos))
    have hc0 : c ≠ 0 := fun h => hqc (h ▸ dvd_zero _)
    have hcK : ((c : ℤ) : ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))) ≠ 0 := Int.cast_ne_zero.mpr hc0
    have hα0 : α ≠ 0 := by
      intro h
      rw [h, zero_pow hℓ.ne_zero] at hcα
      exact hcK hcα.symm
    have hpow1 : (σ α * α⁻¹) ^ ℓ = 1 := by
      rw [mul_pow, ← map_pow, inv_pow, hcα, map_intCast, mul_inv_cancel₀ hcK]
    obtain ⟨ξ, hξ, hξpow'⟩ := exists_ringOfIntegers_pow_eq (S := ({(v : ℚ)} : Finset ℚ))
      hℓ.ne_zero (c := 1) (α := σ α * α⁻¹) (by rw [hpow1]; push_cast; ring)
    have hξpow : ξ ^ ℓ = 1 := by simpa using hξpow'
    have hmul : σ • β - β = (ξ - 1) * β := by
      apply RingOfIntegers.ext
      show σ (β : ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))) - (β : _)
        = ((ξ : ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))) - 1) * (β : _)
      rw [hξ, hβ, sub_mul, inv_mul_cancel_right₀ hα0, one_mul]
    have hsub : ξ - 1 ∈ Q :=
      ((Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹Q.IsPrime›).mp (hmul ▸ hσ β (hβ ▸ hα))).resolve_right
        hβQ
    have hξ1 : ξ = 1 := eq_one_of_pow_eq_one_of_sub_mem hℓ hq hqℓ hξpow hsub
    have hfin : σ α * α⁻¹ = 1 := by rw [← hξ, hξ1]; rfl
    field_simp at hfin
    exact hfin
  -- The `q`-th power map fixes every generator modulo `Q`.
  have hβq : ∀ β : 𝓞 ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ)),
      (β : ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))) ∈ radicalGens ℓ {(v : ℚ)} →
        β ^ q - β ∈ Q := by
    intro β hβmem
    obtain ⟨c, -, hcpow, hcα⟩ := exists_intCast_pow_eq_of_mem_radicalGens hq hqv hvpow hβmem
    obtain ⟨β', hβ', hβpow⟩ := exists_ringOfIntegers_pow_eq hℓ.ne_zero hcα
    rw [show β' = β from RingOfIntegers.ext hβ'] at hβpow
    have hq1 : q = ℓ * ((q - 1) / ℓ) + 1 := by rw [Nat.mul_div_cancel' hdvd]; omega
    have hexp : β ^ q - β = ((c ^ ((q - 1) / ℓ) - 1 : ℤ) :
        𝓞 ↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))) * β := by
      conv_lhs => rw [hq1]
      rw [pow_succ, pow_mul, hβpow]
      push_cast
      ring
    rw [hexp]
    exact Ideal.mul_mem_right _ _ ((hQint _).mpr hcpow)
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = q := by
    rw [← Ideal.over_def Q (Ideal.span {(q : ℤ)}),
      Nat.card_congr (Int.quotientSpanNatEquivZMod q).toEquiv, Nat.card_eq_fintype_card, ZMod.card]
  rw [splitsCompletely_iff_inertia_eq_bot_and_arithFrobAt_eq_one q Q]
  refine ⟨eq_bot_iff.mpr fun σ hσ => Subgroup.mem_bot.mpr (hgen σ fun β _ => hσ β), ?_⟩
  refine hgen _ fun β hβmem => ?_
  have h1 := IsArithFrobAt.arithFrobAt ℤ Gal(↥(radicalField ℓ ({(v : ℚ)} : Finset ℚ))/ℚ) Q β
  rw [hcard] at h1
  have h2 := Ideal.add_mem Q h1 (hβq β hβmem)
  rwa [sub_add_sub_cancel] at h2

end InverseGalois.CFT
