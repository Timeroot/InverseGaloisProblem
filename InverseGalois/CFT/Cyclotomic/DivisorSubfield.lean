/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.CFT.Cyclotomic.SubfieldFrobenius

/-!
# The subfield of prescribed degree of a cyclotomic field of prime conductor

Let `q` be a prime.  The Galois group of `ℚ(ζ_q)` over `ℚ` is cyclic of order `q - 1`, identified
with `(ℤ/qℤ)ˣ` in such a way that the Frobenius at a rational prime `p ≠ q` becomes the class of
`p`.  A cyclic group of order `q - 1` has exactly one subgroup of index `d` for each divisor `d` of
`q - 1`, namely the kernel of the `((q - 1) / d)`-th power map; its fixed field is therefore a
cyclic extension of `ℚ` of degree `d` inside `ℚ(ζ_q)`.

Because the Frobenius at `p` corresponds to the class of `p`, splitting completely in that fixed
field is membership of the class of `p` in the kernel of the `((q - 1) / d)`-th power map, that is,
the congruence `p ^ ((q - 1) / d) = 1` modulo `q`.  Since `ℚ(ζ_q)` is unramified away from `q`, so
is every subfield.

The same computation carried out on a power of the Frobenius measures the local degree and not
merely its triviality: the decomposition group at a prime above `p` has order dividing `m` exactly
when `p ^ (m * ((q - 1) / d)) = 1` modulo `q`.

## Main results

* `InverseGalois.CFT.exists_intermediateField_finrank_eq_and_splitsCompletely`: for a prime `q` and
  a nonzero divisor `d` of `q - 1`, the cyclotomic field `ℚ(ζ_q)` contains a cyclic extension of
  `ℚ` of degree `d`, unramified outside `q`, in which a rational prime `p ≠ q` splits completely
  precisely when `p ^ ((q - 1) / d) = 1` in `ZMod q`, and whose decomposition group at a prime
  above `p` has order dividing `m` precisely when `p ^ (m * ((q - 1) / d)) = 1` in `ZMod q`.
* `InverseGalois.CFT.exists_intermediateField_finrank_eq_pow_and_splitsCompletely`: the same
  statement for the prime-power degree `d = ℓ ^ e`.
-/

set_option synthInstance.maxHeartbeats 1000000

open NumberField IsCyclotomicExtension InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

attribute [local instance] Int.ideal_span_isMaximal_of_prime

/-- **The subfield of prescribed degree of a cyclotomic field of prime conductor, and its
splitting law.**  Let `q` be a prime and let `d` be a nonzero divisor of `q - 1`.  The kernel of
the `((q - 1) / d)`-th power map on `(ℤ/qℤ)ˣ ≃ Gal(ℚ(ζ_q)/ℚ)` is a subgroup of index `d`, so its
fixed field `F` is a cyclic extension of `ℚ` of degree `d`.  A rational prime `p ≠ q` splits
completely in `F` exactly when its Frobenius lies in that kernel, that is, exactly when
`p ^ ((q - 1) / d) = 1` in `ZMod q`; the same computation on the `m`-th power of the Frobenius
reads off the order of the decomposition group at a prime above `p`; and `F` is unramified at every
prime not above `q`. -/
theorem exists_intermediateField_finrank_eq_and_splitsCompletely (q : ℕ) [hq : Fact q.Prime]
    {d : ℕ} (hd : d ≠ 0) (hdvd : d ∣ q - 1) (E : Type*) [Field E] [NumberField E]
    [IsCyclotomicExtension {q} ℚ E] :
    ∃ F : IntermediateField ℚ E, Module.finrank ℚ F = d ∧ IsGalois ℚ F ∧
      IsCyclic Gal(F/ℚ) ∧
      (∀ p : ℕ, p.Prime → p ≠ q →
        (SplitsCompletely F p ↔ (p : ZMod q) ^ ((q - 1) / d) = 1)) ∧
      (∀ (p : ℕ), p.Prime → p ≠ q → ∀ (P : Ideal (𝓞 F)) (_ : P.IsPrime)
        (_ : P.LiesOver (Ideal.span {(p : ℤ)})) (m : ℕ),
          (Nat.card ↥(MulAction.stabilizer Gal(F/ℚ) P) ∣ m ↔
            (p : ZMod q) ^ (m * ((q - 1) / d)) = 1)) ∧
      (∀ (Q : Ideal (𝓞 F)) [Q.IsPrime], Q ≠ ⊥ → (q : 𝓞 F) ∉ Q →
        Algebra.IsUnramifiedAt ℤ Q) := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {q} ℚ E
  haveI : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime hq.out
  haveI : IsCyclic Gal(E/ℚ) :=
    isCyclic_of_surjective (Rat.galEquivZMod q E).symm (Rat.galEquivZMod q E).symm.surjective
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq.out]
  have hq1 : q - 1 ≠ 0 := by
    have := hq.out.two_le
    omega
  have hmne : (q - 1) / d ≠ 0 := Nat.div_ne_zero_iff_of_dvd hdvd |>.mpr ⟨hq1, hd⟩
  have hmdvd : (q - 1) / d ∣ q - 1 := Nat.div_dvd_of_dvd hdvd
  set H := Subgroup.comap (Rat.galEquivZMod q E).toMonoidHom
    (MonoidHom.ker (powMonoidHom ((q - 1) / d) : (ZMod q)ˣ →* (ZMod q)ˣ)) with hH
  haveI : H.Normal := Subgroup.Normal.comap (MonoidHom.normal_ker _) _
  have hindex : H.index = d := by
    rw [hH, Subgroup.index_comap_of_surjective (f := (Rat.galEquivZMod q E).toMonoidHom) _
        (Rat.galEquivZMod q E).surjective,
      Subgroup.index_ker, card_range_powMonoidHom hmne (hcard ▸ hmdvd), hcard,
      Nat.div_div_self hdvd hq1]
  have hrank : Module.finrank ℚ ↥(IntermediateField.fixedField H) = d := by
    rw [finrank_fixedField_eq_index, hindex]
  -- unramifiedness away from `q`, inherited from the cyclotomic field
  have hunram : ∀ (Q : Ideal (𝓞 ↥(IntermediateField.fixedField H))) [Q.IsPrime], Q ≠ ⊥ →
      (q : 𝓞 ↥(IntermediateField.fixedField H)) ∉ Q → Algebra.IsUnramifiedAt ℤ Q := by
    intro Q _ hQ hqQ
    refine isUnramifiedAt_of_forall_prime_not_dvd_of_algebra q E Q hQ fun r hr hrQ hrdvd => ?_
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hq.out).mp hrdvd
    exact hqQ hrQ
  -- the Galois group of the fixed field is a quotient of the cyclic group `Gal(E/ℚ)`
  have hcyc : IsCyclic Gal(↥(IntermediateField.fixedField H)/ℚ) :=
    isCyclic_of_surjective
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := E) ↥(IntermediateField.fixedField H))
      (AlgEquiv.restrictNormalHom_surjective _)
  haveI : IsGalois ℚ ↥(IntermediateField.fixedField H) := inferInstance
  -- a prime of the cyclotomic field away from `q` is unramified
  have hunrE : ∀ (p : ℕ), p.Prime → ¬ p ∣ q → ∀ (P : Ideal (𝓞 E)) (_ : P.IsPrime)
      (_ : P.LiesOver (Ideal.span {(p : ℤ)})), Algebra.IsUnramifiedAt ℤ P := by
    intro p hp hpn P _ _
    haveI : Fact p.Prime := ⟨hp⟩
    have hPne : P ≠ ⊥ := ne_bot_of_liesOver p P
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ) hPne,
      ← Ideal.over_def P (Ideal.span {(p : ℤ)})]
    exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p E P hpn
  refine ⟨IntermediateField.fixedField H, hrank, inferInstance, hcyc, ?_, ?_, hunram⟩
  · -- the splitting law
    intro p hp hpq
    haveI : Fact p.Prime := ⟨hp⟩
    have hpn : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq.out).mp h)
    obtain ⟨⟨P, hP⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)))
    haveI : P.IsPrime := hP.1
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
    haveI : Finite (𝓞 E ⧸ P) := finite_quotient_of_ne_bot P (ne_bot_of_liesOver p P)
    rw [splitsCompletely_intermediateField_iff_mem_fixingSubgroup _ p P (hunrE p hp hpn P ‹_› ‹_›),
      IntermediateField.fixingSubgroup_fixedField, hH, Subgroup.mem_comap, MonoidHom.mem_ker,
      MulEquiv.coe_toMonoidHom,
      galEquivZMod_arithFrobAt q E hp hpn P (Ideal.over_def P (Ideal.span {(p : ℤ)})).symm,
      powMonoidHom_apply, ← Units.val_eq_one, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  · -- the order of the decomposition group
    intro p hp hpq Q hQ hQo m
    haveI : Fact p.Prime := ⟨hp⟩
    haveI := hQ
    haveI := hQo
    have hpn : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq.out).mp h)
    obtain ⟨⟨P, hP⟩⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 E)))
    haveI : P.IsPrime := hP.1
    haveI : P.LiesOver Q := hP.2
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P Q (Ideal.span {(p : ℤ)})
    haveI : Finite (𝓞 E ⧸ P) := finite_quotient_of_ne_bot P (ne_bot_of_liesOver p P)
    have hunder : P.under (𝓞 ↥(IntermediateField.fixedField H)) = Q :=
      (Ideal.LiesOver.over (p := Q)).symm
    rw [← hunder,
      card_stabilizer_under_dvd_iff_mem_fixingSubgroup _ p P (hunrE p hp hpn P ‹_› ‹_›),
      IntermediateField.fixingSubgroup_fixedField, hH, Subgroup.mem_comap, MonoidHom.mem_ker,
      MulEquiv.coe_toMonoidHom, map_pow,
      galEquivZMod_arithFrobAt q E hp hpn P (Ideal.over_def P (Ideal.span {(p : ℤ)})).symm,
      powMonoidHom_apply, ← pow_mul, ← Units.val_eq_one, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime]

/-- **The subfield of prime-power degree of a cyclotomic field of prime conductor.**  For a prime
`q` and a prime power `ℓ ^ e` dividing `q - 1`, the cyclotomic field `ℚ(ζ_q)` contains a cyclic
extension of `ℚ` of degree `ℓ ^ e`, unramified outside `q`, in which a rational prime `p ≠ q`
splits completely exactly when `p ^ ((q - 1) / ℓ ^ e) = 1` in `ZMod q`. -/
theorem exists_intermediateField_finrank_eq_pow_and_splitsCompletely (q : ℕ) [Fact q.Prime]
    {ℓ e : ℕ} (hℓ : ℓ.Prime) (hdvd : ℓ ^ e ∣ q - 1) (E : Type*) [Field E] [NumberField E]
    [IsCyclotomicExtension {q} ℚ E] :
    ∃ F : IntermediateField ℚ E, Module.finrank ℚ F = ℓ ^ e ∧ IsGalois ℚ F ∧
      IsCyclic Gal(F/ℚ) ∧
      (∀ p : ℕ, p.Prime → p ≠ q →
        (SplitsCompletely F p ↔ (p : ZMod q) ^ ((q - 1) / ℓ ^ e) = 1)) ∧
      (∀ (Q : Ideal (𝓞 F)) [Q.IsPrime], Q ≠ ⊥ → (q : 𝓞 F) ∉ Q →
        Algebra.IsUnramifiedAt ℤ Q) := by
  obtain ⟨F, hrank, hgal, hcyc, hsplit, -, hunram⟩ :=
    exists_intermediateField_finrank_eq_and_splitsCompletely q (pow_ne_zero e hℓ.ne_zero) hdvd E
  exact ⟨F, hrank, hgal, hcyc, hsplit, hunram⟩

end InverseGalois.CFT
