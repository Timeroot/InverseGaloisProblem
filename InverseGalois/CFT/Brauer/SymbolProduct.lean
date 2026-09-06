/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceSymbol
import InverseGalois.CFT.Kummer.PowerCriterion
import InverseGalois.CFT.Units.OrbitPlaces

/-!
# The product formula for the power residue symbol

Let `k` be a number field containing a primitive `n`-th root of unity, with `n` prime.  Then the
`n`-th power residue symbols of a pair of units of `k`, computed in the completion at each finite
place, multiply to one over all the finite places.

The proof reads global reciprocity through a single cyclic algebra.  If the second argument is an
`n`-th power then every local symbol is already trivial.  Otherwise the polynomial `X ^ n - b` is
irreducible over `k`, and its splitting field is a cyclic extension of degree `n` presented by a
radical: the automorphism matching the chosen root of unity generates the Galois group and
multiplies the radical by that root of unity.  The invariant of the cyclic algebra with the first
argument as coefficient is then, at **every** finite place, the inverse of the local symbol.  The
archimedean invariants of a Brauer class over a totally complex field all vanish, so global
reciprocity leaves exactly the product of the local symbols.

A number field containing a primitive root of unity of order bigger than two is totally complex,
so for an odd prime the hypothesis on the field is automatic.

## Main results

* `InverseGalois.CFT.isTotallyComplex_of_isPrimitiveRoot`: a number field containing a primitive
  root of unity of order bigger than two is totally complex.
* `InverseGalois.CFT.finprod_localSymbol_eq_one`: **the power residue symbols of two units of a
  totally complex number field multiply to one over the finite places.**
* `InverseGalois.CFT.prod_localSymbol_eq_one`: the same, read over a finite set of places carrying
  the symbols.
* `InverseGalois.CFT.finprod_localSymbol_eq_one_of_ne_two`,
  `InverseGalois.CFT.prod_localSymbol_eq_one_of_ne_two`: **the product formula for an odd prime,
  with no hypothesis on the field beyond containing the roots of unity.**

## Tags

power residue symbol, Hilbert symbol, product formula, global reciprocity, cyclic algebra, radical
extension, totally complex field, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField Polynomial

/-! ### A generator of the cyclic group of order `n` -/

/-- One generates the integers modulo `n` as a group. -/
theorem forall_mem_zpowers_ofAdd_one_zmod {n : ℕ} [NeZero n] (y : Multiplicative (ZMod n)) :
    y ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod n)) := by
  refine ⟨((Multiplicative.toAdd y).val : ℤ), ?_⟩
  show Multiplicative.ofAdd (1 : ZMod n) ^ ((Multiplicative.toAdd y).val : ℤ) = y
  rw [← ofAdd_zsmul, zsmul_eq_mul, mul_one, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  rfl

/-! ### The product formula -/

section Product

variable {k : Type} [Field k] [NumberField k] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 k) → ℕ}

omit [NeZero n] in
/-- A number field containing a primitive root of unity of order bigger than two has no real
place. -/
theorem isTotallyComplex_of_isPrimitiveRoot {ζ : k} (hn : 2 < n) (hζ : IsPrimitiveRoot ζ n) :
    IsTotallyComplex k :=
  NumberField.nrRealPlaces_eq_zero_iff.mp
    (NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hn hζ)

/-- **The power residue symbols of two units of a totally complex number field multiply to one over
the finite places**, for an exponent which is prime and whose roots of unity the field contains.
An argument which is a power makes every symbol trivial; otherwise the splitting field of the
polynomial cutting out its root is a cyclic extension of prime degree presented by a radical, at
every finite place the invariant of the cyclic algebra built on the other argument is the inverse
of the symbol, and the archimedean invariants vanish, so global reciprocity is the product
formula. -/
theorem finprod_localSymbol_eq_one [IsTotallyComplex k] (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a b : kˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
          (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1 := by
  by_cases hb : ∃ y : k, y ^ n = (b : k)
  · obtain ⟨y, hy⟩ := hb
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, zero_pow (NeZero.ne n)] at hy
      exact b.ne_zero hy.symm
    have hall : ∀ v : HeightOneSpectrum (𝓞 k),
        localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
          (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1 := by
      intro v
      refine localSymbol_eq_one_of_isPow_right _ _ _ _
        ⟨Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom (Units.mk0 y hy0), ?_⟩
      rw [← map_pow]
      congr 1
      exact Units.ext hy
    calc ∏ᶠ v : HeightOneSpectrum (𝓞 k), _
        = ∏ᶠ _ : HeightOneSpectrum (𝓞 k), (1 : Multiplicative QModZ) := finprod_congr hall
      _ = 1 := finprod_one
  · push_neg at hb
    haveI : NumberField (X ^ n - C (b : k)).SplittingField := NumberField.of_module_finite k _
    have hirr : Irreducible (X ^ n - C (b : k)) := X_pow_sub_C_irreducible_of_prime hn hb
    have hprim : (primitiveRoots n k).Nonempty := ⟨ζ, (mem_primitiveRoots hn.pos).mpr hζ⟩
    haveI : IsGalois k (X ^ n - C (b : k)).SplittingField :=
      isGalois_of_isSplittingField_X_pow_sub_C hprim hirr _
    have hdegL : finrank k (X ^ n - C (b : k)).SplittingField = n :=
      finrank_of_isSplittingField_X_pow_sub_C hprim hirr _
    have hpow : (rootOfSplitsXPowSubC (NeZero.pos n) (b : k)
        (X ^ n - C (b : k)).SplittingField) ^ n
          = algebraMap k (X ^ n - C (b : k)).SplittingField (b : k) :=
      rootOfSplitsXPowSubC_pow (b : k) _
    set σ₀ := (autEquivZmod hirr (X ^ n - C (b : k)).SplittingField hζ).symm
      (Multiplicative.ofAdd (1 : ZMod n)) with hσ₀def
    have hact : σ₀ (rootOfSplitsXPowSubC (NeZero.pos n) (b : k)
        (X ^ n - C (b : k)).SplittingField)
          = algebraMap k (X ^ n - C (b : k)).SplittingField ζ *
            rootOfSplitsXPowSubC (NeZero.pos n) (b : k) (X ^ n - C (b : k)).SplittingField := by
      have h := autEquivZmod_symm_apply_natCast hirr (X ^ n - C (b : k)).SplittingField hpow hζ 1
      rw [Nat.cast_one] at h
      rw [hσ₀def, h, pow_one, Algebra.smul_def]
    have hσ₀ : ∀ x : Gal((X ^ n - C (b : k)).SplittingField/k), x ∈ Subgroup.zpowers σ₀ :=
      forall_mem_zpowers_mulEquiv
        (autEquivZmod hirr (X ^ n - C (b : k)).SplittingField hζ).symm
        forall_mem_zpowers_ofAdd_one_zmod
    have hdeg : Nat.card Gal((X ^ n - C (b : k)).SplittingField/k) = n := by
      rw [IsGalois.card_aut_eq_finrank, hdegL]
    have key : ∀ v : HeightOneSpectrum (𝓞 k),
        placeInvariant k v (cyclicBrauerHom hσ₀ a)
          = (localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
              (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
              (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
              (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b))⁻¹ := by
      intro v
      obtain ⟨w, rfl⟩ := exists_primeUnder_eq (𝓞 k) (𝓞 (X ^ n - C (b : k)).SplittingField) v
      exact placeInvariant_cyclicBrauerHom_eq_inv_localSymbol k w hn (hres _) hζ hσ₀ hdeg
        hpow hact a
    have hglob := finprod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one k
      (cyclicBrauerHom hσ₀ a)
    have hinf : ∏ u : InfinitePlace k,
        infinitePlaceInvariant k u (cyclicBrauerHom hσ₀ a) = 1 := by
      refine Finset.prod_eq_one fun u _ => ?_
      rw [infinitePlaceInvariant_of_isComplex k (IsTotallyComplex.isComplex u)]
      rfl
    rw [hinf, mul_one] at hglob
    have hstep : ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        (localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
            (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
            (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
            (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b))⁻¹ = 1 :=
      (finprod_congr fun v => (key v).symm).trans hglob
    rw [finprod_inv_distrib] at hstep
    exact inv_eq_one.mp hstep

/-- **The product formula for the power residue symbol**, read over a finite set of finite places
outside which the symbols are trivial. -/
theorem prod_localSymbol_eq_one [IsTotallyComplex k] (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a b : kˣ) (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hS : ∀ v ∉ S,
      localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1) :
    ∏ v ∈ S, localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1 := by
  have hsub : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 k) =>
      localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b)) ⊆ (S : Set _) := by
    intro v hv
    by_contra hvS
    exact hv (hS v hvS)
  rw [← finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact finprod_localSymbol_eq_one hn hres hζ a b

/-- **The product formula for the power residue symbol of odd prime exponent**: a number field
containing the roots of unity of that order is automatically totally complex. -/
theorem finprod_localSymbol_eq_one_of_ne_two (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a b : kˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
          (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1 := by
  haveI := isTotallyComplex_of_isPrimitiveRoot (lt_of_le_of_ne hn.two_le (Ne.symm hn2)) hζ
  exact finprod_localSymbol_eq_one hn hres hζ a b

/-- **The product formula for the power residue symbol of odd prime exponent**, read over a finite
set of finite places outside which the symbols are trivial. -/
theorem prod_localSymbol_eq_one_of_ne_two (hn : n.Prime) (hn2 : n ≠ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a b : kˣ) (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hS : ∀ v ∉ S,
      localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1) :
    ∏ v ∈ S, localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1 := by
  haveI := isTotallyComplex_of_isPrimitiveRoot (lt_of_le_of_ne hn.two_le (Ne.symm hn2)) hζ
  exact prod_localSymbol_eq_one hn hres hζ a b S hS

end Product

end InverseGalois.CFT
