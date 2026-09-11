/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RealCyclicSign
import InverseGalois.CFT.Brauer.RealPlace
import InverseGalois.CFT.Brauer.RealSymbolProduct

/-!
# The symbol at a real place and the product formula over all the places

The Brauer group of the reals has order two, so a real place of a number field carries a symbol of
its own: the pairing which sends a pair of real units to the class of one half exactly when both
are negative.  It is the invariant of the quaternion algebra on the two units, and it is the
archimedean companion of the power residue symbol at the finite places.

Global reciprocity says the invariants of a Brauer class add up to zero over **all** the places, so
the product formula for the power residue symbol holds only after the archimedean places have been
accounted for.  Over a totally complex field they contribute nothing.  Over a field with a real
place the exponent is forced to be two, and the archimedean contribution is exactly the symbol
described above: the cyclic algebra presenting the symbol is split at the place when the second
argument is positive there, because a square root of it is then real, and otherwise the splitting
field has no real embedding over the place, so restriction identifies its Galois group with the
Galois group of the complex numbers over the reals and the invariant becomes the sign of the first
argument.

## Main definitions

* `InverseGalois.CFT.realSymbol`: the symbol of a pair of real units, the class of one half when
  both are negative and zero otherwise.
* `InverseGalois.CFT.archSymbol`: the symbol at an infinite place of a number field, read through
  the real embedding at a real place and trivial at a complex place.

## Main results

* `InverseGalois.CFT.realSymbol_of_neg_right`, `InverseGalois.CFT.realSymbol_of_pos_right`: the
  symbol is the sign of the first argument when the second is negative, and trivial when it is
  positive.
* `InverseGalois.CFT.baseChangeHom_cyclicBrauerHom_real_of_isEmpty`: **base change to the reals
  carries a cyclic algebra whose splitting field is a quadratic extension with no real embedding
  over the base to the cyclic algebra over the reals with the same coefficient.**
* `InverseGalois.CFT.infinitePlaceInvariant_cyclicBrauerHom_of_forall_ne`: **the invariant of such
  an algebra at a real place is the sign of the coefficient there.**
* `InverseGalois.CFT.finprod_localSymbol_mul_prod_archSymbol_eq_one`: **the product formula over
  all the places** — the power residue symbols of two units at the finite places, multiplied by
  the symbols at the infinite places, give one.
* `InverseGalois.CFT.prod_localSymbol_mul_prod_archSymbol_eq_one`: the same, read over a finite set
  of finite places carrying the symbols.

## Tags

Hilbert symbol, real place, product formula, global reciprocity, cyclic algebra, quaternion
algebra, sign, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField Polynomial

/-! ### The symbol of a pair of real units -/

theorem toAdd_realSign_mul (a b : ℝˣ) :
    Multiplicative.toAdd (realSign (a * b))
      = Multiplicative.toAdd (realSign a) + Multiplicative.toAdd (realSign b) :=
  congrArg Multiplicative.toAdd (map_mul realSign a b)

/-- **The symbol of a pair of real units**, the product of their signs read in the group of order
two inside the rationals modulo the integers.  It is the class of one half exactly when both units
are negative. -/
noncomputable def realSymbol (a b : ℝˣ) : Multiplicative QModZ :=
  Multiplicative.ofAdd
    (zmodQModZ 2 (Multiplicative.toAdd (realSign a) * Multiplicative.toAdd (realSign b)))

theorem realSymbol_mul_left (a₁ a₂ b : ℝˣ) :
    realSymbol (a₁ * a₂) b = realSymbol a₁ b * realSymbol a₂ b := by
  simp only [realSymbol]
  rw [toAdd_realSign_mul, add_mul, map_add, ofAdd_add]

theorem realSymbol_mul_right (a b₁ b₂ : ℝˣ) :
    realSymbol a (b₁ * b₂) = realSymbol a b₁ * realSymbol a b₂ := by
  simp only [realSymbol]
  rw [toAdd_realSign_mul, mul_add, map_add, ofAdd_add]

/-- The symbol of a pair of real units is symmetric. -/
theorem realSymbol_comm (a b : ℝˣ) : realSymbol a b = realSymbol b a := by
  show Multiplicative.ofAdd (zmodQModZ 2 (_ * _)) = Multiplicative.ofAdd (zmodQModZ 2 (_ * _))
  rw [mul_comm]

/-- The symbol of a pair of real units has order dividing two. -/
theorem realSymbol_sq (a b : ℝˣ) : realSymbol a b ^ 2 = 1 := by
  have hz : ∀ z : ZMod 2, z + z = 0 := by decide
  show Multiplicative.ofAdd (zmodQModZ 2
    (Multiplicative.toAdd (realSign a) * Multiplicative.toAdd (realSign b))) ^ 2 = 1
  rw [sq, ← ofAdd_add, ← map_add, hz, map_zero]
  rfl

/-- **The sign of a real unit, read in the rationals modulo the integers, is the invariant of the
cyclic algebra it presents over the reals.** -/
theorem ofAdd_zmodQModZ_toAdd_realSign (a : ℝˣ) :
    Multiplicative.ofAdd (zmodQModZ 2 (Multiplicative.toAdd (realSign a)))
      = realCyclicInvariant a := by
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha
  · have hs : Multiplicative.toAdd (realSign a) = (1 : ZMod 2) := by
      rw [realSign_of_neg ha]
      rfl
    have h1 : zmodQModZ 2 (1 : ZMod 2) = QuotientAddGroup.mk (1 / 2 : ℚ) := by
      have h := zmodQModZ_intCast 2 1
      rw [Int.cast_one] at h
      rw [h]
      norm_num
    rw [hs, h1]
    refine (eq_ofAdd_half_of_sq_eq_one (realCyclicInvariant_sq a) ?_).symm
    rw [Ne, realCyclicInvariant_eq_one_iff]
    exact not_lt.mpr ha.le
  · have hs : Multiplicative.toAdd (realSign a) = (0 : ZMod 2) := by
      rw [realSign_of_pos ha]
      rfl
    rw [hs, map_zero, (realCyclicInvariant_eq_one_iff a).mpr ha]
    rfl

/-- The symbol of a pair of real units whose second member is negative is the sign of the first. -/
theorem realSymbol_of_neg_right (a : ℝˣ) {b : ℝˣ} (hb : (b : ℝ) < 0) :
    realSymbol a b = realCyclicInvariant a := by
  have hs : Multiplicative.toAdd (realSign b) = (1 : ZMod 2) := by
    rw [realSign_of_neg hb]
    rfl
  show Multiplicative.ofAdd
    (zmodQModZ 2 (Multiplicative.toAdd (realSign a) * Multiplicative.toAdd (realSign b))) = _
  rw [hs, mul_one]
  exact ofAdd_zmodQModZ_toAdd_realSign a

/-- The symbol of a pair of real units whose second member is positive is trivial. -/
theorem realSymbol_of_pos_right (a : ℝˣ) {b : ℝˣ} (hb : 0 < (b : ℝ)) : realSymbol a b = 1 := by
  have hs : Multiplicative.toAdd (realSign b) = (0 : ZMod 2) := by
    rw [realSign_of_pos hb]
    rfl
  show Multiplicative.ofAdd
    (zmodQModZ 2 (Multiplicative.toAdd (realSign a) * Multiplicative.toAdd (realSign b))) = 1
  rw [hs, mul_zero, map_zero]
  rfl

/-! ### The symbol at an infinite place -/

section Arch

variable (k : Type) [Field k] [NumberField k]

open Classical in
/-- **The symbol at an infinite place of a number field.**  At a real place it is the symbol of the
two arguments read through the associated real embedding, and at a complex place it is trivial. -/
noncomputable def archSymbol (u : InfinitePlace k) (a b : kˣ) : Multiplicative QModZ :=
  if hu : u.IsReal then
    realSymbol (Units.map (InfinitePlace.embedding_of_isReal hu).toMonoidHom a)
      (Units.map (InfinitePlace.embedding_of_isReal hu).toMonoidHom b)
  else 1

omit [NumberField k] in
/-- At a real place the symbol is the symbol of the real embeddings of the arguments. -/
theorem archSymbol_of_isReal {u : InfinitePlace k} (hu : u.IsReal) (a b : kˣ) :
    archSymbol k u a b
      = realSymbol (Units.map (InfinitePlace.embedding_of_isReal hu).toMonoidHom a)
        (Units.map (InfinitePlace.embedding_of_isReal hu).toMonoidHom b) := by
  simp only [archSymbol, dif_pos hu]

omit [NumberField k] in
/-- At a complex place the symbol is trivial. -/
theorem archSymbol_of_isComplex {u : InfinitePlace k} (hu : u.IsComplex) (a b : kˣ) :
    archSymbol k u a b = 1 := by
  simp only [archSymbol, dif_neg (InfinitePlace.not_isReal_iff_isComplex.mpr hu)]

omit [NumberField k] in
/-- The symbol at an infinite place has order dividing two. -/
theorem archSymbol_sq (u : InfinitePlace k) (a b : kˣ) : archSymbol k u a b ^ 2 = 1 := by
  rcases u.isReal_or_isComplex with hu | hu
  · rw [archSymbol_of_isReal k hu]
    exact realSymbol_sq _ _
  · rw [archSymbol_of_isComplex k hu, one_pow]

/-- The product of the symbols over the infinite places has order dividing two. -/
theorem prod_archSymbol_sq (a b : kˣ) : (∏ u : InfinitePlace k, archSymbol k u a b) ^ 2 = 1 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one fun u _ => archSymbol_sq k u a b

end Arch

/-! ### Base change of a cyclic algebra to the reals -/

section Compositum

variable {k E : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
  [IsGalois k E] [Algebra k ℝ]

/-- **Base change to the reals carries a cyclic algebra over a number field whose splitting field
is a quadratic extension admitting no real embedding over the base to the cyclic algebra over the
reals with the same coefficient.**  The splitting field embeds into the complex numbers over the
given real embedding of the base, and that embedding is not real, so restricting an automorphism of
the complex numbers over the reals to the splitting field is an injection of a group of order two
into a group of order two, hence a bijection carrying complex conjugation to the chosen generator.
Base change along a field that is not intermediate then keeps the coefficient. -/
theorem baseChangeHom_cyclicBrauerHom_real_of_isEmpty (hdeg : finrank k E = 2)
    (hno : IsEmpty (E →ₐ[k] ℝ)) {σ₀ : Gal(E/k)}
    (hσ₀ : ∀ x : Gal(E/k), x ∈ Subgroup.zpowers σ₀) (a : kˣ) :
    BrauerGroup.baseChangeHom ℝ (cyclicBrauerHom hσ₀ a)
      = cyclicBrauerHom forall_mem_zpowers_conjAe (Units.map (algebraMap k ℝ).toMonoidHom a) := by
  letI : Algebra k ℂ := ((algebraMap ℝ ℂ).comp (algebraMap k ℝ)).toAlgebra
  haveI : IsScalarTower k ℝ ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic k E := Algebra.IsAlgebraic.of_finite k E
  let φ : E →ₐ[k] ℂ := IsAlgClosed.lift
  letI : Algebra E ℂ := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k E ℂ := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  let f : Gal(ℂ/ℝ) →* Gal(E/k) :=
    (AlgEquiv.restrictNormalHom E).comp
      { toFun := fun σ => σ.restrictScalars k
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
  have he : ∀ (σ : Gal(ℂ/ℝ)) (x : E), σ (algebraMap E ℂ x) = algebraMap E ℂ (f σ x) :=
    fun σ x => (AlgEquiv.restrictNormal_commutes (σ.restrictScalars k) E x).symm
  have hconj : f Complex.conjAe ≠ 1 := by
    intro h
    have hreal : ComplexEmbedding.IsReal (φ : E →+* ℂ) :=
      ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun x => by
        have hx := he Complex.conjAe x
        rw [h, AlgEquiv.one_apply] at hx
        exact hx)
    have hcom : ∀ x : k, hreal.embedding (algebraMap k E x) = algebraMap k ℝ x := by
      intro x
      refine Complex.ofReal_injective ?_
      rw [ComplexEmbedding.IsReal.coe_embedding_apply]
      show φ (algebraMap k E x) = _
      rw [φ.commutes, IsScalarTower.algebraMap_apply k ℝ ℂ, Complex.coe_algebraMap]
    exact hno.elim (AlgHom.mk hreal.embedding hcom)
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr fun σ hσ => ?_
    rcases eq_one_or_eq_conjAe σ with h | h
    · exact h
    · rw [h] at hσ
      exact absurd hσ hconj
  have hσ₀ne : σ₀ ≠ 1 := by
    intro h
    refine hconj ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hσ₀ (f Complex.conjAe))
    rw [← hm, h, one_zpow]
  have hcard : Nat.card Gal(E/k) = 2 := by rw [IsGalois.card_aut_eq_finrank k E, hdeg]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Gal(E/k))).mp hcard
  have hgen : f Complex.conjAe = σ₀ := (hy _ hconj).trans (hy _ hσ₀ne).symm
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hσ₀ z)
    exact ⟨Complex.conjAe ^ m, by rw [map_zpow, hgen, hm]⟩
  exact baseChangeHom_cyclicBrauerHom_compositum (e := MulEquiv.ofBijective f ⟨hinj, hsurj⟩) hσ₀
    forall_mem_zpowers_conjAe hgen he a

end Compositum

/-! ### The invariant at a real place -/

section Place

variable {k E : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
  [IsGalois k E]

/-- **The invariant at a real place of a cyclic algebra whose splitting field is a quadratic
extension admitting no real embedding over the place is the sign of the coefficient there.**  The
completion at the place is the reals along the associated embedding, and base change there keeps
the coefficient. -/
theorem infinitePlaceInvariant_cyclicBrauerHom_of_forall_ne (hdeg : finrank k E = 2)
    {σ₀ : Gal(E/k)} (hσ₀ : ∀ x : Gal(E/k), x ∈ Subgroup.zpowers σ₀) {u : InfinitePlace k}
    (hu : u.IsReal)
    (hno : ∀ ψ : E →+* ℝ,
      ψ.comp (algebraMap k E) ≠ (InfinitePlace.embedding_of_isReal hu : k →+* ℝ))
    (a : kˣ) :
    infinitePlaceInvariant k u (cyclicBrauerHom hσ₀ a)
      = realCyclicInvariant
          (Units.map (InfinitePlace.embedding_of_isReal hu).toMonoidHom a) := by
  letI : Algebra k ℝ := (InfinitePlace.embedding_of_isReal hu).toAlgebra
  have hempty : IsEmpty (E →ₐ[k] ℝ) :=
    ⟨fun ψ => hno ψ.toRingHom (RingHom.ext fun x => ψ.commutes x)⟩
  rw [infinitePlaceInvariant_of_isReal k hu]
  show realEmbeddingInvariant k (cyclicBrauerHom hσ₀ a) = _
  rw [realEmbeddingInvariant_apply,
    baseChangeHom_cyclicBrauerHom_real_of_isEmpty hdeg hempty hσ₀ a]
  rfl

end Place

/-! ### The product formula over all the places -/

section Product

variable {k : Type} [Field k] [NumberField k] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 k) → ℕ}

/-- **The product formula for the symbol over all the places of a number field**: the power residue
symbols of two units at the finite places, multiplied by the symbols at the infinite places, give
one.  A field carrying a real place forces the exponent to be two, because a field containing the
roots of unity of any bigger order is totally complex.  At such a place the radical extension
presenting the cyclic algebra embeds into the reals when the second argument is positive there, so
the invariant vanishes and so does the symbol; and when the second argument is negative there the
extension has no real embedding, so the invariant is the sign of the first argument, which is again
the symbol.  Global reciprocity is then exactly the product formula. -/
theorem finprod_localSymbol_mul_prod_archSymbol_eq_one (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a b : kˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 k),
        localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
          (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
          (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b)) *
        ∏ u : InfinitePlace k, archSymbol k u a b = 1 := by
  have hreal2 : ∀ u : InfinitePlace k, u.IsReal → n = 2 := by
    intro u hu
    by_contra hne
    haveI := isTotallyComplex_of_isPrimitiveRoot (lt_of_le_of_ne hn.two_le (Ne.symm hne)) hζ
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex u)) hu
  have hbne : ∀ (u : InfinitePlace k) (hu : u.IsReal),
      InfinitePlace.embedding_of_isReal hu (b : k) ≠ 0 := by
    intro u hu h
    exact b.ne_zero ((InfinitePlace.embedding_of_isReal hu).injective (by rw [h, map_zero]))
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
    have harch : ∀ u : InfinitePlace k, archSymbol k u a b = 1 := by
      intro u
      rcases u.isReal_or_isComplex with hu | hu
      · rw [archSymbol_of_isReal k hu]
        have hyne : InfinitePlace.embedding_of_isReal hu y ≠ 0 := fun h =>
          hy0 ((InfinitePlace.embedding_of_isReal hu).injective (by rw [h, map_zero]))
        have hbv : InfinitePlace.embedding_of_isReal hu (b : k)
            = InfinitePlace.embedding_of_isReal hu y ^ 2 := by
          rw [← hy, map_pow, hreal2 u hu]
        refine realSymbol_of_pos_right _ ?_
        show (0 : ℝ) < InfinitePlace.embedding_of_isReal hu (b : k)
        rw [hbv]
        exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hyne))
      · rw [archSymbol_of_isComplex k hu]
    rw [finprod_congr hall, finprod_one,
      Finset.prod_congr rfl fun u _ => harch u, Finset.prod_const_one, one_mul]
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
    have hinf : ∀ u : InfinitePlace k,
        infinitePlaceInvariant k u (cyclicBrauerHom hσ₀ a) = archSymbol k u a b := by
      intro u
      rcases u.isReal_or_isComplex with hu | hu
      · have hn2 := hreal2 u hu
        rw [archSymbol_of_isReal k hu]
        rcases lt_or_gt_of_ne (hbne u hu) with hneg | hpos
        · have hnegu : ((Units.map (InfinitePlace.embedding_of_isReal hu).toMonoidHom b :
              ℝˣ) : ℝ) < 0 := hneg
          rw [realSymbol_of_neg_right _ hnegu]
          refine infinitePlaceInvariant_cyclicBrauerHom_of_forall_ne ?_ hσ₀ hu ?_ a
          · rw [hdegL, hn2]
          · intro ψ hψ
            have hex : ∃ x : ℝ, x ^ n = InfinitePlace.embedding_of_isReal hu (b : k) :=
              ⟨ψ (rootOfSplitsXPowSubC (NeZero.pos n) (b : k)
                (X ^ n - C (b : k)).SplittingField), by
                  rw [← _root_.map_pow, hpow, ← RingHom.comp_apply, hψ]⟩
            obtain ⟨x, hx⟩ := hex
            rw [hn2] at hx
            exact absurd hx.symm (ne_of_lt (lt_of_lt_of_le hneg (sq_nonneg x)))
        · have hposu : (0 : ℝ) < ((Units.map (InfinitePlace.embedding_of_isReal hu).toMonoidHom b :
              ℝˣ) : ℝ) := hpos
          rw [realSymbol_of_pos_right _ hposu]
          letI : Algebra k ℝ := (InfinitePlace.embedding_of_isReal hu).toAlgebra
          have hsplit : Splits (((X ^ n - C (b : k)) : k[X]).map (algebraMap k ℝ)) := by
            rw [hn2, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
            exact splits_X_pow_two_sub_C_of_nonneg hpos.le
          exact infinitePlaceInvariant_eq_one_of_algHom_real hu rfl
            (IsSplittingField.lift (X ^ n - C (b : k)).SplittingField _ hsplit)
            (cyclicBrauerHom_mem_relative hσ₀ a)
      · rw [infinitePlaceInvariant_of_isComplex k hu, MonoidHom.one_apply,
          archSymbol_of_isComplex k hu]
    have harchprod : ∏ u : InfinitePlace k, archSymbol k u a b
        = ∏ u : InfinitePlace k, infinitePlaceInvariant k u (cyclicBrauerHom hσ₀ a) :=
      Finset.prod_congr rfl fun u _ => (hinf u).symm
    have hglob := finprod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one k
      (cyclicBrauerHom hσ₀ a)
    have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v (cyclicBrauerHom hσ₀ a)
        = (∏ᶠ v : HeightOneSpectrum (𝓞 k),
            localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
              (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
              (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
              (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b))⁻¹ := by
      rw [← finprod_inv_distrib]
      exact finprod_congr key
    rw [hfin] at hglob
    rw [inv_mul_eq_one.mp hglob, ← harchprod, ← sq]
    exact prod_archSymbol_sq k a b

/-- **The product formula for the symbol over all the places**, read over a finite set of finite
places outside which the power residue symbols are trivial. -/
theorem prod_localSymbol_mul_prod_archSymbol_eq_one (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), HasResidueChar (v.adicCompletion k) (P v) (E v))
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (a b : kˣ) (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hS : ∀ v ∉ S,
      localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b) = 1) :
    (∏ v ∈ S, localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b)) *
        ∏ u : InfinitePlace k, archSymbol k u a b = 1 := by
  have hsub : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 k) =>
      localSymbol (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
        (hζ.map_of_injective (algebraMap k (v.adicCompletion k)).injective)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom a)
        (Units.map (algebraMap k (v.adicCompletion k)).toMonoidHom b)) ⊆ (S : Set _) := by
    intro v hv
    by_contra hvS
    exact hv (hS v hvS)
  rw [← finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact finprod_localSymbol_mul_prod_archSymbol_eq_one hn hres hζ a b

end Product

end InverseGalois.CFT
