/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.Kummer.RootIndex
import InverseGalois.CFT.Kummer.Unramified
import InverseGalois.CFT.Units.NormIndex
import InverseGalois.CFT.Units.SplitPowNorm

/-!
# A local criterion for being a global power

Let `K` be a number field containing a primitive `p`-th root of unity, let `S` be a finite set of
places large enough to carry the ideal classes and every prime above `p`, and let `T` be a finite
set of auxiliary places disjoint from `S` at which the `S`-units surject onto the local units modulo
`p`-th powers.  An element of `K` which is a `p`-th power in every completion at an infinite place
and at every place of `S`, and which is a unit outside `S` and `T`, is a `p`-th power in `K`.

Were it not, the polynomial `X ^ p - b` would be irreducible, and its splitting field a cyclic
extension of degree `p` which splits completely at the infinite places and at the places of `S`, and
is unramified outside `S` and `T`: the decomposition group at a place fixes the radical exactly when
the radicand is a local `p`-th power there, and the radical generates.  Every idele which is a local
`p`-th power at the places of `T` and a unit outside the two sets is then a norm from that
extension, and together with the principal ideles those ideles are everything.  The first inequality
bounds the degree of the extension by one, which contradicts its being `p`.

## Main results

* `InverseGalois.CFT.subsingleton_gal_of_forall_localPow`: **a cyclic radical extension of degree
  `p` whose radicand is a local `p`-th power at the infinite places and at the places of the first
  set, and a unit outside the two sets, is trivial.**
* `InverseGalois.CFT.exists_pow_eq_of_forall_localPow`: **an element of a number field which is a
  `p`-th power in the completion at every infinite place and at every place of the first set, and a
  unit outside the two sets, is a `p`-th power.**

## Tags

number field, class field theory, second inequality, Kummer theory, local-global, power
-/

namespace InverseGalois.CFT

open IsDedekindDomain IntermediateField MulAction NumberField Polynomial Rigidity.RET

/-! ### The extension cut out by a radical is trivial -/

section Trivial

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic Gal(L/K)] {p : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **A cyclic radical extension of degree `p` whose radicand is a local `p`-th power at the
infinite places and at the places of the first set, and a unit outside the two sets, is trivial.**
The decomposition group at such a place fixes the radical, and the radical generates the extension,
so the extension splits completely there; outside the two sets it is unramified.  Every idele which
is a local `p`-th power at the auxiliary places and a unit outside is therefore a norm, and those
ideles together with the principal ones exhaust the ideles, so the first inequality bounds the
degree by one. -/
theorem subsingleton_gal_of_forall_localPow (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hdeg : Module.finrank K L = p) {S T : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (hT : T.Finite) (hTS : ∀ v ∈ T, v ∉ S)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ S, ord K v (a : K) = m v)
    (hsurj : ∀ c : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ,
      (∀ v ∈ T, Valued.v ((c v : v.adicCompletion K)) = 1) →
      ∃ u : Kˣ, u ∈ sUnits K S ∧ ∀ v ∈ T, ∃ z : (v.adicCompletion K)ˣ,
        adicUnitHom v u = c v * z ^ p)
    {b : K} {β : L} (hβ : β ^ p = algebraMap K L b)
    (hgenβ : IntermediateField.adjoin K ({β} : Set L) = ⊤)
    (hbinf : ∀ w : InfinitePlace K, ∃ c : w.Completion, c ^ p = algebraMap K w.Completion b)
    (hbS : ∀ v ∈ S, ∃ c : v.adicCompletion K, c ^ p = algebraMap K (v.adicCompletion K) b)
    (hbunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → v.valuation K b = 1) :
    Subsingleton Gal(L/K) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨σ, hσgen⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have hcard : Nat.card Gal(L/K) = p := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  have hone : ∀ g : Gal(L/K), g β = β → g = 1 := by
    intro g hg
    have hmem : g ∈ (K⟮β⟯ : IntermediateField K L).fixingSubgroup := by
      rw [fixingSubgroup_adjoin_simple_eq_stabilizer]
      exact hg
    rw [hgenβ] at hmem
    exact AlgEquiv.ext fun x => hmem ⟨x, IntermediateField.mem_top⟩
  have hsplitInf : ∀ w : InfinitePlace L, stabilizer Gal(L/K) w = ⊥ := fun w =>
    (Subgroup.eq_bot_iff_forall _).mpr fun g hg => hone g
      ((forall_stabilizer_smul_eq_iff_exists_pow_infinite w hζ hp.ne_zero hβ.symm).mpr
        (hbinf _) ⟨g, hg⟩)
  have hsplitS : ∀ v : HeightOneSpectrum (𝓞 L), primeUnder (𝓞 K) v ∈ S →
      stabilizer Gal(L/K) v = ⊥ := fun v hv =>
    (Subgroup.eq_bot_iff_forall _).mpr fun g hg => hone g
      ((forall_stabilizer_smul_eq_iff_exists_pow v hζ hp.ne_zero hβ.symm).mpr
        (hbS _ hv) ⟨g, hg⟩)
  have hunram : ∀ v : HeightOneSpectrum (𝓞 L), primeUnder (𝓞 K) v ∉ S →
      primeUnder (𝓞 K) v ∉ T → Algebra.IsUnramifiedAt (𝓞 K) v.asIdeal := by
    intro v hvS hvT
    refine isUnramifiedAt_of_radicals hp hζ (α := fun _ : Unit => β) (a := fun _ => b)
      (fun _ => hβ) (by rwa [Set.range_const]) ?_ fun _ => hbunit _ hvS hvT
    intro hmem
    refine hvS (hpS _ ?_)
    rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  have hnorm : splitPowIdele K S T p ≤ (ideleNorm K L).range :=
    splitPowIdele_le_range_ideleNorm hσgen hcard hS hT (by rw [hcard]) hsplitInf hsplitS hunram
  have htop : (ideleDiag K).range ⊔ splitPowIdele K S T p = ⊤ :=
    ideleDiag_range_sup_splitPowIdele_eq_top hTS hrepr hsurj
  refine subsingleton_gal_of_ideleDiag_sup_ideleNorm_eq_top hcard hσgen ?_
  rw [eq_top_iff, ← htop]
  exact sup_le_sup_left hnorm _

end Trivial

/-! ### The criterion -/

section Criterion

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **An element of a number field which is a `p`-th power in the completion at every infinite place
and at every place of the first set, and a unit outside the two sets, is a `p`-th power.**  Were it
not, the polynomial `X ^ p - b` would be irreducible and its splitting field a cyclic extension of
degree `p` cut out by a radical, which the local hypotheses force to be trivial. -/
theorem exists_pow_eq_of_forall_localPow (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {S T : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) (hT : T.Finite)
    (hTS : ∀ v ∈ T, v ∉ S)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ S, ord K v (a : K) = m v)
    (hsurj : ∀ c : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ,
      (∀ v ∈ T, Valued.v ((c v : v.adicCompletion K)) = 1) →
      ∃ u : Kˣ, u ∈ sUnits K S ∧ ∀ v ∈ T, ∃ z : (v.adicCompletion K)ˣ,
        adicUnitHom v u = c v * z ^ p)
    {b : K}
    (hbinf : ∀ w : InfinitePlace K, ∃ c : w.Completion, c ^ p = algebraMap K w.Completion b)
    (hbS : ∀ v ∈ S, ∃ c : v.adicCompletion K, c ^ p = algebraMap K (v.adicCompletion K) b)
    (hbunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → v.valuation K b = 1) :
    ∃ y : K, y ^ p = b := by
  by_contra hcon
  push_neg at hcon
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hirr : Irreducible (X ^ p - C b) := X_pow_sub_C_irreducible_of_prime hp hcon
  have hprim : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  haveI : NumberField (X ^ p - C b).SplittingField := NumberField.of_module_finite K _
  haveI : IsGalois K (X ^ p - C b).SplittingField :=
    isGalois_of_isSplittingField_X_pow_sub_C hprim hirr _
  haveI : IsCyclic Gal((X ^ p - C b).SplittingField/K) :=
    isCyclic_of_isSplittingField_X_pow_sub_C hprim hirr _
  have hdeg : Module.finrank K (X ^ p - C b).SplittingField = p :=
    finrank_of_isSplittingField_X_pow_sub_C hprim hirr _
  have hβ : (rootOfSplitsXPowSubC (NeZero.pos p) b (X ^ p - C b).SplittingField) ^ p
      = algebraMap K (X ^ p - C b).SplittingField b :=
    rootOfSplitsXPowSubC_pow b _
  have hgenβ : IntermediateField.adjoin K
      ({rootOfSplitsXPowSubC (NeZero.pos p) b (X ^ p - C b).SplittingField} :
        Set (X ^ p - C b).SplittingField) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ Algebra.adjoin K
        ({rootOfSplitsXPowSubC (NeZero.pos p) b (X ^ p - C b).SplittingField} :
          Set (X ^ p - C b).SplittingField) :=
      (Algebra.adjoin_root_eq_top_of_isSplittingField hprim hirr hβ) ▸ Algebra.mem_top
    exact IntermediateField.algebra_adjoin_le_adjoin K _ hx
  haveI := subsingleton_gal_of_forall_localPow (L := (X ^ p - C b).SplittingField) hp hζ hdeg hS hT
    hTS hpS hrepr hsurj hβ hgenβ hbinf hbS hbunit
  have hone : Nat.card Gal((X ^ p - C b).SplittingField/K) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  rw [IsGalois.card_aut_eq_finrank, hdeg] at hone
  exact hp.one_lt.ne' hone

end Criterion

end InverseGalois.CFT
