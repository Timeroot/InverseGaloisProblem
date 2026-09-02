/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.BaseCyclicClass
import InverseGalois.CFT.Cyclotomic.ImaginarySubfield

/-!
# The sign correcting Brauer classes of a number field

Reciprocity for a class of two-power order needs a supply of classes whose archimedean invariants
can be prescribed, since a class killed by a power of two is not automatically split by the reals.
Over the rationals a single class does the job, the quaternion algebra ramified at three and at
infinity, because there is only one archimedean place to correct.  Over an arbitrary number field
there are as many real places as there are real embeddings, and the corrections must be able to
distinguish them.

The construction that distinguishes them is the same cyclic algebra as before, only now with a
*totally complex* quadratic splitting field: the invariant of such an algebra at a real place is the
sign of its coefficient at that place, so a coefficient whose signs are prescribed produces a class
whose archimedean invariants are prescribed.  The quadratic field is taken inside the cyclotomic
field of an auxiliary prime conductor congruent to three modulo four, composed with the base; the
conductor being unramified in the base, the compositum is again quadratic, and it is totally complex
because the quadratic field already is.

That the resulting classes satisfy reciprocity is the comparison with the rationals carried out for
the cyclotomic compositum, in the variant where the archimedean invariants are compared through the
sign of the norm rather than being trivial on both sides.  As before an arbitrary unit is reduced,
by a norm from the splitting field, to an algebraic integer which is a unit at the conductor, which
is where the comparison applies.

## Main results

* `InverseGalois.CFT.exists_signCorrector_base`: **the sign correcting Brauer classes of a number
  field**, killed by two, with trivial total invariant, and with the sign of the coefficient as
  invariant at every real place.

## Tags

Brauer group, number field, cyclic algebra, real place, sign, totally complex, reciprocity,
class field theory
-/

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField InverseGalois.NumberTheory

open scoped Pointwise

/-! ### The correcting classes with prescribed signs -/

section Construction

/-- **The sign correcting Brauer classes of a number field.**  For a prime conductor congruent to
three modulo four and unramified in the base, the compositum of the base with the imaginary
quadratic subfield of the cyclotomic field of the conductor is a totally complex quadratic
extension, and the cyclic algebras it carries are killed by two, satisfy reciprocity, and have as
invariant at a real place of the base the sign of the coefficient there. -/
theorem exists_signCorrector_base (k : Type) [Field k] [NumberField k] {q : ℕ} (hq : q.Prime)
    (hq2 : 2 < q) (hqk : q ∉ ramifiedSet k) (hqodd : Odd ((q - 1) / 2)) :
    ∃ Y : kˣ →* BrauerGroup.{0, 0} k,
      (∀ a : kˣ, Y a ^ 2 = 1) ∧
      (∀ a : kˣ, totalInvariant k (Y a) = 1) ∧
      ∀ (a : kˣ) (u : InfinitePlace k) (hu : u.IsReal), infinitePlaceInvariant k u (Y a)
        = realCyclicInvariant
            (Units.map (InfinitePlace.embedding_of_isReal hu).toMonoidHom a) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hodd : Odd q := hq.odd_of_ne_two (by omega)
  have hdvd2 : 2 ∣ q - 1 := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  obtain ⟨g, hg, hgord⟩ := exists_nat_primitiveRoot_of_prime hq
  haveI : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ _
  haveI : IsCyclotomicExtension {q ^ 1} ℚ (CyclotomicField q ℚ) := by rw [pow_one]; infer_instance
  obtain ⟨F, hrankF, hgalF, hcycF, himF, -, -, hinertia₀⟩ :=
    exists_intermediateField_subcyclotomic_imaginary q hq2 (d := 2) (by norm_num) hdvd2 hqodd
      (CyclotomicField q ℚ)
  haveI := hgalF
  haveI := hcycF
  haveI := himF
  haveI : FiniteDimensional ℚ ↥F := IntermediateField.finiteDimensional_left F
  haveI : NumberField ↥F := ⟨⟩
  obtain ⟨ιL⟩ : Nonempty (CyclotomicField q ℚ →ₐ[ℚ] AlgebraicClosure k) := ⟨IsAlgClosed.lift⟩
  set ιF : ↥F →ₐ[ℚ] AlgebraicClosure k := ιL.comp F.val with hιF
  haveI : IsScalarTower ℚ k ↥(baseCompositum ιL) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : IsScalarTower ℚ k ↥(baseCompositum ιF) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hle : baseCompositum ιF ≤ baseCompositum ιL :=
    baseCompositum_le_of_range_subset ιF ιL (by rintro _ ⟨y, rfl⟩; exact ⟨F.val y, rfl⟩)
  letI : Algebra ↥(baseCompositum ιF) ↥(baseCompositum ιL) :=
    (IntermediateField.inclusion hle).toAlgebra
  haveI : IsScalarTower k ↥(baseCompositum ιF) ↥(baseCompositum ιL) :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hle).commutes x).symm
  have hgenK : Algebra.adjoin k
      (Set.range (algebraMap (CyclotomicField q ℚ) ↥(baseCompositum ιL))) = ⊤ :=
    adjoin_range_algebraMap_eq_top ιL
  have hgenE : Algebra.adjoin k (Set.range (algebraMap ↥F ↥(baseCompositum ιF))) = ⊤ :=
    adjoin_range_algebraMap_eq_top ιF
  have hramL : ramifiedSet (CyclotomicField q ℚ) ⊆ {q} :=
    ramifiedSet_subset_singleton_primePow q 1 (CyclotomicField q ℚ) (CyclotomicField q ℚ)
  have hramF : ramifiedSet ↥F ⊆ {q} :=
    ramifiedSet_subset_singleton_primePow q 1 (CyclotomicField q ℚ) ↥F
  have hdisjL : Disjoint (ramifiedSet (CyclotomicField q ℚ)) (ramifiedSet k) :=
    Set.disjoint_left.mpr fun p hp hpk => hqk (by rwa [Set.mem_singleton_iff.mp (hramL hp)] at hpk)
  have hdisjF : Disjoint (ramifiedSet ↥F) (ramifiedSet k) :=
    Set.disjoint_left.mpr fun p hp hpk => hqk (by rwa [Set.mem_singleton_iff.mp (hramF hp)] at hpk)
  set ζ₀ : CyclotomicField q ℚ := IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ) with hζ₀def
  have hζ₀ : IsPrimitiveRoot ζ₀ q := IsCyclotomicExtension.zeta_spec q ℚ _
  set ζ : ↥(baseCompositum ιL) :=
    algebraMap (CyclotomicField q ℚ) ↥(baseCompositum ιL) ζ₀ with hζdef
  have hζ : IsPrimitiveRoot ζ q :=
    hζ₀.map_of_injective (algebraMap (CyclotomicField q ℚ) ↥(baseCompositum ιL)).injective
  have hθ : IntermediateField.adjoin ℚ ({ζ₀} : Set (CyclotomicField q ℚ)) = ⊤ := by
    refine IntermediateField.toSubalgebra_injective ?_
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsIntegral.isIntegral ζ₀).isAlgebraic, IntermediateField.top_toSubalgebra]
    exact adjoin_zeta_rat_eq_top q (CyclotomicField q ℚ)
  have hgenζ : Algebra.adjoin k ({ζ} : Set ↥(baseCompositum ιL)) = ⊤ :=
    adjoin_singleton_eq_top ιL hθ
  set σ : Gal(↥(baseCompositum ιL)/k) :=
    (galEquivSub k (CyclotomicField q ℚ) ↥(baseCompositum ιL) hgenK hdisjL).symm
      (cyclotomicPowerAut q (CyclotomicField q ℚ) hg) with hσdef
  have hres : galRestrictSub k (CyclotomicField q ℚ) ↥(baseCompositum ιL) σ
      = cyclotomicPowerAut q (CyclotomicField q ℚ) hg := by
    rw [hσdef]
    exact (galEquivSub k (CyclotomicField q ℚ) ↥(baseCompositum ιL) hgenK
      hdisjL).apply_symm_apply _
  have hσ : ∀ x : Gal(↥(baseCompositum ιL)/k), x ∈ Subgroup.zpowers σ := by
    intro x
    obtain ⟨n, hn⟩ := forall_mem_zpowers_cyclotomicPowerAut q (CyclotomicField q ℚ) hq hg hgord
      (galEquivSub k (CyclotomicField q ℚ) ↥(baseCompositum ιL) hgenK hdisjL x)
    refine ⟨n, ?_⟩
    refine (galEquivSub k (CyclotomicField q ℚ) ↥(baseCompositum ιL) hgenK hdisjL).injective ?_
    rw [map_zpow, hσdef, MulEquiv.apply_symm_apply]
    exact hn
  have hσζ : σ ζ = ζ ^ g := by
    have h2 := galRestrictSub_algebraMap (k := k) (F₀ := CyclotomicField q ℚ)
      (E := ↥(baseCompositum ιL)) σ ζ₀
    rw [hres, cyclotomicPowerAut_apply q (CyclotomicField q ℚ) hg hζ₀.pow_eq_one, map_pow] at h2
    exact h2.symm
  have hcardF₀ : Nat.card Gal(↥F/ℚ) = 2 := by rw [IsGalois.card_aut_eq_finrank ℚ ↥F, hrankF]
  have hrankE : finrank k ↥(baseCompositum ιF) = 2 := by
    rw [finrank_eq_of_adjoin_eq_top hgenE hdisjF, hrankF]
  haveI : IsTotallyComplex ↥(baseCompositum ιF) :=
    NumberField.isTotallyComplex_of_algebra ↥F ↥(baseCompositum ιF)
  have hrecip : ∀ a : kˣ, totalInvariant k
      (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := ↥(baseCompositum ιF)) hσ) a)
        = 1 := by
    intro a
    refine totalInvariant_eq_one_of_integral_qunit (E := ↥(baseCompositum ιF)) hq _
      (fun θ => MonoidHom.mem_ker.mp ((mem_ker_cyclicBrauerHom_iff _ _).mpr ⟨θ, rfl⟩))
      (fun W hW => inertia_eq_top_of_natCast_mem hq hqk hinertia₀ hgenE W hW)
      (fun a hab hav => ?_) a
    obtain ⟨b, hb⟩ := hab
    exact totalInvariant_cyclicBrauerHom_base_cyclotomic_two hq hodd hcardF₀ hqk hinertia₀ hg
      hgord hσ hζ hgenζ hσζ hgenK hgenE hb hav
  refine ⟨cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := ↥(baseCompositum ιF)) hσ),
    fun a => ?_, hrecip, fun a u hu => ?_⟩
  · have h := pow_finrank_eq_one_of_mem_relative
      (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := ↥(baseCompositum ιF)) hσ) a)
      (cyclicBrauerHom_mem_relative
        (forall_mem_zpowers_restrictNormal (L := ↥(baseCompositum ιF)) hσ) a)
    rwa [hrankE] at h
  · exact infinitePlaceInvariant_cyclicBrauerHom_of_isTotallyComplex hrankE
      (forall_mem_zpowers_restrictNormal (L := ↥(baseCompositum ιF)) hσ) hu a

end Construction

end InverseGalois.CFT
