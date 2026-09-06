/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.BaseTotallyRamified
import InverseGalois.CFT.Brauer.BaseSubcyclotomic
import InverseGalois.CFT.Brauer.CyclotomicGenerator
import InverseGalois.CFT.Brauer.RealCyclicSign
import InverseGalois.CFT.Cyclotomic.CyclicSubfield
import InverseGalois.CFT.Cyclotomic.TotallyRamified

/-!
# Reciprocity for a cyclic algebra split by a cyclotomic compositum

The vanishing of the total invariant of a cyclic algebra over a number field is proved by
comparing the extension with the corresponding cyclotomic extension of the rationals.  The
comparison theorem takes a long list of arithmetic hypotheses: the degrees of the four fields in
the compositum square must match up, the conductor must be totally ramified in the compositum,
the chosen generator of the cyclic Galois group must fix each place above the conductor, and the
compositum must be unramified over the base away from the conductor.

All of these hypotheses come for free once the top field is the compositum of the base with the
cyclotomic field of the conductor, provided only that the conductor is a prime which is unramified
in the base.  This file performs that specialization.  The ramified set of a cyclotomic field of
prime conductor is contained in the singleton consisting of that conductor, so the ramified sets of
the base and of the cyclotomic field are disjoint and the degree of the compositum over the base
equals the degree of the cyclotomic field over the rationals.  Total ramification at the conductor
transfers from the rational side to the compositum by the counting argument for inertia in a
compositum, and unramifiedness away from the conductor transfers by restriction of automorphisms.
Finally, a place above the conductor is totally ramified in the compositum, so its decomposition
group is everything and in particular contains the chosen generator.

What the specialization leaves open is the comparison of the archimedean invariants of the two
sides, and that is settled separately according to the subfield chosen inside the cyclotomic field.
A totally real subfield contributes nothing at either end.  A totally complex quadratic subfield
contributes the signs of the coefficient at the real places of the base, and those multiply out to
the sign of its norm, which is exactly the single archimedean invariant on the rational side.

## Main results

* `InverseGalois.CFT.ramIdx_rat_eq_one_of_notMem_ramifiedSet`: **a rational prime outside the
  ramified set of a number field is unramified at every place above it.**
* `InverseGalois.CFT.totalInvariant_cyclicBrauerHom_base_cyclotomic`: **the total invariant of a
  cyclic algebra over a number field, split by the compositum of the base with a cyclotomic field
  of prime conductor unramified in the base, is trivial.**
* `InverseGalois.CFT.totalInvariant_cyclicBrauerHom_base_cyclotomic_two`: the same conclusion for a
  totally complex quadratic subfield of the cyclotomic field, where the archimedean invariants are
  the signs of the coefficient and multiply out to the sign of its norm.

## Tags

number field, cyclotomic field, compositum, cyclic algebra, Brauer group, reciprocity,
class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField InverseGalois.NumberTheory

/-! ### Places outside the ramified set -/

section Unramified

variable {K : Type*} [Field K] [NumberField K] {q : ℕ}

/-- A rational prime which does not belong to the ramified set of a number field has ramification
index one, over the integers, at every place of that field above it. -/
theorem ramIdx_int_eq_one_of_notMem_ramifiedSet (hq : q.Prime) (hqK : q ∉ ramifiedSet K)
    (v : HeightOneSpectrum (𝓞 K)) (hmem : ((q : ℕ) : 𝓞 K) ∈ v.asIdeal) : ramIdx ℤ v = 1 := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI := liesOver_span_of_natCast_mem hq v hmem
  by_contra hne
  refine hqK ⟨hq, v.asIdeal, ⟨v.isPrime, inferInstance⟩, fun h => hne ?_⟩
  show Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (primeUnder ℤ v).asIdeal v.asIdeal = 1
  rw [primeUnder_asIdeal, ← Ideal.LiesOver.over (p := Ideal.span {(q : ℤ)}) (P := v.asIdeal)]
  exact h

/-- **A rational prime outside the ramified set of a number field is unramified at every place
above it.**  This is the same statement as for the ramification index over the integers, transported
along the identification of the ring of integers of the rationals with the integers. -/
theorem ramIdx_rat_eq_one_of_notMem_ramifiedSet (hq : q.Prime) (hqK : q ∉ ramifiedSet K)
    (v : HeightOneSpectrum (𝓞 K)) (hmem : ((q : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ramIdx (𝓞 ℚ) v = 1 := by
  rw [ramIdx_rat_eq_ramificationIdx_int]
  exact ramIdx_int_eq_one_of_notMem_ramifiedSet hq hqK v hmem

end Unramified

/-! ### Reciprocity for the cyclotomic compositum -/

section BaseCyclotomic

variable {q : ℕ} [NeZero q] {k K E L₀ F₀ : Type} [Field k] [NumberField k]
  [Field K] [NumberField K] [Algebra k K] [IsGalois k K]
  [Field E] [NumberField E] [Algebra k E] [IsGalois k E] [Algebra E K] [IsScalarTower k E K]
  [Field L₀] [NumberField L₀] [IsCyclotomicExtension {q} ℚ L₀] [IsGalois ℚ L₀]
  [Field F₀] [NumberField F₀] [Algebra F₀ L₀] [IsScalarTower ℚ F₀ L₀] [IsGalois ℚ F₀]
  [IsTotallyReal F₀] [Algebra F₀ E] [Algebra L₀ K] [IsScalarTower ℚ L₀ K] [IsScalarTower ℚ k K]
  [IsScalarTower ℚ k E] [IsScalarTower ℚ F₀ E]

omit [IsTotallyReal F₀] in
/-- **The total invariant of a cyclic algebra over a number field, split by the compositum of the
base with a cyclotomic field of prime conductor unramified in the base, is trivial** as soon as its
archimedean invariants multiply to those of the corresponding algebra over the rationals.  The
compositum square is controlled entirely by the ramified sets: the cyclotomic field is ramified only
at the conductor, which is unramified in the base, so the two ramified sets are disjoint, the
degrees of the two sides of the square agree, total ramification at the conductor and
unramifiedness away from it both transfer to the compositum, and the chosen generator of the cyclic
Galois group fixes every place above the conductor because such a place is totally ramified. -/
theorem totalInvariant_cyclicBrauerHom_base_cyclotomic_arch (hq : q.Prime) (hodd : Odd q) {N : ℕ}
    [NeZero N] (hcardF₀ : Nat.card Gal(F₀/ℚ) = N) (hqk : q ∉ ramifiedSet k)
    (hinertia₀ : ∀ (Q : Ideal (𝓞 F₀)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
      Ideal.inertia Gal(F₀/ℚ) Q = ⊤)
    {g : ℕ} (hg : Nat.Coprime g q) (hgord : ∀ m : ℕ, q ∣ g ^ m - 1 → (q - 1) ∣ m)
    {σ : Gal(K/k)} (hσ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ) {ζ : K}
    (hζ : IsPrimitiveRoot ζ q) (hgenζ : Algebra.adjoin k ({ζ} : Set K) = ⊤) (hσζ : σ ζ = ζ ^ g)
    (hgenK : Algebra.adjoin k (Set.range (algebraMap L₀ K)) = ⊤)
    (hgenE : Algebra.adjoin k (Set.range (algebraMap F₀ E)) = ⊤)
    {a : kˣ} {b : 𝓞 k} (hab : (a : k) = algebraMap (𝓞 k) k b)
    (hav : ∀ v : HeightOneSpectrum (𝓞 k), ((q : ℕ) : 𝓞 k) ∈ v.asIdeal → placeValue v a = 0)
    (harch : (∏ u : InfinitePlace k, infinitePlaceInvariant k u
          (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := E) hσ) a))
        = ∏ u : InfinitePlace ℚ, infinitePlaceInvariant ℚ u
          (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := F₀)
            (forall_mem_zpowers_cyclotomicPowerAut q L₀ hq hg hgord))
            (Units.map (Algebra.norm ℚ : k →* ℚ) a))) :
    totalInvariant k (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := E) hσ) a) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsCyclotomicExtension {q ^ 1} ℚ L₀ := by rw [pow_one]; infer_instance
  have hramL : ramifiedSet L₀ ⊆ {q} := ramifiedSet_subset_singleton_primePow q 1 L₀ L₀
  have hramF : ramifiedSet F₀ ⊆ {q} := ramifiedSet_subset_singleton_primePow q 1 L₀ F₀
  have hdisjL : Disjoint (ramifiedSet L₀) (ramifiedSet k) :=
    Set.disjoint_left.mpr fun p hp hpk => hqk (by rwa [Set.mem_singleton_iff.mp (hramL hp)] at hpk)
  have hdisjF : Disjoint (ramifiedSet F₀) (ramifiedSet k) :=
    Set.disjoint_left.mpr fun p hp hpk => hqk (by rwa [Set.mem_singleton_iff.mp (hramF hp)] at hpk)
  -- the degrees of the four fields in the compositum square
  have hrankL : finrank ℚ L₀ = q - 1 := finrank_cyclotomic_of_prime q L₀
  have hrankF : finrank ℚ F₀ = N := (IsGalois.card_aut_eq_finrank ℚ F₀).symm.trans hcardF₀
  have hrankE : finrank k E = N := by rw [finrank_eq_of_adjoin_eq_top hgenE hdisjF, hrankF]
  have hcardE : Nat.card Gal(E/k) = N := (IsGalois.card_aut_eq_finrank k E).trans hrankE
  have hrankK : finrank k K = q - 1 := by rw [finrank_eq_of_adjoin_eq_top hgenK hdisjL, hrankL]
  have hMN : finrank E K * N = q - 1 := by
    rw [← hrankE, mul_comm, Module.finrank_mul_finrank (F := k) (K := E) (A := K), hrankK]
  have hMN₀ : finrank F₀ L₀ * N = q - 1 := by
    rw [← hrankF, mul_comm, Module.finrank_mul_finrank (F := ℚ) (K := F₀) (A := L₀), hrankL]
  -- the conductor is unramified in the base
  have hunramk : ∀ v : HeightOneSpectrum (𝓞 k), ((q : ℕ) : 𝓞 k) ∈ v.asIdeal → ramIdx ℤ v = 1 :=
    fun v hv => ramIdx_int_eq_one_of_notMem_ramifiedSet hq hqk v hv
  -- total ramification passes to the compositum with the totally real subfield
  have hinertiaE : ∀ (Q : Ideal (𝓞 E)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
      Ideal.inertia Gal(E/k) Q = ⊤ := by
    intro Q hQp hQo
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := ne_bot_of_liesOver_natCast hq hQo
    set w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQp, hQ0⟩ with hwdef
    have hmemE : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal := natCast_mem_of_liesOver_span Q
    have hmemk : ((q : ℕ) : 𝓞 k) ∈ (primeUnder (𝓞 k) w).asIdeal := by
      rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hmemE
    have hmemF : ((q : ℕ) : 𝓞 F₀) ∈ (primeUnder (𝓞 F₀) w).asIdeal := by
      rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hmemE
    haveI := liesOver_span_of_natCast_mem hq (primeUnder (𝓞 F₀) w) hmemF
    have hk : ramIdx (𝓞 ℚ) (primeUnder (𝓞 k) w) = 1 :=
      ramIdx_rat_eq_one_of_notMem_ramifiedSet hq hqk _ hmemk
    exact inertia_eq_top_of_inertia_base_eq_top hgenE w hk
      (hinertia₀ (primeUnder (𝓞 F₀) w).asIdeal (primeUnder (𝓞 F₀) w).isPrime inferInstance)
  -- the generator fixes every place above the conductor
  have hσW : ∀ W : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ W.asIdeal → σ • W = W := by
    intro W hW
    have hmemk : ((q : ℕ) : 𝓞 k) ∈ (primeUnder (𝓞 k) W).asIdeal := by
      rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hW
    have hmemL : ((q : ℕ) : 𝓞 L₀) ∈ (primeUnder (𝓞 L₀) W).asIdeal := by
      rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hW
    haveI := liesOver_span_of_natCast_mem hq (primeUnder (𝓞 L₀) W) hmemL
    haveI : (primeUnder (𝓞 L₀) W).asIdeal.IsPrime := (primeUnder (𝓞 L₀) W).isPrime
    have hk : ramIdx (𝓞 ℚ) (primeUnder (𝓞 k) W) = 1 :=
      ramIdx_rat_eq_one_of_notMem_ramifiedSet hq hqk _ hmemk
    have hinert : Ideal.inertia Gal(K/k) W.asIdeal = ⊤ :=
      inertia_eq_top_of_inertia_base_eq_top hgenK W hk
        (inertia_eq_top_cyclotomic_primePow q 1 L₀ (primeUnder (𝓞 L₀) W).asIdeal)
    have hstab : σ ∈ stabilizer Gal(K/k) W := by
      rw [stabilizer_place_eq_top_of_inertia_eq_top W hinert]
      exact Subgroup.mem_top σ
    exact hstab
  -- the compositum is unramified over the base away from the conductor
  have hunramK : ∀ (w : HeightOneSpectrum (𝓞 K)) (p : ℕ), p.Prime → ¬ p ∣ q →
      ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → ramIdx (𝓞 k) w = 1 := by
    intro w p hp hpq hmem
    haveI : Fact p.Prime := ⟨hp⟩
    have hmemL : ((p : ℕ) : 𝓞 L₀) ∈ (primeUnder (𝓞 L₀) w).asIdeal := by
      rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hmem
    haveI := liesOver_span_of_natCast_mem hp (primeUnder (𝓞 L₀) w) hmemL
    exact ramIdx_eq_one_of_ramIdx_eq_one hgenK w
      (ramIdx_rat_eq_one_of_not_dvd q L₀ p (primeUnder (𝓞 L₀) w) hpq)
  exact totalInvariant_cyclicBrauerHom_base_subcyclotomic_arch hq hodd hcardE hcardF₀ hMN hMN₀ hg
    hgord (forall_mem_zpowers_cyclotomicPowerAut q L₀ hq hg hgord) hinertia₀ hσ hζ hgenζ hσζ
    hinertiaE hσW hunramk hunramK hab hav harch

/-- **The total invariant of a cyclic algebra over a number field, split by the compositum of the
base with a totally real subfield of a cyclotomic field of prime conductor unramified in the base,
is trivial.**  Both splitting fields are generated by a totally real field, so nothing is
contributed at the infinite places on either side and the archimedean comparison is automatic. -/
theorem totalInvariant_cyclicBrauerHom_base_cyclotomic (hq : q.Prime) (hodd : Odd q) {N : ℕ}
    [NeZero N] (hcardF₀ : Nat.card Gal(F₀/ℚ) = N) (hqk : q ∉ ramifiedSet k)
    (hinertia₀ : ∀ (Q : Ideal (𝓞 F₀)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
      Ideal.inertia Gal(F₀/ℚ) Q = ⊤)
    {g : ℕ} (hg : Nat.Coprime g q) (hgord : ∀ m : ℕ, q ∣ g ^ m - 1 → (q - 1) ∣ m)
    {σ : Gal(K/k)} (hσ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ) {ζ : K}
    (hζ : IsPrimitiveRoot ζ q) (hgenζ : Algebra.adjoin k ({ζ} : Set K) = ⊤) (hσζ : σ ζ = ζ ^ g)
    (hgenK : Algebra.adjoin k (Set.range (algebraMap L₀ K)) = ⊤)
    (hgenE : Algebra.adjoin k (Set.range (algebraMap F₀ E)) = ⊤)
    {a : kˣ} {b : 𝓞 k} (hab : (a : k) = algebraMap (𝓞 k) k b)
    (hav : ∀ v : HeightOneSpectrum (𝓞 k), ((q : ℕ) : 𝓞 k) ∈ v.asIdeal → placeValue v a = 0) :
    totalInvariant k (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := E) hσ) a) = 1 := by
  refine totalInvariant_cyclicBrauerHom_base_cyclotomic_arch hq hodd hcardF₀ hqk hinertia₀ hg
    hgord hσ hζ hgenζ hσζ hgenK hgenE hab hav ?_
  have h1 : ∀ u : InfinitePlace k, infinitePlaceInvariant k u
      (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := E) hσ) a) = 1 :=
    fun u => infinitePlaceInvariant_cyclicBrauerHom_of_adjoin_isTotallyReal
      (forall_mem_zpowers_restrictNormal (L := E) hσ) hgenE a u
  have h2 : ∀ u : InfinitePlace ℚ, infinitePlaceInvariant ℚ u
      (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := F₀)
        (forall_mem_zpowers_cyclotomicPowerAut q L₀ hq hg hgord))
        (Units.map (Algebra.norm ℚ : k →* ℚ) a)) = 1 :=
    fun u => infinitePlaceInvariant_cyclicBrauerHom_of_isTotallyReal
      (forall_mem_zpowers_restrictNormal (L := F₀)
        (forall_mem_zpowers_cyclotomicPowerAut q L₀ hq hg hgord)) _ u
  simp only [h1, h2, Finset.prod_const_one]

omit [IsTotallyReal F₀] in
/-- **The total invariant of a cyclic algebra over a number field, split by the compositum of the
base with a totally complex quadratic subfield of a cyclotomic field of prime conductor unramified
in the base, is trivial.**  The compositum with a quadratic field is again quadratic, and it is
totally complex because the subfield already is, so the invariant of the algebra at a real place of
the base is the sign of the coefficient there; those signs multiply out to the sign of the norm of
the coefficient, which is the archimedean invariant on the rational side. -/
theorem totalInvariant_cyclicBrauerHom_base_cyclotomic_two [IsTotallyComplex F₀] (hq : q.Prime)
    (hodd : Odd q) (hcardF₀ : Nat.card Gal(F₀/ℚ) = 2) (hqk : q ∉ ramifiedSet k)
    (hinertia₀ : ∀ (Q : Ideal (𝓞 F₀)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
      Ideal.inertia Gal(F₀/ℚ) Q = ⊤)
    {g : ℕ} (hg : Nat.Coprime g q) (hgord : ∀ m : ℕ, q ∣ g ^ m - 1 → (q - 1) ∣ m)
    {σ : Gal(K/k)} (hσ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ) {ζ : K}
    (hζ : IsPrimitiveRoot ζ q) (hgenζ : Algebra.adjoin k ({ζ} : Set K) = ⊤) (hσζ : σ ζ = ζ ^ g)
    (hgenK : Algebra.adjoin k (Set.range (algebraMap L₀ K)) = ⊤)
    (hgenE : Algebra.adjoin k (Set.range (algebraMap F₀ E)) = ⊤)
    {a : kˣ} {b : 𝓞 k} (hab : (a : k) = algebraMap (𝓞 k) k b)
    (hav : ∀ v : HeightOneSpectrum (𝓞 k), ((q : ℕ) : 𝓞 k) ∈ v.asIdeal → placeValue v a = 0) :
    totalInvariant k (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := E) hσ) a) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsCyclotomicExtension {q ^ 1} ℚ L₀ := by rw [pow_one]; infer_instance
  haveI : IsTotallyComplex E := NumberField.isTotallyComplex_of_algebra F₀ E
  have hramF : ramifiedSet F₀ ⊆ {q} := ramifiedSet_subset_singleton_primePow q 1 L₀ F₀
  have hdisjF : Disjoint (ramifiedSet F₀) (ramifiedSet k) :=
    Set.disjoint_left.mpr fun p hp hpk => hqk (by rwa [Set.mem_singleton_iff.mp (hramF hp)] at hpk)
  have hrankF : finrank ℚ F₀ = 2 := (IsGalois.card_aut_eq_finrank ℚ F₀).symm.trans hcardF₀
  have hrankE : finrank k E = 2 := by rw [finrank_eq_of_adjoin_eq_top hgenE hdisjF, hrankF]
  refine totalInvariant_cyclicBrauerHom_base_cyclotomic_arch hq hodd hcardF₀ hqk hinertia₀ hg
    hgord hσ hζ hgenζ hσζ hgenK hgenE hab hav ?_
  exact prod_infinitePlaceInvariant_cyclicBrauerHom_eq_rat hrankE hrankF _ _ a

end BaseCyclotomic

end InverseGalois.CFT
