/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.EighthRootSubfield
import InverseGalois.CFT.KroneckerWeber
import InverseGalois.CFT.PGroupCompositum
import InverseGalois.CFT.Scholz.CentralStepTwo
import InverseGalois.CFT.Scholz.CompositumTransport
import InverseGalois.CFT.Scholz.CorrectingCharacter
import InverseGalois.CFT.Scholz.CorrectingSubfield
import InverseGalois.CFT.Scholz.DyadicCorrector
import InverseGalois.CFT.Scholz.DyadicResidueDegree
import InverseGalois.CFT.Scholz.UnramifiedFactorInertia
import InverseGalois.CFT.Scholz.UnramifiedSolution

/-!
# A solution at the prime two ramifying no more than the problem it solves

At an odd residue characteristic the primes that a central step ramifies unnecessarily are removed
by twisting inside a field of odd prime power degree, where every inertia subgroup is automatically
cyclic.  At the residue characteristic two the same plan runs into two obstructions: the twist at
the prime two itself needs a square root of `-1` and a square root of `2`, and it needs the residue
degree at two to be divisible by the order of the group being realised.

Both are supplied by cyclotomic layers.  The eighth cyclotomic layer contributes the two square
roots and has degree four, so it costs nothing in the degree.  A layer of Fermat conductor
`2 ^ 2 ^ k + 1` makes the class of two of order `2 ^ (k + 1)` in the residue field, which forces the
residue degree at two to be divisible by `2 ^ k`; that layer is not of two-power degree, but every
prime divisor of a Fermat number exceeds the next power of two, so the conductor can be chosen prime
to all the primes that have to be corrected.  At those primes the inertia subgroup therefore embeds
into the two-group belonging to the rest of the field, so it is tame and hence cyclic, which is what
the twist there requires.

## Main results

* `InverseGalois.CFT.exists_galEquiv_ramifiedSet_subset_two`: **a central Frattini embedding problem
  with kernel of order two over a field satisfying the level condition has a solution which ramifies
  nowhere outside the ramified set of that field.**

## Tags

embedding problem, Scholz condition, ramified prime, twist, two-group, Fermat number
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

open IntermediateField

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem with kernel of order two over a field satisfying the
level condition has a solution ramifying nowhere outside the ramified set of that field.**  The
solution produced by the central step is enlarged by the eighth cyclotomic layer, by a cyclotomic
layer of Fermat conductor large enough to be prime to every prime at which the solution ramifies
unnecessarily, and by the quadratic extensions attached to those primes; inside that enlargement the
unwanted primes are removed one at a time by twisting, and the twisted solution is cut down to the
field it defines. -/
theorem exists_galEquiv_ramifiedSet_subset_two {N : ℕ} {G H : Type} [Group G] [Group H] [Finite G]
    {f : G →* H} (hf : Function.Surjective f) (hpg : IsPGroup 2 G)
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = 2)
    (hHdvd : Nat.card H ∣ 2 ^ N) (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥A]
    [NumberField ↥A] (hsch : IsScholz 2 (N + 1) ↥A) (e : Gal(↥A/ℚ) ≃* H) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAL : A ≤ L), NumberField ↥L ∧
      IsGalois ℚ ↥L ∧ ramifiedSet ↥L ⊆ ramifiedSet ↥A ∧
      ∃ ψ : Gal(↥L/ℚ) ≃* G, ∀ τ, f (ψ τ) = e (galRestrictLE hAL τ) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  -- the solution of the embedding problem, with Galois group the group to be realised
  obtain ⟨L₀, hAL₀, hNF₀, hGal₀, ψ₀, hcomp₀⟩ :=
    exists_galEquiv_of_centralStep_two hf hpg hZ hfr hcard hHdvd A hsch e
  haveI := hNF₀
  haveI := hGal₀
  have hpg₀ : IsPGroup 2 Gal(↥L₀/ℚ) := hpg.of_equiv ψ₀.symm
  -- the primes at which it ramifies unnecessarily
  set S : Set ℕ := ramifiedSet ↥A with hSdef
  set T : Finset ℕ :=
    (finite_ramifiedSet ↥L₀).toFinset \ (finite_ramifiedSet ↥A).toFinset with hTdef
  have hTmem : ∀ p ∈ T, p ∈ ramifiedSet ↥L₀ ∧ p ∉ S := by
    intro p hp
    rw [hTdef, Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    exact hp
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => (hTmem p hp).1.1
  -- a Fermat conductor prime to all of them, and large enough to force the residue degree at two
  obtain ⟨k, hkG, hkT⟩ : ∃ k : ℕ, Nat.card G ∣ 2 ^ k ∧ ∀ p ∈ T, ¬ p ∣ 2 ^ 2 ^ k + 1 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpg
    refine ⟨max m (T.sup id), by rw [hm]; exact pow_dvd_pow 2 (le_max_left _ _), fun p hp => ?_⟩
    refine not_dvd_fermat_of_le (hTp p hp) ?_
    have h1 : p ≤ max m (T.sup id) := le_trans (Finset.le_sup (f := id) hp) (le_max_right _ _)
    have h2 : max m (T.sup id) < 2 ^ max m (T.sup id) := Nat.lt_two_pow_self
    have h3 : (2 : ℕ) ^ max m (T.sup id) ≤ 2 ^ (max m (T.sup id) + 1) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
    omega
  haveI : NeZero (2 ^ 2 ^ k + 1) := ⟨by positivity⟩
  -- the quadratic extension correcting each unwanted prime
  have hex : ∀ q : {q // q ∈ T}, ∃ Dq : IntermediateField ℚ (AlgebraicClosure ℚ),
      ∃ _ : NumberField ↥Dq, IsGalois ℚ ↥Dq ∧ IsPGroup 2 Gal(↥Dq/ℚ) ∧
        ramifiedSet ↥Dq ⊆ {q.1} ∧
        (∀ (Q : Ideal (𝓞 ↥Dq)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q.1 : ℤ)})),
          Ideal.inertia Gal(↥Dq/ℚ) Q = ⊤) ∧ ∃ χ : Gal(↥Dq/ℚ) →* G, χ.range = f.ker := by
    intro q
    have hq : q.1.Prime := hTp q.1 q.2
    refine exists_totallyRamified_hom_range_eq Nat.prime_two hq ?_ f.ker hcard
    rcases eq_or_ne q.1 2 with h | h
    · exact Or.inl h
    · exact Or.inr (by
        obtain ⟨j, hj⟩ := hq.odd_of_ne_two h
        omega)
  choose D hDNF hDgal hDpg hDram hDtot χ hχrange using hex
  haveI : ∀ q, NumberField ↥(D q) := hDNF
  haveI : ∀ q, IsGalois ℚ ↥(D q) := hDgal
  -- the two-power part of the field over which all the twists take place
  set M₁ : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    L₀ ⊔ Finset.univ.sup D ⊔ cycSubfield 8 with hM₁def
  haveI : FiniteDimensional ℚ ↥(Finset.univ.sup D) := finiteDimensional_finsetSup D Finset.univ
  haveI : Normal ℚ ↥(Finset.univ.sup D) := normal_finsetSup D Finset.univ
  haveI : FiniteDimensional ℚ ↥M₁ := by rw [hM₁def]; infer_instance
  haveI : Normal ℚ ↥M₁ := by rw [hM₁def]; infer_instance
  haveI : NumberField ↥M₁ := ⟨⟩
  haveI : IsGalois ℚ ↥M₁ := ⟨⟩
  have hpgM₁ : IsPGroup 2 Gal(↥M₁/ℚ) := by
    rw [hM₁def]
    exact isPGroup_sup (L₀ ⊔ Finset.univ.sup D) (cycSubfield 8)
      (isPGroup_sup L₀ (Finset.univ.sup D) hpg₀ (isPGroup_finsetSup D hDpg Finset.univ))
      isPGroup_gal_cycSubfield_eight
  -- and the whole field, with the Fermat cyclotomic layer adjoined
  set M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    M₁ ⊔ cycSubfield (2 ^ 2 ^ k + 1) with hMdef
  haveI : FiniteDimensional ℚ ↥M := by rw [hMdef]; infer_instance
  haveI : Normal ℚ ↥M := by rw [hMdef]; infer_instance
  haveI : NumberField ↥M := ⟨⟩
  haveI : IsGalois ℚ ↥M := ⟨⟩
  have hM₁M : M₁ ≤ M := by rw [hMdef]; exact le_sup_left
  have hFM : cycSubfield (2 ^ 2 ^ k + 1) ≤ M := by rw [hMdef]; exact le_sup_right
  have hL₀M : L₀ ≤ M := le_trans (by rw [hM₁def]; exact le_sup_of_le_left le_sup_left) hM₁M
  have h8M : cycSubfield 8 ≤ M := le_trans (by rw [hM₁def]; exact le_sup_right) hM₁M
  have hAM : A ≤ M := hAL₀.trans hL₀M
  have hDM : ∀ q, D q ≤ M := fun q =>
    le_trans (by
      rw [hM₁def]
      exact le_sup_of_le_left (le_sup_of_le_right (Finset.le_sup (Finset.mem_univ q)))) hM₁M
  -- the two layers generate the field, and the Fermat layer is unramified at the unwanted primes
  have htop : IntermediateField.restrict hM₁M ⊔
      IntermediateField.restrict hFM = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict]
  have hFunram : ∀ p ∈ T, p ∉ ramifiedSet ↥(cycSubfield (2 ^ 2 ^ k + 1)) := by
    intro p hp hmem
    exact hkT p hp (Nat.dvd_of_mem_primeFactors (Finset.mem_coe.mp
      (ramifiedSet_subset_primeFactors (2 ^ 2 ^ k + 1) ↥(cycSubfield (2 ^ 2 ^ k + 1)) hmem)))
  -- the solution, read over that field
  set Ψ : Gal(↥M/ℚ) →* G := ψ₀.toMonoidHom.comp (galRestrictLE hL₀M) with hΨdef
  have hΨsurj : Function.Surjective Ψ := ψ₀.surjective.comp (galRestrictLE_surjective hL₀M)
  have hcompM : ∀ σ, f (Ψ σ) = e (galRestrictLE hAM σ) := by
    intro σ
    rw [hΨdef]
    exact (hcomp₀ (galRestrictLE hL₀M σ)).trans
      (congrArg e (galRestrictLE_galRestrictLE hAL₀ hL₀M σ))
  have hfixΨ : ramifiedSet ↥(IntermediateField.fixedField Ψ.ker) = ramifiedSet ↥L₀ := by
    have hker : Ψ.ker = (galRestrictLE hL₀M).ker := by
      rw [hΨdef]
      ext σ
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff]
    rw [hker, fixedField_ker_galRestrictLE hL₀M, ramifiedSet_restrict]
  have hfixcomp : ramifiedSet ↥(IntermediateField.fixedField (f.comp Ψ).ker) = ramifiedSet ↥A :=
    ramifiedSet_fixedField_ker_comp hAM Ψ e hcompM
  have hπ : ∀ p ∈ T, p ∉ S → p ∉ ramifiedSet ↥(IntermediateField.fixedField (f.comp Ψ).ker) := by
    intro p _ hpS
    rw [hfixcomp]
    exact hpS
  -- every unwanted prime has a correcting character available
  have hcharΨ : ∀ p ∈ T, p ∉ S → HasCorrectingCharAt ↥M f p Ψ := by
    intro p hpT hpS
    have hp : p.Prime := hTp p hpT
    haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
      rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
      exact Nat.prime_iff_prime_int.mp hp
    obtain ⟨⟨P, hPp, hPo⟩⟩ := (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 ↥M)
    haveI := hPp
    haveI := hPo
    rcases eq_or_ne p 2 with rfl | hne
    · -- at the prime two the dyadic square-class analysis supplies the character
      refine hasCorrectingCharAt_two hZ hcard
        (exists_sq_eq_neg_one_of_cycSubfield_eight_le M h8M)
        (exists_sq_eq_two_of_cycSubfield_eight_le M h8M) P
        (hkG.trans (pow_dvd_inertiaDeg_two_of_cycSubfield_le k M hFM P)) ?_
      intro σ hσ
      exact MonoidHom.mem_ker.mpr (eq_one_of_notMem_ramifiedSet_fixedField_ker (f.comp Ψ)
        Nat.prime_two (hπ 2 hpT hpS) P hσ)
    · -- at an odd prime the inertia subgroup is tame, hence cyclic, and the quadratic extension
      -- attached to the prime supplies the character
      haveI : IsCyclic ↥(Ideal.inertia Gal(↥M/ℚ) P) :=
        isCyclic_inertia_of_sup_eq_top (IntermediateField.restrict hM₁M)
          (IntermediateField.restrict hFM) Nat.prime_two htop hp hne
          (by rw [ramifiedSet_restrict hFM]; exact hFunram p hpT)
          (isPGroup_restrict hM₁M hpgM₁) P
      exact hasCorrectingCharAt_of_hasCorrectingChar hp
        (hasCorrectingChar_of_le (hDM ⟨p, hpT⟩) hp (hDram ⟨p, hpT⟩) (hDtot ⟨p, hpT⟩)
          (χ ⟨p, hpT⟩) (hχrange ⟨p, hpT⟩) P (hasInertiaCancellation_of_isCyclic P f.ker))
        (hπ p hpT hpS)
  have hsub : ramifiedSet ↥(IntermediateField.fixedField Ψ.ker) \ S ⊆ ↑T := by
    rw [hfixΨ]
    intro q hq
    refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Set.Finite.mem_toFinset _ |>.mpr hq.1, ?_⟩)
    exact fun h => hq.2 ((Set.Finite.mem_toFinset _).mp h)
  obtain ⟨ψ', hψ'surj, hψ'comp, hψ'ram⟩ :=
    exists_twist_ramifiedSet_inter hf hfr hZ S T hTp Ψ hΨsurj hcharΨ hπ hsub
  -- the field cut out by the twisted solution
  have hker' : ψ'.ker ≤ (galRestrictLE hAM).ker := by
    intro σ hσ
    have h1 : e (galRestrictLE hAM σ) = 1 := by
      rw [← hcompM σ, ← MonoidHom.comp_apply, ← hψ'comp, MonoidHom.comp_apply,
        MonoidHom.mem_ker.mp hσ, map_one]
    exact MonoidHom.mem_ker.mpr (by simpa using h1)
  have hAL' : A ≤ cutField ψ' := le_cutField ψ' hAM hker'
  haveI : FiniteDimensional ℚ ↥(cutField ψ') :=
    (IntermediateField.liftAlgEquiv
      (IntermediateField.fixedField ψ'.ker)).toLinearEquiv.finiteDimensional
  haveI : NumberField ↥(cutField ψ') := ⟨⟩
  haveI : IsGalois ℚ ↥(cutField ψ') := ⟨⟩
  have hramL : ramifiedSet ↥(cutField ψ') =
      ramifiedSet ↥(IntermediateField.fixedField ψ'.ker) := by
    have h1 := ramifiedSet_restrict (cutField_le ψ')
    rw [restrict_cutField_le] at h1
    exact h1.symm
  refine ⟨cutField ψ', hAL', inferInstance, inferInstance, ?_,
    galEquivCutField ψ' hψ'surj, fun τ => ?_⟩
  · rw [hramL]
    exact fun q hq => (hψ'ram hq).2
  · obtain ⟨σ, rfl⟩ := galRestrictLE_surjective (cutField_le ψ') τ
    rw [galEquivCutField_galRestrictLE ψ' hψ'surj σ,
      galRestrictLE_galRestrictLE hAL' (cutField_le ψ') σ, ← MonoidHom.comp_apply, hψ'comp,
      MonoidHom.comp_apply]
    exact hcompM σ

end InverseGalois.CFT
