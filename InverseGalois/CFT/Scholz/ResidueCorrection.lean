/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.KroneckerWeber
import InverseGalois.CFT.Scholz.AuxPrimeField
import InverseGalois.CFT.Scholz.FrobeniusDefect
import InverseGalois.CFT.Scholz.FrobeniusSymbol
import InverseGalois.CFT.Scholz.PrimeOrderInertia
import InverseGalois.CFT.Scholz.Realization
import InverseGalois.CFT.Scholz.UnramifiedSolution
import InverseGalois.CFT.SplitCompositum
import InverseGalois.CFT.SplitInertiaPrime
import InverseGalois.CFT.UnramifiedCompositum

/-!
# The residue correction of the Scholz–Reichardt construction

A central step of the Scholz–Reichardt induction is first solved by a field ramifying nowhere
outside the field the problem is posed over.  What that solution does not control is the residue
degrees: at a prime ramified in the field below, the image of an arithmetic Frobenius need not lie
in the image of the inertia group, and the difference is one element of the kernel of the central
step.  Correcting it is the last thing the induction needs.

The correction is a twist by a character of the units modulo an auxiliary modulus, read through the
cyclotomic subfield of a compositum.  The modulus is chosen before the defects are computed — its
prime factors avoid the primes already in play, are congruent to one modulo the relevant power of
the residue characteristic and split completely in the solution — and it is chosen so that every
prescribed vector of power residue symbols is realised.  Feeding it the vector of defects produces a
character which cancels the defect at every prime ramified below, while leaving the ramification
there untouched, because those primes do not divide the modulus.

At the primes dividing the modulus nothing has to be checked: they split completely in the solution,
so the whole decomposition group is seen only through the correcting character, and its image lies
in the kernel of the central step, a group of prime order in which ramification alone forces the
image of the inertia group to be everything.  Both families of primes are congruent to one modulo
the required power of the residue characteristic, so the level condition survives, and the field cut
out by the corrected solution satisfies Serre's condition in full.

Which vectors of power residue symbols a character can realise is where the residue characteristic
enters: the exponent vectors whose radicand is already a power in the constraint field constrain the
vectors that are available, so the defects have to be orthogonal to them.  That orthogonality is
carried as a hypothesis, and for an odd residue characteristic it holds because no nonzero exponent
vector has a radicand which is already a power there.

## Main results

* `InverseGalois.CFT.isScholzRealizable_of_solution_of_forall_prod_eq_one`: **a solution of a
  central Frattini embedding problem with kernel of prime order ramifying no more than the Scholz
  field below it, whose Frobenius defects are orthogonal to the exponent vectors already radical in
  the constraint field, gives a Scholz realization at the given level.**
* `InverseGalois.CFT.isScholzRealizable_of_centralStep`: **a central Frattini embedding problem
  with kernel of prime order over a Scholz realization at the next level has a Scholz realization
  at the given level.**

## Tags

Scholz–Reichardt, embedding problem, power residue symbol, split inertia, twist
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

open IntermediateField

variable {ℓ : ℕ}

/-! ### Realizations cut out by a homomorphism -/

/-- **A group realised by the fixed field of the kernel of a surjection is Scholz realizable**, as
soon as that fixed field satisfies Serre's condition. -/
theorem isScholzRealizable_of_isScholz_fixedField {G : Type*} [Group G] {n : ℕ} (F : Type*)
    [Field F] [NumberField F] [IsGalois ℚ F] (ψ : Gal(F/ℚ) →* G) (hψ : Function.Surjective ψ)
    (h : IsScholz ℓ n ↥(IntermediateField.fixedField ψ.ker)) : IsScholzRealizable G ℓ n := by
  haveI : NumberField ↥(IntermediateField.fixedField ψ.ker) := ⟨⟩
  exact isScholzRealizable_of_isGalois ↥(IntermediateField.fixedField ψ.ker) h
    ((IsGalois.normalAutEquivQuotient ψ.ker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))

/-! ### The corrected realization -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **A solution of a central Frattini embedding problem with kernel of prime order ramifying no
more than the Scholz field below it, whose Frobenius defects are orthogonal to the exponent vectors
already radical in the constraint field, gives a Scholz realization at the given level.**  The
solution is enlarged by the roots of unity of an auxiliary modulus, and twisted by the character of
the units modulo that modulus whose power residue symbols are the Frobenius defects at the primes
ramified below; the orthogonality is exactly what makes such a character available.  The twist
cancels those defects without disturbing the inertia there, and at the primes dividing the modulus
the decomposition group is seen only through the character, whose values lie in a kernel of prime
order. -/
theorem isScholzRealizable_of_solution_of_forall_prod_eq_one (hℓ : ℓ.Prime) [NeZero ℓ] {N : ℕ}
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H} (hf : Function.Surjective f)
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = ℓ)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hschA : IsScholz ℓ (N + 1) ↥A) (eA : Gal(↥A/ℚ) ≃* H)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] [IsGalois ℚ ↥L] (hAL : A ≤ L)
    (hramL : ramifiedSet ↥L ⊆ ramifiedSet ↥A) (ψ₀ : Gal(↥L/ℚ) ≃* G)
    (hcomp₀ : ∀ τ, f (ψ₀ τ) = eA (galRestrictLE hAL τ))
    (horth : ∀ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥M] [IsGalois ℚ ↥M]
      (hLM : L ≤ M) (Θ : Gal(↥M/ℚ) →* G), (∀ σ, Θ σ = ψ₀ (galRestrictLE hLM σ)) →
      ∀ ν : Multiplicative (ZMod ℓ) →* G, (∀ x, ν x ∈ f.ker) → Function.Injective ν →
      ∀ t : {q // q ∈ (finite_ramifiedSet ↥A).toFinset} → ZMod ℓ,
      (∀ q : {q // q ∈ (finite_ramifiedSet ↥A).toFinset}, ∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ * ν (Multiplicative.ofAdd (t q)) ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) →
      ∀ a : {q // q ∈ (finite_ramifiedSet ↥A).toFinset} → ZMod ℓ,
        (∃ u ∈ auxConstraintField L ℓ (N + 1), u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ)
          ((residueRadicand (finite_ramifiedSet ↥A).toFinset a : ℕ) : ℚ)) →
        ∑ i, t i * a i = 0) :
    IsScholzRealizable G ℓ N := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  -- the primes ramified in the field below
  set S : Finset ℕ := (finite_ramifiedSet ↥A).toFinset with hSdef
  have hSmem : ∀ q, q ∈ S ↔ q ∈ ramifiedSet ↥A := fun q => Set.Finite.mem_toFinset _
  have hSprime : ∀ q ∈ S, q.Prime := fun q hq => ((hSmem q).mp hq).1
  -- the auxiliary modulus
  obtain ⟨Q, hQ0, hQr, hQκ⟩ :=
    exists_modulus_of_forall_pow_eq (B := L) (ℓ := ℓ) (k := N + 1) (Nat.succ_ne_zero N) hSprime
  haveI : NeZero Q := ⟨hQ0⟩
  -- the field over which the correction takes place
  obtain ⟨M, hMdef, hsupeq⟩ :
      ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), M = L ⊔ cycSubfield Q ∧
        ramifiedSet ↥M = ramifiedSet ↥L ∪ ramifiedSet ↥(cycSubfield Q) := by
    refine ⟨L ⊔ cycSubfield Q, rfl, ?_⟩
    haveI : NumberField ↥(L ⊔ cycSubfield Q) := ⟨⟩
    have htop : IntermediateField.restrict (le_sup_left : L ≤ L ⊔ cycSubfield Q) ⊔
        IntermediateField.restrict (le_sup_right : cycSubfield Q ≤ L ⊔ cycSubfield Q) =
        (⊤ : IntermediateField ℚ ↥(L ⊔ cycSubfield Q)) := restrict_sup_restrict L (cycSubfield Q)
    have h1 : ramifiedSet ↥(⊤ : IntermediateField ℚ ↥(L ⊔ cycSubfield Q)) =
        ramifiedSet ↥L ∪ ramifiedSet ↥(cycSubfield Q) := by
      rw [← htop, ramifiedSet_sup, ramifiedSet_restrict, ramifiedSet_restrict]
    rw [← h1]
    exact (ramifiedSet_eq_of_ringEquiv (IntermediateField.topEquiv (F := ℚ)
      (E := ↥(L ⊔ cycSubfield Q))).toRingEquiv).symm
  haveI : FiniteDimensional ℚ ↥M := by rw [hMdef]; infer_instance
  haveI : Normal ℚ ↥M := by rw [hMdef]; infer_instance
  haveI : NumberField ↥M := ⟨⟩
  haveI : IsGalois ℚ ↥M := ⟨⟩
  have hLM : L ≤ M := by rw [hMdef]; exact le_sup_left
  have hCM : cycSubfield Q ≤ M := by rw [hMdef]; exact le_sup_right
  have hAM : A ≤ M := hAL.trans hLM
  -- the solution, read over that field
  set Ψ : Gal(↥M/ℚ) →* G := ψ₀.toMonoidHom.comp (galRestrictLE hLM) with hΨdef
  have hΨsurj : Function.Surjective Ψ := ψ₀.surjective.comp (galRestrictLE_surjective hLM)
  have hcompM : ∀ σ, f (Ψ σ) = eA (galRestrictLE hAM σ) := by
    intro σ
    rw [hΨdef]
    exact (hcomp₀ (galRestrictLE hLM σ)).trans
      (congrArg eA (galRestrictLE_galRestrictLE hAL hLM σ))
  have hcomp' : ∀ τ : Gal(↥M/ℚ), f (Ψ τ) =
      ((AlgEquiv.autCongr (IntermediateField.restrict_algEquiv hAM)).symm.trans eA)
        (AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hAM) τ) := hcompM
  -- the cyclotomic subfield of that field
  haveI : IsCyclotomicExtension {Q} ℚ ↥(IntermediateField.restrict hCM) :=
    IsCyclotomicExtension.equiv _ _ _ (IntermediateField.restrict_algEquiv hCM)
  -- the Frobenius defect at each prime ramified below
  have hex : ∀ q : {q // q ∈ S}, ∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
      ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∃ z ∈ f.ker,
        ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Ψ σ * z ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Ψ := by
    rintro ⟨q, hq⟩
    have hqp : q.Prime := hSprime q hq
    haveI : (Ideal.span {(q : ℤ)}).IsPrime := by
      rw [Ideal.span_singleton_prime (by exact_mod_cast hqp.ne_zero)]
      exact Nat.prime_iff_prime_int.mp hqp
    obtain ⟨⟨P, hPp, hPo⟩⟩ := (Ideal.span {(q : ℤ)}).nonempty_primesOver (S := 𝓞 ↥M)
    haveI := hPp
    haveI := hPo
    have hmemA : q ∈ ramifiedSet ↥(IntermediateField.restrict hAM) := by
      rw [ramifiedSet_restrict hAM]
      exact (hSmem q).mp hq
    obtain ⟨z, hz, hzspec⟩ :=
      exists_mem_ker_mul_mem_map_inertia (p := q) (IntermediateField.restrict hAM) hmemA
        (isScholz_restrict hAM hschA).2 P Ψ
        ((AlgEquiv.autCongr (IntermediateField.restrict_algEquiv hAM)).symm.trans eA) hcomp'
    exact ⟨P, hPp, hPo, z, hz, hzspec⟩
  choose Pq hPqp hPqo zq hzq hzqspec using hex
  -- the kernel of the central step as a cyclic group of order `ℓ`
  have hcardZ : Nat.card (Multiplicative (ZMod ℓ)) = ℓ := by simp
  set ι : Multiplicative (ZMod ℓ) ≃* ↥f.ker := mulEquivOfPrimeCardEq hcardZ hcard with hιdef
  -- the correcting character
  set t : {q // q ∈ S} → ZMod ℓ := fun q => Multiplicative.toAdd (ι.symm ⟨zq q, hzq q⟩) with htdef
  have hνval : ∀ q : {q // q ∈ S},
      (f.ker.subtype.comp ι.toMonoidHom) (Multiplicative.ofAdd (t q)) = zq q :=
    fun q => congrArg Subtype.val (ι.apply_symm_apply _)
  -- the defects are orthogonal to the exponent vectors already radical in the constraint field
  have hadm : ∀ a : {q // q ∈ S} → ZMod ℓ,
      (∃ u ∈ auxConstraintField L ℓ (N + 1), u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ)
        ((residueRadicand S a : ℕ) : ℚ)) → ∑ i, t i * a i = 0 := by
    refine horth M hLM Ψ (fun σ => rfl) (f.ker.subtype.comp ι.toMonoidHom) (fun x => (ι x).2)
      (fun x y hxy => ι.injective (Subtype.ext hxy)) t fun q => ⟨Pq q, hPqp q, hPqo q, ?_⟩
    intro σ hσ
    rw [hνval q]
    exact hzqspec q σ hσ
  obtain ⟨κ, hκ⟩ := hQκ t hadm
  set χ₀ : Gal(↥M/ℚ) →* ↥f.ker :=
    ι.toMonoidHom.comp (κ.comp
      ((IsCyclotomicExtension.Rat.galEquivZMod Q ↥(IntermediateField.restrict hCM)).toMonoidHom.comp
        (AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hCM)))) with hχ₀def
  set χ : Gal(↥M/ℚ) →* G := f.ker.subtype.comp χ₀ with hχdef
  have hχker : ∀ x, χ x ∈ f.ker := by
    intro x
    rw [hχdef]
    exact (χ₀ x).2
  have hχcen : ∀ x, χ x ∈ Subgroup.center G := fun x => hZ (hχker x)
  -- the character kills inertia away from the modulus
  have hχ1 : ∀ q : ℕ, q.Prime → ¬ q ∣ Q → ∀ P : Ideal (𝓞 ↥M), P.IsPrime →
      P.LiesOver (Ideal.span {(q : ℤ)}) → ∀ σ ∈ Ideal.inertia Gal(↥M/ℚ) P, χ σ = 1 := by
    intro q hqp hqQ P hPp hPo σ hσ
    haveI := hPp
    haveI := hPo
    have hCram : q ∉ ramifiedSet ↥(IntermediateField.restrict hCM) := by
      rw [ramifiedSet_restrict hCM]
      exact fun hmem => hqQ (Nat.dvd_of_mem_primeFactors
        (Finset.mem_coe.mp (ramifiedSet_subset_primeFactors Q ↥(cycSubfield Q) hmem)))
    have h1 : AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hCM) σ = 1 :=
      restrictNormalHom_eq_one_of_mem_inertia (IntermediateField.restrict hCM) hqp P hCram hσ
    rw [hχdef, hχ₀def]
    simp [h1]
  -- the character takes the value of the defect on an arithmetic Frobenius
  have hχ2 : ∀ (q : ℕ) (hqS : q ∈ S), ¬ q ∣ Q → ∀ P : Ideal (𝓞 ↥M), P.IsPrime →
      P.LiesOver (Ideal.span {(q : ℤ)}) → ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
        χ σ = zq ⟨q, hqS⟩ := by
    intro q hqS hqQ P hPp hPo σ hσ
    haveI := hPp
    haveI := hPo
    have hval := map_galEquivZMod_restrictNormal_of_isArithFrobAt
      (IntermediateField.restrict hCM) κ (hSprime q hqS) hqQ P hσ
    have hcalc : χ σ = f.ker.subtype (ι (Multiplicative.ofAdd (powerResidueSymbol κ q))) := by
      rw [hχdef, hχ₀def]
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hval]
    rw [hcalc, hκ q hqS]
    simp only [htdef]
    exact congrArg Subtype.val (ι.apply_symm_apply _)
  -- the corrected solution
  set ψ' : Gal(↥M/ℚ) →* G := mulCentral Ψ χ hχcen with hψ'def
  have hψ'surj : Function.Surjective ψ' := surjective_mulCentral hf hfr hΨsurj hχcen hχker
  -- the corrected solution has split inertia
  have hsplitψ' : IsSplitInertia ↥(IntermediateField.fixedField ψ'.ker) := by
    refine isSplitInertia_fixedField_ker_of_exists ψ' fun q hqram => ?_
    have hqp : q.Prime := hqram.1
    haveI : (Ideal.span {(q : ℤ)}).IsPrime := by
      rw [Ideal.span_singleton_prime (by exact_mod_cast hqp.ne_zero)]
      exact Nat.prime_iff_prime_int.mp hqp
    by_cases hqS : q ∈ S
    · -- a prime ramified below: the correction cancels the defect
      have hqQ : ¬ q ∣ Q := fun hd => (hQr q hqp hd).1 hqS
      obtain ⟨P, hPp, hPo, hzspec⟩ : ∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
          ∃ _ : P.LiesOver (Ideal.span {(q : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
            Ψ σ * zq ⟨q, hqS⟩ ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Ψ :=
        ⟨Pq ⟨q, hqS⟩, hPqp ⟨q, hqS⟩, hPqo ⟨q, hqS⟩, hzqspec ⟨q, hqS⟩⟩
      haveI := hPp
      haveI := hPo
      refine ⟨P, hPp, hPo, ?_⟩
      have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_natCast hqp hPo
      haveI : Finite (𝓞 ↥M ⧸ P) := finite_quotient_of_ne_bot P hP0
      obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ₀ P :=
        ⟨_, IsArithFrobAt.arithFrobAt ℤ Gal(↥M/ℚ) P⟩
      have hag : ∀ σ ∈ Ideal.inertia Gal(↥M/ℚ) P, ψ' σ = Ψ σ := by
        intro σ hσ
        rw [hψ'def, mulCentral_apply, hχ1 q hqp hqQ P hPp hPo σ hσ, mul_one]
      have hmapeq : (Ideal.inertia Gal(↥M/ℚ) P).map ψ' = (Ideal.inertia Gal(↥M/ℚ) P).map Ψ := by
        ext x
        simp only [Subgroup.mem_map]
        constructor
        · rintro ⟨σ, hσ, rfl⟩
          exact ⟨σ, hσ, (hag σ hσ).symm⟩
        · rintro ⟨σ, hσ, rfl⟩
          exact ⟨σ, hσ, hag σ hσ⟩
      refine map_stabilizer_le_map_inertia P ψ' hP0 hσ₀ ?_
      rw [hmapeq, hψ'def, mulCentral_apply, hχ2 q hqS hqQ P hPp hPo σ₀ hσ₀]
      exact hzspec σ₀ hσ₀
    · -- a prime dividing the modulus: the whole decomposition group lands in the kernel
      have hqM : q ∈ ramifiedSet ↥M :=
        ramifiedSet_subset ↥(IntermediateField.fixedField ψ'.ker) ↥M hqram
      rw [hsupeq] at hqM
      have hqQ : q ∣ Q := by
        rcases hqM with h | h
        · exact absurd ((hSmem q).mpr (hramL h)) hqS
        · exact Nat.dvd_of_mem_primeFactors
            (Finset.mem_coe.mp (ramifiedSet_subset_primeFactors Q ↥(cycSubfield Q) h))
      obtain ⟨-, -, -, hsplitL⟩ := hQr q hqp hqQ
      obtain ⟨⟨P, hPp, hPo⟩⟩ := (Ideal.span {(q : ℤ)}).nonempty_primesOver (S := 𝓞 ↥M)
      haveI := hPp
      haveI := hPo
      refine ⟨P, hPp, hPo, ?_⟩
      refine map_stabilizer_le_map_inertia_of_card_prime hqp P ψ' hℓ hcard ?_ hqram
      rintro - ⟨σ, hσ, rfl⟩
      haveI := liesOver_under_intermediateField (p := q) (IntermediateField.restrict hLM) P
      haveI : IsGalois ℚ ↥(IntermediateField.restrict hLM) := ⟨⟩
      have hres : AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hLM) σ = 1 := by
        have hmem := restrictNormal_mem_stabilizer (IntermediateField.restrict hLM) P hσ
        rw [stabilizer_eq_bot_of_splitsCompletely ↥(IntermediateField.restrict hLM) hqp
          (P.under (𝓞 ↥(IntermediateField.restrict hLM)))
          (splitsCompletely_restrict hLM hqp hsplitL)] at hmem
        simpa using hmem
      have hgr : galRestrictLE hLM σ = 1 :=
        MonoidHom.mem_ker.mp (by
          rw [ker_galRestrictLE hLM, ← IntermediateField.restrictNormalHom_ker]
          exact MonoidHom.mem_ker.mpr hres)
      have hΨ1 : Ψ σ = 1 := by
        rw [hΨdef]
        simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hgr, map_one]
      rw [hψ'def, mulCentral_apply, hΨ1, one_mul]
      exact hχker σ
  -- the corrected solution keeps the level
  have hlevelM : IsLevel ℓ (N + 1) ↥M := by
    intro q hq
    rw [hsupeq] at hq
    rcases hq with hq | hq
    · exact hschA.1 q (hramL hq)
    · have hmem : q ∈ Q.primeFactors :=
        Finset.mem_coe.mp (ramifiedSet_subset_primeFactors Q ↥(cycSubfield Q) hq)
      exact (hQr q (Nat.prime_of_mem_primeFactors hmem)
        (Nat.dvd_of_mem_primeFactors hmem)).2.2.1
  haveI : NumberField ↥(IntermediateField.fixedField ψ'.ker) := ⟨⟩
  have hlevel : IsLevel ℓ N ↥(IntermediateField.fixedField ψ'.ker) :=
    (IsLevel.of_tower (E := ↥(IntermediateField.fixedField ψ'.ker)) (M := ↥M) hlevelM).mono
      (Nat.le_succ N)
  exact isScholzRealizable_of_isScholz_fixedField ↥M ψ' hψ'surj ⟨hlevel, hsplitψ'⟩

/-- **A central Frattini embedding problem with kernel of prime order over a Scholz realization at
the next level has a Scholz realization at the given level.**  The solution ramifying no more than
the field below is enlarged by the roots of unity of an auxiliary modulus, and twisted by the
character of the units modulo that modulus whose power residue symbols are the Frobenius defects at
the primes ramified below.  For an odd residue characteristic there is nothing to check about which
vectors of symbols are available: adjoining the roots of unity leaves the constraint field a
nilpotent extension of the rationals, in which a product of distinct primes is a power only when the
exponents all vanish. -/
theorem isScholzRealizable_of_centralStep (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hrank : IsInertiaRankOneAt ℓ) {N : ℕ} {G H : Type} [Group G] [Group H] [Finite G]
    {f : G →* H} (hf : Function.Surjective f) (hpg : IsPGroup ℓ G)
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = ℓ)
    (hHdvd : Nat.card H ∣ ℓ ^ N) (hH : IsScholzRealizable H ℓ (N + 1)) :
    IsScholzRealizable G ℓ N := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨R⟩ := hH
  obtain ⟨L, hAL, hNFL, hGalL, hramL, ψ₀, hcomp₀⟩ :=
    exists_galEquiv_ramifiedSet_subset hℓ hodd hrank hf hpg hZ hfr hcard hHdvd R.carrier
      R.isScholz R.galEquiv
  haveI := hNFL
  haveI := hGalL
  refine isScholzRealizable_of_solution_of_forall_prod_eq_one hℓ hf hZ hfr hcard R.carrier
    R.isScholz R.galEquiv L hAL hramL ψ₀ hcomp₀ ?_
  intro M _ _ hLM Θ _ ν _ _ t _ a ha
  obtain ⟨u, huA, hu⟩ := ha
  obtain ⟨ζ, hζ, hζA⟩ :=
    isPrimitiveRoot_mem_auxConstraintField (B := L) (ℓ := ℓ) (k := N + 1) (Nat.succ_ne_zero N)
  have ha0 : a = 0 :=
    eq_zero_of_pow_eq_residueRadicand hodd
      (isNilpotent_auxConstraintField (hpg.of_equiv ψ₀.symm)) hζ hζA
      (fun q hq => ((Set.Finite.mem_toFinset _).mp hq).1) huA hu
  simp [ha0]

end InverseGalois.CFT
