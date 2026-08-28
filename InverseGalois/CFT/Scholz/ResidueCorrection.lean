/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CutField
import InverseGalois.CFT.KroneckerWeber
import InverseGalois.CFT.Scholz.AuxPrimeField
import InverseGalois.CFT.Scholz.FrobeniusDefect
import InverseGalois.CFT.Scholz.FrobeniusSymbol
import InverseGalois.CFT.Scholz.PrimeOrderInertia
import InverseGalois.CFT.Scholz.Realization
import InverseGalois.CFT.Scholz.SplitInertiaAt
import InverseGalois.CFT.Scholz.SubfieldScholz
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

At the primes not ramified below nothing has to be checked, as long as they split completely in the
field the problem is posed over: the whole decomposition group is then seen inside the kernel of the
central step, a group of prime order in which ramification alone forces the image of the inertia
group to be everything.  That covers the primes dividing the modulus, which split completely in the
solution, and equally any fresh ramification the solution itself carries over a prime split
completely below.  All these primes are congruent to one modulo the required power of the residue
characteristic, so the level condition survives, and the field cut out by the corrected solution
satisfies Serre's condition in full.

Which vectors of power residue symbols a character can realise is where the residue characteristic
enters: the exponent vectors whose radicand is already a power in the constraint field constrain the
vectors that are available, so the defects have to be orthogonal to them.  That orthogonality is
carried as a hypothesis, and for an odd residue characteristic it holds because no nonzero exponent
vector has a radicand which is already a power there.

## Main results

* `InverseGalois.CFT.exists_scholz_solution_lift_of_forall_prod_eq_one`: **the same correction
  performed on a solution presented as a quotient of a fixed cover, carrying the cover along and
  leaving untouched every subfield of it cut out by a character trivial on a chosen lift of the
  kernel.**
* `InverseGalois.CFT.exists_scholz_solution_of_forall_prod_eq_one`: **a solution of a central
  Frattini embedding problem with kernel of prime order ramifying harmlessly over the Scholz field
  below it, whose Frobenius defects are orthogonal to the exponent vectors already radical in the
  constraint field, is corrected to a Scholz field over that one.**
* `InverseGalois.CFT.isScholzRealizable_of_solution_of_forall_prod_eq_one`: the same statement,
  read as a Scholz realization at the given level.
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
/-- **The residue correction of a solution presented as a quotient of a fixed cover, carrying the
cover along and leaving untouched every subfield of it cut out by a character trivial on a chosen
lift of the kernel.**  The solution is enlarged by the roots of unity of an auxiliary modulus, and
twisted by the character of the units modulo that modulus whose power residue symbols are the
Frobenius defects at the primes ramified below; the orthogonality carried as a hypothesis is exactly
what makes such a character available.  The twist cancels those defects without disturbing the
inertia there, and at a prime split completely below — one dividing the modulus, or one the solution
ramifies at afresh — the decomposition group lands in the kernel of the step, a group of prime
order.

The defects are read at a prescribed finite set of primes containing the ramified ones, whose
further members split completely below; at such a member the defect is an arithmetic Frobenius
itself, again an element of the kernel of the step.  Cancelling the defect there costs nothing and
buys residue degree one at every prime of the set, ramified in the correction or not.

The twist is applied to the cover rather than to its quotient, along a homomorphic lift of the
kernel of the step.  A character of the cover that kills the image of that lift therefore takes the
same values before and after the twist, so the subfield of the cover it cuts out is the same one; in
particular the ramification of the twisted cover is bounded by that of the untwisted one together
with the corrected solution. -/
theorem exists_scholz_solution_lift_of_forall_prod_eq_one (hℓ : ℓ.Prime) [NeZero ℓ] {N : ℕ}
    {Ĝ G H : Type} [Group Ĝ] [Group G] [Group H] [Finite Ĝ]
    {f : G →* H} {g : Ĝ →* G} {fg : Ĝ →* H} (hfg : ∀ x, fg x = f (g x))
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hZ : fg.ker ≤ Subgroup.center Ĝ) (hfr : fg.ker ≤ frattini Ĝ)
    (hcard : Nat.card ↥f.ker = ℓ) (s : ↥f.ker →* ↥fg.ker) (hs : ∀ z : ↥f.ker, g ↑(s z) = ↑z)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hschA : IsScholz ℓ (N + 1) ↥A) (eA : Gal(↥A/ℚ) ≃* H)
    (T : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥T] [IsGalois ℚ ↥T] (hAT : A ≤ T)
    (hramT : IsScholzOver ℓ (N + 1) ↥A ↥T) (ψ₀ : Gal(↥T/ℚ) ≃* Ĝ)
    (hcomp₀ : ∀ τ, fg (ψ₀ τ) = eA (galRestrictLE hAT τ)) (S : Finset ℕ)
    (hSprime : ∀ q ∈ S, q.Prime) (hAS : ∀ q ∈ ramifiedSet ↥A, q ∈ S)
    (hSsplit : ∀ q ∈ S, q ∉ ramifiedSet ↥A → SplitsCompletely ↥A q)
    (horth : ∀ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥M] [IsGalois ℚ ↥M]
      (hTM : T ≤ M) (Θ : Gal(↥M/ℚ) →* G), (∀ σ, Θ σ = g (ψ₀ (galRestrictLE hTM σ))) →
      ∀ ν : Multiplicative (ZMod ℓ) →* G, (∀ x, ν x ∈ f.ker) → Function.Injective ν →
      ∀ t : {q // q ∈ S} → ZMod ℓ,
      (∀ q : {q // q ∈ S}, ∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ * ν (Multiplicative.ofAdd (t q)) ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) →
      (∀ q : {q // q ∈ S}, (∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) → t q = 0) →
      ∀ a : {q // q ∈ S} → ZMod ℓ,
        (∃ u ∈ auxConstraintField T ℓ (N + 1), u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ)
          ((residueRadicand S a : ℕ) : ℚ)) →
        ∑ i, t i * a i = 0) :
    ∃ (E T' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAE : A ≤ E) (hET' : E ≤ T')
      (_ : NumberField ↥E) (_ : IsGalois ℚ ↥E) (_ : NumberField ↥T') (_ : IsGalois ℚ ↥T'),
      IsScholz ℓ (N + 1) ↥E ∧ (∀ q ∈ S, IsSplitInertiaAt ↥E q) ∧
        ramifiedSet ↥T' ⊆ ramifiedSet ↥T ∪ ramifiedSet ↥E ∧ IsLevel ℓ (N + 1) ↥T' ∧
        ∃ (ψ : Gal(↥E/ℚ) ≃* G) (Ψ : Gal(↥T'/ℚ) ≃* Ĝ),
          (∀ τ, f (ψ τ) = eA (galRestrictLE hAE τ)) ∧
          (∀ τ, ψ (galRestrictLE hET' τ) = g (Ψ τ)) ∧
          ∀ (W : Type) [Group W] (u : Ĝ →* W), (∀ z : ↥f.ker, u ↑(s z) = 1) →
            cutField (u.comp Ψ.toMonoidHom) = cutField (u.comp ψ₀.toMonoidHom) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Finite G := Finite.of_surjective _ hg
  -- the two presentations of the cover
  have hfgsurj : Function.Surjective fg := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    obtain ⟨z, rfl⟩ := hg x
    exact ⟨z, by rw [hfg]; exact hx⟩
  have hZ' : f.ker ≤ Subgroup.center G := by
    intro x hx
    obtain ⟨y, rfl⟩ := hg x
    have hy : y ∈ fg.ker := MonoidHom.mem_ker.mpr (by rw [hfg]; exact MonoidHom.mem_ker.mp hx)
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := hg z
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZ hy) w]
  -- the auxiliary modulus
  obtain ⟨Q, hQ0, hQr, hQκ⟩ :=
    exists_modulus_of_forall_pow_eq (B := T) (ℓ := ℓ) (k := N + 1) (Nat.succ_ne_zero N) hSprime
  haveI : NeZero Q := ⟨hQ0⟩
  -- the field over which the correction takes place
  obtain ⟨M, hMdef, hsupeq⟩ :
      ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), M = T ⊔ cycSubfield Q ∧
        ramifiedSet ↥M = ramifiedSet ↥T ∪ ramifiedSet ↥(cycSubfield Q) :=
    ⟨T ⊔ cycSubfield Q, rfl, ramifiedSet_sup_intermediateField T (cycSubfield Q)⟩
  haveI : FiniteDimensional ℚ ↥M := by rw [hMdef]; infer_instance
  haveI : Normal ℚ ↥M := by rw [hMdef]; infer_instance
  haveI : NumberField ↥M := ⟨⟩
  haveI : IsGalois ℚ ↥M := ⟨⟩
  have hTM : T ≤ M := by rw [hMdef]; exact le_sup_left
  have hCM : cycSubfield Q ≤ M := by rw [hMdef]; exact le_sup_right
  have hAM : A ≤ M := hAT.trans hTM
  -- the cover and the solution, read over that field
  obtain ⟨Φ, hΦapp⟩ : ∃ Φ : Gal(↥M/ℚ) →* Ĝ, ∀ σ, Φ σ = ψ₀ (galRestrictLE hTM σ) :=
    ⟨ψ₀.toMonoidHom.comp (galRestrictLE hTM), fun _ => rfl⟩
  have hΦsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨τ, rfl⟩ := ψ₀.surjective y
    obtain ⟨σ, rfl⟩ := galRestrictLE_surjective hTM τ
    exact ⟨σ, hΦapp σ⟩
  obtain ⟨Ψ, hΨapp⟩ : ∃ Ψ : Gal(↥M/ℚ) →* G, ∀ σ, Ψ σ = g (Φ σ) := ⟨g.comp Φ, fun _ => rfl⟩
  have hΨsurj : Function.Surjective Ψ := by
    intro x
    obtain ⟨y, rfl⟩ := hg x
    obtain ⟨σ, rfl⟩ := hΦsurj y
    exact ⟨σ, hΨapp σ⟩
  have hcompM : ∀ σ, f (Ψ σ) = eA (galRestrictLE hAM σ) := by
    intro σ
    have h1 : f (Ψ σ) = fg (Φ σ) := by rw [hΨapp σ, hfg]
    rw [h1, hΦapp σ]
    exact (hcomp₀ (galRestrictLE hTM σ)).trans
      (congrArg eA (galRestrictLE_galRestrictLE hAT hTM σ))
  have hcomp' : ∀ τ : Gal(↥M/ℚ), f (Ψ τ) =
      ((AlgEquiv.autCongr (IntermediateField.restrict_algEquiv hAM)).symm.trans eA)
        (AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hAM) τ) := hcompM
  -- the cyclotomic subfield of that field
  haveI : IsCyclotomicExtension {Q} ℚ ↥(IntermediateField.restrict hCM) :=
    IsCyclotomicExtension.equiv _ _ _ (IntermediateField.restrict_algEquiv hCM)
  -- at a prime split completely below, the decomposition group lands in the kernel of the step
  have hkerD : ∀ q : ℕ, q.Prime → SplitsCompletely ↥A q → ∀ (P : Ideal (𝓞 ↥M)) (_ : P.IsPrime)
      (_ : P.LiesOver (Ideal.span {(q : ℤ)})) (σ : Gal(↥M/ℚ)),
      σ ∈ MulAction.stabilizer Gal(↥M/ℚ) P → Ψ σ ∈ f.ker := by
    intro q hqp hsplitA P hPp hPo σ hσ
    haveI := hPp
    haveI := hPo
    haveI := liesOver_under_intermediateField (p := q) (IntermediateField.restrict hAM) P
    haveI : IsGalois ℚ ↥(IntermediateField.restrict hAM) := ⟨⟩
    have hres : AlgEquiv.restrictNormalHom ↥(IntermediateField.restrict hAM) σ = 1 := by
      have hmem := restrictNormal_mem_stabilizer (IntermediateField.restrict hAM) P hσ
      rw [stabilizer_eq_bot_of_splitsCompletely ↥(IntermediateField.restrict hAM) hqp
        (P.under (𝓞 ↥(IntermediateField.restrict hAM)))
        (splitsCompletely_restrict hAM hqp hsplitA)] at hmem
      simpa using hmem
    have hgr : galRestrictLE hAM σ = 1 :=
      MonoidHom.mem_ker.mp (by
        rw [ker_galRestrictLE hAM, ← IntermediateField.restrictNormalHom_ker]
        exact MonoidHom.mem_ker.mpr hres)
    rw [MonoidHom.mem_ker, hcompM σ, hgr, map_one]
  -- the Frobenius defect at each prime ramified below
  have hex : ∀ q : {q // q ∈ S}, ∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
      ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∃ z ∈ f.ker,
        (∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Ψ σ * z ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Ψ) ∧
        ((∃ P' : Ideal (𝓞 ↥M), ∃ _ : P'.IsPrime,
          ∃ _ : P'.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P' →
            Ψ σ ∈ (Ideal.inertia Gal(↥M/ℚ) P').map Ψ) → z = 1) := by
    rintro ⟨q, hq⟩
    by_cases htriv : ∃ P' : Ideal (𝓞 ↥M), ∃ _ : P'.IsPrime,
        ∃ _ : P'.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P' →
          Ψ σ ∈ (Ideal.inertia Gal(↥M/ℚ) P').map Ψ
    · obtain ⟨P, hPp, hPo, hP⟩ := htriv
      exact ⟨P, hPp, hPo, 1, one_mem _, fun σ hσ => by simpa using hP σ hσ, fun _ => rfl⟩
    have hqp : q.Prime := hSprime q hq
    haveI : (Ideal.span {(q : ℤ)}).IsPrime := by
      rw [Ideal.span_singleton_prime (by exact_mod_cast hqp.ne_zero)]
      exact Nat.prime_iff_prime_int.mp hqp
    obtain ⟨⟨P, hPp, hPo⟩⟩ := (Ideal.span {(q : ℤ)}).nonempty_primesOver (S := 𝓞 ↥M)
    haveI := hPp
    haveI := hPo
    by_cases hqA : q ∈ ramifiedSet ↥A
    · have hmemA : q ∈ ramifiedSet ↥(IntermediateField.restrict hAM) := by
        rw [ramifiedSet_restrict hAM]
        exact hqA
      obtain ⟨z, hz, hzspec⟩ :=
        exists_mem_ker_mul_mem_map_inertia (p := q) (IntermediateField.restrict hAM) hmemA
          (isScholz_restrict hAM hschA).2 P Ψ
          ((AlgEquiv.autCongr (IntermediateField.restrict_algEquiv hAM)).symm.trans eA) hcomp'
      exact ⟨P, hPp, hPo, z, hz, hzspec, fun hc => absurd hc htriv⟩
    · -- a prime split completely below: an arithmetic Frobenius is itself the defect
      have hsplitA : SplitsCompletely ↥A q := hSsplit q hq hqA
      have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_natCast hqp hPo
      haveI : Finite (𝓞 ↥M ⧸ P) := finite_quotient_of_ne_bot P hP0
      obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ₀ P :=
        ⟨_, IsArithFrobAt.arithFrobAt ℤ Gal(↥M/ℚ) P⟩
      refine ⟨P, hPp, hPo, (Ψ σ₀)⁻¹,
        inv_mem (hkerD q hqp hsplitA P hPp hPo σ₀ (mem_stabilizer_of_isArithFrobAt P hσ₀)),
        fun σ hσ => ?_, fun hc => absurd hc htriv⟩
      have hmem : σ * σ₀⁻¹ ∈ Ideal.inertia Gal(↥M/ℚ) P := hσ.mul_inv_mem_inertia hσ₀
      have heq : Ψ σ * (Ψ σ₀)⁻¹ = Ψ (σ * σ₀⁻¹) := by rw [map_mul, map_inv]
      rw [heq]
      exact Subgroup.mem_map_of_mem Ψ hmem
  choose Pq hPqp hPqo zq hzq hzqspec hztriv using hex
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
      (∃ u ∈ auxConstraintField T ℓ (N + 1), u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ)
        ((residueRadicand S a : ℕ) : ℚ)) → ∑ i, t i * a i = 0 := by
    refine horth M hTM Ψ (fun σ => by rw [hΨapp σ, hΦapp σ]) (f.ker.subtype.comp ι.toMonoidHom)
      (fun x => (ι x).2)
      (fun x y hxy => ι.injective (Subtype.ext hxy)) t (fun q => ⟨Pq q, hPqp q, hPqo q, ?_⟩) ?_
    · intro σ hσ
      rw [hνval q]
      exact hzqspec q σ hσ
    · intro q hq
      have h1 : (⟨zq q, hzq q⟩ : ↥f.ker) = 1 := Subtype.ext (hztriv q hq)
      simp [htdef, h1]
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
  have hχcen : ∀ x, χ x ∈ Subgroup.center G := fun x => hZ' (hχker x)
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
  -- the same correction, applied to the cover along the chosen lift of the kernel
  obtain ⟨η, hηapp⟩ : ∃ η : Gal(↥M/ℚ) →* Ĝ, ∀ x, η x = ↑(s (χ₀ x)) :=
    ⟨fg.ker.subtype.comp (s.comp χ₀), fun _ => rfl⟩
  have hηker : ∀ x, η x ∈ fg.ker := fun x => by rw [hηapp x]; exact (s (χ₀ x)).2
  have hηcen : ∀ x, η x ∈ Subgroup.center Ĝ := fun x => hZ (hηker x)
  have hgη : ∀ x, g (η x) = χ x := by
    intro x
    rw [hηapp x, hχdef]
    exact hs (χ₀ x)
  obtain ⟨Φ', hΦ'app, hΦ'surj⟩ :
      ∃ Φ' : Gal(↥M/ℚ) →* Ĝ, (∀ σ, Φ' σ = Φ σ * η σ) ∧ Function.Surjective Φ' :=
    ⟨mulCentral Φ η hηcen, fun _ => rfl, surjective_mulCentral hfgsurj hfr hΦsurj hηcen hηker⟩
  have hgΦ' : ∀ σ, g (Φ' σ) = ψ' σ := by
    intro σ
    rw [hΦ'app σ, map_mul, hgη σ, ← hΨapp σ, hψ'def, mulCentral_apply]
  have hψ'surj : Function.Surjective ψ' := by
    intro x
    obtain ⟨y, rfl⟩ := hg x
    obtain ⟨σ, rfl⟩ := hΦ'surj y
    exact ⟨σ, (hgΦ' σ).symm⟩
  -- at each prime of the prescribed set the correction cancels the defect
  have habsorb : ∀ q : {q // q ∈ S}, (MulAction.stabilizer Gal(↥M/ℚ) (Pq q)).map ψ' ≤
      (Ideal.inertia Gal(↥M/ℚ) (Pq q)).map ψ' := by
    rintro ⟨q, hqS⟩
    have hqp : q.Prime := hSprime q hqS
    have hqQ : ¬ q ∣ Q := fun hd => (hQr q hqp hd).1 hqS
    haveI := hPqp ⟨q, hqS⟩
    haveI := hPqo ⟨q, hqS⟩
    have hP0 : Pq ⟨q, hqS⟩ ≠ ⊥ := ne_bot_of_liesOver_natCast hqp (hPqo ⟨q, hqS⟩)
    haveI : Finite (𝓞 ↥M ⧸ Pq ⟨q, hqS⟩) := finite_quotient_of_ne_bot _ hP0
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ₀ (Pq ⟨q, hqS⟩) :=
      ⟨_, IsArithFrobAt.arithFrobAt ℤ Gal(↥M/ℚ) _⟩
    have hag : ∀ σ ∈ Ideal.inertia Gal(↥M/ℚ) (Pq ⟨q, hqS⟩), ψ' σ = Ψ σ := by
      intro σ hσ
      rw [hψ'def, mulCentral_apply,
        hχ1 q hqp hqQ (Pq ⟨q, hqS⟩) (hPqp ⟨q, hqS⟩) (hPqo ⟨q, hqS⟩) σ hσ, mul_one]
    have hmapeq : (Ideal.inertia Gal(↥M/ℚ) (Pq ⟨q, hqS⟩)).map ψ' =
        (Ideal.inertia Gal(↥M/ℚ) (Pq ⟨q, hqS⟩)).map Ψ := by
      ext x
      simp only [Subgroup.mem_map]
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        exact ⟨σ, hσ, (hag σ hσ).symm⟩
      · rintro ⟨σ, hσ, rfl⟩
        exact ⟨σ, hσ, hag σ hσ⟩
    refine map_stabilizer_le_map_inertia (Pq ⟨q, hqS⟩) ψ' hP0 hσ₀ ?_
    rw [hmapeq, hψ'def, mulCentral_apply,
      hχ2 q hqS hqQ (Pq ⟨q, hqS⟩) (hPqp ⟨q, hqS⟩) (hPqo ⟨q, hqS⟩) σ₀ hσ₀]
    exact hzqspec ⟨q, hqS⟩ σ₀ hσ₀
  -- the corrected solution has split inertia
  have hsplitψ' : IsSplitInertia ↥(IntermediateField.fixedField ψ'.ker) := by
    refine isSplitInertia_fixedField_ker_of_exists ψ' fun q hqram => ?_
    have hqp : q.Prime := hqram.1
    haveI : (Ideal.span {(q : ℤ)}).IsPrime := by
      rw [Ideal.span_singleton_prime (by exact_mod_cast hqp.ne_zero)]
      exact Nat.prime_iff_prime_int.mp hqp
    by_cases hqS : q ∈ S
    · -- a prime of the prescribed set: the correction cancels the defect
      exact ⟨Pq ⟨q, hqS⟩, hPqp ⟨q, hqS⟩, hPqo ⟨q, hqS⟩, habsorb ⟨q, hqS⟩⟩
    · -- a prime outside it: the whole decomposition group lands in the kernel
      have hqM : q ∈ ramifiedSet ↥M :=
        ramifiedSet_subset ↥(IntermediateField.fixedField ψ'.ker) ↥M hqram
      rw [hsupeq] at hqM
      have hsplitA : SplitsCompletely ↥A q := by
        rcases hqM with h | h
        · exact ((hramT q h).resolve_left fun hA => hqS (hAS q hA)).2
        · have hqQ : q ∣ Q := Nat.dvd_of_mem_primeFactors
            (Finset.mem_coe.mp (ramifiedSet_subset_primeFactors Q ↥(cycSubfield Q) h))
          exact splitsCompletely_of_le hAT hqp (hQr q hqp hqQ).2.2.2
      obtain ⟨⟨P, hPp, hPo⟩⟩ := (Ideal.span {(q : ℤ)}).nonempty_primesOver (S := 𝓞 ↥M)
      haveI := hPp
      haveI := hPo
      refine ⟨P, hPp, hPo, ?_⟩
      refine map_stabilizer_le_map_inertia_of_card_prime hqp P ψ' hℓ hcard ?_ hqram
      rintro - ⟨σ, hσ, rfl⟩
      rw [hψ'def, mulCentral_apply]
      exact Subgroup.mul_mem _ (hkerD q hqp hsplitA P hPp hPo σ hσ) (hχker σ)
  -- the corrected solution has residue degree one at every prime of the prescribed set
  have hsplitS : ∀ q ∈ S, IsSplitInertiaAt ↥(IntermediateField.fixedField ψ'.ker) q := fun q hqS =>
    isSplitInertiaAt_fixedField_ker_of_exists ψ' (hSprime q hqS)
      ⟨Pq ⟨q, hqS⟩, hPqp ⟨q, hqS⟩, hPqo ⟨q, hqS⟩, habsorb ⟨q, hqS⟩⟩
  -- the corrected solution keeps the level
  have hlevelM : IsLevel ℓ (N + 1) ↥M := by
    intro q hq
    rw [hsupeq] at hq
    rcases hq with hq | hq
    · exact (hramT q hq).elim (hschA.1 q) And.left
    · have hmem : q ∈ Q.primeFactors :=
        Finset.mem_coe.mp (ramifiedSet_subset_primeFactors Q ↥(cycSubfield Q) hq)
      exact (hQr q (Nat.prime_of_mem_primeFactors hmem)
        (Nat.dvd_of_mem_primeFactors hmem)).2.2.1
  haveI : NumberField ↥(IntermediateField.fixedField ψ'.ker) := ⟨⟩
  have hlevel : IsLevel ℓ (N + 1) ↥(IntermediateField.fixedField ψ'.ker) :=
    IsLevel.of_tower (E := ↥(IntermediateField.fixedField ψ'.ker)) (M := ↥M) hlevelM
  -- the corrected solution is cut out of the enlarged field by its kernel
  have hcompψ' : ∀ σ, f (ψ' σ) = eA (galRestrictLE hAM σ) := by
    intro σ
    rw [hψ'def, mulCentral_apply, map_mul, MonoidHom.mem_ker.mp (hχker σ), mul_one]
    exact hcompM σ
  have hker' : ψ'.ker ≤ (galRestrictLE hAM).ker := by
    intro σ hσ
    have h1 : eA (galRestrictLE hAM σ) = 1 := by
      rw [← hcompψ' σ, MonoidHom.mem_ker.mp hσ, map_one]
    exact MonoidHom.mem_ker.mpr (by simpa using h1)
  have hAE : A ≤ cutField ψ' := le_cutField ψ' hAM hker'
  haveI : FiniteDimensional ℚ ↥(cutField ψ') :=
    (IntermediateField.liftAlgEquiv
      (IntermediateField.fixedField ψ'.ker)).toLinearEquiv.finiteDimensional
  haveI : NumberField ↥(cutField ψ') := ⟨⟩
  haveI : IsGalois ℚ ↥(cutField ψ') := ⟨⟩
  have hsch : IsScholz ℓ (N + 1) ↥(cutField ψ') :=
    IsScholz.of_ringEquiv (IntermediateField.liftAlgEquiv
      (IntermediateField.fixedField ψ'.ker)).toRingEquiv ⟨hlevel, hsplitψ'⟩
  -- the twisted cover, and the field it cuts out
  have hkerΦ'le : Φ'.ker ≤ ψ'.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    rw [← hgΦ' σ, hσ, map_one]
  have hET' : cutField ψ' ≤ cutField Φ' := cutField_le_cutField Φ' ψ' hkerΦ'le
  haveI : FiniteDimensional ℚ ↥(cutField Φ') :=
    (IntermediateField.liftAlgEquiv
      (IntermediateField.fixedField Φ'.ker)).toLinearEquiv.finiteDimensional
  haveI : NumberField ↥(cutField Φ') := ⟨⟩
  haveI : IsGalois ℚ ↥(cutField Φ') := ⟨⟩
  haveI : IsGalois ℚ ↥(T ⊔ cutField ψ') := ⟨⟩
  haveI : NumberField ↥(T ⊔ cutField ψ') := ⟨⟩
  have hTEM : T ⊔ cutField ψ' ≤ M := sup_le hTM (cutField_le ψ')
  have hkerle : (galRestrictLE hTEM).ker ≤ Φ'.ker := by
    intro σ hσ
    have hT1 : galRestrictLE hTM σ = 1 := by
      have h2 := galRestrictLE_galRestrictLE (le_sup_left : T ≤ T ⊔ cutField ψ') hTEM σ
      rw [MonoidHom.mem_ker.mp hσ, map_one] at h2
      exact h2.symm
    have hE1 : galRestrictLE (cutField_le ψ') σ = 1 := by
      have h2 := galRestrictLE_galRestrictLE
        (le_sup_right : cutField ψ' ≤ T ⊔ cutField ψ') hTEM σ
      rw [MonoidHom.mem_ker.mp hσ, map_one] at h2
      exact h2.symm
    have hmem : σ ∈ ψ'.ker := by
      rw [← ker_galRestrictLE_cutField ψ']
      exact MonoidHom.mem_ker.mpr hE1
    have hΦ1 : Φ σ = 1 := by rw [hΦapp σ, hT1, map_one]
    have hΨ1 : Ψ σ = 1 := by rw [hΨapp σ, hΦ1, map_one]
    have hχ1' : χ σ = 1 := by
      have h3 := MonoidHom.mem_ker.mp hmem
      rw [hψ'def, mulCentral_apply, hΨ1, one_mul] at h3
      exact h3
    have hχ₀1 : χ₀ σ = 1 := by
      rw [hχdef] at hχ1'
      exact Subtype.ext hχ1'
    have hη1 : η σ = 1 := by simp [hηapp σ, hχ₀1]
    rw [MonoidHom.mem_ker, hΦ'app σ, hΦ1, hη1, one_mul]
  have hT'sup : cutField Φ' ≤ T ⊔ cutField ψ' := by
    have h1 : cutField Φ' ≤ cutField (galRestrictLE hTEM) :=
      cutField_le_cutField (galRestrictLE hTEM) Φ' hkerle
    rwa [cutField_galRestrictLE hTEM] at h1
  have hramT' : ramifiedSet ↥(cutField Φ') ⊆ ramifiedSet ↥T ∪ ramifiedSet ↥(cutField ψ') := by
    rw [← ramifiedSet_sup_intermediateField T (cutField ψ')]
    exact ramifiedSet_of_le hT'sup
  have hlevelT' : IsLevel ℓ (N + 1) ↥(cutField Φ') := fun q hq =>
    hlevelM q (ramifiedSet_of_le (cutField_le Φ') hq)
  refine ⟨cutField ψ', cutField Φ', hAE, hET', inferInstance, inferInstance, inferInstance,
    inferInstance, hsch, fun q hqS => IsSplitInertiaAt.of_ringEquiv (hSprime q hqS)
      (IntermediateField.liftAlgEquiv
        (IntermediateField.fixedField ψ'.ker)).toRingEquiv (hsplitS q hqS),
    hramT', hlevelT', galEquivCutField ψ' hψ'surj, galEquivCutField Φ' hΦ'surj, ?_, ?_, ?_⟩
  · intro τ
    obtain ⟨σ, rfl⟩ := galRestrictLE_surjective (cutField_le ψ') τ
    rw [galEquivCutField_galRestrictLE ψ' hψ'surj σ,
      galRestrictLE_galRestrictLE hAE (cutField_le ψ') σ]
    exact hcompψ' σ
  · intro τ
    obtain ⟨σ, rfl⟩ := galRestrictLE_surjective (cutField_le Φ') τ
    have h1 : galRestrictLE hET' (galRestrictLE (cutField_le Φ') σ) =
        galRestrictLE (cutField_le ψ') σ :=
      galRestrictLE_galRestrictLE hET' (cutField_le Φ') σ
    rw [h1, galEquivCutField_galRestrictLE ψ' hψ'surj σ,
      galEquivCutField_galRestrictLE Φ' hΦ'surj σ]
    exact (hgΦ' σ).symm
  · intro W _ u hu
    have hcomp1 : (u.comp (galEquivCutField Φ' hΦ'surj).toMonoidHom).comp
        (galRestrictLE (cutField_le Φ')) = u.comp Φ' := by
      ext σ
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [galEquivCutField_galRestrictLE Φ' hΦ'surj σ]
    have hcomp2 : (u.comp ψ₀.toMonoidHom).comp (galRestrictLE hTM) = u.comp Φ := by
      ext σ
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hΦapp σ]
    have hcomp3 : u.comp Φ' = u.comp Φ := by
      ext σ
      simp only [MonoidHom.coe_comp, Function.comp_apply]
      rw [hΦ'app σ, map_mul, hηapp σ, hu (χ₀ σ), mul_one]
    calc cutField (u.comp (galEquivCutField Φ' hΦ'surj).toMonoidHom)
        = cutField ((u.comp (galEquivCutField Φ' hΦ'surj).toMonoidHom).comp
            (galRestrictLE (cutField_le Φ'))) :=
          (cutField_comp_galRestrictLE (cutField_le Φ') _).symm
      _ = cutField (u.comp Φ') := by rw [hcomp1]
      _ = cutField (u.comp Φ) := by rw [hcomp3]
      _ = cutField ((u.comp ψ₀.toMonoidHom).comp (galRestrictLE hTM)) := by rw [hcomp2]
      _ = cutField (u.comp ψ₀.toMonoidHom) := cutField_comp_galRestrictLE hTM _

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A solution of a central Frattini embedding problem with kernel of prime order ramifying
harmlessly over the Scholz field below it, whose Frobenius defects are orthogonal to the exponent
vectors already radical in the constraint field, is corrected to a Scholz field over that one.**
The solution is enlarged by the roots of unity of an auxiliary modulus, and twisted by the character
of the units modulo that modulus whose power residue symbols are the Frobenius defects at the primes
ramified below; the orthogonality is exactly what makes such a character available.  The twist
cancels those defects without disturbing the inertia there, and at a prime split completely below —
one dividing the modulus, or one the solution ramifies at afresh — the decomposition group lands in
the kernel of the step, a group of prime order.

The defects are read at a prescribed finite set of primes containing the ramified ones, whose
further members split completely below; at such a member the defect is an arithmetic Frobenius
itself, again an element of the kernel of the step.  Cancelling the defect there costs nothing and
buys residue degree one at every prime of the set, ramified in the correction or not. -/
theorem exists_scholz_solution_of_forall_prod_eq_one (hℓ : ℓ.Prime) [NeZero ℓ] {N : ℕ}
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H} (hf : Function.Surjective f)
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = ℓ)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hschA : IsScholz ℓ (N + 1) ↥A) (eA : Gal(↥A/ℚ) ≃* H)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] [IsGalois ℚ ↥L] (hAL : A ≤ L)
    (hramL : IsScholzOver ℓ (N + 1) ↥A ↥L) (ψ₀ : Gal(↥L/ℚ) ≃* G)
    (hcomp₀ : ∀ τ, f (ψ₀ τ) = eA (galRestrictLE hAL τ)) (S : Finset ℕ)
    (hSprime : ∀ q ∈ S, q.Prime) (hAS : ∀ q ∈ ramifiedSet ↥A, q ∈ S)
    (hSsplit : ∀ q ∈ S, q ∉ ramifiedSet ↥A → SplitsCompletely ↥A q)
    (horth : ∀ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥M] [IsGalois ℚ ↥M]
      (hLM : L ≤ M) (Θ : Gal(↥M/ℚ) →* G), (∀ σ, Θ σ = ψ₀ (galRestrictLE hLM σ)) →
      ∀ ν : Multiplicative (ZMod ℓ) →* G, (∀ x, ν x ∈ f.ker) → Function.Injective ν →
      ∀ t : {q // q ∈ S} → ZMod ℓ,
      (∀ q : {q // q ∈ S}, ∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ * ν (Multiplicative.ofAdd (t q)) ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) →
      (∀ q : {q // q ∈ S}, (∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) → t q = 0) →
      ∀ a : {q // q ∈ S} → ZMod ℓ,
        (∃ u ∈ auxConstraintField L ℓ (N + 1), u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ)
          ((residueRadicand S a : ℕ) : ℚ)) →
        ∑ i, t i * a i = 0) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAE : A ≤ E) (_ : NumberField ↥E),
      IsGalois ℚ ↥E ∧ IsScholz ℓ N ↥E ∧ (∀ q ∈ S, IsSplitInertiaAt ↥E q) ∧
        ∃ ψ : Gal(↥E/ℚ) ≃* G, ∀ τ, f (ψ τ) = eA (galRestrictLE hAE τ) := by
  obtain ⟨E, _T', hAE, _hET', hNF, hGal, _hNFT, _hGalT, hsch, hsplit, _hram, _hlev, ψ, _Ψ,
      hcompψ, _h2, _h3⟩ :=
    exists_scholz_solution_lift_of_forall_prod_eq_one (Ĝ := G) (g := MonoidHom.id G) (fg := f)
      hℓ (fun _ => rfl) hf (fun x => ⟨x, rfl⟩) hZ hfr hcard (MonoidHom.id ↥f.ker) (fun _ => rfl)
      A hschA eA L hAL hramL ψ₀ hcomp₀ S hSprime hAS hSsplit horth
  exact ⟨E, hAE, hNF, hGal, hsch.mono (Nat.le_succ N), hsplit, ψ, hcompψ⟩

/-- **A solution of a central Frattini embedding problem with kernel of prime order ramifying
harmlessly over the Scholz field below it, whose Frobenius defects are orthogonal to the exponent
vectors already radical in the constraint field, gives a Scholz realization at the given level.** -/
theorem isScholzRealizable_of_solution_of_forall_prod_eq_one (hℓ : ℓ.Prime) [NeZero ℓ] {N : ℕ}
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H} (hf : Function.Surjective f)
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = ℓ)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hschA : IsScholz ℓ (N + 1) ↥A) (eA : Gal(↥A/ℚ) ≃* H)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] [IsGalois ℚ ↥L] (hAL : A ≤ L)
    (hramL : IsScholzOver ℓ (N + 1) ↥A ↥L) (ψ₀ : Gal(↥L/ℚ) ≃* G)
    (hcomp₀ : ∀ τ, f (ψ₀ τ) = eA (galRestrictLE hAL τ))
    (horth : ∀ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥M] [IsGalois ℚ ↥M]
      (hLM : L ≤ M) (Θ : Gal(↥M/ℚ) →* G), (∀ σ, Θ σ = ψ₀ (galRestrictLE hLM σ)) →
      ∀ ν : Multiplicative (ZMod ℓ) →* G, (∀ x, ν x ∈ f.ker) → Function.Injective ν →
      ∀ t : {q // q ∈ (finite_ramifiedSet ↥A).toFinset} → ZMod ℓ,
      (∀ q : {q // q ∈ (finite_ramifiedSet ↥A).toFinset}, ∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ * ν (Multiplicative.ofAdd (t q)) ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) →
      (∀ q : {q // q ∈ (finite_ramifiedSet ↥A).toFinset}, (∃ P : Ideal (𝓞 ↥M), ∃ _ : P.IsPrime,
        ∃ _ : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}), ∀ σ : Gal(↥M/ℚ), IsArithFrobAt ℤ σ P →
          Θ σ ∈ (Ideal.inertia Gal(↥M/ℚ) P).map Θ) → t q = 0) →
      ∀ a : {q // q ∈ (finite_ramifiedSet ↥A).toFinset} → ZMod ℓ,
        (∃ u ∈ auxConstraintField L ℓ (N + 1), u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ)
          ((residueRadicand (finite_ramifiedSet ↥A).toFinset a : ℕ) : ℚ)) →
        ∑ i, t i * a i = 0) :
    IsScholzRealizable G ℓ N := by
  obtain ⟨E, -, hNF, hGal, hsch, -, ψ, -⟩ :=
    exists_scholz_solution_of_forall_prod_eq_one hℓ hf hZ hfr hcard A hschA eA L hAL hramL ψ₀
      hcomp₀ (finite_ramifiedSet ↥A).toFinset (fun q hq => ((Set.Finite.mem_toFinset _).mp hq).1)
      (fun q hq => (Set.Finite.mem_toFinset _).mpr hq)
      (fun q hq hq' => absurd ((Set.Finite.mem_toFinset _).mp hq) hq') horth
  haveI := hNF
  haveI := hGal
  exact isScholzRealizable_of_isGalois ↥E hsch ψ

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
    R.isScholz R.galEquiv L hAL (IsScholzOver.of_subset hramL) ψ₀ hcomp₀ ?_
  intro M _ _ hLM Θ _ ν _ _ t _ _ a ha
  obtain ⟨u, huA, hu⟩ := ha
  obtain ⟨ζ, hζ, hζA⟩ :=
    isPrimitiveRoot_mem_auxConstraintField (B := L) (ℓ := ℓ) (k := N + 1) (Nat.succ_ne_zero N)
  have ha0 : a = 0 :=
    eq_zero_of_pow_eq_residueRadicand hodd
      (isNilpotent_auxConstraintField (hpg.of_equiv ψ₀.symm)) hζ hζA
      (fun q hq => ((Set.Finite.mem_toFinset _).mp hq).1) huA hu
  simp [ha0]

end InverseGalois.CFT
