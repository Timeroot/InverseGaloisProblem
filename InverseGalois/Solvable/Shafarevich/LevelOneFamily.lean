/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharPlace
import InverseGalois.CFT.Kummer.LocalPowerConverse
import InverseGalois.CFT.PoitouTate.PositiveClasses
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.Solvable.Shafarevich.LevelOneArith

/-!
# The prescribed subgroups of the first rung

The character of the first rung has to be killed on a prescribed family of subgroups of the Galois
group, and on every conjugate of every element of that family.  The family the ladder hands down
consists of decomposition subgroups: one at a prime of the whole extension above each place of a
finite Galois stable set of places of the level, together with the decomposition subgroup at each
archimedean place.  This file shows that a family of units which are local powers at every place of
that set kills the character on all of them.

At a finite place the mechanism is the local power itself.  A unit which is an `ℓ`-th power in the
completion at a place stays an `ℓ`-th power after passing to the completion of any extension, so
every automorphism in the decomposition subgroup at a prime above that place fixes each `ℓ`-th root
of the unit, and the corresponding coordinate of the character vanishes there.  Conjugation is free
of charge because the set of places is stable: the place below a translate of a prime is the
translate of the place below it, so a conjugate of the decomposition subgroup is the decomposition
subgroup at another prime lying over another place of the same set.

At an archimedean place the mechanism is parity.  An automorphism fixing an archimedean place either
fixes the corresponding embedding, in which case it is the identity, or composes it with complex
conjugation, in which case it is an involution; either way its square is trivial.  An involution
over the level multiplies an `ℓ`-th root of a unit of the level by a root of unity, which the level
already contains, and applying the involution twice shows that root of unity is a square root of
one.  For an odd prime exponent the only root of unity killed by both the exponent and two is one,
so the involution fixes the root and the coordinate vanishes there as well.

At the exponent two that parity argument says nothing, both square roots of one being available, and
the archimedean hypothesis carried by the unit takes over.  An automorphism which composes the
embedding of an archimedean place with complex conjugation and fixes the level makes that embedding
real on the level; a unit of the level which is a local square at every archimedean place is
positive at every real embedding, so its square root has a real image, which complex conjugation
leaves alone.

## Main results

* `sq_eq_one_of_mem_stabilizer_infinitePlace`: an automorphism fixing an archimedean place is an
  involution.
* `smul_eq_of_sq_eq_one`: an involution over a level containing the roots of unity of an odd prime
  exponent fixes every radical of a unit of that level.
* `smul_eq_of_mem_stabilizer_infinitePlace`: an automorphism fixing a level and an archimedean place
  of the whole extension fixes every radical of a unit of the level which is a local power at every
  archimedean place of the level.
* `smul_eq_of_localClassHom_eq_one`: the decomposition subgroup at a prime fixes every radical of a
  unit which is a local power at the place below.
* `forall_conj_smul_eq_of_mem_decomposition`: a family of units which are local powers at every
  place of a stable set is fixed, root and all, by the decomposition subgroups of that set and by
  the archimedean ones.
* `hasLevelOneCharacter_of_places_nat`: a family of units indexed by a long enough initial segment
  of the natural numbers gives the first rung of the ladder its character.

## Tags

Shafarevich, embedding problem, Kummer theory, decomposition group, archimedean place
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### An automorphism fixing an infinite place is an involution -/

section Infinite

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- An automorphism fixing an archimedean place is an involution. -/
theorem sq_eq_one_of_mem_stabilizer_infinitePlace (w : InfinitePlace K) {σ : Gal(K/k)}
    (hσ : σ ∈ stabilizer Gal(K/k) w) : σ ^ 2 = 1 := by
  have hmk : InfinitePlace.mk (w.embedding.comp (σ.symm : K →+* K))
      = InfinitePlace.mk w.embedding := by
    rw [← InfinitePlace.smul_mk, InfinitePlace.mk_embedding]
    exact mem_stabilizer_iff.1 hσ
  rcases InfinitePlace.mk_eq_iff.1 hmk with h | h
  · have hid : ∀ x : K, σ x = x := by
      intro x
      have h1 : w.embedding (σ.symm (σ x)) = w.embedding (σ x) := RingHom.congr_fun h (σ x)
      rw [AlgEquiv.symm_apply_apply] at h1
      exact (w.embedding.injective h1).symm
    have hσ1 : σ = 1 := AlgEquiv.ext fun x => (hid x).trans (AlgEquiv.one_apply x).symm
    rw [hσ1, one_pow]
  · have hc : ∀ x : K, (starRingEnd ℂ) (w.embedding (σ.symm x)) = w.embedding x :=
      fun x => RingHom.congr_fun h x
    have h2 : ∀ x : K, σ.symm (σ.symm x) = x := by
      intro x
      have e2 : w.embedding (σ.symm x) = (starRingEnd ℂ) (w.embedding x) := by
        rw [← hc x, Complex.conj_conj]
      have e1 := hc (σ.symm x)
      rw [e2] at e1
      have e3 := congrArg (starRingEnd ℂ) e1
      rw [Complex.conj_conj, Complex.conj_conj] at e3
      exact w.embedding.injective e3
    refine AlgEquiv.ext fun z => ?_
    rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    have h4 := h2 (σ (σ z))
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply] at h4
    exact h4.symm

end Infinite

/-! ### The roots of unity of a level -/

section Mu

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {ℓ : ℕ}
  [NeZero ℓ]

/-- An automorphism over a level fixes every root of unity whose order divides the exponent, the
level containing a primitive one. -/
theorem smul_eq_of_pow_eq_one_of_mem_fixingSubgroup {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    {y : Gal(Ω/k)} (hy : y ∈ K.fixingSubgroup) {ξ : Ωˣ} (hξ : ξ ^ ℓ = 1) : y • ξ = ξ := by
  have hζΩ : IsPrimitiveRoot ((ζ : Ω)) ℓ :=
    hζ.map_of_injective (f := (algebraMap ↥K Ω)) (algebraMap ↥K Ω).injective
  have hval : ((ξ : Ω)) ^ ℓ = 1 := by
    have h := congrArg (fun u : Ωˣ => (u : Ω)) hξ
    simpa using h
  obtain ⟨j, -, hj⟩ := hζΩ.eq_pow_of_pow_eq_one hval
  have hfix : y (ζ : Ω) = (ζ : Ω) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hy _ ζ.2
  refine Units.ext ?_
  show y (ξ : Ω) = (ξ : Ω)
  rw [← hj, _root_.map_pow, hfix]

/-- **An involution over a level fixes every radical of a unit of the level**, the exponent being
an odd prime: the involution multiplies the radical by a root of unity of order dividing both the
exponent and two. -/
theorem smul_eq_of_sq_eq_one (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    {a : (↥K)ˣ} {β : Ωˣ} (hβ : β ^ ℓ = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)
    {y : Gal(Ω/k)} (hy : y ∈ K.fixingSubgroup) (hy2 : y ^ 2 = 1) : y • β = β := by
  have hafix : y • (β ^ ℓ) = β ^ ℓ := by
    rw [hβ]
    refine Units.ext ?_
    show y ((algebraMap ↥K Ω) (a : ↥K)) = (algebraMap ↥K Ω) (a : ↥K)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hy _ (a : ↥K).2
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : Ωˣ, y • β = ξ * β := ⟨(y • β) * β⁻¹, by group⟩
  have hsp : ∀ m : ℕ, y • β ^ m = (y • β) ^ m := fun m =>
    _root_.map_pow (MulDistribMulAction.toMonoidHom Ωˣ y) β m
  have hξpow : ξ ^ ℓ = 1 := by
    have h1 : y • β ^ ℓ = ξ ^ ℓ * β ^ ℓ := by rw [hsp ℓ, hξdef, mul_pow]
    rw [hafix] at h1
    exact mul_right_cancel (b := β ^ ℓ) (by rw [one_mul]; exact h1.symm)
  have hyξ : y • ξ = ξ := smul_eq_of_pow_eq_one_of_mem_fixingSubgroup K hζ hy hξpow
  have hsq : ξ ^ 2 * β = β := by
    have h2 : y • (y • β) = β := by rw [smul_smul, ← pow_two, hy2, one_smul]
    rw [hξdef, smul_mul', hyξ, hξdef, ← mul_assoc, ← pow_two] at h2
    exact h2
  have hξ2 : ξ ^ 2 = 1 := mul_right_cancel (b := β) (by rw [one_mul]; exact hsq)
  have hcop : Nat.Coprime 2 ℓ := (Nat.coprime_primes Nat.prime_two hℓ).2 fun h => hodd h.symm
  have hdvd : orderOf ξ ∣ Nat.gcd 2 ℓ :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hξ2) (orderOf_dvd_of_pow_eq_one hξpow)
  rw [hcop.gcd_eq_one] at hdvd
  rw [hξdef, orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd), one_mul]

end Mu

/-! ### A radical at an infinite place where the unit is a local square -/

section Square

/-- A complex number whose square is a positive real is real. -/
theorem conj_eq_self_of_mul_self_eq_ofReal {z : ℂ} {r : ℝ} (hr : 0 < r) (h : z * z = (r : ℂ)) :
    (starRingEnd ℂ) z = z := by
  refine Complex.conj_eq_iff_im.2 ?_
  have h1 : (z * z).im = 0 := by rw [h]; simp
  have h2 : (z * z).re = r := by rw [h]; simp
  rw [Complex.mul_im, mul_comm z.im z.re] at h1
  rw [Complex.mul_re] at h2
  by_contra hne
  have hre : z.re = 0 := by
    rcases mul_eq_zero.1 (show z.re * z.im = 0 by linarith) with h3 | h3
    · exact h3
    · exact absurd h3 hne
  rw [hre, zero_mul, zero_sub] at h2
  have h4 := mul_self_nonneg z.im
  linarith

end Square

section Arch

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {ℓ : ℕ}

/-- **An automorphism fixing a level and an archimedean place of the whole extension fixes every
square root of a unit of the level which is a local square at every archimedean place of the
level.**  Such an automorphism either fixes the embedding attached to the place, in which case it is
the identity, or composes it with complex conjugation; in the second case the embedding is real on
the level, so the unit is positive there, so its square root has a real image. -/
theorem smul_eq_of_forall_infClassHom_eq_one {a : (↥K)ˣ}
    (ha : ∀ u : InfinitePlace ↥K, infClassHom u 2 a = 1) {β : Ωˣ}
    (hβ : β ^ 2 = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a) {W : InfinitePlace Ω}
    {y : Gal(Ω/k)} (hyfix : y ∈ K.fixingSubgroup) (hyst : y ∈ stabilizer Gal(Ω/k) W) :
    y • β = β := by
  have hmk : InfinitePlace.mk (W.embedding.comp (y.symm : Ω →+* Ω))
      = InfinitePlace.mk W.embedding := by
    rw [← InfinitePlace.smul_mk, InfinitePlace.mk_embedding]
    exact mem_stabilizer_iff.1 hyst
  rcases InfinitePlace.mk_eq_iff.1 hmk with h | h
  · have hid : ∀ x : Ω, y x = x := by
      intro x
      have h1 : W.embedding (y.symm (y x)) = W.embedding (y x) := RingHom.congr_fun h (y x)
      rw [AlgEquiv.symm_apply_apply] at h1
      exact (W.embedding.injective h1).symm
    have hy1 : y = 1 := AlgEquiv.ext fun x => (hid x).trans (AlgEquiv.one_apply x).symm
    rw [hy1, one_smul]
  · have hcy : ∀ x : Ω, (starRingEnd ℂ) (W.embedding x) = W.embedding (y x) := by
      intro x
      have h1 : (starRingEnd ℂ) (W.embedding (y.symm (y x))) = W.embedding (y x) :=
        RingHom.congr_fun h (y x)
      rwa [AlgEquiv.symm_apply_apply] at h1
    have hfixK : ∀ x : ↥K, y (algebraMap ↥K Ω x) = algebraMap ↥K Ω x :=
      fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hyfix _ x.2
    have hψ : ComplexEmbedding.IsReal (W.embedding.comp (algebraMap ↥K Ω)) := by
      refine ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)
      show (starRingEnd ℂ) (W.embedding (algebraMap ↥K Ω x)) = W.embedding (algebraMap ↥K Ω x)
      rw [hcy, hfixK]
    have hpos : 0 < ComplexEmbedding.IsReal.embedding hψ (a : ↥K) :=
      forall_pos_of_forall_infClassHom_eq_one (dvd_refl 2) ha _
    have hba : algebraMap ↥K Ω (a : ↥K) = ((β : Ω)) ^ 2 := by
      have h1 := congrArg (fun u : Ωˣ => (u : Ω)) hβ
      simpa using h1.symm
    have hz2 : W.embedding (β : Ω) * W.embedding (β : Ω)
        = ((ComplexEmbedding.IsReal.embedding hψ (a : ↥K) : ℝ) : ℂ) := by
      rw [ComplexEmbedding.IsReal.coe_embedding_apply]
      show _ = W.embedding (algebraMap ↥K Ω (a : ↥K))
      rw [hba, _root_.map_pow, pow_two]
    refine Units.ext ?_
    show y (β : Ω) = (β : Ω)
    refine W.embedding.injective ?_
    rw [← hcy, conj_eq_self_of_mul_self_eq_ofReal hpos hz2]

/-- **An automorphism fixing a level and an archimedean place of the whole extension fixes every
radical of a unit of the level which is a local power at every archimedean place of the level.**  At
an odd exponent the archimedean hypothesis asks nothing and parity alone settles it; at the exponent
two it is what makes the radical real at the place the automorphism fixes. -/
theorem smul_eq_of_mem_stabilizer_infinitePlace (hℓ : ℓ.Prime) {ζ : ↥K}
    (hζ : IsPrimitiveRoot ζ ℓ) {a : (↥K)ˣ}
    (ha : ∀ u : InfinitePlace ↥K, infClassHom u ℓ a = 1) {β : Ωˣ}
    (hβ : β ^ ℓ = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a) {W : InfinitePlace Ω}
    {y : Gal(Ω/k)} (hyfix : y ∈ K.fixingSubgroup) (hyst : y ∈ stabilizer Gal(Ω/k) W) :
    y • β = β := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  by_cases hodd : ℓ = 2
  · subst hodd
    exact smul_eq_of_forall_infClassHom_eq_one K ha hβ hyfix hyst
  · exact smul_eq_of_sq_eq_one K hℓ hodd hζ hβ hyfix
      (sq_eq_one_of_mem_stabilizer_infinitePlace W hyst)

end Arch

/-! ### A radical at a place where the unit is a local power -/

section Local

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
  [NumberField ↥K] [IsGalois ↥K Ω] {ℓ : ℕ} [NeZero ℓ]

/-- **The decomposition subgroup at a prime fixes every radical of a unit which is a local power at
the place below**, the level containing the roots of unity of the exponent. -/
theorem smul_eq_of_localClassHom_eq_one {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) {P : Ideal (𝓞 Ω)}
    [P.IsPrime] {v : HeightOneSpectrum (𝓞 ↥K)} (hv : v.asIdeal = Ideal.under (𝓞 ↥K) P)
    {a : (↥K)ˣ} (hloc : localClassHom v ℓ a = 1) {y : Gal(Ω/k)} (hyfix : y ∈ K.fixingSubgroup)
    (hyst : y ∈ stabilizer Gal(Ω/k) P) {β : Ωˣ}
    (hβ : β ^ ℓ = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a) : y • β = β := by
  obtain ⟨τ, hτ⟩ := exists_galSubHom_eq K hyfix
  have hτst : τ ∈ stabilizer Gal(Ω/↥K) P :=
    (mem_stabilizer_galSubHom_iff K τ P).1 (hτ ▸ hyst)
  have ha : algebraMap ↥K Ω (a : ↥K) = ((β : Ω)) ^ ℓ := by
    have h := congrArg (fun u : Ωˣ => (u : Ω)) hβ
    simpa using h.symm
  have hc : ∃ c : v.adicCompletion ↥K, c ^ ℓ = algebraMap ↥K (v.adicCompletion ↥K) (a : ↥K) :=
    (localClassHom_eq_one_iff_exists_pow v a).1 hloc
  have hfix := forall_stabilizer_smul_eq_of_exists_pow_adicCompletion hζ (NeZero.ne ℓ) ha hv hc
    ⟨τ, hτst⟩
  refine Units.ext ?_
  show y (β : Ω) = (β : Ω)
  rw [← hτ]
  exact hfix

end Local

/-! ### The character is trivial along the family -/

section Family

variable {ℓ : ℕ} {U : Type} [Group U] {k Ω : Type} [Field k] [Field Ω]
  [Algebra k Ω] [IsGalois k Ω]

/-- **A family of units which are local powers at every place of a stable set is fixed, root and
all, by the decomposition subgroups of that set and by the archimedean ones.** -/
theorem forall_conj_smul_eq_of_mem_decomposition (hℓ : ℓ.Prime)
    {φ : Gal(Ω/k) →* U} (K : IntermediateField k Ω) [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    {Tn : Set (HeightOneSpectrum (𝓞 ↥K))}
    (hTnst : ∀ (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tn → σ • v ∈ Tn)
    {ι : Type*} {z : ι → (↥K)ˣ} (hz : ∀ (i : ι), ∀ v ∈ Tn, localClassHom v ℓ (z i) = 1)
    (hzinf : ∀ (i : ι), ∀ u : InfinitePlace ↥K, infClassHom u ℓ (z i) = 1)
    {Tf : Set (Subgroup Gal(Ω/k))}
    (hTf : ∀ E ∈ Tf, (∃ P : Ideal (𝓞 Ω), ∃ _ : P.IsPrime,
        (∃ v ∈ Tn, v.asIdeal = Ideal.under (𝓞 ↥K) P) ∧ E = stabilizer Gal(Ω/k) P) ∨
      ∃ w : InfinitePlace Ω, E = stabilizer Gal(Ω/k) w) :
    ∀ E ∈ Tf, ∀ x ∈ E, φ x = 1 → ∀ (g : Gal(Ω/k)) (i : ι) (β : Ωˣ),
      β ^ ℓ = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (z i) → (g⁻¹ * x * g) • β = β := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  intro E hE x hx hφ g i β hβ
  have hφy : φ (g⁻¹ * x * g) = 1 := by
    rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, hφ, mul_one, inv_mul_cancel]
  have hyfix : g⁻¹ * x * g ∈ K.fixingSubgroup := by
    rw [hKker]
    exact MonoidHom.mem_ker.2 hφy
  rcases hTf E hE with ⟨P, hPp, ⟨v, hvTn, hvP⟩, rfl⟩ | ⟨w, rfl⟩
  · haveI := hPp
    have hyst : g⁻¹ * x * g ∈ stabilizer Gal(Ω/k) (g⁻¹ • P) := by
      have h := mem_stabilizer_conj hx g⁻¹
      rwa [inv_inv] at h
    have hvunder :
        ((AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g⁻¹) • v).asIdeal
          = Ideal.under (𝓞 ↥K) (g⁻¹ • P) := by
      rw [asIdeal_smul, under_smul_ringOfIntegers, hvP]
    exact smul_eq_of_localClassHom_eq_one K hζ hvunder (hz i _ (hTnst _ _ hvTn)) hyfix hyst hβ
  · have hyst : g⁻¹ * x * g ∈ stabilizer Gal(Ω/k) (g⁻¹ • w) := by
      have h := mem_stabilizer_conj hx g⁻¹
      rwa [inv_inv] at h
    exact smul_eq_of_mem_stabilizer_infinitePlace K hℓ hζ (hzinf i) hβ hyfix hyst

end Family

/-! ### Indexing the family by the natural numbers -/

section Nat

variable {ℓ : ℕ} {U S : Type} [Group U] [Finite U] [Group S] [Finite S]
  {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]

attribute [local instance] zmodTrivialAction

/-- **A family of units indexed by an initial segment of the natural numbers long enough to cover
the layer gives the first rung of the ladder its character**, the local hypotheses being read off
from a Galois stable set of places containing those above the exponent. -/
theorem hasLevelOneCharacter_of_places_nat (hℓ : ℓ.Prime) (n : ℕ)
    {φ : Gal(Ω/k) →* U} (hsurj : Function.Surjective φ) (Tf : Set (Subgroup Gal(Ω/k)))
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hmu : ∀ y : Ωˣ, y ^ (ℓ * ℓ) = 1 → ∀ σ ∈ φ.ker, σ • y = y)
    {Tn : Set (HeightOneSpectrum (𝓞 ↥K))}
    (hTnst : ∀ (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : 𝓞 ↥K) ∈ v.asIdeal → v ∈ Tn)
    (hTfsh : ∀ E ∈ Tf, (∃ P : Ideal (𝓞 Ω), ∃ _ : P.IsPrime,
        (∃ v ∈ Tn, v.asIdeal = Ideal.under (𝓞 ↥K) P) ∧ E = stabilizer Gal(Ω/k) P) ∨
      ∃ w : InfinitePlace Ω, E = stabilizer Gal(Ω/k) w)
    (d : ℕ) (hd : Nat.card ↥(layerSub ℓ (Generic U n S) 0) ≤ d)
    (Q R E : ℕ → HeightOneSpectrum (𝓞 ↥K)) (z : ℕ → (↥K)ˣ)
    (hz : ∀ i < d, ∀ v ∈ Tn, localClassHom v ℓ (z i) = 1)
    (hzinf : ∀ i < d, ∀ u : InfinitePlace ↥K, infClassHom u ℓ (z i) = 1)
    (hunram : ∀ i < d, ∀ w : HeightOneSpectrum (𝓞 ↥K), w ≠ Q i → w ≠ R i → w ≠ E i →
      (ℓ : ℤ) ∣ placeValue w (z i))
    (hramQ : ∀ i < d, ¬ (ℓ : ℤ) ∣ placeValue (Q i) (z i))
    (hconjQ : ∀ i < d, ∀ σ : Gal(↥K/k), σ ≠ 1 → localClassHom (σ • Q i) ℓ (z i) = 1)
    (hconjR : ∀ i < d, ∀ σ : Gal(↥K/k), σ ≠ 1 → localClassHom (σ • R i) ℓ (z i) = 1)
    (hconjE : ∀ i < d, ∀ σ : Gal(↥K/k), σ ≠ 1 → localClassHom (σ • E i) ℓ (z i) = 1)
    (hcrossQ : ∀ i < d, ∀ j < d, i ≠ j → ∀ σ : Gal(↥K/k), localClassHom (σ • Q j) ℓ (z i) = 1)
    (hcrossR : ∀ i < d, ∀ j < d, i ≠ j → ∀ σ : Gal(↥K/k), localClassHom (σ • R j) ℓ (z i) = 1)
    (hcrossE : ∀ i < d, ∀ j < d, i ≠ j → ∀ σ : Gal(↥K/k), localClassHom (σ • E j) ℓ (z i) = 1)
    (hstabQ : ∀ i < d, stabilizer Gal(↥K/k) (Q i) = ⊥)
    (hstabR : ∀ i < d, stabilizer Gal(↥K/k) (R i) = ⊥)
    (hstabE : ∀ i < d, stabilizer Gal(↥K/k) (E i) = ⊥) :
    HasLevelOneCharacter ℓ U S φ Tf n := by
  classical
  letI : Fintype ↥(layerSub ℓ (Generic U n S) 0) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(layerSub ℓ (Generic U n S) 0) ≤ d := by
    rwa [Nat.card_eq_fintype_card] at hd
  obtain ⟨e, helt, heinj⟩ : ∃ e : ↥(layerSub ℓ (Generic U n S) 0) → ℕ,
      (∀ i, e i < d) ∧ Function.Injective e :=
    ⟨fun i => ((Fintype.equivFin _ i : Fin _) : ℕ),
      fun i => lt_of_lt_of_le (Fintype.equivFin _ i).2 hcard,
      fun i j h => (Fintype.equivFin _).injective (Fin.val_injective h)⟩
  refine hasLevelOneCharacter_of_places hℓ n hsurj Tf K hKker hζ hmu (fun i => Q (e i))
    (fun i => R (e i)) (fun i => E (e i)) (fun i => z (e i))
    (fun i w hw => hz _ (helt i) w (hpTn w hw))
    (fun i w h1 h2 h3 => hunram _ (helt i) w h1 h2 h3) (fun i => hramQ _ (helt i))
    (fun i σ hσ => hconjQ _ (helt i) σ hσ) (fun i σ hσ => hconjR _ (helt i) σ hσ)
    (fun i σ hσ => hconjE _ (helt i) σ hσ)
    (fun i j hij σ => hcrossQ _ (helt i) _ (helt j) (fun h => hij (heinj h)) σ)
    (fun i j hij σ => hcrossR _ (helt i) _ (helt j) (fun h => hij (heinj h)) σ)
    (fun i j hij σ => hcrossE _ (helt i) _ (helt j) (fun h => hij (heinj h)) σ)
    (fun i => hstabQ _ (helt i)) (fun i => hstabR _ (helt i)) (fun i => hstabE _ (helt i)) ?_
  exact forall_conj_smul_eq_of_mem_decomposition hℓ K hKker hζ hTnst
    (fun i => hz _ (helt i)) (fun i => hzinf _ (helt i)) hTfsh

end Nat

end InverseGalois.Shafarevich
