/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.RelativeFrobenius
import InverseGalois.CFT.RelativeFrobeniusBase
import InverseGalois.CFT.Units.FrobeniusPlace
import InverseGalois.CFT.Units.IdeleNormTower
import InverseGalois.CFT.Units.PlaceRestrict
import InverseGalois.CFT.Units.PlaceTower

/-!
# A completely split place at which a radicand is not a local power

Let `k ⊆ F ⊆ N` be number fields with both `F` and `N` normal over `k`.  The primes of `k` that
split completely in the middle field but not in the top one have positive density, so there are
infinitely many of them and one avoids any prescribed finite set.  Above such a prime the
decomposition group over the base is nontrivial, and it restricts to the trivial group on the
middle field, so it is made of automorphisms over the middle field.  This is the only place where
anything analytic is used, and it is used exactly once.

The point of the construction is that the decomposition group is read off by radicals.  If the
middle field contains the roots of unity of a given exponent and the top field is generated over it
by radicals of that exponent, then an automorphism over the middle field fixes a radical exactly
when its radicand is a power in the completion below.  A nontrivial decomposition group moves one
of the radicals, so at the prime it produces the corresponding radicand is not a power in the
completion of the middle field, while the prime of the base below is completely split.

The hypothesis that the top field is strictly larger is itself read off by radicals: were the two
fields equal, every radical would already lie in the middle field and every radicand would be a
power there.

## Main results

* `InverseGalois.CFT.finrank_lt_of_not_exists_pow`: a radicand which is not a power in the middle
  field forces the top field to be strictly larger.
* `InverseGalois.CFT.exists_place_splitsCompletelyIn_stabilizer_ne_bot`: **outside any prescribed
  finite set of primes of the base there is a prime of the top field whose prime below is
  completely split in the middle field and whose decomposition group over the middle field is
  nontrivial.**
* `InverseGalois.CFT.exists_place_splitsCompletelyIn_not_exists_pow`: **outside any prescribed
  finite set of primes of the base there is a completely split prime of the middle field at which
  one of the radicands is not a power in the completion.**

## Tags

number field, Chebotarev, completely split, decomposition group, Kummer theory, local power
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField InverseGalois.NumberTheory

open scoped Pointwise

section SplitPlacePower

variable {k F N : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Field N]
  [NumberField N] [Algebra k F] [Algebra k N] [Algebra F N] [IsScalarTower k F N]
  [IsGalois k F] [IsGalois k N]

/-! ### The top field is strictly larger -/

omit [IsGalois k F] [IsGalois k N] in
/-- **A radicand which is not a power in the middle field forces the top field to be strictly
larger.**  Were the degrees equal the top field would be the middle field, so the radical would be
the image of an element of the middle field, whose power would then be the radicand. -/
theorem finrank_lt_of_not_exists_pow {p : ℕ} {b : F} {β : N} (hβ : β ^ p = algebraMap F N b)
    (hb : ¬ ∃ c : F, c ^ p = b) : Module.finrank k F < Module.finrank k N := by
  have hone : Module.finrank F N ≠ 1 := by
    intro h
    have htop : (⊥ : Subalgebra F N) = ⊤ := Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h
    have hmem : β ∈ (⊥ : Subalgebra F N) := by rw [htop]; exact Algebra.mem_top
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 hmem
    exact hb ⟨c, (algebraMap F N).injective (by rw [map_pow, hc, hβ])⟩
  have hmul := Module.finrank_mul_finrank k F N
  have hpos : 0 < Module.finrank k F := Module.finrank_pos
  have h2 : 2 ≤ Module.finrank F N := by
    have := Module.finrank_pos (R := F) (M := N)
    omega
  nlinarith [hmul, hpos, h2]

/-! ### The completely split prime with nontrivial decomposition above -/

/-- **Outside any prescribed finite set of primes of the base there is a prime of the top field
whose prime below is completely split in the middle field and whose decomposition group over the
middle field is nontrivial.**  The primes of the base splitting completely in the middle field but
not in the top one are infinite in number, so one of them avoids the prescribed set; above it the
splitting fails at some prime, whose decomposition group over the base is therefore nontrivial.
That decomposition group restricts to the decomposition group in the middle field, which is trivial
because the prime is completely split there, so its elements fix the middle field and are
automorphisms over it. -/
theorem exists_place_splitsCompletelyIn_stabilizer_ne_bot
    (hlt : Module.finrank k F < Module.finrank k N) (T : Finset (HeightOneSpectrum (𝓞 k))) :
    ∃ P : HeightOneSpectrum (𝓞 N), primeUnder (𝓞 k) P ∉ T ∧
      SplitsCompletelyIn k F (primeUnder (𝓞 k) P) ∧ stabilizer Gal(N/F) P ≠ ⊥ := by
  classical
  obtain ⟨v, ⟨hsplit, hnsplit⟩, hvT⟩ :=
    (infinite_setOf_splitsCompletelyIn_not_splitsCompletelyIn k F N hlt).exists_notMem_finset T
  have hex : ∃ P ∈ v.asIdeal.primesOver (𝓞 N),
      ¬ (Ideal.ramificationIdx (algebraMap (𝓞 k) (𝓞 N)) v.asIdeal P = 1 ∧
        v.asIdeal.inertiaDeg P = 1) := by
    by_contra hc
    refine hnsplit fun P hP => ?_
    by_contra hc2
    exact hc ⟨P, hP, hc2⟩
  obtain ⟨P, ⟨hPprime, hPover⟩, hPne⟩ := hex
  haveI := hPprime
  haveI := hPover
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hunder : P.under (𝓞 k) = v.asIdeal :=
    (Ideal.LiesOver.over (A := 𝓞 k) (P := P) (p := v.asIdeal)).symm
  set Pl : HeightOneSpectrum (𝓞 N) := ⟨P, hPprime, hP0⟩ with hPl
  have hPlv : primeUnder (𝓞 k) Pl = v := HeightOneSpectrum.ext hunder
  -- the decomposition group over the base is nontrivial
  have hstabne : stabilizer Gal(N/k) Pl ≠ ⊥ := by
    rw [stabilizer_eq_stabilizer_asIdeal]
    intro hb
    refine hPne ?_
    have hef := (relStabilizer_eq_bot_iff P hP0).mp hb
    rwa [hunder] at hef
  obtain ⟨τ, hτmem, hτ1⟩ := (stabilizer Gal(N/k) Pl).bot_or_exists_ne_one.resolve_left hstabne
  -- it restricts to the identity on the middle field
  set Q : HeightOneSpectrum (𝓞 F) := primeUnder (𝓞 F) Pl with hQ
  haveI : (Q.asIdeal).IsPrime := Q.isPrime
  haveI : (Q.asIdeal).LiesOver v.asIdeal := by
    refine ⟨?_⟩
    rw [← hunder]
    exact (Ideal.under_under (A := 𝓞 k) (B := 𝓞 F) P).symm
  have hQbot : stabilizer Gal(F/k) Q = ⊥ := by
    rw [stabilizer_eq_stabilizer_asIdeal]
    exact relStabilizer_eq_bot_of_splitsCompletelyIn hsplit Q.asIdeal
  have hrestr : AlgEquiv.restrictNormalHom F τ = 1 := by
    have hmem : AlgEquiv.restrictNormalHom F τ ∈ stabilizer Gal(F/k) Q := by
      rw [mem_stabilizer_iff, hQ, ← primeUnder_smul F τ Pl, mem_stabilizer_iff.mp hτmem]
    rwa [hQbot, Subgroup.mem_bot] at hmem
  obtain ⟨ρ, hρ⟩ := exists_restrictScalars_of_restrictNormalHom_eq_one k hrestr
  refine ⟨Pl, by rw [hPlv]; exact hvT, by rw [hPlv]; exact hsplit, ?_⟩
  intro hbot
  have hρmem : ρ ∈ stabilizer Gal(N/F) Pl := by
    rw [mem_stabilizer_iff]
    refine HeightOneSpectrum.ext ?_
    rw [asIdeal_smul, ← relRestrictScalars_smul_ideal (k := k) ρ Pl.asIdeal, hρ]
    exact congrArg HeightOneSpectrum.asIdeal (mem_stabilizer_iff.mp hτmem)
  rw [hbot, Subgroup.mem_bot] at hρmem
  exact hτ1 (by rw [← hρ, hρmem]; rfl)

/-! ### The radicand that is not a local power -/

variable {p s : ℕ}

/-- **Outside any prescribed finite set of primes of the base there is a completely split prime of
the middle field at which one of the radicands is not a power in the completion.**  Above the prime
of the base produced by the density argument the decomposition group over the middle field is
nontrivial, so one of its elements moves one of the radicals; an automorphism in a decomposition
group fixes a radical exactly when the radicand is a power in the completion below, so that
radicand is not. -/
theorem exists_place_splitsCompletelyIn_not_exists_pow (hp : p ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {b : Fin s → F} {w : Fin s → N}
    (hw : ∀ i, w i ^ p = algebraMap F N (b i))
    (hgen : ∀ ρ : Gal(N/F), (∀ i, ρ (w i) = w i) → ρ = 1)
    (hlt : Module.finrank k F < Module.finrank k N) (T : Finset (HeightOneSpectrum (𝓞 k))) :
    ∃ (W : HeightOneSpectrum (𝓞 F)) (i : Fin s), primeUnder (𝓞 k) W ∉ T ∧
      SplitsCompletelyIn k F (primeUnder (𝓞 k) W) ∧
      ¬ ∃ c : W.adicCompletion F, c ^ p = algebraMap F (W.adicCompletion F) (b i) := by
  haveI : IsGalois F N := IsGalois.tower_top_of_isGalois k F N
  obtain ⟨P, hPT, hPsplit, hPstab⟩ :=
    exists_place_splitsCompletelyIn_stabilizer_ne_bot (F := F) hlt T
  obtain ⟨ρ, hρmem, hρ1⟩ := (stabilizer Gal(N/F) P).bot_or_exists_ne_one.resolve_left hPstab
  have hmove : ∃ i, ρ (w i) ≠ w i := by
    by_contra hc
    push_neg at hc
    exact hρ1 (hgen ρ hc)
  obtain ⟨i, hi⟩ := hmove
  refine ⟨primeUnder (𝓞 F) P, i, ?_, ?_, ?_⟩
  · rwa [primeUnder_primeUnder k F P]
  · rwa [primeUnder_primeUnder k F P]
  · intro hpow
    exact hi ((forall_stabilizer_smul_eq_iff_exists_pow P hζ hp (hw i).symm).mpr hpow ⟨ρ, hρmem⟩)

end SplitPlacePower

end InverseGalois.CFT
