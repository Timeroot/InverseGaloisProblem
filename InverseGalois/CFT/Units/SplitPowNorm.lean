/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicUnramified
import InverseGalois.CFT.Units.Decomposition
import InverseGalois.CFT.Units.FirstInequality
import InverseGalois.CFT.Units.SIdeleNorm
import InverseGalois.CFT.Units.SplitPowIdele

/-!
# Local powers at the auxiliary places are global norms

The algebraic proof of the second inequality of class field theory rests on the statement that, for
a cyclic extension of number fields which splits completely at the infinite places and at a finite
set `S` of finite places and is unramified outside `S` and a second finite set `T`, every idele of
the base field which is an `n`-th power at the places of `T` and a unit of the valuation ring
outside the two sets is a norm.

Each of the three local conditions is a local norm for its own reason.  At an infinite place and at
a place of `S` the decomposition group is trivial, so the local norm map is onto and there is
nothing to check.  At a place of `T` the order of the decomposition group divides the degree and
hence the exponent, so an `n`-th power of a local unit coming from the base field is a local norm.
Outside the two sets the extension is unramified, so the local component being a unit of the
valuation ring makes it a norm by the vanishing of the Tate groups of the local units there.

The places above `S ∪ T` are exactly the places at which something has to be checked, and there are
only finitely many of them because a prime of the base field has only finitely many primes above it.
Taking that finite invariant set as the set of chosen places makes the idele, read in the extension,
an `S`-idele, and the local-to-global criterion exhibits it as a norm.

## Main results

* `InverseGalois.CFT.finite_setOf_primeUnder_mem`: **only finitely many places of an extension lie
  above a finite set of places of the base field.**
* `InverseGalois.CFT.splitPowIdele_le_range_ideleNorm`: **an idele of the base field that is a local
  power at the auxiliary places and a unit outside the two sets of places is a norm from a cyclic
  extension which splits completely at the infinite places and at the first set and is unramified
  outside.**

## Tags

number field, idele, norm, split completely, unramified, decomposition group, second inequality
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### The places above a finite set of places -/

section Above

variable (k : Type*) {K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **Only finitely many places of an extension lie above a finite set of places of the base
field.**  A prime of the base field has only finitely many primes above it, and a place of the
extension is determined by its ideal. -/
theorem finite_setOf_primeUnder_mem {S : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite) :
    {v : HeightOneSpectrum (𝓞 K) | primeUnder (𝓞 k) v ∈ S}.Finite := by
  have hbig : (⋃ p ∈ S, Ideal.primesOver p.asIdeal (𝓞 K)).Finite := by
    refine hS.biUnion fun p _ => ?_
    haveI : p.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal p.isPrime p.ne_bot
    exact primesOver_finite p.asIdeal (𝓞 K)
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) (hbig.subset ?_)
    (fun v _ w _ h => HeightOneSpectrum.ext h)
  rintro _ ⟨v, hv, rfl⟩
  exact Set.mem_biUnion hv ⟨v.isPrime, ⟨rfl⟩⟩

end Above

/-! ### The cyclic case -/

section Cyclic

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **An idele of the base field that is a local power at the auxiliary places and a unit outside
the two sets of places is a norm from a cyclic extension which splits completely at the infinite
places and at the first set and is unramified outside.**  The exponent has to be a multiple of the
degree, so that the order of every decomposition group divides it and the local component is a local
norm at a place above the second set. -/
theorem splitPowIdele_le_range_ideleNorm {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ} (hn : Nat.card Gal(K/k) = n)
    {S T : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite) (hT : T.Finite) {N : ℕ}
    (hN : Nat.card Gal(K/k) ∣ N)
    (hsplitInf : ∀ w : InfinitePlace K, stabilizer Gal(K/k) w = ⊥)
    (hsplitS : ∀ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∈ S →
      stabilizer Gal(K/k) v = ⊥)
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∉ S → primeUnder (𝓞 k) v ∉ T →
      Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal) :
    splitPowIdele k S T N ≤ (ideleNorm k K).range := by
  classical
  intro d hd
  set A : Set (HeightOneSpectrum (𝓞 K)) :=
    {v : HeightOneSpectrum (𝓞 K) | primeUnder (𝓞 k) v ∈ S ∪ T} with hAdef
  have hAfin : A.Finite := finite_setOf_primeUnder_mem k (hS.union hT)
  have hAstable : ∀ (g : Gal(K/k)) (x : HeightOneSpectrum (𝓞 K)), g • x ∈ A ↔ x ∈ A := by
    intro g x
    show primeUnder (𝓞 k) (g • x) ∈ S ∪ T ↔ primeUnder (𝓞 k) x ∈ S ∪ T
    rw [primeUnder_smul_eq]
  haveI : Finite ↥A := hAfin.to_subtype
  letI : MulAction Gal(K/k) ↥A := stableAction hAstable
  set f : ↥(idele K) := ideleComap k K d with hfdef
  have hι : ∀ (g : Gal(K/k)) (y : ↥A),
      (Subtype.val (g • y) : HeightOneSpectrum (𝓞 K)) = g • (y : HeightOneSpectrum (𝓞 K)) :=
    fun _ _ => rfl
  have hrange : Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K)) = A := Subtype.range_coe
  have hAr : (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K))).Finite :=
    Set.finite_range _
  have hsupp : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A → unitVal ((f : FullIdele K).2 v) = 0 := by
    intro v hv
    show unitVal (adicUnitsComap k v ((d : FullIdele k).2 (primeUnder (𝓞 k) v))) = 0
    rw [unitVal_adicUnitsComap_eq_zero_iff]
    exact hd.2 _ (fun h => hv (Or.inl h)) (fun h => hv (Or.inr h))
  have hmem : ∀ v : HeightOneSpectrum (𝓞 K),
      (f : FullIdele K).2 v ∈ adicSUnits (Set.range (Subtype.val : ↥A → _)) v := by
    intro v
    by_cases hv : v ∈ Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K))
    · rw [adicSUnits_of_mem _ hv]
      trivial
    · rw [adicSUnits_of_notMem _ hv, AddMonoidHom.mem_ker]
      rw [hrange] at hv
      exact hsupp v hv
  set fS : SIdele (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K))) :=
    ((f : FullIdele K).1, fun v => ⟨(f : FullIdele K).2 v, hmem v⟩) with hfSdef
  have hincl : sIdeleIncl (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K))) fS
      = (f : FullIdele K) := rfl
  have htoIdele : sIdeleToIdele (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K))) hAr fS
      = f := Subtype.ext hincl
  have hffix : fullIdeleAut (k := k) σ (f : FullIdele K) = (f : FullIdele K) :=
    congrArg Subtype.val (ideleAut_ideleComap k K σ d)
  have hfix : sIdeleAut hι σ fS = fS := by
    refine sIdeleIncl_injective _ ?_
    rw [sIdeleIncl_sIdeleAut hι σ fS, hincl, hffix]
  have hunramπ : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∉ Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K)) →
      ∃ π : (v.adicCompletion K)ˣ,
        (∀ g : ↥(stabilizer Gal(K/k) v),
            g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
          ∧ unitVal (Additive.ofMul π) = 1 := by
    intro v hv
    rw [hrange] at hv
    exact exists_fixedUniformizer_of_isUnramifiedAt v
      (hunram v (fun h => hv (Or.inl h)) (fun h => hv (Or.inr h)))
  have hinf : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
      ∃ (m : ℕ) (x : Additive ((orbitOut ω : ω.orbit) : InfinitePlace K).Completionˣ),
        Nat.card ↥(stabilizer Gal(K/k) ((orbitOut ω : ω.orbit) : InfinitePlace K)) ∣ m
          ∧ smulUnitsAut
              (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit_infinite (orbitOut ω))) x = x
          ∧ fS.1 ((orbitOut ω : ω.orbit) : InfinitePlace K) = m • x := by
    intro ω
    haveI : Subsingleton ↥(stabilizer Gal(K/k) ((orbitOut ω : ω.orbit) : InfinitePlace K)) := by
      rw [hsplitInf _]
      infer_instance
    refine ⟨1, _, Nat.dvd_one.mpr (Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩), ?_,
      (one_nsmul _).symm⟩
    rw [Subsingleton.elim (orbitTurn σ (orbitOut ω)
      (mem_stabilizer_of_smul_orbit_infinite (orbitOut ω))) 1, map_one]
    rfl
  have hfin : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      ω.out ∈ Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K)) →
      ∃ (m : ℕ) (x : Additive
          (((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ),
        Nat.card ↥(stabilizer Gal(K/k) ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) ∣ m
          ∧ smulUnitsAut
              (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit (orbitOut ω))) x = x
          ∧ ((fS.2 ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) :
                ↥(adicSUnits (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K)))
                  ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))) :
              Additive (((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)
            = m • x := by
    intro ω hω
    rw [hrange] at hω
    have hωA : primeUnder (𝓞 k) ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) ∈ S ∪ T := hω
    by_cases hvS : primeUnder (𝓞 k) ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) ∈ S
    · haveI : Subsingleton ↥(stabilizer Gal(K/k)
          ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) := by
        rw [hsplitS _ hvS]
        infer_instance
      refine ⟨1, _, Nat.dvd_one.mpr (Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩), ?_,
        (one_nsmul _).symm⟩
      rw [Subsingleton.elim (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit (orbitOut ω)))
        1, map_one]
      rfl
    · obtain ⟨z, hz⟩ := hd.1 _ (hωA.resolve_left hvS)
      refine ⟨N, adicUnitsComap k _ z, (Subgroup.card_subgroup_dvd_card _).trans hN,
        smulUnitsAut_adicUnitsComap k _ _ z, ?_⟩
      show adicUnitsComap k _ ((d : FullIdele k).2 _) = N • adicUnitsComap k _ z
      rw [hz, map_nsmul]
  obtain ⟨u, hu⟩ := exists_normHom_sIdeleAut_of_nsmul hι hgen hn hunramπ hfix hinf hfin
  refine ⟨sIdeleToIdele (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K))) hAr u,
    ideleComap_injective k K ?_⟩
  rw [ideleComap_ideleNorm_eq_normHom k K hgen hn,
    ← map_normHom (sIdeleToIdele (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K))) hAr)
      (sIdeleToIdele_sIdeleAut hι hAr σ) n u, hu, htoIdele, hfdef]

end Cyclic

end InverseGalois.CFT
