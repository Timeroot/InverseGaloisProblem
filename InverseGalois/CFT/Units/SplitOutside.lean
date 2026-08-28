/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.Decomposition
import InverseGalois.CFT.Units.FirstInequality
import InverseGalois.CFT.Units.LocalPowIdele
import InverseGalois.CFT.Units.SIdeleNorm

/-!
# An extension in which almost every place splits completely is trivial

An extension of number fields in which every place outside a finite exceptional set splits
completely is trivial as soon as its Galois group is solvable.  Only the finite places outside the
set are constrained; nothing at all is assumed at the infinite places or at the exceptional ones.

The proof is the norm criterion applied to the ideles that are local `n`-th powers at the infinite
places and at the exceptional ones.  Such an idele of the base field, read in the extension, is a
local norm everywhere: at a place above an exceptional one, and at every infinite place, its
component is an `n`-th power of a local unit coming from the base, and the order of the
decomposition group divides `n`, so a multiple of that order carries it; at a place above a
non-exceptional one the decomposition group is trivial and there is nothing to check.  Enlarging the
support of the idele together with the finitely many places lacking a fixed uniformizer to a finite
invariant set makes the idele an `S`-idele, and the local-to-global criterion then exhibits it as a
norm.

Together with the statement that the principal ideles and the local `n`-th powers exhaust the ideles
this makes the norms and the principal ideles exhaust the ideles, and the solvable case of the first
inequality finishes the argument.  The exceptional set costs nothing because the local powers are
imposed there, which is exactly what the classical argument achieves by a density statement.

## Main results

* `InverseGalois.CFT.localPowIdele_le_range_ideleNorm`: **an idele of the base field that is a local
  power at the infinite places and at the exceptional ones is a norm from a cyclic extension in
  which every other place splits completely.**
* `InverseGalois.CFT.subsingleton_gal_of_isSolvable_of_splits_outside`: **a solvable extension of
  number fields in which every place outside a finite set of places splits completely is trivial.**
* `InverseGalois.CFT.exists_stabilizer_ne_bot_of_notMem`: **a nontrivial solvable extension of
  number fields has, outside any finite set of places of the base field, a place that does not split
  completely.**

## Tags

number field, idele, norm, split completely, decomposition group, solvable extension
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### The cyclic case -/

section Cyclic

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **An idele of the base field that is a local power at the infinite places and at the exceptional
places is a norm from a cyclic extension in which every other place splits completely.**  The
exponent has to be a multiple of the degree, so that the order of every decomposition group divides
it and the local component is a local norm wherever the decomposition group is not already
trivial. -/
theorem localPowIdele_le_range_ideleNorm {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ} (hn : Nat.card Gal(K/k) = n)
    {S : Set (HeightOneSpectrum (𝓞 k))} {N : ℕ} (hN : Nat.card Gal(K/k) ∣ N)
    (hsplit : ∀ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∉ S →
      stabilizer Gal(K/k) v = ⊥) :
    localPowIdele k S N ≤ (ideleNorm k K).range := by
  classical
  intro d hd
  obtain ⟨B, hBfin, -, -, hBunram⟩ := exists_ramification_and_class_set k (K := K)
  set f : ↥(idele K) := ideleComap k K d with hfdef
  have hsupp : {v : HeightOneSpectrum (𝓞 K) | unitVal ((f : FullIdele K).2 v) ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp ((mem_idele K).mp f.2)
  obtain ⟨T, hTsub, hTfin, hTstable⟩ := exists_finite_stable_superset (G := Gal(K/k))
    ({v : HeightOneSpectrum (𝓞 K) | unitVal ((f : FullIdele K).2 v) ≠ 0} ∪ B) (hsupp.union hBfin)
  haveI : Finite ↥T := hTfin.to_subtype
  letI : MulAction Gal(K/k) ↥T := stableAction hTstable
  have hι : ∀ (g : Gal(K/k)) (y : ↥T),
      (Subtype.val (g • y) : HeightOneSpectrum (𝓞 K)) = g • (y : HeightOneSpectrum (𝓞 K)) :=
    fun _ _ => rfl
  have hrange : Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K)) = T := Subtype.range_coe
  have hTr : (Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K))).Finite :=
    Set.finite_range _
  have hmem : ∀ v : HeightOneSpectrum (𝓞 K),
      (f : FullIdele K).2 v ∈ adicSUnits (Set.range (Subtype.val : ↥T → _)) v := by
    intro v
    by_cases hv : v ∈ Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K))
    · rw [adicSUnits_of_mem _ hv]
      trivial
    · rw [adicSUnits_of_notMem _ hv, AddMonoidHom.mem_ker]
      by_contra hc
      exact hv (by rw [hrange]; exact hTsub (Or.inl hc))
  set fS : SIdele (Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K))) :=
    ((f : FullIdele K).1, fun v => ⟨(f : FullIdele K).2 v, hmem v⟩) with hfSdef
  have hincl : sIdeleIncl (Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K))) fS
      = (f : FullIdele K) := rfl
  have htoIdele : sIdeleToIdele (Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K))) hTr fS
      = f := Subtype.ext hincl
  have hffix : fullIdeleAut (k := k) σ (f : FullIdele K) = (f : FullIdele K) :=
    congrArg Subtype.val (ideleAut_ideleComap k K σ d)
  have hfix : sIdeleAut hι σ fS = fS := by
    refine sIdeleIncl_injective _ ?_
    rw [sIdeleIncl_sIdeleAut hι σ fS, hincl, hffix]
  have hunram : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∉ Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K)) →
      ∃ π : (v.adicCompletion K)ˣ,
        (∀ g : ↥(stabilizer Gal(K/k) v),
            g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
          ∧ unitVal (Additive.ofMul π) = 1 := by
    intro v hv
    refine hBunram v fun hvB => hv ?_
    rw [hrange]
    exact hTsub (Or.inr hvB)
  have hinf : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
      ∃ (m : ℕ) (x : Additive ((orbitOut ω : ω.orbit) : InfinitePlace K).Completionˣ),
        Nat.card ↥(stabilizer Gal(K/k) ((orbitOut ω : ω.orbit) : InfinitePlace K)) ∣ m
          ∧ smulUnitsAut
              (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit_infinite (orbitOut ω))) x = x
          ∧ fS.1 ((orbitOut ω : ω.orbit) : InfinitePlace K) = m • x := by
    intro ω
    obtain ⟨z, hz⟩ :=
      hd.1 ((((orbitOut ω : ω.orbit) : InfinitePlace K)).comap (algebraMap k K))
    refine ⟨N, infiniteUnitsComap k _ z, (Subgroup.card_subgroup_dvd_card _).trans hN,
      smulUnitsAut_infiniteUnitsComap k _ _ z, ?_⟩
    show infiniteUnitsComap k _ ((d : FullIdele k).1 _) = N • infiniteUnitsComap k _ z
    rw [hz, map_nsmul]
  have hfin : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      ω.out ∈ Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K)) →
      ∃ (m : ℕ) (x : Additive
          (((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ),
        Nat.card ↥(stabilizer Gal(K/k) ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) ∣ m
          ∧ smulUnitsAut
              (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit (orbitOut ω))) x = x
          ∧ ((fS.2 ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) :
                ↥(adicSUnits (Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K)))
                  ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))) :
              Additive (((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)
            = m • x := by
    intro ω _
    by_cases hvS : primeUnder (𝓞 k) ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) ∈ S
    · obtain ⟨z, hz⟩ := hd.2 _ hvS
      refine ⟨N, adicUnitsComap k _ z, (Subgroup.card_subgroup_dvd_card _).trans hN,
        smulUnitsAut_adicUnitsComap k _ _ z, ?_⟩
      show adicUnitsComap k _ ((d : FullIdele k).2 _) = N • adicUnitsComap k _ z
      rw [hz, map_nsmul]
    · haveI : Subsingleton ↥(stabilizer Gal(K/k)
          ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) := by
        rw [hsplit _ hvS]
        infer_instance
      refine ⟨1, _, Nat.dvd_one.mpr (Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩), ?_,
        (one_nsmul _).symm⟩
      rw [Subsingleton.elim (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit (orbitOut ω)))
        1, map_one]
      rfl
  obtain ⟨u, hu⟩ := exists_normHom_sIdeleAut_of_nsmul hι hgen hn hunram hfix hinf hfin
  refine ⟨sIdeleToIdele (Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K))) hTr u,
    ideleComap_injective k K ?_⟩
  rw [ideleComap_ideleNorm_eq_normHom k K hgen hn,
    ← map_normHom (sIdeleToIdele (Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K))) hTr)
      (sIdeleToIdele_sIdeleAut hι hTr σ) n u, hu, htoIdele, hfdef]

end Cyclic

/-! ### The solvable case -/

section Solvable

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **A solvable extension of number fields in which every place outside a finite set of places
splits completely is trivial.**  A nontrivial one would have a nontrivial cyclic subextension, in
which every place outside the set splits completely as well, because an automorphism of the
subextension fixing a place is the restriction of an automorphism of the top field fixing a place
above that very place; the ideles that are local powers at the infinite places and at the
exceptional ones are then norms from the subextension, and together with the principal ideles they
are all the ideles, contradicting the cyclic case of the first inequality. -/
theorem subsingleton_gal_of_isSolvable_of_splits_outside [IsSolvable Gal(K/k)]
    {S : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite)
    (hsplit : ∀ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∉ S →
      stabilizer Gal(K/k) v = ⊥) :
    Subsingleton Gal(K/k) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  obtain ⟨ψ, hψ⟩ := exists_complexChar_ker_ne_top Gal(K/k)
  haveI : IsCyclic (Gal(K/k) ⧸ ψ.ker) := isCyclic_quotient_ker_units ψ
  haveI : Nontrivial (Gal(K/k) ⧸ ψ.ker) := nontrivial_quotient_of_ne_top ψ.ker hψ
  set F := IntermediateField.fixedField ψ.ker with hF
  haveI : IsCyclic Gal(↥F/k) := isCyclic_of_surjective (IsGalois.normalAutEquivQuotient ψ.ker)
    (IsGalois.normalAutEquivQuotient ψ.ker).surjective
  haveI : Nontrivial Gal(↥F/k) := (IsGalois.normalAutEquivQuotient ψ.ker).injective.nontrivial
  have hsplitF : ∀ u : HeightOneSpectrum (𝓞 ↥F), primeUnder (𝓞 k) u ∉ S →
      stabilizer Gal(↥F/k) u = ⊥ := by
    intro u hu
    refine (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => ?_
    obtain ⟨ρ, ⟨v, hvu, hv⟩, hres⟩ := exists_restrictNormalHom_eq_of_prime_above K τ hτ
    have hvS : primeUnder (𝓞 k) v ∉ S := by
      rwa [← primeUnder_primeUnder k ↥F v, hvu]
    have hρ1 : ρ = 1 := by
      have hmem : ρ ∈ stabilizer Gal(K/k) v := hv
      rw [hsplit v hvS, Subgroup.mem_bot] at hmem
      exact hmem
    rw [← hres, hρ1, map_one]
  have hdvd : Nat.card Gal(↥F/k) ∣ Nat.card Gal(K/k) := by
    rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient ψ.ker).toEquiv]
    exact ψ.ker.index_dvd_card
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(↥F/k))
  have hDle : localPowIdele k S (Nat.card Gal(K/k)) ≤ (ideleNorm k ↥F).range :=
    localPowIdele_le_range_ideleNorm hσ rfl hdvd hsplitF
  have htop0 : (ideleDiag k).range ⊔ localPowIdele k S (Nat.card Gal(K/k)) = ⊤ :=
    ideleDiag_range_sup_localPowIdele_eq_top k hS Nat.card_pos.ne'
  have hsub : (ideleDiag k).range ⊔ (ideleNorm k ↥F).range = ⊤ :=
    top_le_iff.mp (htop0 ▸ sup_le_sup_left hDle (ideleDiag k).range)
  haveI : NeZero (Nat.card Gal(↥F/k)) := ⟨Nat.card_pos.ne'⟩
  exact (not_nontrivial_iff_subsingleton.mpr
    (subsingleton_gal_of_ideleDiag_sup_ideleNorm_eq_top (K := ↥F) rfl hσ hsub)) inferInstance

/-- **A nontrivial solvable extension of number fields has, outside any finite set of places of the
base field, a place that does not split completely.**  Were every such place to split completely the
extension would be trivial. -/
theorem exists_stabilizer_ne_bot_of_notMem [IsSolvable Gal(K/k)] [Nontrivial Gal(K/k)]
    {S : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∉ S ∧ stabilizer Gal(K/k) v ≠ ⊥ := by
  by_contra hc
  push_neg at hc
  exact not_subsingleton Gal(K/k) (subsingleton_gal_of_isSolvable_of_splits_outside hS hc)

end Solvable

end InverseGalois.CFT
