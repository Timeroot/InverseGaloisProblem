/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.PowIdele
import InverseGalois.CFT.Units.SplitPowNorm

/-!
# The ideles carrying the local powers are global norms

The counting proof of the second inequality of class field theory compares a subgroup of the ideles
of the base field with the norms from a cyclic extension of prime degree.  The subgroup in question
is the one carrying the local powers: its component is a `p`-th power at the infinite places and at
a finite set `S` of finite places, is arbitrary at a second finite set `T`, and is a unit of the
valuation ring at every remaining place.  The extension is required to split completely at the
places above `T` and to be unramified outside `S` and `T`.

Each of the three local conditions is a local norm for its own reason, and the reason is the same
one twice.  Because the degree is a prime `p`, the order of every decomposition group divides `p`,
so a `p`-th power of a local element coming from the base field is automatically a local norm; this
covers the infinite places and the places above `S` with no hypothesis at all on the extension
there.  Above `T` the decomposition group is trivial, so the local norm map is onto and nothing has
to be checked.  Outside the two sets the extension is unramified, so the local component being a
unit of the valuation ring makes it a norm by the vanishing of the Tate groups of the local units.

The places above `S ∪ T` are exactly the places carrying a condition, and there are only finitely
many of them.  Taking that finite invariant set as the set of chosen places makes the idele, read in
the extension, an `S`-idele, and the local-to-global criterion exhibits it as a norm.

## Main results

* `InverseGalois.CFT.mem_toAddSubgroup_range_powMonoidHom`: the additive description of the `n`-th
  powers of a commutative group.
* `InverseGalois.CFT.powSIdele_le_range_ideleNorm`: **an idele of the base field which is a local
  power at the infinite places and at the first set of places and a unit outside the two sets is a
  norm from a cyclic extension of prime degree which splits completely above the second set and is
  unramified outside.**

## Tags

number field, idele, norm, prime degree, split completely, unramified, second inequality
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### The powers of a commutative group, additively -/

section Pow

variable {G : Type*} [CommGroup G] {n : ℕ}

/-- The additive description of the `n`-th powers of a commutative group: an element of the additive
copy of the group lies in the image of the `n`-th power map exactly when it is `n` times an
element. -/
theorem mem_toAddSubgroup_range_powMonoidHom {u : Additive G} :
    u ∈ Subgroup.toAddSubgroup (powMonoidHom n : G →* G).range ↔ ∃ z, u = n • z := by
  rw [Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨Additive.ofMul z, ?_⟩
    rw [← ofMul_pow, ← powMonoidHom_apply, hz]
    rfl
  · rintro ⟨z, rfl⟩
    exact ⟨Additive.toMul z, by rw [powMonoidHom_apply, ← toMul_nsmul]⟩

end Pow

/-! ### The cyclic case of prime degree -/

section Cyclic

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **An idele of the base field which is a local power at the infinite places and at the first set
of places and a unit outside the two sets is a norm from a cyclic extension of prime degree which
splits completely above the second set and is unramified outside.**  Nothing is asked of the
extension at the infinite places nor above the first set: the order of a decomposition group divides
the degree, which is the very exponent of the local powers, so those components are local norms for
free. -/
theorem powSIdele_le_range_ideleNorm {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {p : ℕ} (hp : Nat.card Gal(K/k) = p)
    {S T : Set (HeightOneSpectrum (𝓞 k))} [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hS : S.Finite) (hT : T.Finite)
    (hsplitT : ∀ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∉ S →
      primeUnder (𝓞 k) v ∈ T → stabilizer Gal(K/k) v = ⊥)
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∉ S → primeUnder (𝓞 k) v ∉ T →
      Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal)
    {x : ↥(idele k)} (hx : (x : FullIdele k) ∈ powSIdele S T p) :
    x ∈ (ideleNorm k K).range := by
  classical
  rw [powSIdele, AddSubgroup.mem_prod] at hx
  have hxinf : ∀ w : InfinitePlace k, ∃ z, (x : FullIdele k).1 w = p • z := by
    intro w
    have hw := (AddSubgroup.mem_pi Set.univ).mp hx.1 w (Set.mem_univ w)
    rwa [infinitePow, mem_toAddSubgroup_range_powMonoidHom] at hw
  have hxS : ∀ v ∈ S, ∃ z, (x : FullIdele k).2 v = p • z := by
    intro v hv
    have hvm := (AddSubgroup.mem_pi Set.univ).mp hx.2 v (Set.mem_univ v)
    rwa [adicPowSIdele_of_mem S T p hv, mem_toAddSubgroup_range_powMonoidHom] at hvm
  have hxout : ∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v ∉ T →
      unitVal ((x : FullIdele k).2 v) = 0 := by
    intro v hvS hvT
    have hvm := (AddSubgroup.mem_pi Set.univ).mp hx.2 v (Set.mem_univ v)
    rwa [adicPowSIdele_of_notMem S T p hvS, adicSUnits_of_notMem T hvT,
      AddMonoidHom.mem_ker] at hvm
  set A : Set (HeightOneSpectrum (𝓞 K)) :=
    {v : HeightOneSpectrum (𝓞 K) | primeUnder (𝓞 k) v ∈ S ∪ T} with hAdef
  have hAfin : A.Finite := finite_setOf_primeUnder_mem k (hS.union hT)
  have hAstable : ∀ (g : Gal(K/k)) (y : HeightOneSpectrum (𝓞 K)), g • y ∈ A ↔ y ∈ A := by
    intro g y
    show primeUnder (𝓞 k) (g • y) ∈ S ∪ T ↔ primeUnder (𝓞 k) y ∈ S ∪ T
    rw [primeUnder_smul_eq]
  haveI : Finite ↥A := hAfin.to_subtype
  letI : MulAction Gal(K/k) ↥A := stableAction hAstable
  set f : ↥(idele K) := ideleComap k K x with hfdef
  have hι : ∀ (g : Gal(K/k)) (y : ↥A),
      (Subtype.val (g • y) : HeightOneSpectrum (𝓞 K)) = g • (y : HeightOneSpectrum (𝓞 K)) :=
    fun _ _ => rfl
  have hrange : Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K)) = A := Subtype.range_coe
  have hAr : (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K))).Finite :=
    Set.finite_range _
  have hsupp : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A → unitVal ((f : FullIdele K).2 v) = 0 := by
    intro v hv
    show unitVal (adicUnitsComap k v ((x : FullIdele k).2 (primeUnder (𝓞 k) v))) = 0
    rw [unitVal_adicUnitsComap_eq_zero_iff]
    exact hxout _ (fun h => hv (Or.inl h)) (fun h => hv (Or.inr h))
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
    congrArg Subtype.val (ideleAut_ideleComap k K σ x)
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
      ∃ (m : ℕ) (y : Additive ((orbitOut ω : ω.orbit) : InfinitePlace K).Completionˣ),
        Nat.card ↥(stabilizer Gal(K/k) ((orbitOut ω : ω.orbit) : InfinitePlace K)) ∣ m
          ∧ smulUnitsAut
              (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit_infinite (orbitOut ω))) y = y
          ∧ fS.1 ((orbitOut ω : ω.orbit) : InfinitePlace K) = m • y := by
    intro ω
    obtain ⟨z, hz⟩ := hxinf ((((orbitOut ω : ω.orbit) : InfinitePlace K)).comap (algebraMap k K))
    refine ⟨p, infiniteUnitsComap k _ z, (Subgroup.card_subgroup_dvd_card _).trans (dvd_of_eq hp),
      smulUnitsAut_infiniteUnitsComap k _ _ z, ?_⟩
    show infiniteUnitsComap k _ ((x : FullIdele k).1 _) = p • infiniteUnitsComap k _ z
    rw [hz, map_nsmul]
  have hfin : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      ω.out ∈ Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K)) →
      ∃ (m : ℕ) (y : Additive
          (((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ),
        Nat.card ↥(stabilizer Gal(K/k) ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) ∣ m
          ∧ smulUnitsAut
              (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit (orbitOut ω))) y = y
          ∧ ((fS.2 ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) :
                ↥(adicSUnits (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K)))
                  ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))) :
              Additive (((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)
            = m • y := by
    intro ω hω
    rw [hrange] at hω
    have hωA : primeUnder (𝓞 k) ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) ∈ S ∪ T := hω
    by_cases hvS : primeUnder (𝓞 k) ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) ∈ S
    · obtain ⟨z, hz⟩ := hxS _ hvS
      refine ⟨p, adicUnitsComap k _ z, (Subgroup.card_subgroup_dvd_card _).trans (dvd_of_eq hp),
        smulUnitsAut_adicUnitsComap k _ _ z, ?_⟩
      show adicUnitsComap k _ ((x : FullIdele k).2 _) = p • adicUnitsComap k _ z
      rw [hz, map_nsmul]
    · haveI : Subsingleton ↥(stabilizer Gal(K/k)
          ((orbitOut ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) := by
        rw [hsplitT _ hvS (hωA.resolve_left hvS)]
        infer_instance
      refine ⟨1, _, Nat.dvd_one.mpr (Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩), ?_,
        (one_nsmul _).symm⟩
      rw [Subsingleton.elim (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit (orbitOut ω)))
        1, map_one]
      rfl
  obtain ⟨u, hu⟩ := exists_normHom_sIdeleAut_of_nsmul hι hgen hp hunramπ hfix hinf hfin
  refine ⟨sIdeleToIdele (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K))) hAr u,
    ideleComap_injective k K ?_⟩
  rw [ideleComap_ideleNorm_eq_normHom k K hgen hp,
    ← map_normHom (sIdeleToIdele (Set.range (Subtype.val : ↥A → HeightOneSpectrum (𝓞 K))) hAr)
      (sIdeleToIdele_sIdeleAut hι hAr σ) p u, hu, htoIdele, hfdef]

end Cyclic

end InverseGalois.CFT
