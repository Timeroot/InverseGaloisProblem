/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.FirstInequality
import InverseGalois.CFT.Units.HasseNorm
import InverseGalois.CFT.Units.SIdeleNorm

/-!
# The norm theorem in local form

A unit of the base field of a cyclic extension of number fields which is a norm from the completion
of the extension at every place is the norm of a unit of the extension.  This is the local form of
the norm theorem: being a norm is a condition that can be tested one place at a time.

Three steps join the local conditions to the global conclusion.  The first is local and purely
algebraic: the decomposition group at a place acts faithfully on the completion there, it commutes
with the scalars of the completion of the base, and every automorphism of the completion over the
completion of the base is the action of an element of it, so the decomposition group is the Galois
group of the local extension and the field norm of the completion is the product of the conjugates
under the decomposition group.  That product is exactly the norm operator of the Tate formalism for
a full turn of the orbit of the place, a full turn generating the decomposition group.

The second step is the local-to-global criterion already available: an idele that is a unit outside
a finite invariant set of places is a norm as soon as it is a local norm at one place above each
place of the base field.  Enlarging the support of the idele together with the places lacking a
fixed uniformizer to a finite invariant set of places makes the criterion apply, and it exhibits the
idele as the norm of an idele of the extension.

The third step is the norm theorem for the idele class group: a unit of the base field whose
principal idele is the norm of an idele is the norm of a unit of the extension.

## Main results

* `InverseGalois.CFT.algebraMap_norm_eq_prod_smul`: the field norm is the product of the conjugates
  under a group of automorphisms exhausting the Galois group.
* `InverseGalois.CFT.exists_normHom_smulUnitsAut_of_mem_normSubgroup`: a unit of the base field that
  is a norm is a value of the norm operator of a generator.
* `InverseGalois.CFT.mem_range_ideleNorm_of_forall_mem_normSubgroup`: **an idele of the base field
  that is a local norm at every place is the norm of an idele.**
* `InverseGalois.CFT.mem_normSubgroup_of_forall_local`: **the norm theorem in local form**, that a
  unit of the base field of a cyclic extension which is a local norm at every place is the norm of a
  unit of the extension.

## Tags

Hasse norm theorem, local norm, decomposition group, idele, cyclic extension
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

/-! ### The field norm as a product over a group of automorphisms -/

section GroupNorm

variable {G : Type*} [Group G] [Fintype G]

/-- The Tate norm operator of a generator, on the units of a ring acted on by the group, is the
product of the conjugates over the whole group. -/
theorem coe_normHom_smulUnitsAut {R : Type*} [CommRing R] [MulSemiringAction G R] {τ : G}
    (hτ : ∀ g : G, g ∈ Subgroup.zpowers τ) (b : Rˣ) :
    ((Additive.toMul
        (normHom (smulUnitsAut (R := R) τ) (Nat.card G) (Additive.ofMul b)) : Rˣ) : R)
      = ∏ g : G, g • (b : R) := by
  have hstep : ∀ i : ℕ,
      ((Additive.toMul (((smulUnitsAut (R := R) τ) ^ i) (Additive.ofMul b)) : Rˣ) : R)
        = (τ ^ i) • (b : R) := by
    intro i
    rw [← map_pow (smulUnitsAut (R := R)) τ i]
    exact coe_smulUnitsAut_apply (τ ^ i) (Additive.ofMul b)
  rw [normHom_apply, ← prod_range_card_pow hτ fun g : G => g • (b : R)]
  induction Nat.card G with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ, ← ih]
    show ((Additive.toMul (_ + _) : Rˣ) : R) = _
    rw [show ∀ x y : Additive Rˣ,
        ((Additive.toMul (x + y) : Rˣ) : R)
          = ((Additive.toMul x : Rˣ) : R) * ((Additive.toMul y : Rˣ) : R) from fun _ _ => rfl,
      hstep m]

variable {k₀ L : Type*} [Field k₀] [Field L] [Algebra k₀ L] [FiniteDimensional k₀ L]
  [IsGalois k₀ L] [MulSemiringAction G L] [FaithfulSMul G L] [SMulCommClass G k₀ L]

/-- **The field norm is the product of the conjugates under a group of automorphisms** exhausting
the Galois group. -/
theorem algebraMap_norm_eq_prod_smul
    (hsurj : ∀ τ : L ≃ₐ[k₀] L, ∃ g : G, ∀ z : L, g • z = τ z) (x : L) :
    algebraMap k₀ L (Algebra.norm k₀ x) = ∏ g : G, g • x := by
  rw [Algebra.norm_eq_prod_automorphisms]
  refine (Fintype.prod_bijective (fun g : G => MulSemiringAction.toAlgEquiv k₀ L g)
    ⟨fun g g' h => ?_, fun τ => ?_⟩ _ _ fun _ => rfl).symm
  · refine eq_of_smul_eq_smul (α := L) fun z => ?_
    exact congrArg (fun e : L ≃ₐ[k₀] L => e z) h
  · obtain ⟨g, hg⟩ := hsurj τ
    exact ⟨g, AlgEquiv.ext hg⟩

/-- **A unit of the base field that is a norm is a value of the Tate norm operator** of a generator
of a group of automorphisms exhausting the Galois group. -/
theorem exists_normHom_smulUnitsAut_of_mem_normSubgroup
    (hsurj : ∀ τ : L ≃ₐ[k₀] L, ∃ g : G, ∀ z : L, g • z = τ z) {τ : G}
    (hτ : ∀ g : G, g ∈ Subgroup.zpowers τ) {a : k₀ˣ} (ha : a ∈ normSubgroup k₀ L) :
    ∃ b, normHom (smulUnitsAut (R := L) τ) (Nat.card G) b
      = Additive.ofMul (Units.map (algebraMap k₀ L).toMonoidHom a) := by
  obtain ⟨y, hy⟩ := (mem_normSubgroup_iff a).mp ha
  refine ⟨Additive.ofMul y, Additive.toMul.injective (Units.ext ?_)⟩
  rw [coe_normHom_smulUnitsAut hτ y, ← algebraMap_norm_eq_prod_smul hsurj (y : L), hy]
  rfl

end GroupNorm

/-! ### The decomposition group as a group of automorphisms of the completion -/

section Decomposition

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The decomposition group at a finite place commutes with the scalars of the completion of the
base field. -/
instance instSMulCommClassStabilizerAdicCompletion (w : HeightOneSpectrum (𝓞 K)) :
    SMulCommClass ↥(stabilizer Gal(K/k) w) ((primeUnder (𝓞 k) w).adicCompletion k)
      (w.adicCompletion K) where
  smul_comm g c z := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', stabilizer_smul_algebraMap k w g c]

/-- The decomposition group at an infinite place commutes with the scalars of the completion of the
base field. -/
instance instSMulCommClassStabilizerInfiniteCompletion (w : InfinitePlace K) :
    SMulCommClass ↥(stabilizer Gal(K/k) w) (w.comap (algebraMap k K)).Completion w.Completion where
  smul_comm g c z := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul',
      stabilizer_smul_algebraMap_infinite k w g c]

variable [IsGalois k K]

variable (k) in
/-- **Every automorphism of the completion at a finite place is given by the decomposition
group.** -/
theorem exists_stabilizer_smul_eq (w : HeightOneSpectrum (𝓞 K))
    (τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) :
    ∃ g : ↥(stabilizer Gal(K/k) w), ∀ z : w.adicCompletion K, g • z = τ z :=
  ⟨⟨restrictToBase k w τ, restrictToBase_mem_stabilizer k w τ⟩,
    fun z => adicCompletionAut_restrictToBase k w τ z⟩

variable (k) in
/-- **Every automorphism of the completion at an infinite place is given by the decomposition
group.** -/
theorem exists_stabilizer_smul_eq_infinite (w : InfinitePlace K)
    (τ : w.Completion ≃ₐ[(w.comap (algebraMap k K)).Completion] w.Completion) :
    ∃ g : ↥(stabilizer Gal(K/k) w), ∀ z : w.Completion, g • z = τ z :=
  ⟨⟨restrictToBaseInfinite k w τ, restrictToBaseInfinite_mem_stabilizer k w τ⟩,
    fun z => infiniteCompletionAut_restrictToBaseInfinite k w τ z⟩

end Decomposition

/-! ### Local norms at a place of the extension -/

section LocalNorm

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)

include hgen

/-- **A local norm at a finite place is a value of the Tate norm operator** of a full turn of the
orbit of that place. -/
theorem exists_normHom_orbitTurn_adicUnits_of_mem_normSubgroup
    {ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K))} (v₀ : ω.orbit) [Fintype ω.orbit]
    (hH : ∀ g : Gal(K/k), g • v₀ = v₀ → g ∈ stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)))
    {a : ((primeUnder (𝓞 k) (v₀ : HeightOneSpectrum (𝓞 K))).adicCompletion k)ˣ}
    (ha : a ∈ normSubgroup ((primeUnder (𝓞 k) (v₀ : HeightOneSpectrum (𝓞 K))).adicCompletion k)
      ((v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)) :
    ∃ b, normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
        (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K) (orbitTurn σ v₀ hH))
        (Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)))) b
      = adicUnitsComap k (v₀ : HeightOneSpectrum (𝓞 K)) (Additive.ofMul a) := by
  haveI : Fintype ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) := Fintype.ofFinite _
  haveI := isGalois_adicCompletion k (v₀ : HeightOneSpectrum (𝓞 K))
  exact exists_normHom_smulUnitsAut_of_mem_normSubgroup
    (exists_stabilizer_smul_eq k (v₀ : HeightOneSpectrum (𝓞 K)))
    (mem_zpowers_orbitTurn v₀ hH hgen (smul_orbit_of_mem_stabilizer v₀)) ha

/-- **A local norm at an infinite place is a value of the Tate norm operator** of a full turn of
the orbit of that place. -/
theorem exists_normHom_orbitTurn_infiniteUnits_of_mem_normSubgroup
    {ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K)} (w₀ : ω.orbit) [Fintype ω.orbit]
    (hH : ∀ g : Gal(K/k), g • w₀ = w₀ → g ∈ stabilizer Gal(K/k) (w₀ : InfinitePlace K))
    {a : (((w₀ : InfinitePlace K).comap (algebraMap k K)).Completion)ˣ}
    (ha : a ∈ normSubgroup (((w₀ : InfinitePlace K).comap (algebraMap k K)).Completion)
      (w₀ : InfinitePlace K).Completion) :
    ∃ b, normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)))
        (R := (w₀ : InfinitePlace K).Completion) (orbitTurn σ w₀ hH))
        (Nat.card ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K))) b
      = infiniteUnitsComap k (w₀ : InfinitePlace K) (Additive.ofMul a) := by
  haveI : Fintype ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)) := Fintype.ofFinite _
  haveI := isGalois_infiniteCompletion k (w₀ : InfinitePlace K)
  exact exists_normHom_smulUnitsAut_of_mem_normSubgroup
    (exists_stabilizer_smul_eq_infinite k (w₀ : InfinitePlace K))
    (mem_zpowers_orbitTurn w₀ hH hgen (smul_orbit_of_mem_stabilizer_infinite w₀)) ha

end LocalNorm

/-! ### The norm theorem in local form -/

section Global

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **An idele of the base field that is a local norm at every place is a norm of an idele.** -/
theorem mem_range_ideleNorm_of_forall_mem_normSubgroup {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ} (hn : Nat.card Gal(K/k) = n)
    (d : ↥(idele k))
    (hinf : ∀ w : InfinitePlace K,
      Additive.toMul ((d : FullIdele k).1 (w.comap (algebraMap k K)))
        ∈ normSubgroup ((w.comap (algebraMap k K)).Completion) w.Completion)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 K),
      Additive.toMul ((d : FullIdele k).2 (primeUnder (𝓞 k) w))
        ∈ normSubgroup ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)) :
    d ∈ (ideleNorm k K).range := by
  classical
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
  have hinf' : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ∃ b,
      normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) ω.out)) (R := (ω.out).Completion)
          (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit_infinite (orbitOut ω))))
        (Nat.card ↥(stabilizer Gal(K/k) ω.out)) b = fS.1 ω.out := by
    intro ω
    haveI : Fintype ω.orbit := Fintype.ofFinite _
    exact exists_normHom_orbitTurn_infiniteUnits_of_mem_normSubgroup hgen (orbitOut ω)
      (mem_stabilizer_of_smul_orbit_infinite (orbitOut ω)) (hinf ω.out)
  have hfin' : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      ω.out ∈ Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K)) → ∃ b,
        normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) ω.out))
            (R := (ω.out).adicCompletion K)
            (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit (orbitOut ω))))
          (Nat.card ↥(stabilizer Gal(K/k) ω.out)) b
        = ((fS.2 ω.out : ↥(adicSUnits (Set.range (Subtype.val : ↥T → _)) ω.out)) :
            Additive ((ω.out).adicCompletion K)ˣ) := by
    intro ω _
    haveI : Fintype ω.orbit := Fintype.ofFinite _
    exact exists_normHom_orbitTurn_adicUnits_of_mem_normSubgroup hgen (orbitOut ω)
      (mem_stabilizer_of_smul_orbit (orbitOut ω)) (hfin ω.out)
  obtain ⟨u, hu⟩ := exists_normHom_sIdeleAut hι hgen hn hunram hfix hinf' hfin'
  refine ⟨sIdeleToIdele (Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K))) hTr u,
    ideleComap_injective k K ?_⟩
  rw [ideleComap_ideleNorm_eq_normHom k K hgen hn,
    ← map_normHom (sIdeleToIdele (Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K))) hTr)
      (sIdeleToIdele_sIdeleAut hι hTr σ) n u, hu, htoIdele, hfdef]

/-- **The norm theorem in local form for a cyclic extension of number fields.**  A unit of the base
field that is a local norm at every place is the norm of a unit of the extension. -/
theorem mem_normSubgroup_of_forall_local [IsCyclic Gal(K/k)] (a : kˣ)
    (hinf : ∀ w : InfinitePlace K,
      infiniteUnitHom (w.comap (algebraMap k K)) a
        ∈ normSubgroup ((w.comap (algebraMap k K)).Completion) w.Completion)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 K),
      adicUnitHom (primeUnder (𝓞 k) w) a
        ∈ normSubgroup ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)) :
    a ∈ normSubgroup k K := by
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_generator (α := Gal(K/k))
  exact mem_normSubgroup_of_mem_range_ideleNorm a
    (mem_range_ideleNorm_of_forall_mem_normSubgroup hgen rfl _ hinf hfin)

end Global

end InverseGalois.CFT
