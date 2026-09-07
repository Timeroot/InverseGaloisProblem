/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.RelativeFrobenius

/-!
# Prescribing a decomposition group that is only normal over an intermediate field

Realising a cyclic group of prime order as a decomposition group asks that group to be normal, so
that its fixed field is Galois over the base and the density of the primes splitting completely
there can be compared with the density of the primes splitting completely above.  An element of a
Galois group is often normal only over an intermediate field: it generates a normal subgroup of the
automorphisms fixing that field without generating a normal subgroup of the whole group.

The comparison can then be run over the intermediate field, and its outcome carried down to the
base along a prime of residue degree one.  A prime `w` of the intermediate field whose absolute
norm is its residue characteristic lies over a prime `v` of the base with the same absolute norm,
because the norm of `w` is a power of the norm of `v` and a prime number is not a proper power of
an integer exceeding one.  Reading the absolute norm of a prime `P` of the top field in both ways
shows that `P` has the same residue degree over `v` as over `w`; asking in addition that `v` be
unramified in the top field makes the two decomposition groups have the same order.  One of them
contains the other, so they are equal, and the automorphism prescribed over the intermediate field
generates the decomposition group over the base.

## Main definitions

* `InverseGalois.CFT.relRestrictScalarsHom` — restriction of scalars as a homomorphism between
  groups of automorphisms.

## Main results

* `InverseGalois.CFT.relRestrictScalars_mem_stabilizer` — restriction of scalars preserves
  decomposition groups.
* `InverseGalois.CFT.absNorm_primeBelow_eq` — a prime whose absolute norm is its residue
  characteristic lies over a prime of the base with the same absolute norm.
* `InverseGalois.CFT.inertiaDeg_primeBelow_eq` — above such a prime the residue degree over the
  base agrees with the residue degree over the intermediate field.
* `InverseGalois.CFT.exists_relStabilizer_eq_zpowers_restrictScalars` — **an element of prime order
  generating a subgroup normal in the automorphisms of an intermediate field is the decomposition
  group over the base at infinitely many primes**, and the Frobenius there generates the group it
  generates.

## Tags

Frobenius, decomposition group, Chebotarev, restriction of scalars, residue degree, number field
-/

open NumberField IsDedekindDomain InverseGalois.NumberTheory

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

/-! ### Restriction of scalars and the decomposition group -/

section RestrictScalars

variable {k F N : Type*} [Field k] [Field F] [Field N] [Algebra k F] [Algebra k N] [Algebra F N]
  [IsScalarTower k F N]

variable (k) in
/-- **Restriction of scalars as a homomorphism between groups of automorphisms**: an automorphism
of the top field fixing an intermediate field is in particular one fixing the base. -/
def relRestrictScalarsHom : Gal(N/F) →* Gal(N/k) where
  toFun τ := τ.restrictScalars k
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp]
theorem relRestrictScalarsHom_apply (τ : Gal(N/F)) :
    relRestrictScalarsHom k τ = τ.restrictScalars k := rfl

theorem relRestrictScalarsHom_injective :
    Function.Injective (relRestrictScalarsHom (F := F) (N := N) k) :=
  AlgEquiv.restrictScalars_injective k

/-- Restriction of scalars does not change the order of an automorphism. -/
theorem orderOf_relRestrictScalars (τ : Gal(N/F)) :
    orderOf (τ.restrictScalars k) = orderOf τ :=
  orderOf_injective (relRestrictScalarsHom (F := F) (N := N) k) relRestrictScalarsHom_injective τ

/-- Restriction of scalars does not change the action on the ideals of the ring of integers. -/
theorem relRestrictScalars_smul_ideal (τ : Gal(N/F)) (P : Ideal (𝓞 N)) :
    (τ.restrictScalars k) • P = τ • P := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

/-- **Restriction of scalars sends decomposition into decomposition.** -/
theorem relRestrictScalars_mem_stabilizer {P : Ideal (𝓞 N)} {τ : Gal(N/F)}
    (hτ : τ ∈ MulAction.stabilizer Gal(N/F) P) :
    τ.restrictScalars k ∈ MulAction.stabilizer Gal(N/k) P := by
  rw [MulAction.mem_stabilizer_iff] at hτ ⊢
  rw [relRestrictScalars_smul_ideal, hτ]

end RestrictScalars

/-! ### Descending a prime of residue degree one -/

section Descent

variable {k F : Type*} [Field k] [NumberField k] [Field F] [NumberField F] [Algebra k F]

variable (F) in
/-- **Only finitely many primes of an extension lie above a finite set of primes of the base.** -/
theorem finite_preimage_primeBelow {S : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite) :
    (primeBelow (L := F) k ⁻¹' S).Finite := by
  have hcover : (primeBelow (L := F) k ⁻¹' S)
      = ⋃ v ∈ S, (primeBelow (L := F) k ⁻¹' {v}) := by
    ext w
    simp
  rw [hcover]
  exact hS.biUnion fun v _ => Set.toFinite _

/-- **A prime whose absolute norm is its residue characteristic lies over a prime of the base with
the same absolute norm.**  The norm below divides the norm above, which is prime, and it is at
least two. -/
theorem absNorm_primeBelow_eq {w : HeightOneSpectrum (𝓞 F)}
    (hw : Ideal.absNorm w.asIdeal = resChar w) :
    Ideal.absNorm (primeBelow k w).asIdeal = Ideal.absNorm w.asIdeal := by
  set v : HeightOneSpectrum (𝓞 k) := primeBelow k w with hvdef
  have hpow : Ideal.absNorm w.asIdeal
      = Ideal.absNorm v.asIdeal ^ (v.asIdeal.inertiaDeg w.asIdeal) :=
    Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := two_le_absNorm v
  have hprime : (Ideal.absNorm w.asIdeal).Prime := hw ▸ resChar_prime w
  have hf0 : v.asIdeal.inertiaDeg w.asIdeal ≠ 0 := by
    intro h
    rw [h, pow_zero] at hpow
    exact hprime.one_lt.ne' hpow
  have hdvd : Ideal.absNorm v.asIdeal ∣ Ideal.absNorm w.asIdeal := by
    rw [hpow]
    exact dvd_pow_self _ hf0
  rcases hprime.eq_one_or_self_of_dvd _ hdvd with h | h
  · omega
  · exact h

/-- A prime whose absolute norm is its residue characteristic lies over a prime of the base of the
same kind. -/
theorem absNorm_primeBelow_eq_resChar {w : HeightOneSpectrum (𝓞 F)}
    (hw : Ideal.absNorm w.asIdeal = resChar w) :
    Ideal.absNorm (primeBelow k w).asIdeal = resChar (primeBelow k w) := by
  have h := absNorm_primeBelow_eq (k := k) hw
  show Ideal.absNorm (primeBelow k w).asIdeal = (Ideal.absNorm (primeBelow k w).asIdeal).minFac
  rw [h]
  exact hw

variable {N : Type*} [Field N] [NumberField N] [Algebra k N] [Algebra F N] [IsScalarTower k F N]

/-- **Above a prime of residue degree one the residue degree over the base agrees with the residue
degree over the intermediate field**, since the absolute norm of the prime above is the same power
of the same integer read either way. -/
theorem inertiaDeg_primeBelow_eq {w : HeightOneSpectrum (𝓞 F)}
    (hw : Ideal.absNorm w.asIdeal = resChar w) (P : Ideal (𝓞 N)) [P.IsPrime]
    [P.LiesOver w.asIdeal] :
    (primeBelow k w).asIdeal.inertiaDeg P = w.asIdeal.inertiaDeg P := by
  haveI : P.LiesOver (primeBelow k w).asIdeal :=
    Ideal.LiesOver.trans P w.asIdeal (primeBelow k w).asIdeal
  set v : HeightOneSpectrum (𝓞 k) := primeBelow k w with hvdef
  have hq : Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal := absNorm_primeBelow_eq (k := k) hw
  have h1 : Ideal.absNorm P = Ideal.absNorm v.asIdeal ^ (v.asIdeal.inertiaDeg P) :=
    Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P v.asIdeal v.isPrime v.ne_bot
  have h2 : Ideal.absNorm P = Ideal.absNorm w.asIdeal ^ (w.asIdeal.inertiaDeg P) :=
    Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P w.asIdeal w.isPrime w.ne_bot
  refine Nat.pow_right_injective (two_le_absNorm v) ?_
  show Ideal.absNorm v.asIdeal ^ (v.asIdeal.inertiaDeg P)
    = Ideal.absNorm v.asIdeal ^ (w.asIdeal.inertiaDeg P)
  rw [← h1, h2, hq]

end Descent

/-! ### Realising a subgroup of prime order over the base -/

section Base

variable {k F N : Type*} [Field k] [NumberField k] [Field F] [NumberField F] [Field N]
  [NumberField N] [Algebra k F] [Algebra k N] [Algebra F N] [IsScalarTower k F N] [IsGalois k N]

/-- **An element of prime order generating a subgroup normal in the automorphisms of an
intermediate field is the decomposition group over the base at infinitely many primes.**  Over the
intermediate field the subgroup it generates is realised as a decomposition group at a prime `w` of
residue degree one over the rationals, avoiding the primes above a prescribed finite set of primes
of the base and above the primes of the base ramifying at the top.  The prime `v` below `w` then has
the same absolute norm as `w`, so a prime above has the same residue degree over `v` as over `w`;
since `v` is unramified the two decomposition groups have the same order, and one contains the
other. -/
theorem exists_relStabilizer_eq_zpowers_restrictScalars {σ : Gal(N/F)}
    (hnorm : (Subgroup.zpowers σ).Normal) (hp : (orderOf σ).Prime)
    (T : Finset (HeightOneSpectrum (𝓞 k))) :
    ∃ v : HeightOneSpectrum (𝓞 k), v ∉ T ∧ v ∉ relRamifiedSet k N ∧
      Ideal.absNorm v.asIdeal = resChar v ∧
      ∃ (P : Ideal (𝓞 N)) (_ : P.IsPrime) (_ : P.LiesOver v.asIdeal) (_ : Finite (𝓞 N ⧸ P)),
        MulAction.stabilizer Gal(N/k) P = Subgroup.zpowers (σ.restrictScalars k) ∧
        Subgroup.zpowers (arithFrobAt (𝓞 k) Gal(N/k) P)
          = Subgroup.zpowers (σ.restrictScalars k) := by
  classical
  haveI : IsGalois F N := IsGalois.tower_top_of_isGalois k F N
  have hSfin : ((T : Set (HeightOneSpectrum (𝓞 k))) ∪ relRamifiedSet k N).Finite :=
    T.finite_toSet.union (finite_relRamifiedSet (k := k) (L := N))
  have hT'fin := finite_preimage_primeBelow (k := k) F hSfin
  obtain ⟨w, hwT', hwram, hwdeg, P, hPprime, hPoverW, hPfin, hstabF, _⟩ :=
    exists_relStabilizer_eq_zpowers (k := F) (L := N) hnorm hp hT'fin.toFinset
  haveI := hPprime
  haveI := hPoverW
  haveI := hPfin
  set v : HeightOneSpectrum (𝓞 k) := primeBelow k w with hvdef
  have hvmem : v ∉ ((T : Set (HeightOneSpectrum (𝓞 k))) ∪ relRamifiedSet k N) := fun h =>
    hwT' ((Set.Finite.mem_toFinset hT'fin).mpr h)
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hvmem
  obtain ⟨hvT, hvram⟩ := hvmem
  haveI hPoverV : P.LiesOver v.asIdeal := Ideal.LiesOver.trans P w.asIdeal v.asIdeal
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hunderk : P.under (𝓞 k) = v.asIdeal :=
    (Ideal.LiesOver.over (A := 𝓞 k) (P := P) (p := v.asIdeal)).symm
  have hunderF : P.under (𝓞 F) = w.asIdeal :=
    (Ideal.LiesOver.over (A := 𝓞 F) (P := P) (p := w.asIdeal)).symm
  -- the prime below is unramified at the top, and so is the prime of the intermediate field
  have hunr : Algebra.IsUnramifiedAt (𝓞 k) P := by
    refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 k) hP0).mpr ?_
    rw [hunderk]
    by_contra hc
    exact hvram ⟨P, ⟨hPprime, hPoverV⟩, hc⟩
  have hunrF : Algebra.IsUnramifiedAt (𝓞 F) P := by
    refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 F) hP0).mpr ?_
    rw [hunderF]
    by_contra hc
    exact hwram ⟨P, ⟨hPprime, hPoverW⟩, hc⟩
  -- the two decomposition groups have the same order
  have hcardF : Nat.card (MulAction.stabilizer Gal(N/F) P) = w.asIdeal.inertiaDeg P := by
    rw [card_relStabilizer (k := F) P hP0,
      (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 F) hP0).mp hunrF, one_mul, hunderF]
  have hcardk : Nat.card (MulAction.stabilizer Gal(N/k) P) = v.asIdeal.inertiaDeg P := by
    rw [card_relStabilizer (k := k) P hP0,
      (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 k) hP0).mp hunr, one_mul, hunderk]
  have hff : v.asIdeal.inertiaDeg P = w.asIdeal.inertiaDeg P :=
    inertiaDeg_primeBelow_eq (k := k) hwdeg P
  have hcardσ : Nat.card (MulAction.stabilizer Gal(N/F) P) = orderOf σ := by
    rw [hstabF, Nat.card_zpowers]
  -- the restriction of the prescribed automorphism lies in the decomposition group over the base
  have hmemF : σ ∈ MulAction.stabilizer Gal(N/F) P := by
    rw [hstabF]
    exact Subgroup.mem_zpowers σ
  have hmemk : σ.restrictScalars k ∈ MulAction.stabilizer Gal(N/k) P :=
    relRestrictScalars_mem_stabilizer hmemF
  have hstabeq : MulAction.stabilizer Gal(N/k) P = Subgroup.zpowers (σ.restrictScalars k) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmemk) ?_).symm
    rw [Nat.card_zpowers, orderOf_relRestrictScalars, hcardk, hff, ← hcardF, hcardσ]
  exact ⟨v, hvT, hvram, absNorm_primeBelow_eq_resChar (k := k) hwdeg, P, hPprime, hPoverV,
    hPfin, hstabeq, (relStabilizer_eq_zpowers_arithFrobAt P hP0 hunr).symm.trans hstabeq⟩

end Base

end InverseGalois.CFT
