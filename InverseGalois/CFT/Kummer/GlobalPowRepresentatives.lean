/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LocalPowerConverse
import InverseGalois.CFT.Kummer.LocalPowRepresentatives
import InverseGalois.CFT.Kummer.SupPowSurjective
import InverseGalois.CFT.Units.DecompositionField

/-!
# Finitely many global representatives of the power classes of a decomposition subgroup

At a place of a number field the power classes of the completion have finitely many
representatives, and those representatives may be taken in the field itself.  The present file
carries that finiteness up an infinite algebraic extension: the elements of an algebraic closure
fixed by the subgroup stabilizing a prime of the closure form a field, the henselization of the
base at that prime, and its power classes are represented by the same finite set.

The passage is made one finite Galois level at a time.  An element fixed by the stabilizer of the
prime lies, at any level containing it, in the decomposition field of the prime of that level, so it
is read by the embedding of the decomposition field into the completion; a representative of its
class is chosen there, and a root of the quotient by the representative is taken in the closure.
That root is fixed by the stabilizer only up to a root of unity, because a local power root is
determined only up to one, and the discrepancy is absorbed by multiplying the root by a suitable
power of a primitive root of unity of the level.

## Main results

* `InverseGalois.CFT.exists_pow_smul_eq_of_pow_eq_pow`: **an element whose power comes from the
  completion below becomes fixed by the stabilizer of the place after multiplication by a root of
  unity.**
* `InverseGalois.CFT.exists_finite_pow_representatives_stabilizer`: **finitely many elements
  represent every power class of the elements of an algebraic closure fixed by the stabilizer of a
  prime.**

## Tags

number field, decomposition group, henselization, local power class, Kummer theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### A power root, corrected by a root of unity -/

section GenPower

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (w : HeightOneSpectrum (𝓞 M)) {p : ℕ}

/-- **An element whose power comes from the completion below becomes fixed by the stabilizer of the
place after multiplication by a root of unity.**  The quotient of the element of the completion
below by the image of the element is a root of unity, hence a power of a primitive one, and dividing
by that power lands the element in the image of the completion below, which is exactly the part
fixed by the stabilizer. -/
theorem exists_pow_smul_eq_of_pow_eq_pow {ζ : M} (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0)
    {b : M} (hd : ∃ c : (primeUnder (𝓞 K) w).adicCompletion K,
      algebraMap ((primeUnder (𝓞 K) w).adicCompletion K) (w.adicCompletion M) c ^ p
        = toAdicCompletion w b ^ p) :
    ∃ j : ℕ, ∀ σ : ↥(stabilizer Gal(M/K) w), (σ : Gal(M/K)) (b * ζ ^ j) = b * ζ ^ j := by
  haveI : NeZero p := ⟨hp⟩
  set Kv := (primeUnder (𝓞 K) w).adicCompletion K with hKv
  set Mw := w.adicCompletion M with hMw
  obtain ⟨c, hd⟩ := hd
  have hinjM : Function.Injective (toAdicCompletion w (K := M)) :=
    (toAdicCompletion w (K := M)).injective
  rcases eq_or_ne b 0 with rfl | hb
  · exact ⟨0, fun σ => by rw [pow_zero, mul_one, map_zero]⟩
  have hbne : toAdicCompletion w b ≠ 0 := fun h => hb (hinjM (by simpa using h))
  have hu : (algebraMap Kv Mw c / toAdicCompletion w b) ^ p = 1 := by
    rw [div_pow, hd, div_self (pow_ne_zero p hbne)]
  have hζM : IsPrimitiveRoot (toAdicCompletion w ζ) p := hζ.map_of_injective hinjM
  obtain ⟨j, -, hj⟩ := hζM.eq_pow_of_pow_eq_one hu
  refine ⟨j, fun σ => ?_⟩
  refine hinjM ?_
  rw [← stabilizer_smul_toAdicCompletion]
  revert σ
  rw [mem_range_algebraMap_iff_forall_stabilizer_smul_eq K w (toAdicCompletion w (b * ζ ^ j))]
  refine ⟨c, ?_⟩
  rw [map_mul, map_pow]
  exact ((eq_div_iff hbne).mp hj).symm.trans (mul_comm _ _)

end GenPower

/-! ### The representatives for the fixed field of a stabilizer -/

section Representatives

variable {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω]

/-- **Finitely many elements represent every power class of the elements of an algebraic closure
fixed by the stabilizer of a prime.**  The representatives are the images of a finite set of units
of the base field representing the power classes of the completion there.  A fixed element is read
inside a finite Galois level chosen to contain it, a power root of it, a primitive root of unity and
power roots of the representatives; at that level the element lies in the decomposition field of the
prime, so its image in the completion is a representative times a power, and the corresponding
power root over the closure is fixed by the stabilizer once it is corrected by a root of unity. -/
theorem exists_finite_pow_representatives_stabilizer {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ T : Set Ω, T.Finite ∧ (∀ y ∈ T, ∃ b : kˣ, y = algebraMap k Ω (b : k)) ∧ ∀ x : Ω, x ≠ 0 →
      (∀ σ : ↥(stabilizer Gal(Ω/k) P), (σ : Gal(Ω/k)) x = x) →
        ∃ a ∈ T, ∃ c : Ω, (∀ σ : ↥(stabilizer Gal(Ω/k) P), (σ : Gal(Ω/k)) c = c) ∧
          x = a * c ^ ℓ := by
  have hℓpos : 0 < ℓ := Nat.pos_of_ne_zero hℓ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero ((ℓ : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hℓ⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω ℓ
  have hbot : Ideal.under (𝓞 k) P ≠ ⊥ := Ideal.under_ne_bot (𝓞 k) hP
  haveI : (Ideal.under (𝓞 k) P).IsPrime := Ideal.IsPrime.under _ P
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 k), v.asIdeal = Ideal.under (𝓞 k) P :=
    ⟨⟨Ideal.under (𝓞 k) P, inferInstance, hbot⟩, rfl⟩
  obtain ⟨T₀, hT₀fin, hT₀⟩ := exists_finite_pow_representatives_adicCompletion (K := k) v hℓ
  choose α hα using fun a : kˣ =>
    IsAlgClosed.exists_pow_nat_eq (k := Ω) (algebraMap k Ω (a : k)) hℓpos
  refine ⟨(fun a : kˣ => algebraMap k Ω (a : k)) '' T₀, hT₀fin.image _, ?_, ?_⟩
  · rintro _ ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩
  intro x hx0 hx
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (k := Ω) x hℓpos
  have hsfin : (insert x (insert β (insert ζ (α '' T₀)))).Finite :=
    (((hT₀fin.image α).insert ζ).insert β).insert x
  obtain ⟨M, hMfin, hMgal, hsM⟩ := exists_isGalois_level_subset k _ hsfin
  haveI := hMfin
  haveI := hMgal
  haveI : NumberField ↥M := NumberField.of_module_finite k ↥M
  have hxM : x ∈ M := hsM (Set.mem_insert _ _)
  have hβM : β ∈ M := hsM (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hζMmem : ζ ∈ M :=
    hsM (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hαM : ∀ a ∈ T₀, α a ∈ M := fun a ha =>
    hsM (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)))
  -- the prime of the level below the prime of the whole extension
  have hMbot : Ideal.under (𝓞 ↥M) P ≠ ⊥ := Ideal.under_ne_bot (𝓞 ↥M) hP
  haveI : (Ideal.under (𝓞 ↥M) P).IsPrime := Ideal.IsPrime.under _ P
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 ↥M), w.asIdeal = Ideal.under (𝓞 ↥M) P :=
    ⟨⟨Ideal.under (𝓞 ↥M) P, inferInstance, hMbot⟩, rfl⟩
  have hveq : primeUnder (𝓞 k) w = v :=
    HeightOneSpectrum.ext (by rw [primeUnder_asIdeal, hw, Ideal.under_under, hv])
  subst hveq
  -- the element lies in the decomposition field of the level
  have hxD : (⟨x, hxM⟩ : ↥M) ∈ decompositionField k w := by
    rw [mem_decompositionField_iff]
    intro τ
    obtain ⟨σ, hσ⟩ := stabilizerRestrictPrime_surjective M hw τ
    refine Subtype.ext ?_
    have h : ((τ : Gal(↥M/k)) (⟨x, hxM⟩ : ↥M) : Ω)
        = ((AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥M (σ : Gal(Ω/k))
            (⟨x, hxM⟩ : ↥M) : ↥M) : Ω) := by
      rw [← coe_stabilizerRestrictPrime M hw σ, hσ]
    have hcomm : ((AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥M (σ : Gal(Ω/k))
        (⟨x, hxM⟩ : ↥M) : ↥M) : Ω) = (σ : Gal(Ω/k)) x :=
      AlgEquiv.restrictNormal_commutes (σ : Gal(Ω/k)) ↥M ⟨x, hxM⟩
    rw [h, hcomm]
    exact hx σ
  set Kv := (primeUnder (𝓞 k) w).adicCompletion k with hKvdef
  set Mw := w.adicCompletion ↥M with hMwdef
  set xD : ↥(decompositionField k w) := ⟨⟨x, hxM⟩, hxD⟩ with hxDdef
  have hxD0 : xD ≠ 0 := by
    intro h
    exact hx0 (congrArg (fun u : ↥(decompositionField k w) => ((u : ↥M) : Ω)) h)
  set η : Kv := decompositionFieldHom k w xD with hηdef
  have hη0 : η ≠ 0 := fun h =>
    hxD0 ((decompositionFieldHom k w).injective (by rw [← hηdef, h, map_zero]))
  obtain ⟨a, haT, z, hz⟩ := hT₀ (Units.mk0 η hη0)
  have hzval : η = algebraMap k Kv (a : k) * (z : Kv) ^ ℓ := by
    have h := congrArg (Units.val) hz
    simpa using h
  -- the radical of the quotient by the representative
  have hA0 : algebraMap k Ω (a : k) ≠ 0 := by
    simp
  have hbpow : (β / α a) ^ ℓ = x / algebraMap k Ω (a : k) := by
    rw [div_pow, hβ, hα a]
  have hbM : β / α a ∈ M := div_mem hβM (hαM a haT)
  set bM : ↥M := ⟨β / α a, hbM⟩ with hbMdef
  have htower : ∀ y : k, algebraMap Kv Mw (algebraMap k Kv y)
      = toAdicCompletion w (algebraMap k ↥M y) := by
    intro y
    rw [← IsScalarTower.algebraMap_apply k Kv Mw, IsScalarTower.algebraMap_apply k ↥M Mw]
    rfl
  have hMeq : bM ^ ℓ * algebraMap k ↥M (a : k) = (⟨x, hxM⟩ : ↥M) := by
    refine (algebraMap ↥M Ω).injective ?_
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply k ↥M Ω]
    show (β / α a) ^ ℓ * algebraMap k Ω (a : k) = x
    rw [hbpow, div_mul_cancel₀ _ hA0]
  have hkey : (toAdicCompletion w bM) ^ ℓ * algebraMap Kv Mw (algebraMap k Kv (a : k))
      = algebraMap Kv Mw η := by
    rw [htower, ← map_pow, ← map_mul, hMeq, hηdef]
    exact (algebraMap_decompositionFieldHom k w xD).symm
  have hkey2 : (algebraMap Kv Mw (z : Kv)) ^ ℓ * algebraMap Kv Mw (algebraMap k Kv (a : k))
      = algebraMap Kv Mw η := by
    rw [← map_pow, ← map_mul, hzval, mul_comm]
  have hAv0 : algebraMap Kv Mw (algebraMap k Kv (a : k)) ≠ 0 := by
    refine fun h => hA0 ?_
    rw [htower] at h
    have h2 : algebraMap k ↥M (a : k) = 0 :=
      (toAdicCompletion w (K := ↥M)).injective (by rw [h, map_zero])
    rw [IsScalarTower.algebraMap_apply k ↥M Ω, h2, map_zero]
  have hd : ∃ c : Kv, algebraMap Kv Mw c ^ ℓ = (toAdicCompletion w bM) ^ ℓ :=
    ⟨(z : Kv), mul_right_cancel₀ hAv0 (hkey2.trans hkey.symm)⟩
  obtain ⟨ζM, hζMval⟩ : ∃ y : ↥M, (y : Ω) = ζ := ⟨⟨ζ, hζMmem⟩, rfl⟩
  have hζMalg : algebraMap ↥M Ω ζM = ζ := hζMval
  have hζMprim : IsPrimitiveRoot ζM ℓ := by
    refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥M Ω) ?_
      (algebraMap ↥M Ω).injective
    rw [hζMalg]
    exact hζ
  obtain ⟨j, hfix⟩ := exists_pow_smul_eq_of_pow_eq_pow w hζMprim hℓ hd
  have hcval : ((bM * ζM ^ j : ↥M) : Ω) = (β / α a) * ζ ^ j := by
    have h1 : ((bM * ζM ^ j : ↥M) : Ω) = (bM : Ω) * ((ζM : Ω)) ^ j := by push_cast; ring
    rw [h1, hζMval, hbMdef]
  have hcpow : ((β / α a) * ζ ^ j) ^ ℓ = x / algebraMap k Ω (a : k) := by
    rw [mul_pow, ← pow_mul, mul_comm j ℓ, pow_mul, hζ.pow_eq_one, one_pow, mul_one, hbpow]
  refine ⟨algebraMap k Ω (a : k), ⟨a, haT, rfl⟩, (β / α a) * ζ ^ j, ?_, ?_⟩
  · intro σ
    have h2 : ((stabilizerRestrictPrime M hw σ : Gal(↥M/k)) (bM * ζM ^ j) : Ω)
        = (σ : Gal(Ω/k)) ((β / α a) * ζ ^ j) := by
      rw [coe_stabilizerRestrictPrime, ← hcval]
      exact AlgEquiv.restrictNormal_commutes (σ : Gal(Ω/k)) ↥M (bM * ζM ^ j)
    rw [← h2, hfix (stabilizerRestrictPrime M hw σ)]
    exact hcval
  · rw [hcpow, mul_comm, div_mul_cancel₀ _ hA0]

/-- **An element fixed by the stabilizer of a prime is a unit of the base field times a power of a
fixed element.**  This is the finiteness statement with the representative named directly as a unit
of the base field, which is the form in which the power class of a fixed element is compared with
the power classes coming from below. -/
theorem exists_units_mul_pow_eq_of_forall_stabilizer_smul_eq {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥) {x : Ω} (hx0 : x ≠ 0)
    (hx : ∀ σ : ↥(stabilizer Gal(Ω/k) P), (σ : Gal(Ω/k)) x = x) :
    ∃ (b : kˣ) (c : Ω), (∀ σ : ↥(stabilizer Gal(Ω/k) P), (σ : Gal(Ω/k)) c = c) ∧
      x = algebraMap k Ω (b : k) * c ^ ℓ := by
  obtain ⟨T, -, hTrep, hT⟩ := exists_finite_pow_representatives_stabilizer (k := k) hℓ hP
  obtain ⟨a, haT, c, hcfix, hac⟩ := hT x hx0 hx
  obtain ⟨b, hb⟩ := hTrep a haT
  exact ⟨b, c, hcfix, by rw [← hb]; exact hac⟩

end Representatives

end InverseGalois.CFT
