/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.SUnitExt
import InverseGalois.CFT.PoitouTate.RadicalPlace

/-!
# The place prescribed by a character of the `S`-units

The group of `S`-units of a number field, for a set `X` of finite places carried into itself by
the automorphisms over a subfield, supplies every ingredient the radical construction of a
prescribed place asks for.  It is saturated, because the order of an element at a prime outside `X`
is killed by the exponent; its quotient by the powers of exponent a prime is finite of known order,
so it has a basis modulo those powers; and it is carried into itself by every embedding of an
ambient algebraically closed field, because such an embedding restricts to an automorphism of the
number field, which permutes the primes of `X`.  Radicals of the basis are available in the ambient
field for the same reason it is algebraically closed.

Hence a character of a subgroup of the `S`-units, trivial on the powers of exponent a prime that
the subgroup contains, is read off by the Frobenius automorphism at a finite place, and that place
can be taken outside any prescribed finite set and completely split in the number field.

## Main results

* `InverseGalois.CFT.isEmbeddingStable_sUnits`: **the `S`-units of an intermediate field are
  carried into themselves by every embedding of the ambient field** when the set of primes is
  stable.
* `InverseGalois.CFT.exists_place_frobValue_eq_one_iff_character_sUnits`: **outside any prescribed
  finite set of places of the bottom field there is a completely split place at which the value at
  the Frobenius automorphism is trivial exactly at the `S`-units the character kills.**

## Tags

S-unit, Kummer theory, Frobenius, decomposition group, Chebotarev, completely split
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### Stability of the `S`-units under the embeddings of the ambient field -/

section Stable

variable {k A : Type*} [Field k] [Field A] [Algebra k A] {Ω : IntermediateField k A}
  [NumberField ↥Ω] [Normal k ↥Ω] {Y : Type*} [MulAction Gal(↥Ω/k) Y]
  {ι : Y → HeightOneSpectrum (𝓞 ↥Ω)}

/-- **The `S`-units of an intermediate field are carried into themselves by every embedding of the
ambient field**, when the primes are listed equivariantly.  An embedding of the ambient field
restricts to an automorphism of the intermediate field, which is normal over the base, and the
`S`-units are stable under that automorphism. -/
theorem isEmbeddingStable_sUnits (hι : ∀ (σ : Gal(↥Ω/k)) (y : Y), ι (σ • y) = σ • ι y) :
    IsEmbeddingStable Ω (sUnits ↥Ω (Set.range ι)) := by
  intro τ b hb
  refine ⟨galUnits (τ.restrictNormal' ↥Ω) b, galUnits_mem_sUnits hι _ hb, ?_⟩
  rw [coe_galUnits_apply]
  exact (τ.restrictNormal_commutes ↥Ω (b : ↥Ω)).symm

end Stable

/-! ### The place prescribed by a character of the `S`-units -/

section Assemble

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A]
  {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] {p : ℕ} [NeZero p]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **Outside any prescribed finite set of finite places of the bottom field there is a place,
completely split in the number field the `S`-units are taken from, at which the value at the
Frobenius automorphism is trivial exactly at the `S`-units the character kills.**  The `S`-units
have a basis modulo the powers of exponent the prime, their radicals live in the ambient
algebraically closed field, and the whole group is saturated and stable under the embeddings of
that field, so the construction of a place prescribed by a character applies to it. -/
theorem exists_place_frobValue_eq_one_iff_character_sUnits (hp : p.Prime)
    {X : Set (HeightOneSpectrum (𝓞 ↥Ω))} (hXfin : X.Finite)
    (hXstab : ∀ (σ : Gal(↥Ω/k)) {v : HeightOneSpectrum (𝓞 ↥Ω)}, v ∈ X → σ • v ∈ X)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {U : Subgroup (↥Ω)ˣ} (hU : U ≤ sUnits ↥Ω X) (Φ : ↥U →* (↥Ω)ˣ)
    (hΦ : ∀ (u : (↥Ω)ˣ) (hu : u ∈ U) (y : (↥Ω)ˣ), u = y ^ p → Φ ⟨u, hu⟩ = 1)
    (T : Finset (HeightOneSpectrum (𝓞 k))) :
    ∃ V : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 k) V ∉ T ∧
      stabilizer Gal(↥Ω/k) V = ⊥ ∧ ¬ Pc (primeUnder (𝓞 K) V) ∣ p ∧
      ∀ (u : Kˣ) (hu : Units.map (algebraMap K ↥Ω : K →* ↥Ω) u ∈ U),
        (p : ℤ) ∣ placeValue (primeUnder (𝓞 K) V) u →
          (placeFrobValue hres hζ (primeUnder (𝓞 K) V) u = 1 ↔ Φ ⟨_, hu⟩ = 1) := by
  haveI : Fintype ↥X := hXfin.fintype
  -- the stable set of primes, listed equivariantly by itself
  letI : MulAction Gal(↥Ω/k) ↥X :=
    { smul := fun σ v => ⟨σ • (v : HeightOneSpectrum (𝓞 ↥Ω)), hXstab σ v.2⟩
      one_smul := fun v => Subtype.ext (one_smul _ _)
      mul_smul := fun σ τ v => Subtype.ext (mul_smul _ _ _) }
  have hrange : Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥Ω)) = X := Subtype.range_coe
  have hstab := isEmbeddingStable_sUnits (Ω := Ω)
    (ι := (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥Ω))) fun _ _ => rfl
  rw [hrange] at hstab
  -- the roots of unity, the basis of the `S`-units modulo powers, and the radicals
  have hζΩ : IsPrimitiveRoot (algebraMap K ↥Ω ζ) p :=
    hζ.map_of_injective (algebraMap K ↥Ω).injective
  haveI : HasEnoughRootsOfUnity (↥Ω) p := ⟨⟨_, hζΩ⟩, rootsOfUnity.isCyclic (↥Ω) p⟩
  have hcard := card_powQuotient_sUnits (K := ↥Ω) (p := p)
    (ι := (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥Ω))) Subtype.val_injective
  rw [hrange] at hcard
  have hfin : Finite (powQuotient (sUnits (↥Ω) X) p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨P⟩ := nonempty_powBasis_sUnits (K := ↥Ω) (p := p)
    (ι := (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥Ω))) hp Subtype.val_injective
  rw [hrange] at P
  choose w hw using fun i => IsAlgClosed.exists_pow_nat_eq (algebraMap ↥Ω A (P.rad i)) hp.pos
  exact exists_place_placeFrobValue_eq_one_iff_character hp P hstab
    (fun _ hy => mem_sUnits_of_pow_mem hp.ne_zero hy) hfin hζ w hw hres hU Φ hΦ T

end Assemble

end InverseGalois.CFT
