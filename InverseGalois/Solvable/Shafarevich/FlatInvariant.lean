/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.FlatTensor
import InverseGalois.Solvable.Shafarevich.FlatTensorVal

/-!
# The flat demand, written as an invariant tensor of units

The demand the flat step makes of the arithmetic still carries the chosen root of unity about: the
equivariance asked of the tensor is written against an exponent by which an automorphism raises
that root, and the values prescribed at the named places are asked to be compatible with the same
exponent.  Neither the root nor the exponent belongs in an arithmetic statement; both are
bookkeeping for one character of the automorphisms of the level.

That character is the cyclotomic one: an automorphism raises the root of unity to a power, the power
is well defined modulo the exponent because the root has exactly that order, and the assignment is
multiplicative.  Twisting the action on the target by the character inverse to it turns the
equivariance into the plain invariance of the tensor for the diagonal action, and turns the
compatibility asked of the prescribed values into the plain invariance of each value under the
automorphisms fixing its place.

What is left is a statement about a number field and nothing else: **a family of units of the level
whose tensor against a named basis is invariant, whose orders at finitely many named places are
prescribed, which is a local power on a prescribed finite set, and whose remaining ramification is
confined.**  That is the object the descent through the units for a finite set of places produces,
and it is what the rest of the climb has to build.

What is asked to be invariant is the tensor, not any one of the units it is assembled from.  A
single unit is invariant only up to an exponent-th power, and that is a far heavier demand: a
tensor of rank one is fixed only when both of its factors are, while a tensor of higher rank has
room to be fixed with no factor of it fixed at all.

## Main definitions

* `InverseGalois.Shafarevich.rootChar` — **the character by which the automorphisms of the level
  raise the chosen root of unity.**
* `InverseGalois.Shafarevich.HasInvariantUnitTensor` — **a family of units of a level can be found
  whose tensor against a named basis of a target killed by the exponent is invariant for the
  automorphisms of the level, of prescribed order at each of finitely many named places lying in
  distinct orbits, a local power at a prescribed finite set of places those avoid, and confined
  elsewhere.**

## Main results

* `InverseGalois.Shafarevich.rootChar_spec` — the root of unity raised to the residue the character
  names is its image.
* `InverseGalois.Shafarevich.rootChar_eq_of_pow` — any exponent by which an automorphism raises the
  root of unity is the residue the character names.
* `InverseGalois.Shafarevich.hasFlatPrescribedTensor_of_hasInvariantUnitTensor` — **an invariant
  tensor of units buys the prescribed tensor**, the twist by the character inverse to the cyclotomic
  one turning invariance into the equivariance the assembly asks for.

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, cyclotomic character, invariant tensor
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField TensorProduct

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

/-! ### The character of the root of unity -/

section Char

variable {ℓ : ℕ} [NeZero ℓ] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
  {K : IntermediateField k Ω} {ζ : ↥K}

/-- **The character by which the automorphisms of the level raise the chosen root of unity.**  The
power is well defined modulo the exponent because the root has exactly that order, and the
assignment is multiplicative because a power of a power is the power of the product. -/
noncomputable def rootChar (hζ : IsPrimitiveRoot ζ ℓ) : Gal(↥K/k) →* (ZMod ℓ)ˣ :=
  hζ.autToPow k

/-- The root of unity raised to the residue the character names is its image. -/
theorem rootChar_spec (hζ : IsPrimitiveRoot ζ ℓ) (σ : Gal(↥K/k)) :
    ζ ^ (((rootChar hζ σ : (ZMod ℓ)ˣ) : ZMod ℓ)).val = σ ζ :=
  hζ.autToPow_spec k σ

/-- The inverse character takes the inverse value. -/
theorem rootChar_inv_apply (hζ : IsPrimitiveRoot ζ ℓ) (σ : Gal(↥K/k)) :
    ((rootChar hζ)⁻¹ : Gal(↥K/k) →* (ZMod ℓ)ˣ) σ = (rootChar hζ σ)⁻¹ := rfl

/-- **Any exponent by which an automorphism raises the root of unity is the residue the character
names.** -/
theorem rootChar_eq_of_pow (hζ : IsPrimitiveRoot ζ ℓ) {σ : Gal(↥K/k)} {e : ℕ}
    (he : σ ζ = ζ ^ e) : ((rootChar hζ σ : (ZMod ℓ)ˣ) : ZMod ℓ) = (e : ZMod ℓ) := by
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨ℓ, Nat.pos_of_ne_zero (NeZero.ne ℓ), hζ.pow_eq_one⟩
  have h1 : ζ ^ (((rootChar hζ σ : (ZMod ℓ)ˣ) : ZMod ℓ)).val = ζ ^ e :=
    (rootChar_spec hζ σ).trans he
  have h2 := hfin.pow_eq_pow_iff_modEq.1 h1
  rw [← hζ.eq_orderOf] at h2
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
  rwa [ZMod.natCast_zmod_val] at h3

/-- The value of the inverse character against any exponent by which the automorphism raises the
root of unity is one. -/
theorem rootChar_inv_mul_cast (hζ : IsPrimitiveRoot ζ ℓ) {σ : Gal(↥K/k)} {e : ℕ}
    (he : σ ζ = ζ ^ e) :
    ((((rootChar hζ)⁻¹ σ : (ZMod ℓ)ˣ) : ZMod ℓ)) * (e : ZMod ℓ) = 1 := by
  rw [rootChar_inv_apply, ← rootChar_eq_of_pow hζ he, ← Units.val_mul, inv_mul_cancel,
    Units.val_one]

end Char

/-! ### The arithmetic input, with no root of unity in it -/

section Arith

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **A family of units of a level can be found whose tensor against a named basis of a target
killed by the exponent is invariant for the automorphisms of the level, of prescribed order at each
of finitely many named places lying in distinct orbits, a local power at a prescribed finite set of
places those avoid, and confined elsewhere to places sitting over the named ones or completely
decomposed in a given finite level.**

The target is an arbitrary group killed by the exponent, carrying an action of the automorphisms of
the level and a basis — a family whose powers give every element and only trivially give the
identity.  The family of units is indexed by that basis, and the tensor it names is the sum of the
pure tensors of each unit against its basis vector.

Nothing in the statement mentions a root of unity.  The invariance asked for is the invariance of
the plain diagonal action, and the prescribed values are asked only to be fixed by the automorphisms
fixing their places.  The twist by the cyclotomic character, which the assembly of the embedding
problem needs, is put back afterwards by changing the action on the target rather than the tensor.

The remaining clauses are the local shape of the prescription: the units are local powers at a
prescribed finite set of places the named places avoid, and elsewhere they are confined, a place
where some unit has order prime to the exponent sitting over a named place or having the primes
above it completely decomposed in a finite level named in advance. -/
def HasInvariantUnitTensor (ℓ : ℕ) [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ (M : Type) [CommGroup M] [MulDistribMulAction Gal(↥K/k) M], (∀ m : M, m ^ ℓ = 1) →
      ∀ (T : Type) [Fintype T] (b : T → M),
        (∀ m : M, ∃ d : T → ZMod ℓ, ∏ q, b q ^ (d q).val = m) →
        (∀ d : T → ZMod ℓ, ∏ q, b q ^ (d q).val = 1 → d = 0) →
        ∀ (ι : Type) [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)) (V : ι → M),
          (∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν) →
          (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ = w μ → σ • V μ = V μ) →
          ∀ Tz : Finset (HeightOneSpectrum (𝓞 ↥K)), (∀ μ : ι, w μ ∉ Tz) →
            (∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal) →
            ∃ z : T → (↥K)ˣ,
              (∀ σ : Gal(↥K/k),
                σ • (∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (b q))
                  = ∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (b q)) ∧
              (∀ μ : ι, ∏ q, b q ^ ((placeValue (w μ) (z q) : ZMod ℓ)).val = V μ) ∧
              (∀ (q : T) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz →
                localClassHom v ℓ (z q) = 1) ∧
              ∀ v : HeightOneSpectrum (𝓞 ↥K), (∃ q : T, ¬ (ℓ : ℤ) ∣ placeValue v (z q)) →
                (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
                  ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
                    Ideal.under (𝓞 ↥K) P = v.asIdeal →
                    stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup

end Arith

/-! ### The twist that restores the root of unity -/

section Bridge

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **An invariant tensor of units buys the prescribed tensor.**

The action asked of the target by the prescription is twisted by the character inverse to the
cyclotomic one before it is handed to the arithmetic.  Three things then fall out at once.

The compatibility the prescribed values are asked for — an automorphism fixing a named place carries
the value there to its power by the exponent it raises the roots of unity by — becomes, for the
twisted action, the plain statement that the value is fixed, the two exponents cancelling because
the character is inverted.

The equivariance asked of the tensor — the twist of the tensor by the inverse automorphism and that
exponent is the tensor carried by the map on the coefficient — becomes the plain invariance of the
tensor for the diagonal action, for the same reason.

The local clauses mention neither the action nor the root of unity, and are carried across
unchanged. -/
theorem hasFlatPrescribedTensor_of_hasInvariantUnitTensor {ℓ : ℕ} [NeZero ℓ]
    {K : IntermediateField k Ω} [NumberField ↥K] {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hrad : HasInvariantUnitTensor ℓ K) : HasFlatPrescribedTensor ℓ K ζ := by
  intro E hEfin hEgal hKE M _ hexp T _ b hspan hindep act hone hmul ι _ w V hdist hVcompat Tz
    hwTz hwℓ
  letI : MulDistribMulAction Gal(↥K/k) M :=
    charTwistAction hexp act hone hmul (rootChar hζ)⁻¹
  have hstab : ∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ = w μ → σ • V μ = V μ := by
    intro μ σ hσ
    have hV : V μ ^ (((rootChar hζ σ : (ZMod ℓ)ˣ) : ZMod ℓ)).val = act σ (V μ) :=
      hVcompat μ σ _ (rootChar_spec hζ σ).symm hσ
    have hsm : (σ • V μ : M)
        = act σ (V μ) ^ ((((rootChar hζ)⁻¹ σ : (ZMod ℓ)ˣ) : ZMod ℓ)).val := rfl
    rw [hsm, ← hV, ← pow_mul]
    refine (pow_eq_pow_of_pow_eq_one (hexp (V μ)) (j := 1) ?_).trans (pow_one _)
    rw [Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      rootChar_inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨z, hzinv, hzval, hzTz, hzconf⟩ :=
    hrad E hEfin hEgal hKE M hexp T b hspan hindep ι w V hdist hstab Tz hwTz hwℓ
  refine ⟨z, fun σ e he => ?_, hzval, hzTz, hzconf⟩
  refine twistTensor_eq_coeffTensor_of_smul_eq (f := act σ) (fun m => ?_) (hzinv σ)
  exact charTwistAction_pow hexp act hone hmul ((rootChar hζ)⁻¹)
    (rootChar_inv_mul_cast hζ he) m

end Bridge

end InverseGalois.Shafarevich
