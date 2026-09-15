/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PrescribedValue
import InverseGalois.CFT.Kummer.CharLocalClass
import InverseGalois.Solvable.Shafarevich.FlatPlaces
import InverseGalois.Solvable.Shafarevich.KummerTensor
import InverseGalois.Solvable.Shafarevich.LayerMatrix

/-!
# The flat prescription bought from a single invariant tensor

The prescription made one named prime at a time asks only for equivariance under the decomposition
subgroup of that prime, and pays for it by asking each unit to be a local power at every conjugate
of every other named place, so that the several prescriptions do not disturb one another.  That is
a demand made place by place, and the reciprocity law has a say in it once the places are many.

Here the whole family is bought at once.  A single tensor of the units of the level with the target
is asked for, invariant for the automorphisms of the level acting on the radicand and on the
coefficient at the same time — the coefficient being moved by the exponent to which the automorphism
raises the roots of unity.  The homomorphism such a tensor assembles is equivariant for the *whole*
base group, not merely for one decomposition subgroup, so nothing has to be arranged between the
named places and no local power is asked for at their conjugates.  What is asked at a named place
is only the order of the tensor there, read as the value the prescription forces.

Reading the demand on the tensor rather than on a family removes the indexing: the invariance is one
equation between two maps of one tensor, and the prescription at a named place is one equation
between two elements of the target.  The homomorphism the tensor carries is the homomorphism
assembled out of any family presenting it, so everything the assembled homomorphism is known to
satisfy — triviality where the units are local powers, confinement where their orders are prime to
the exponent — is read off the family as before.

## Main definitions

* `InverseGalois.Shafarevich.IsBaseOrderPlace` — a place of a level whose order is already taken,
  prime to the exponent, by an element the whole group of automorphisms fixes.
* `InverseGalois.Shafarevich.HasFlatPrescribedTensor` — **a tensor of the units of a level with a
  target killed by the exponent and carrying a basis can be found, invariant for the automorphisms
  of the level acting diagonally, of prescribed order at each of finitely many reachable named
  places lying in distinct orbits, a local power at a prescribed finite set of places the orbits of
  those avoid, and confined elsewhere to places sitting over the named ones or completely decomposed
  in a given finite level.**

## Main results

* `InverseGalois.Shafarevich.smul_kummerRootUnit_eq_pow_iff` — an automorphism raises the chosen
  root of unity to a power exactly when its restriction to the level raises the root of unity of
  the level to that power.
* `InverseGalois.Shafarevich.isBaseOrderPlace_of_inertia_le_fixingSubgroup` — **a place of a level
  below a prime whose inertia fixes the level has its order taken by an element the whole group of
  automorphisms fixes**, a uniformiser of the place below.
* `InverseGalois.Shafarevich.not_dvd_ramIdx_of_isBaseOrderPlace` — **such a place has ramification
  index over the base field prime to the exponent.**
* `InverseGalois.Shafarevich.isCyclic_of_isPGroup_of_isBaseOrderPlace` — **a subgroup of order a
  power of the exponent fixing such a place is cyclic.**
* `InverseGalois.Shafarevich.hasFlatKernelPrescription_of_tensorPlaces` — **a level carrying such a
  tensor carries the flat prescription made one field up.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, tensor product, decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField TensorProduct

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

/-! ### The root of unity of the level -/

section Root

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}
  [Normal k ↥K] {ℓ : ℕ} [NeZero ℓ]

/-- **An automorphism raises the chosen root of unity to a power exactly when its restriction to
the level raises the root of unity of the level to that power.**  The chosen root of unity is the
root of unity of the level read in the units of the closure, and restriction commutes with that
reading. -/
theorem smul_kummerRootUnit_eq_pow_iff {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (g : Gal(Ω/k))
    (e : ℕ) :
    g • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ e ↔
      AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g ζ = ζ ^ e := by
  have hinj : Function.Injective (Units.map (algebraMap ↥K Ω : ↥K →* Ω)) :=
    Units.map_injective (algebraMap ↥K Ω).injective
  have hL : (g • kummerRootUnit Ω hζ : Ωˣ)
      = Units.map (algebraMap ↥K Ω : ↥K →* Ω)
          (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g • primitiveRootUnit hζ) :=
    smul_units_algebraMap_intermediateField g (primitiveRootUnit hζ)
  have hR : (kummerRootUnit Ω hζ ^ e : Ωˣ)
      = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (primitiveRootUnit hζ ^ e) :=
    (_root_.map_pow (Units.map (algebraMap ↥K Ω : ↥K →* Ω)) _ _).symm
  have hcoe : ((primitiveRootUnit hζ : (↥K)ˣ) : ↥K) = ζ := IsUnit.unit_spec _
  rw [hL, hR]
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · have h3 := congrArg (fun u : (↥K)ˣ => (u : ↥K)) (hinj hh)
    simp only [Units.val_pow_eq_pow_val, hcoe] at h3
    exact h3
  · refine congrArg _ (Units.ext ?_)
    rw [Units.val_pow_eq_pow_val, hcoe]
    exact hh

end Root

/-! ### The arithmetic input -/

section Arith

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **A place of a level whose order is already taken, prime to the exponent, by an element the
whole group of automorphisms fixes.**

Such an element is an element of the base field, and its order at the place is the ramification
index there, so the condition says exactly that the place is unramified over the base field, or at
worst ramified to a degree prime to the exponent.  It is what makes a demand of invariant units at
the place meetable at all: the elements the automorphisms fixing the place fix are the elements of
the field those automorphisms fix, and their orders at the place run over the multiples of the
ramification index of the place there. -/
def IsBaseOrderPlace (ℓ : ℕ) (K : IntermediateField k Ω) [NumberField ↥K]
    (v : HeightOneSpectrum (𝓞 ↥K)) : Prop :=
  ∃ x : (↥K)ˣ, (∀ σ : Gal(↥K/k), σ • x = x) ∧ ¬ (ℓ : ℤ) ∣ placeValue v x

/-- **Being taken by an element the whole group fixes travels along the orbit of a place.**  Such an
element has the same order at a translate of the place as it has there, because the automorphism
carrying one to the other leaves it alone. -/
theorem IsBaseOrderPlace.smul {ℓ : ℕ} {K : IntermediateField k Ω} [NumberField ↥K]
    [IsGalois k ↥K] {v : HeightOneSpectrum (𝓞 ↥K)} (h : IsBaseOrderPlace ℓ K v)
    (σ : Gal(↥K/k)) : IsBaseOrderPlace ℓ K (σ • v) := by
  obtain ⟨x, hx, hord⟩ := h
  refine ⟨x, hx, fun hc => hord ?_⟩
  have hval : placeValue (σ • v) x = placeValue v x := by
    rw [← placeValue_galSmul v σ x, galUnits_eq_smul, hx σ]
  rwa [hval] at hc

/-- **A place of a level unramified over the base field has its order taken by an element the whole
group of automorphisms fixes.**  A uniformiser of the place below is such an element: the
automorphisms of the level fix the base field pointwise, and the order of an element of the base
field at a place of the level is its order below multiplied by the ramification index, which is one.
-/
theorem isBaseOrderPlace_of_inertia_eq_bot [NumberField k] {ℓ : ℕ} (hℓ : 1 < ℓ)
    {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K]
    {v : HeightOneSpectrum (𝓞 ↥K)} (hv : Ideal.inertia Gal(↥K/k) v.asIdeal = ⊥) :
    IsBaseOrderPlace ℓ K v := by
  have he : ramIdx (𝓞 k) v = 1 := (inertia_eq_bot_iff_ramIdx_eq_one v).1 hv
  obtain ⟨π, hπ⟩ := (primeUnder (𝓞 k) v).valuation_exists_uniformizer k
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact (WithZero.exp_pos (a := (-1 : ℤ))).ne hπ
  have hx0 : algebraMap k ↥K π ≠ 0 := by
    simpa using (algebraMap k ↥K).injective.ne hπ0
  refine ⟨Units.mk0 (algebraMap k ↥K π) hx0, fun σ => Units.ext ?_, ?_⟩
  · show σ (algebraMap k ↥K π) = algebraMap k ↥K π
    exact σ.commutes π
  · have hval : v.valuation ↥K (algebraMap k ↥K π) = WithZero.exp (-1 : ℤ) := by
      rw [valuation_algebraMap (A := 𝓞 k) v π, he, pow_one, hπ]
    rw [Rigidity.RET.valuation_eq_exp_neg_ord ↥K v hx0] at hval
    have hord : Rigidity.RET.ord ↥K v (algebraMap k ↥K π) = 1 := by
      have hlog := congrArg WithZero.log hval
      simpa using hlog
    have hpv : placeValue v (Units.mk0 (algebraMap k ↥K π) hx0) = -1 := by
      rw [placeValue_eq_neg_ord]
      show -Rigidity.RET.ord ↥K v (algebraMap k ↥K π) = -1
      rw [hord]
    rw [hpv]
    intro hc
    have h2 : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd one_pos (dvd_neg.1 hc)
    omega

/-- **A place of a level below a prime whose inertia fixes the level is unramified over the base
field**, so its order is taken by an element the whole group of automorphisms fixes.  Restriction
carries inertia at the prime onto inertia at the place below, and an inertia subgroup fixing the
level restricts to nothing. -/
theorem isBaseOrderPlace_of_inertia_le_fixingSubgroup [NumberField k] [IsGalois k Ω] {ℓ : ℕ}
    (hℓ : 1 < ℓ) {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K] {P : Ideal (𝓞 Ω)}
    [P.IsPrime] (hP : P ≠ ⊥) (h : Ideal.inertia Gal(Ω/k) P ≤ K.fixingSubgroup) :
    IsBaseOrderPlace ℓ K (placeUnder K P hP) := by
  refine isBaseOrderPlace_of_inertia_eq_bot hℓ ?_
  rw [← map_inertia_restrictNormalHom (k := k) (K := Ω) K (P := P) (v := placeUnder K P hP) rfl,
    Subgroup.map_eq_bot_iff, IntermediateField.restrictNormalHom_ker]
  exact h

/-- **The ramification index of a place whose order is taken by an element the whole group of
automorphisms fixes is prime to the exponent.**  Such an element lies in the base field, and its
order at the place is its order below multiplied by the ramification index, so the exponent dividing
the index would make it divide the order. -/
theorem not_dvd_ramIdx_of_isBaseOrderPlace [NumberField k] {ℓ : ℕ}
    {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K]
    {v : HeightOneSpectrum (𝓞 ↥K)} (h : IsBaseOrderPlace ℓ K v) :
    ¬ ℓ ∣ ramIdx (𝓞 k) v := by
  obtain ⟨x, hx, hord⟩ := h
  have hfix : ∀ σ : Gal(↥K/k), σ (x : ↥K) = (x : ↥K) := fun σ => congrArg Units.val (hx σ)
  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := k) (x : ↥K)).mpr hfix
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hq
    exact x.ne_zero hq.symm
  intro hdvd
  refine hord ?_
  have hpv : placeValue v x
      = -(ramIdx (𝓞 k) v * Rigidity.RET.ord k (primeUnder (𝓞 k) v) q) := by
    rw [placeValue_eq_neg_ord]
    show -Rigidity.RET.ord ↥K v (x : ↥K) = _
    rw [← hq, ord_algebraMap_eq_ramIdx_mul k v hq0]
  rw [hpv]
  exact Dvd.dvd.neg_right (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 hdvd) _)

/-- **A subgroup of order a power of the exponent fixing a place whose order is taken by an element
the whole group of automorphisms fixes is cyclic.**  The ramification index there is prime to the
exponent, so the subgroup meets inertia trivially and embeds in the cyclic quotient of the
decomposition group by inertia. -/
theorem isCyclic_of_isPGroup_of_isBaseOrderPlace [NumberField k] {ℓ : ℕ} (hℓp : ℓ.Prime)
    {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K]
    {v : HeightOneSpectrum (𝓞 ↥K)} (h : IsBaseOrderPlace ℓ K v) {P : Subgroup Gal(↥K/k)}
    (hP : IsPGroup ℓ ↥P) (hPfix : ∀ σ ∈ P, σ • v = v) : IsCyclic ↥P := by
  refine isCyclic_of_isPGroup_le_stabilizer hℓp v.asIdeal v.ne_bot ?_ hP ?_
  · rw [card_inertia_eq_ramIdx]
    exact not_dvd_ramIdx_of_isBaseOrderPlace h
  · intro σ hσ
    rw [← stabilizer_eq_stabilizer_asIdeal]
    exact hPfix σ hσ

/-- **A tensor of the units of a level with a target killed by the exponent can be found, invariant
for the automorphisms of the level acting diagonally, of prescribed order at each of finitely many
named places lying in distinct orbits, a local power at a prescribed finite set of places the
orbits of those avoid, and confined elsewhere to places sitting over the named ones or completely
decomposed in a given finite level.**

The set the units are asked to be local powers at is stable under the automorphisms of the level,
and is avoided by the whole orbit of each named place and not merely by the named place itself.
The second is forced by the invariance: the order of an invariant tensor at a conjugate of a named
place is the conjugate of its order at that place, so asking the tensor to be a local power at a
conjugate of a named place would ask the value prescribed there to be trivial.  The first is what
lets the demand be met one orbit at a time, a unit carried by an automorphism staying a local power
at the set exactly when it was one there before.

The target is an arbitrary group killed by the exponent, together with a basis of it — a family
whose powers give every element and only trivially give the identity — and an action of the
automorphisms of the level on it.  The tensor is asked for as a family of units indexed by that
basis, which is the same thing as a tensor because the expression the homomorphism is assembled by
is bilinear and kills the exponent-th powers.

The invariance asked of it is the invariance of the diagonal action twisted on the coefficient: an
automorphism of the level carries the radicand, and raises the coefficient to the exponent by which
it raises the roots of unity.  Written on the tensor this is one equation between two maps, and it
is exactly what makes the assembled homomorphism equivariant for the whole base group.

What is asked at a named place is the order of the tensor there: the product of the powers of the
spanning family by the orders of the corresponding units is the prescribed value.  The prescribed
values are themselves asked to be compatible with the action, in the sense that an automorphism
fixing a named place carries the value there to its power by the exponent by which it raises the
roots of unity — which is exactly what the invariance forces, and what the prescription consumes.

The remaining clauses are the local shape of the prescription, as for one unit at a time: the units
are local powers at that prescribed set of places, which covers the places above the exponent and so
makes the assembled homomorphism unramified there; and elsewhere they are confined, a place where
some unit has order prime to the exponent sitting over a named place or having the primes above it
completely decomposed in a finite level named in advance.

Each named place is asked to be reachable in that finite level, which is the divisor class half of
the demand and the half the level has to be chosen for rather than the half the arithmetic
supplies.  It is also asked to have its order taken by an element the whole group fixes, which is
the statement that its ramification index over the base field is prime to the exponent.

The tensor is not asked for in the target itself but in every quotient of it killing a finite family
of elements named in advance, of a length the set of places a local power is asked at already
bounds.  That is the order the counting argument the ladder runs needs: the arithmetic cannot be
asked to produce a tensor in a target it has no control over, but it can be asked to name, before
any quotient is chosen, the finitely many elements whose death makes its answer good — and a
shrinking of the coefficients can be made to kill a family of a length fixed in advance while
staying onto.  The prescribed values and the spanning family are read in the quotient, which is what
makes the answer one about the quotient alone. -/
def HasFlatPrescribedTensor (ℓ : ℕ) [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K]
    (ζ : ↥K) : Prop :=
  ∀ Tz : Finset (HeightOneSpectrum (𝓞 ↥K)),
    (∀ (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → σ • v ∈ Tz) →
    ∃ D : ℕ, ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
      ∀ (M : Type) [CommGroup M], (∀ m : M, m ^ ℓ = 1) →
        ∀ (T : Type) [Fintype T] (b : T → M),
          (∀ m : M, ∃ d : T → ZMod ℓ, ∏ q, b q ^ (d q).val = m) →
          (∀ d : T → ZMod ℓ, ∏ q, b q ^ (d q).val = 1 → d = 0) →
          ∀ act : Gal(↥K/k) → M →* M, (∀ m : M, act 1 m = m) →
            (∀ (σ τ : Gal(↥K/k)) (m : M), act (σ * τ) m = act σ (act τ m)) →
            ∀ (ι : Type) [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)) (V : ι → M),
              (∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν) →
              (∀ (μ : ι) (σ : Gal(↥K/k)) (e : ℕ), σ ζ = ζ ^ e → σ • w μ = w μ →
                V μ ^ e = act σ (V μ)) →
              (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ∉ Tz) →
              (∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal) →
              (∀ μ : ι, IsReachablePlace ℓ K E (↑Tz) (w μ)) →
              (∀ μ : ι, IsBaseOrderPlace ℓ K (w μ)) →
              ∃ (J : Type) (_ : Finite J) (_ : Nat.card J ≤ D) (x : J → M),
                ∀ (M' : Type) [CommGroup M'] (Φ : M →* M'), Function.Surjective Φ →
                  ∀ act' : Gal(↥K/k) → M' →* M',
                    (∀ (σ : Gal(↥K/k)) (m : M), Φ (act σ m) = act' σ (Φ m)) →
                    (∀ i : J, Φ (x i) = 1) →
                    ∃ z : T → (↥K)ˣ,
                      (∀ (σ : Gal(↥K/k)) (e : ℕ), σ ζ = ζ ^ e →
                        twistTensor M' σ⁻¹ e
                            (∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (Φ (b q)))
                          = coeffTensor M' (act' σ)
                              (∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (Φ (b q)))) ∧
                      (∀ μ : ι,
                        ∏ q, Φ (b q) ^ ((placeValue (w μ) (z q) : ZMod ℓ)).val = Φ (V μ)) ∧
                      (∀ (q : T) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz →
                        localClassHom v ℓ (z q) = 1) ∧
                      ∀ v : HeightOneSpectrum (𝓞 ↥K), (∃ q : T, ¬ (ℓ : ℤ) ∣ placeValue v (z q)) →
                        (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
                          ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
                            Ideal.under (𝓞 ↥K) P = v.asIdeal →
                            stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup

end Arith

/-! ### The prescription -/

section Places

variable {ℓ : ℕ} [Fact ℓ.Prime] [NeZero ℓ] {U : Type} [Group U] [Finite U] {n : ℕ} {S : Type}
  [Group S] [Finite S] {j : ℕ} {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] {φ : Gal(Ω/k) →* U} {t : ℕ} {D : Fin t → Subgroup Gal(Ω/k)}

attribute [local instance] genericQuotAction zmodTrivialAction

/-- **A level carrying an invariant tensor prescribed at named places carries the flat prescription
made one field up.**

A basis of the layer is named and the tensor is read against it, so that the homomorphism the tensor
assembles is the homomorphism assembled out of the family of units it is presented by.  Its
equivariance is read off the invariance of the tensor: conjugating the argument by an automorphism
twists the tensor by the inverse of the automorphism it induces on the level, together with the
exponent by which it raises the roots of unity, and the invariance says exactly that this twist is
the tensor carried by the operator the base realization sends the conjugating element to.  That is
equivariance for the whole base group at once, which is what the prescription made one field up
asks for.

The values prescribed along the part of inertia at a named prime which the base realization kills
are read as before: the prescription there is the power of a single value of the layer by the Kummer
character of any unit whose order at the place below is prime to the exponent, and a unit of order
exactly one there is chosen for that purpose.  The order of the tensor at the named place is
prescribed to be the value those coordinates name, so the two homomorphisms agree on the whole of
that subgroup.

The compatibility the prescribed values are asked to satisfy is exactly what equivariance of the
prescription gives: an automorphism of the level fixing a named place may be lifted to one fixing
the named prime itself — two primes with the same place below differ by an automorphism fixing the
level, and such an automorphism is killed by the base realization — and conjugating by that lift
carries the prescribed value to its image under the operator, which the Kummer character reads as
the power by which the roots of unity are raised.

Triviality along the finite family and the confinement of the new ramification are read off the
family presenting the tensor, exactly as for one unit at a time; no clause is needed at the
conjugates of the named places, equivariance carrying the value there.

The set of places the units are asked to be local powers at is the orbit of the places below the
given finite family of decomposition subgroups, and it is named in advance of the level because the
level is chosen for it.

The rank the generic group is read at is not the one the prescription is asked at.  The arithmetic
names its finite family of coefficients against a rank chosen from the bound the arithmetic itself
announces once the places carrying the local conditions are known, the count then produces a
shrinking onto the intended rank killing that family, and the two homomorphisms are composed: the
level is reached at the larger rank and the answer is read at the smaller one.  That is what keeps
the argument from turning in a circle, the rank being fixed before the level rather than after
it. -/
theorem hasFlatKernelPrescription_of_tensorPlaces (hS : IsPGroup ℓ S)
    (K : IntermediateField k Ω)
    [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hkd : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
    {Pr : Fin t → Ideal (𝓞 Ω)} (hPrp : ∀ ν, (Pr ν).IsPrime) (hPrbot : ∀ ν, Pr ν ≠ ⊥)
    (hDPr : ∀ ν, D ν = stabilizer Gal(Ω/k) (Pr ν))
    (hℓPr : ∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : 𝓞 ↥K) ∈ v.asIdeal →
      ∃ (σ : Gal(↥K/k)) (ν : Fin t), v = σ • placeUnder K (Pr ν) (hPrbot ν))
    (Tz : Finset (HeightOneSpectrum (𝓞 ↥K)))
    (hTz : ∀ v : HeightOneSpectrum (𝓞 ↥K), v ∈ Tz ↔
      ∃ (σ : Gal(↥K/k)) (ν : Fin t), v = σ • placeUnder K (Pr ν) (hPrbot ν))
    (hlevel : ∀ m : ℕ, ∃ N : ℕ, HasReachableLevel ℓ U m S j φ N K (↑Tz))
    (hfam : HasFlatPrescribedTensor ℓ K ζ) :
    HasFlatKernelPrescription ℓ U n S j φ D := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  have hmemTz : ∀ (σ : Gal(↥K/k)) (ν : Fin t),
      σ • placeUnder K (Pr ν) (hPrbot ν) ∈ Tz := fun σ ν => (hTz _).2 ⟨σ, ν, rfl⟩
  have hstabTz : ∀ (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → σ • v ∈ Tz := by
    intro σ v hv
    obtain ⟨τ, ν, rfl⟩ := (hTz v).1 hv
    exact (hTz _).2 ⟨σ * τ, ν, (mul_smul σ τ _).symm⟩
  obtain ⟨Db, hfam'⟩ := hfam Tz hstabTz
  set r : ℕ := (j + 1) * (Db * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) + 1
    with hrdef
  obtain ⟨N, hlevelN⟩ := hlevel (r * n)
  refine ⟨N, ?_⟩
  intro F ι _ Q A a hFsurj hFsm hFright hQp hQbot hQℓ hQconj _ hAker hAeq hQunr hasm haequiv hesc
  haveI : ∀ μ, (Q μ).IsPrime := hQp
  haveI : ∀ ν, (Pr ν).IsPrime := hPrp
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨β₁, hβ₁, hβ₁surj, E, hEfin, hEgal, hKE, hEF, hreach⟩ := hlevelN F hFsurj hFsm hFright
  haveI := hEfin
  haveI := hEgal
  -- a lift of an automorphism of the level, and the operator it names
  choose lift hlift using restrictNormalHom_surjective_level K
  have hφeq : ∀ g g' : Gal(Ω/k),
      AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g
        = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g' → φ g = φ g' := by
    intro g g' hgg
    have hmem : g * g'⁻¹ ∈ φ.ker := by
      refine (restrictNormalHom_eq_one_iff_mem_ker hKker (g * g'⁻¹)).1 ?_
      rw [_root_.map_mul, _root_.map_inv, hgg, mul_inv_cancel]
    have h1 : φ (g * g'⁻¹) = 1 := MonoidHom.mem_ker.1 hmem
    rw [_root_.map_mul, _root_.map_inv, mul_inv_eq_one] at h1
    exact h1
  have hactφ : ∀ g : Gal(Ω/k),
      φ (lift (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g)) = φ g :=
    fun g => hφeq _ _ (hlift _)
  -- the named primes lie in distinct orbits, so their places below are moved off one another
  have hconjw : ∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k),
      σ • placeUnder K (Q μ) (hQbot μ) ≠ placeUnder K (Q ν) (hQbot ν) := by
    intro μ ν hμν σ heq
    obtain ⟨ρ₀, hρ₀⟩ := restrictNormalHom_surjective_level K σ
    have hbot : ρ₀ • Q μ ≠ ⊥ := by
      intro h0
      exact hQbot μ (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ₀⁻¹ • I) h0)
    have hpl : placeUnder K (ρ₀ • Q μ) hbot = placeUnder K (Q ν) (hQbot ν) := by
      refine HeightOneSpectrum.ext ?_
      rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot μ) ρ₀, hρ₀, heq]
    obtain ⟨τ, -, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot (hQbot ν) hpl
    exact hQconj μ ν hμν (τ * ρ₀) (by rw [mul_smul]; exact hτ)
  -- an automorphism of the level fixing the place below a named prime lifts to one fixing the prime
  have hstab : ∀ (μ : ι) (g : Gal(Ω/k)),
      AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g • placeUnder K (Q μ) (hQbot μ)
        = placeUnder K (Q μ) (hQbot μ) →
      ∃ g' : Gal(Ω/k), g' ∈ stabilizer Gal(Ω/k) (Q μ) ∧ φ g' = φ g ∧
        AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g'
          = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g := by
    intro μ g hg
    have hbot : g • Q μ ≠ ⊥ := by
      intro h0
      exact hQbot μ (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => g⁻¹ • I) h0)
    have hpl : placeUnder K (g • Q μ) hbot = placeUnder K (Q μ) (hQbot μ) := by
      refine HeightOneSpectrum.ext ?_
      rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot μ) g, hg, placeUnder_asIdeal]
    obtain ⟨ρ, hρmem, hρ⟩ :=
      exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot (hQbot μ) hpl
    have hρker : ρ ∈ φ.ker := by rw [← hKker]; exact hρmem
    refine ⟨ρ * g, mem_stabilizer_iff.2 ?_, ?_, ?_⟩
    · rw [mul_smul, ← hρ]
    · rw [_root_.map_mul, MonoidHom.mem_ker.1 hρker, one_mul]
    · rw [_root_.map_mul, (restrictNormalHom_eq_one_iff_mem_ker hKker ρ).2 hρker, one_mul]
  -- the named places avoid the places carrying the finite family
  have hdisj : ∀ (μ : ι) (τ : Gal(↥K/k)), τ • placeUnder K (Q μ) (hQbot μ) ∉ Tz := by
    intro μ τ₀ hmem
    obtain ⟨σ₀, ν, hσν⟩ := (hTz _).1 hmem
    have hσν₀ : σ₀ • placeUnder K (Pr ν) (hPrbot ν) = τ₀ • placeUnder K (Q μ) (hQbot μ) := hσν.symm
    set σ : Gal(↥K/k) := τ₀⁻¹ * σ₀ with hσdef
    have hσν' : σ • placeUnder K (Pr ν) (hPrbot ν) = placeUnder K (Q μ) (hQbot μ) := by
      rw [hσdef, mul_smul, hσν₀, inv_smul_smul]
    obtain ⟨ρ₀, hρ₀⟩ := restrictNormalHom_surjective_level K σ
    have hbot : ρ₀ • Pr ν ≠ ⊥ := by
      intro h0
      exact hPrbot ν (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ₀⁻¹ • I) h0)
    have hpl : placeUnder K (ρ₀ • Pr ν) hbot = placeUnder K (Q μ) (hQbot μ) := by
      refine HeightOneSpectrum.ext ?_
      rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hPrbot ν) ρ₀, hρ₀, hσν']
    obtain ⟨τ, -, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot (hQbot μ) hpl
    obtain ⟨y, hy, hyn⟩ := hesc μ ν (τ * ρ₀)⁻¹
    have hy' : y ∈ stabilizer Gal(Ω/k) ((τ * ρ₀) • Pr ν) := by
      rw [mul_smul, ← hτ]
      exact hy
    refine hyn ?_
    rw [hDPr ν, inv_inv]
    exact mem_stabilizer_smul_iff.1 hy'
  have hdisjℓ : ∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (placeUnder K (Q μ) (hQbot μ)).asIdeal := by
    intro μ hmem
    obtain ⟨σ, ν, hσν⟩ := hℓPr _ hmem
    exact hdisj μ 1 (by rw [one_smul]; exact hσν ▸ hmemTz σ ν)
  -- a reference unit of order one at each named place
  have hZex : ∀ μ : ι, ∃ Y : (↥K)ˣ, placeValue (placeUnder K (Q μ) (hQbot μ)) Y = 1 := by
    intro μ
    obtain ⟨θ, hθ⟩ :=
      exists_units_placeValue_eq {placeUnder K (Q μ) (hQbot μ)} (fun _ => (1 : ℤ))
    exact ⟨θ, hθ _ (Finset.mem_singleton_self _)⟩
  choose Z hZ using hZex
  -- the coordinates the prescription forces
  have hasm' : ∀ μ : ι, IsSmooth₁
      (((layerSubMap ℓ β₁ j).comp (a μ) : ↥(A μ) →* ↥(layerSub ℓ (Generic U (r * n) S) j)) :
        ↥(A μ) → ↥(layerSub ℓ (Generic U (r * n) S) j)) := by
    intro μ
    obtain ⟨N₀, hN₀, hcon⟩ := hasm μ
    exact ⟨N₀, hN₀, fun x y hy => congrArg (layerSubMap ℓ β₁ j) (hcon x y hy)⟩
  have hunit : ∀ μ : ι, ∃ x₁ : ↥(A μ), IsUnit (subKummerChar hKker hkd (hAker μ) (Z μ) x₁) := by
    intro μ
    have hord : ¬ (ℓ : ℤ) ∣ Rigidity.RET.ord ↥K (placeUnder K (Q μ) (hQbot μ)) ((Z μ : ↥K)) := by
      intro hd
      have h1 : placeValue (placeUnder K (Q μ) (hQbot μ)) (Z μ) = 1 := hZ μ
      rw [placeValue_eq_neg_ord] at h1
      have h2 : Rigidity.RET.ord ↥K (placeUnder K (Q μ) (hQbot μ)) ((Z μ : ↥K)) = -1 := by omega
      rw [h2] at hd
      have h3 : (ℓ : ℤ) ∣ 1 := dvd_neg.1 hd
      have h4 := Int.le_of_dvd Int.one_pos h3
      have h5 : 1 < ℓ := hℓ.one_lt
      omega
    exact exists_isUnit_kummerChar_of_not_dvd_ord hKker hkd hℓ (hAeq μ) (hAker μ) (Z μ)
      (v := placeUnder K (Q μ) (hQbot μ)) rfl hord
  have hcoord : ∀ μ : ι, ∃ c : Fin (layerDim ℓ (Generic U (r * n) S) j) → ZMod ℓ, ∀ x : ↥(A μ),
      ((layerSubMap ℓ β₁ j).comp (a μ)) x
        = (∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c q).val)
            ^ (subKummerChar hKker hkd (hAker μ) (Z μ) x).val := by
    intro μ
    obtain ⟨x₁, hx₁⟩ := hunit μ
    exact exists_forall_eq_pow_subKummerChar hKker hkd (hQbot μ) (hQℓ μ) (hAeq μ) (hAker μ)
      layerBasis_pow_eq_one (χ := fun q e => layerCoord ℓ (Generic U (r * n) S) j e q)
      prod_layerBasis_pow_layerCoord (fun q e e' => layerCoord_mul e e' q)
      ((layerSubMap ℓ β₁ j).comp (a μ)) (hasm' μ) (Z μ) hx₁
  choose c hc using hcoord
  have hVpow : ∀ μ : ι,
      (∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val) ^ ℓ = 1 :=
    fun _ => prod_pow_pow_eq_one layerBasis_pow_eq_one _
  have hx₀ : ∀ μ : ι, ∃ x₀ : ↥(A μ), subKummerChar hKker hkd (hAker μ) (Z μ) x₀ = 1 := by
    intro μ
    obtain ⟨x₁, hx₁⟩ := hunit μ
    exact exists_subKummerChar_eq_one hKker hkd (hAker μ) (Z μ) hx₁
  have hAI : ∀ ν : ι, A ν ≤ Ideal.inertia Gal(Ω/k) (Q ν) :=
    fun ν => (hAeq ν).le.trans inf_le_left
  have hAmem : ∀ (ν : ι) (y : Gal(Ω/k)),
      y ∈ Ideal.inertia Gal(Ω/k) (Q ν) → y ∈ φ.ker → y ∈ A ν := by
    intro ν y h1 h2
    rw [hAeq ν]
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  -- the reference unit keeps its order under an automorphism fixing the place
  have hplsmul : ∀ (μ : ι) (σ : Gal(↥K/k)),
      σ • placeUnder K (Q μ) (hQbot μ) = placeUnder K (Q μ) (hQbot μ) →
      placeValue (placeUnder K (Q μ) (hQbot μ)) (σ⁻¹ • Z μ)
        = placeValue (placeUnder K (Q μ) (hQbot μ)) (Z μ) := by
    intro μ σ hσ
    have hinv : σ⁻¹ • placeUnder K (Q μ) (hQbot μ) = placeUnder K (Q μ) (hQbot μ) :=
      inv_smul_eq_iff.2 hσ.symm
    rw [placeValue_eq_neg_ord, placeValue_eq_neg_ord]
    refine neg_inj.2 ?_
    conv_lhs => rw [← hinv]
    exact ord_galSmul σ⁻¹ (placeUnder K (Q μ) (hQbot μ)) ((Z μ : ↥K))
  -- the prescribed value is raised to the power by which the automorphism moves the roots
  have hVcompat : ∀ (μ : ι) (σ : Gal(↥K/k)) (e : ℕ), σ ζ = ζ ^ e →
      σ • placeUnder K (Q μ) (hQbot μ) = placeUnder K (Q μ) (hQbot μ) →
      (∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val) ^ e
        = MulDistribMulAction.toMonoidHom ↥(layerSub ℓ (Generic U (r * n) S) j) (φ (lift σ))
            (∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val) := by
    intro μ σ e hσζ hσw
    obtain ⟨g, hgstab, hgφ, hgσ⟩ := hstab μ (lift σ) (by rw [hlift]; exact hσw)
    have hgres : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g = σ := by rw [hgσ, hlift]
    have hge : g • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ e :=
      (smul_kummerRootUnit_eq_pow_iff hζ g e).2 (by rw [hgres]; exact hσζ)
    show (∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val) ^ e
      = φ (lift σ) • ∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val
    rw [← hgφ]
    obtain ⟨x₀, hx₀1⟩ := hx₀ μ
    have hx₀I : (x₀ : Gal(Ω/k)) ∈ Ideal.inertia Gal(Ω/k) (Q μ) := hAI μ x₀.2
    have hconjmem : g * (x₀ : Gal(Ω/k)) * g⁻¹ ∈ A μ := by
      refine hAmem μ _ ?_ ?_
      · have h1 := mem_inertia_conj hx₀I g
        rwa [mem_stabilizer_iff.1 hgstab] at h1
      · have h2 : (x₀ : Gal(Ω/k)) ∈ φ.ker := hAker μ x₀.2
        rw [MonoidHom.mem_ker] at h2 ⊢
        rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, h2, mul_one, mul_inv_cancel]
    have hτ : galSubHom K (kerGalEquiv hKker ⟨g * (x₀ : Gal(Ω/k)) * g⁻¹, hAker μ hconjmem⟩)
        = g * galSubHom K (kerGalEquiv hKker ⟨(x₀ : Gal(Ω/k)), hAker μ x₀.2⟩) * g⁻¹ := by
      rw [galSubHom_kerGalEquiv, galSubHom_kerGalEquiv]
    have hZa : AlgEquiv.restrictNormalHom (↥K) g
        • ((AlgEquiv.restrictNormalHom (↥K) g)⁻¹ • Z μ) = Z μ * (1 : (↥K)ˣ) ^ ℓ := by
      rw [smul_inv_smul, one_pow, mul_one]
    have hτI : kerGalEquiv hKker ⟨(x₀ : Gal(Ω/k)), hAker μ x₀.2⟩
        ∈ Ideal.inertia Gal(Ω/↥K) (Q μ) := by
      rw [← mem_inertia_galSubHom_iff K, galSubHom_kerGalEquiv]
      exact hx₀I
    have hchar0 : kummerChar hkd ((AlgEquiv.restrictNormalHom (↥K) g)⁻¹ • Z μ)
        (kerGalEquiv hKker ⟨(x₀ : Gal(Ω/k)), hAker μ x₀.2⟩)
        = kummerChar hkd (Z μ) (kerGalEquiv hKker ⟨(x₀ : Gal(Ω/k)), hAker μ x₀.2⟩) := by
      refine kummerChar_eq_of_dvd_placeValue hkd hℓ (hQℓ μ)
        (v := placeUnder K (Q μ) (hQbot μ)) rfl ?_ hτI
      have hpl : placeValue (placeUnder K (Q μ) (hQbot μ))
          ((AlgEquiv.restrictNormalHom (↥K) g)⁻¹ • Z μ)
          = placeValue (placeUnder K (Q μ) (hQbot μ)) (Z μ) := by
        rw [hgres]
        exact hplsmul μ σ hσw
      have h2 := placeValue_mul (placeUnder K (Q μ) (hQbot μ))
        (((AlgEquiv.restrictNormalHom (↥K) g)⁻¹ • Z μ) * (Z μ)⁻¹) (Z μ)
      rw [inv_mul_cancel_right, hpl] at h2
      have h3 : placeValue (placeUnder K (Q μ) (hQbot μ))
          (((AlgEquiv.restrictNormalHom (↥K) g)⁻¹ • Z μ) * (Z μ)⁻¹) = 0 := by omega
      rw [h3]
      exact dvd_zero _
    have hsub : subKummerChar hKker hkd (hAker μ) (Z μ)
        ⟨g * (x₀ : Gal(Ω/k)) * g⁻¹, hconjmem⟩ = (e : ZMod ℓ) := by
      simp only [subKummerChar] at hx₀1 ⊢
      rw [kummerChar_conj_of_smul_eq_mul_pow hkd hge hZa hτ, hchar0, hx₀1, mul_one]
    have hleft : layerSubMap ℓ β₁ j (a μ ⟨g * (x₀ : Gal(Ω/k)) * g⁻¹, hconjmem⟩)
        = φ g • layerSubMap ℓ β₁ j (a μ x₀) := by
      rw [haequiv μ g x₀ hconjmem, layerSubMap_smul hβ₁]
    have hright : layerSubMap ℓ β₁ j (a μ x₀)
        = ∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val := by
      have hx := hc μ x₀
      rw [hx₀1, ZMod.val_one, pow_one] at hx
      exact hx
    have hleft' : layerSubMap ℓ β₁ j (a μ ⟨g * (x₀ : Gal(Ω/k)) * g⁻¹, hconjmem⟩)
        = (∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val) ^ (e : ZMod ℓ).val := by
      have hx := hc μ ⟨g * (x₀ : Gal(Ω/k)) * g⁻¹, hconjmem⟩
      rw [hsub] at hx
      exact hx
    have hkey : (∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val) ^ (e : ZMod ℓ).val
        = φ g • ∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val := by
      rw [← hleft', hleft, hright]
    rw [← hkey]
    exact pow_eq_pow_of_pow_eq_one (hVpow μ) (ZMod.natCast_zmod_val _).symm
  -- the family of coefficients the arithmetic names, read at a rank large enough for the count
  obtain ⟨J, hJfin, hJcard, kill, hkill⟩ := hfam' E hEfin hEgal hKE
    ↥(layerSub ℓ (Generic U (r * n) S) j) (layerSub_pow_eq_one ℓ (Generic U (r * n) S) j)
    (Fin (layerDim ℓ (Generic U (r * n) S) j)) (layerBasis ℓ (Generic U (r * n) S) j)
    (fun m => ⟨layerCoord ℓ (Generic U (r * n) S) j m, prod_layerBasis_pow_layerCoord m⟩)
    (fun d hd => funext fun i => by
      have h := congrArg (fun m => layerCoord ℓ (Generic U (r * n) S) j m i) hd
      simpa only [layerCoord_prod_layerBasis_pow, layerCoord_one, Pi.zero_apply] using h)
    (fun σ =>
      MulDistribMulAction.toMonoidHom ↥(layerSub ℓ (Generic U (r * n) S) j) (φ (lift σ)))
    (fun m => by
      show φ (lift (1 : Gal(↥K/k))) • m = m
      rw [hφeq (lift 1) 1 (by rw [hlift, _root_.map_one]), _root_.map_one, one_smul])
    (fun σ τ m => by
      show φ (lift (σ * τ)) • m = φ (lift σ) • (φ (lift τ) • m)
      rw [← mul_smul, ← _root_.map_mul]
      refine congrArg (fun u : U => u • m) (hφeq _ _ ?_)
      rw [hlift, _root_.map_mul, hlift, hlift])
    ι (fun μ => placeUnder K (Q μ) (hQbot μ))
    (fun μ => ∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val)
    hconjw hVcompat hdisj hdisjℓ (fun μ => hreach _)
    (fun μ => isBaseOrderPlace_of_inertia_le_fixingSubgroup hℓ.one_lt (hQbot μ)
      (by rw [hKker]; exact hQunr μ))
  -- the shrinking onto the intended rank which kills that family
  haveI := hJfin
  have hrlt : (j + 1) * (Nat.card J *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r := by
    rw [hrdef]
    exact Nat.lt_succ_of_le (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hJcard))
  obtain ⟨as, hassurj, haskill⟩ :=
    exists_genericShrink_forall_layerSubMap_eq_one U r n S hS hrlt kill
  set γ : Generic U (r * n) S →* Generic U n S := genericShrink U r n S as with hγdef
  have hγ : IsOperatorHom γ := isOperatorHom_genericShrink U r n S as
  -- the tensor the arithmetic supplies, read in the shrunk layer
  obtain ⟨z, hzinv, hzpres, hzT, hzconf⟩ := hkill ↥(layerSub ℓ (Generic U n S) j)
    (layerSubMap ℓ γ j) (surjective_layerSubMap γ hassurj)
    (fun σ => MulDistribMulAction.toMonoidHom ↥(layerSub ℓ (Generic U n S) j) (φ (lift σ)))
    (fun σ m => layerSubMap_smul hγ (φ (lift σ)) m) haskill
  obtain ⟨bb, hbb, hbbq⟩ :
      ∃ (bb : Fin (layerDim ℓ (Generic U (r * n) S) j) → ↥(layerSub ℓ (Generic U n S) j))
        (_ : ∀ q, bb q ^ ℓ = 1),
        ∀ q, bb q = layerSubMap ℓ γ j (layerBasis ℓ (Generic U (r * n) S) j q) :=
    ⟨_, fun _ => layerSub_pow_eq_one ℓ (Generic U n S) j _, fun _ => rfl⟩
  simp only [← hbbq] at hzinv hzpres
  have hz1 : ∀ (q : Fin (layerDim ℓ (Generic U (r * n) S) j))
      (v : HeightOneSpectrum (𝓞 ↥K)),
      (ℓ : 𝓞 ↥K) ∈ v.asIdeal → localClassHom v ℓ (z q) = 1 := by
    intro q v hv
    obtain ⟨σ, ν, rfl⟩ := hℓPr v hv
    exact hzT q _ (hmemTz σ ν)
  have hβcomp : ∀ v : ↥(layerSub ℓ (Generic U N S) j),
      layerSubMap ℓ (γ.comp β₁) j v = layerSubMap ℓ γ j (layerSubMap ℓ β₁ j v) :=
    fun v => DFunLike.congr_fun (layerSubMap_comp γ β₁) v
  refine ⟨γ.comp β₁, hγ.comp hβ₁, hassurj.comp hβ₁surj,
    kummerKernelHom hKker hkd bb hbb z, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨V, hV, hV1⟩ := exists_isOpenNormal_forall_kummerKernelHom_eq_one hKker hkd
      (fun _ : Fin 1 => bb) (fun _ q => hbb q) (fun _ : Fin 1 => z)
    exact ⟨V, hV, fun y hy => hV1 0 y hy⟩
  · intro g y hy
    obtain ⟨e, hge⟩ := exists_smul_kummerRootUnit_eq_pow (hζ := hζ) g
    have hσζ : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g ζ = ζ ^ e :=
      (smul_kummerRootUnit_eq_pow_iff hζ g e).1 hge
    have ht := hzinv (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g) e hσζ
    rw [hactφ g] at ht
    have hkey := kummerTensorKernelHom_conj hKker hkd
      (layerSub_pow_eq_one ℓ (Generic U n S) j) hge
      (MulDistribMulAction.toMonoidHom ↥(layerSub ℓ (Generic U n S) j) (φ g)) ht y hy
    rw [kummerTensorKernelHom_sum, kummerTensorKernelHom_sum] at hkey
    exact hkey
  · intro ν y hyD
    have hmem : placeUnder K (Pr ν) (hPrbot ν) ∈ Tz := by
      have h1 := hmemTz 1 ν
      rwa [one_smul] at h1
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd bb hbb z
      (w := placeUnder K (Pr ν) (hPrbot ν)) rfl (fun q => hzT q _ hmem)
      (by rw [← hDPr ν]; exact hyD)
  · intro μ x hx
    have hτI : kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hx⟩ ∈ Ideal.inertia Gal(Ω/↥K) (Q μ) := by
      rw [← mem_inertia_galSubHom_iff K, galSubHom_kerGalEquiv]
      exact hAI μ x.2
    have hchar : ∀ q : Fin (layerDim ℓ (Generic U (r * n) S) j),
        kummerChar hkd (z q) (kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hx⟩)
          = kummerChar hkd
              (Z μ ^ ((placeValue (placeUnder K (Q μ) (hQbot μ)) (z q) : ZMod ℓ)).val)
              (kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hx⟩) := by
      intro q
      refine kummerChar_eq_of_dvd_placeValue hkd hℓ (hQℓ μ)
        (v := placeUnder K (Q μ) (hQbot μ)) rfl ?_ hτI
      have hval : (ℓ : ℤ) ∣ placeValue (placeUnder K (Q μ) (hQbot μ)) (z q)
          - ((((placeValue (placeUnder K (Q μ) (hQbot μ)) (z q) : ZMod ℓ)).val : ℕ) : ℤ) := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).1 ?_
        push_cast [ZMod.natCast_zmod_val]
        ring
      have h2 := placeValue_mul (placeUnder K (Q μ) (hQbot μ))
        (z q * (Z μ ^ ((placeValue (placeUnder K (Q μ) (hQbot μ)) (z q) : ZMod ℓ)).val)⁻¹)
        (Z μ ^ ((placeValue (placeUnder K (Q μ) (hQbot μ)) (z q) : ZMod ℓ)).val)
      rw [inv_mul_cancel_right, placeValue_pow, hZ μ, mul_one] at h2
      have h3 : placeValue (placeUnder K (Q μ) (hQbot μ))
          (z q * (Z μ ^ ((placeValue (placeUnder K (Q μ) (hQbot μ)) (z q) : ZMod ℓ)).val)⁻¹)
          = placeValue (placeUnder K (Q μ) (hQbot μ)) (z q)
            - ((((placeValue (placeUnder K (Q μ) (hQbot μ)) (z q) : ZMod ℓ)).val : ℕ) : ℤ) := by
        omega
      rw [h3]
      exact hval
    have hzz : kummerKernelHom hKker hkd bb hbb z ⟨(x : Gal(Ω/k)), hx⟩
        = kummerKernelHom hKker hkd bb hbb
            (fun q => Z μ ^ ((placeValue (placeUnder K (Q μ) (hQbot μ)) (z q) : ZMod ℓ)).val)
            ⟨(x : Gal(Ω/k)), hx⟩ := by
      rw [kummerKernelHom_apply, kummerKernelHom_apply]
      exact Finset.prod_congr rfl fun q _ => by rw [hchar q]
    have hfin : layerSubMap ℓ (γ.comp β₁) j (a μ x)
        = (layerSubMap ℓ γ j (∏ q, layerBasis ℓ (Generic U (r * n) S) j q ^ (c μ q).val))
          ^ (subKummerChar hKker hkd (hAker μ) (Z μ) x).val := by
      rw [hβcomp, show layerSubMap ℓ β₁ j (a μ x) = ((layerSubMap ℓ β₁ j).comp (a μ)) x from rfl,
        hc μ x, _root_.map_pow]
    rw [hzz, kummerKernelHom_eq_pow hKker hkd bb hbb (Z μ)
      (fun q => ((placeValue (placeUnder K (Q μ) (hQbot μ)) (z q) : ZMod ℓ))), hzpres μ]
    exact hfin.symm
  · rintro P hPp hPbot ⟨y, hyI, hyne⟩
    haveI := hPp
    obtain ⟨q, hq⟩ := exists_not_dvd_placeValue_of_kummerKernelHom_ne_one hKker hkd
      bb hbb z hℓ hPbot hz1 hyI hyne
    rcases hzconf (placeUnder K P hPbot) ⟨q, hq⟩ with ⟨ν, σ, hvσ⟩ | hsplit
    · obtain ⟨ρ, hρ⟩ := restrictNormalHom_surjective_level K σ
      have hbot : ρ • Q ν ≠ ⊥ := by
        intro h0
        exact hQbot ν (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ⁻¹ • I) h0)
      have hpl : placeUnder K (ρ • Q ν) hbot = placeUnder K P hPbot := by
        refine HeightOneSpectrum.ext ?_
        rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot ν) ρ, hρ, ← hvσ]
      obtain ⟨τ, -, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot hPbot hpl
      exact Or.inl ⟨ν, τ * ρ, by rw [mul_smul]; exact hτ⟩
    · refine Or.inr fun x hx => ?_
      have h1 : layerSemidirectMap ℓ hβ₁ (j + 1) (F x) = 1 :=
        MonoidHom.mem_ker.1 (hEF (hsplit P hPp hPbot rfl hx))
      rw [← layerSemidirectMap_comp ℓ hβ₁ hγ (hγ.comp hβ₁) (j + 1) (F x), h1, _root_.map_one]

end Places

end InverseGalois.Shafarevich
