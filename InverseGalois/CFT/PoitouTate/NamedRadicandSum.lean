/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedWeighted
import InverseGalois.CFT.PoitouTate.NamedRadicand
import InverseGalois.CFT.PoitouTate.TensorKill

/-!
# The whole prescription answered by one radicand, at the cost of one class

A prescription names finitely many places in distinct orbits and asks for an invariant radicand with
the prescribed value at each.  Answering the demands one orbit at a time costs one obstruction class
for each named place, and a count that has to kill those obstructions would then have to be sized by
the number of named places — which a construction choosing its places after its count cannot afford.

The demands need not be answered separately.  The divisors carried by the several orbits are added
into a **single** divisor, which is still equivariant because each summand is, and a single radicand
realises it; so the whole prescription costs exactly **one** class in the first cohomology of the
group with coefficients in the kernel of the valuation, tensored with the module.  Killing that one
class costs a family of elements of the module indexed by the group times a spanning family of the
kernel — a size the field and the set of places decide, before a single place is named.

## Main definitions

* `InverseGalois.CFT.namedRadicand`: the divisor of a whole prescription, the sum over the named
  places of the divisor carried by the orbit of each.

## Main results

* `InverseGalois.CFT.exists_kill_family_of_named`: **a finite family of elements of the module, of a
  size the group and the spanning family alone decide, whose death under an equivariant
  homomorphism hands back an invariant tensor with the prescribed value at each named place and no
  value away from their orbits.**
* `InverseGalois.CFT.exists_kill_family_of_named_of_subgroup`: the same when the class is read on a
  subgroup of the kernel of the valuation, the spanning family being a spanning family of that
  subgroup.
* `InverseGalois.CFT.exists_kill_family_of_confined_named`: the same for the units of a number field
  which are local powers at one set of places and have order divisible by the exponent outside
  another.
* `InverseGalois.CFT.exists_kill_family_of_confined_named_of_span`: the same with the class read on
  the confined units of no order outside a finite set of places, which is the form in which the
  spanning family is finite and its size is decided by the field alone.

## Tags

number field, S-unit, tensor product, divisor, orbit, descent, group cohomology, obstruction
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField TensorProduct groupCohomology

/-! ### The divisor of a whole prescription -/

section Divisor

variable (Q : Type*) [Group Q] [Finite Q] {X : Type*} [MulAction Q X]
variable {C : Type*} [CommGroup C] [MulDistribMulAction Q C]
variable {ι : Type*} [Fintype ι]

/-- **The divisor of a prescription at finitely many named places**: the sum over the named places
of the divisor carried by the orbit of each. -/
noncomputable def namedRadicand (x : ι → X) (V : ι → C) : X →₀ Additive C :=
  ∑ μ : ι, orbitRadicand Q (x μ) (V μ)

/-- The value of the divisor of a prescription is the sum of the values of its summands. -/
theorem namedRadicand_apply (x : ι → X) (V : ι → C) (z : X) :
    namedRadicand Q x V z = ∑ μ : ι, orbitRadicand Q (x μ) (V μ) z :=
  Finsupp.finset_sum_apply Finset.univ (fun μ : ι => orbitRadicand Q (x μ) (V μ)) z

/-- **The divisor of a prescription is equivariant**, each of its summands being so. -/
theorem namedRadicand_smul_apply (x : ι → X) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Q (x μ), s • V μ = V μ) (σ : Q) (z : X) :
    namedRadicand Q x V (σ • z) = Additive.ofMul (σ • (namedRadicand Q x V z).toMul) := by
  calc namedRadicand Q x V (σ • z)
      = ∑ μ : ι, orbitRadicand Q (x μ) (V μ) (σ • z) := namedRadicand_apply Q x V _
    _ = ∑ μ : ι, Additive.ofMul (σ • (orbitRadicand Q (x μ) (V μ) z).toMul) :=
        Finset.sum_congr rfl fun μ _ => orbitRadicand_smul_apply Q (x μ) (V μ) (hV μ) σ z
    _ = Additive.ofMul (∏ μ : ι, σ • (orbitRadicand Q (x μ) (V μ) z).toMul) := by
        rw [_root_.ofMul_prod]
    _ = Additive.ofMul (σ • ∏ μ : ι, (orbitRadicand Q (x μ) (V μ) z).toMul) := by
        rw [Finset.smul_prod']
    _ = Additive.ofMul (σ • (namedRadicand Q x V z).toMul) := by
        rw [← _root_.toMul_sum, ← namedRadicand_apply]

/-- The value of the divisor of a prescription at a named place is the value prescribed there, the
other summands being carried by orbits that place does not meet. -/
theorem namedRadicand_apply_self (x : ι → X) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Q (x μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → x μ ∉ orbit Q (x ν)) (ν : ι) :
    namedRadicand Q x V (x ν) = Additive.ofMul (V ν) := by
  classical
  rw [namedRadicand_apply]
  refine (Finset.sum_eq_single ν (fun μ _ hμ => ?_)
    (fun h => absurd (Finset.mem_univ ν) h)).trans ?_
  · exact orbitRadicand_apply_of_notMem Q (x μ) (V μ) (hdisj ν μ (Ne.symm hμ))
  · exact orbitRadicand_apply_self Q (x ν) (V ν) (hV ν)

/-- The divisor of a prescription has no value away from the orbits of the named places. -/
theorem namedRadicand_apply_of_notMem (x : ι → X) (V : ι → C) {z : X}
    (hz : ∀ μ : ι, z ∉ orbit Q (x μ)) : namedRadicand Q x V z = 0 := by
  rw [namedRadicand_apply]
  exact Finset.sum_eq_zero fun μ _ => orbitRadicand_apply_of_notMem Q (x μ) (V μ) (hz μ)

end Divisor

/-! ### The whole prescription at the cost of one class -/

section Named

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C : Type} [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]

/-- **A finite family of elements of the module, of a size the group and the spanning family alone
decide, whose death under an equivariant homomorphism hands back an invariant tensor with the
prescribed value at each named place and no value away from their orbits.**

The whole prescription is carried by one divisor, the sum of the divisors carried by the several
orbits; the valuation is onto, so that divisor is realised, and it is equivariant, so the valuation
of the realising tensor is invariant.  What is left is the single obstruction class of that tensor,
and the family is the family of coordinates of its cocycle against the spanning family of the
kernel of the valuation: a homomorphism killing all of them kills the class, and the correction it
supplies changes no value of the divisor. -/
theorem exists_kill_family_of_named
    (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    {d : ℕ} (b : Fin d → Additive ↥B) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {ι : Type} [Fintype ι] (x : ι → X) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Q (x μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → x μ ∉ orbit Q (x ν)) :
    ∃ y : Q × Fin d → C,
      ∀ (C' : Type) [CommGroup C'] [MulDistribMulAction Q C'] (φ : C →* C')
        (_hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w), (∀ ν, φ (y ν) = 1) →
        ∃ s : Additive A ⊗[ℤ] Additive C',
          (∀ σ : Q, σ • s = s) ∧
          (∀ μ : ι, tensorVal C' g s (x μ) = Additive.ofMul (φ (V μ))) ∧
          ∀ z : X, (∀ μ : ι, z ∉ orbit Q (x μ)) → tensorVal C' g s z = 0 := by
  have hgeq' : ∀ (σ : Q) (a : A) (z : X),
      g (Additive.ofMul (σ • a)) (σ • z) = g (Additive.ofMul a) z := by
    intro σ a z
    rw [hgeq σ a (σ • z), inv_smul_smul]
  obtain ⟨t, ht⟩ := tensorVal_surjective C g hg (namedRadicand Q x V)
  have hinv : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t :=
    tensorVal_smul_eq_of_eq C g hgeq' ht (namedRadicand_smul_apply Q x V hV)
  obtain ⟨y, hy⟩ := exists_kill_family_of_span b hb (tensorInvariantClass C g B hg hB hinv)
  refine ⟨y, fun C' _ _ φ hφ hkill => ?_⟩
  obtain ⟨s, hs, hsval⟩ := exists_invariant_tensorCoeff_of_map_tensorInvariantClass_eq_zero
    g B hg hB φ hφ hinv (hy C' φ hφ hkill)
  refine ⟨s, hs, fun μ => ?_, fun z hz => ?_⟩
  · rw [hsval (x μ), ht, namedRadicand_apply_self Q x V hV hdisj μ, _root_.toMul_ofMul]
  · rw [hsval z, ht, namedRadicand_apply_of_notMem Q x V hz, _root_.toMul_zero, _root_.map_one,
      _root_.ofMul_one]

variable (B' : Subgroup ↥B) [IsStableSubgroup Q B']

/-- **The same family, read on a subgroup of the kernel of the valuation.**

The kernel of the valuation is as big as the module it sits in and carries no finite spanning family
of its own; a subgroup of it does, provided the class is known to come from that subgroup.  The
family is then the family of coordinates of a chosen preimage there, and killing it kills the
preimage, hence the class itself, the homomorphism of the module commuting with the inclusion of the
subgroup. -/
theorem exists_kill_family_of_named_of_subgroup
    (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hrange : ∀ (t : Additive A ⊗[ℤ] Additive C)
      (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t),
      tensorInvariantClass C g B hg hB ht ∈
        LinearMap.range (groupCohomology.map (MonoidHom.id Q)
          (A := Rep.ofDistribMulAction ℤ Q (Additive ↥B' ⊗[ℤ] Additive C))
          (tensorSubInclRep Q C B') 1).hom)
    {d : ℕ} (b : Fin d → Additive ↥B') (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {ι : Type} [Fintype ι] (x : ι → X) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Q (x μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → x μ ∉ orbit Q (x ν)) :
    ∃ y : Q × Fin d → C,
      ∀ (C' : Type) [CommGroup C'] [MulDistribMulAction Q C'] (φ : C →* C')
        (_hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w), (∀ ν, φ (y ν) = 1) →
        ∃ s : Additive A ⊗[ℤ] Additive C',
          (∀ σ : Q, σ • s = s) ∧
          (∀ μ : ι, tensorVal C' g s (x μ) = Additive.ofMul (φ (V μ))) ∧
          ∀ z : X, (∀ μ : ι, z ∉ orbit Q (x μ)) → tensorVal C' g s z = 0 := by
  have hgeq' : ∀ (σ : Q) (a : A) (z : X),
      g (Additive.ofMul (σ • a)) (σ • z) = g (Additive.ofMul a) z := by
    intro σ a z
    rw [hgeq σ a (σ • z), inv_smul_smul]
  obtain ⟨t, ht⟩ := tensorVal_surjective C g hg (namedRadicand Q x V)
  have hinv : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t :=
    tensorVal_smul_eq_of_eq C g hgeq' ht (namedRadicand_smul_apply Q x V hV)
  obtain ⟨u, hu⟩ := hrange t hinv
  obtain ⟨y, hy⟩ := exists_kill_family_of_span b hb u
  refine ⟨y, fun C' _ _ φ hφ hkill => ?_⟩
  have hzero := map_tensorCoeffRep_eq_zero_of_map_tensorSubInclRep (A := ↥B) B' φ hφ hu
    (hy C' φ hφ hkill)
  obtain ⟨s, hs, hsval⟩ := exists_invariant_tensorCoeff_of_map_tensorInvariantClass_eq_zero
    g B hg hB φ hφ hinv hzero
  refine ⟨s, hs, fun μ => ?_, fun z hz => ?_⟩
  · rw [hsval (x μ), ht, namedRadicand_apply_self Q x V hV hdisj μ, _root_.toMul_ofMul]
  · rw [hsval z, ht, namedRadicand_apply_of_notMem Q x V hz, _root_.toMul_zero, _root_.map_one,
      _root_.ofMul_one]

end Named

/-! ### The confined units of a number field -/

section Confined

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
variable (n : ℕ) (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite ↥Xs] [DecidableEq ↥Xs]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K Xs]
variable {C : Type} [CommGroup C] [MulDistribMulAction Gal(K/k) C]

/-- **A finite family of elements of the module whose death under an equivariant homomorphism hands
back an invariant radicand of confined units with the prescribed value at each named place.**  The
units which are local powers at one set of places and have order divisible by the exponent outside
another form a subgroup carried into itself by the Galois group, and the vector of their orders at
the named places is an equivariant valuation onto the free abelian group on those places, so the
descent applies verbatim: the size of the family is the order of the Galois group times the size of
a spanning family of the units without order at the read places. -/
theorem exists_kill_family_of_confined_named
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    {d : ℕ} (b : Fin d → Additive ↥(confinedSUnits n Tz Y Xs))
    (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {ι : Type} [Fintype ι] (w : ι → ↥Xs) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Gal(K/k) (w μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → w μ ∉ orbit Gal(K/k) (w ν)) :
    ∃ y : Gal(K/k) × Fin d → C,
      ∀ (C' : Type) [CommGroup C'] [MulDistribMulAction Gal(K/k) C'] (φ : C →* C')
        (_hφ : ∀ (σ : Gal(K/k)) (u : C), φ (σ • u) = σ • φ u),
        (∀ ν, φ (y ν) = 1) →
        ∃ s : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C',
          (∀ σ : Gal(K/k), σ • s = s) ∧
          (∀ μ : ι, tensorVal C' (confinedOrd n Tz Y Xs) s (w μ) = Additive.ofMul (φ (V μ))) ∧
          ∀ z : ↥Xs, (∀ μ : ι, z ∉ orbit Gal(K/k) (w μ)) →
            tensorVal C' (confinedOrd n Tz Y Xs) s z = 0 :=
  exists_kill_family_of_named (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs) hsurj
    (mem_confinedSUnits_iff n Tz Y Xs) (confinedOrd_smul_apply n Tz Y Xs) b hb w V hV hdisj

variable (T : Set (HeightOneSpectrum (𝓞 K))) [IsGaloisStablePlaces k K T]

/-- **The same family, with the class read on the confined units of no order outside a finite set of
places.**

The units of no order at the named places are as big as the units themselves and carry no finite
spanning family; reading their order a second time, at every place outside a finite set, cuts them
down to the units supported in that set, and those are finitely generated.  Nothing is asked of the
second reading except that it be onto, and the size of the family is then the order of the Galois
group times the number of generators the second reading leaves — a number the field and the two
finite sets of places decide, before a single place is named. -/
theorem exists_kill_family_of_confined_named_of_span
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hsurjT : Function.Surjective (confinedSWeightedOrd n Tz Y Xs T))
    {d : ℕ} (b : Fin d → Additive ↥(confinedTUnits n Tz Y Xs T))
    (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {ι : Type} [Fintype ι] (w : ι → ↥Xs) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Gal(K/k) (w μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → w μ ∉ orbit Gal(K/k) (w ν)) :
    ∃ y : Gal(K/k) × Fin d → C,
      ∀ (C' : Type) [CommGroup C'] [MulDistribMulAction Gal(K/k) C'] (φ : C →* C')
        (_hφ : ∀ (σ : Gal(K/k)) (u : C), φ (σ • u) = σ • φ u),
        (∀ ν, φ (y ν) = 1) →
        ∃ s : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C',
          (∀ σ : Gal(K/k), σ • s = s) ∧
          (∀ μ : ι, tensorVal C' (confinedOrd n Tz Y Xs) s (w μ) = Additive.ofMul (φ (V μ))) ∧
          ∀ z : ↥Xs, (∀ μ : ι, z ∉ orbit Gal(K/k) (w μ)) →
            tensorVal C' (confinedOrd n Tz Y Xs) s z = 0 :=
  exists_kill_family_of_named_of_subgroup (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs)
    (confinedTUnits n Tz Y Xs T) hsurj (mem_confinedSUnits_iff n Tz Y Xs)
    (confinedOrd_smul_apply n Tz Y Xs)
    (fun _ ht => mem_range_map_tensorSubInclRep_confinedTensorInvariantClass n Tz Y Xs T hsurj
      hsurjT ht)
    b hb w V hV hdisj

end Confined

end InverseGalois.CFT
