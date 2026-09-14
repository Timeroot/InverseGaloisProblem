/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.FlatStabilizerUnits

/-!
# The obstruction, bought under a subgroup of the decomposition group of order a prime power

The units the obstruction is bought with are asked to be fixed modulo exponent-th powers by every
automorphism fixing their place.  That demand only has to be met under a subgroup of the
decomposition group whose order is a power of the exponent.  The product of the translates of such a
unit along a transversal of that subgroup is fixed modulo exponent-th powers by the whole
decomposition group, and its order at the place is the index of the subgroup, which is prime to the
exponent when the subgroup is a Sylow one, so a power of the product brings the order back to one.

Nothing about the subgroup is used but its index.  In particular no normality is asked of it: the
translate of a representative of a coset is again a representative, of the translated coset, up to
an element of the subgroup, and the invariance modulo exponent-th powers available there is exactly
what absorbs that element.  Reindexing the product along the permutation of cosets the automorphism
induces returns the product to itself.

What this buys is that the class the units are asked to be fixed in is only ever read under a group
whose order is a power of the exponent, and such a group fixes the roots of unity of order the
exponent, so the level over which the demand is made carries them.

## Main definitions

* `InverseGalois.Shafarevich.HasSylowConfinedUnits`: the units the obstruction is bought with,
  asked to be fixed modulo exponent-th powers only under a subgroup of order a power of the
  exponent.
* `Shafarevich.SylowConfinedUnitsEP`: the same, made of every level.

## Main results

* `InverseGalois.Shafarevich.exists_pow_smul_prod_out`: **the product along a transversal is fixed
  modulo exponent-th powers by the whole group**, when the factor is fixed modulo exponent-th powers
  by the subgroup.
* `InverseGalois.Shafarevich.exists_forall_smul_eq_mul_pow`: the same product, with the order at the
  named place brought back to one by a power, the index being prime to the exponent.
* `InverseGalois.Shafarevich.hasStabilizerConfinedUnits_of_hasSylowConfinedUnits`: **a Sylow
  subgroup of the decomposition group is enough.**
* `Shafarevich.genericLevelStepEPRoots_of_sylowConfinedUnitsEP`: the step of the ladder over an odd
  prime, in exchange for the units asked under a Sylow subgroup alone.

## Tags

Shafarevich's theorem, embedding problem, Sylow subgroup, transversal, decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain MulAction NumberField

set_option synthInstance.maxHeartbeats 800000

/-! ### Spreading invariance along a transversal -/

section Transversal

variable {G A X : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- **The product along a transversal is fixed modulo exponent-th powers by the whole group.**

An element of the group carries a representative of a coset to a representative of the translated
coset, up to an element of the subgroup, and what that element does to the factor is an exponent-th
power.  Reindexing the product along the permutation of cosets the element induces returns it to
itself, so only the exponent-th powers survive. -/
theorem exists_pow_smul_prod_out {S : Subgroup G} (P : Subgroup ↥S) [Fintype (↥S ⧸ P)] (ℓ : ℕ)
    (u : A) (h : ∀ σ : ↥S, σ ∈ P → ∃ v : A, (σ : G) • u = u * v ^ ℓ) (g : ↥S) :
    ∃ w : A, (g : G) • (∏ c : ↥S ⧸ P, ((Quotient.out c : ↥S) : G) • u)
      = (∏ c : ↥S ⧸ P, ((Quotient.out c : ↥S) : G) • u) * w ^ ℓ := by
  classical
  have hd : ∀ c : ↥S ⧸ P, (Quotient.out (g • c))⁻¹ * (g * Quotient.out c) ∈ P := fun c => by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
  choose v hv using fun c : ↥S ⧸ P => h _ (hd c)
  refine ⟨∏ c : ↥S ⧸ P, ((Quotient.out (g • c) : ↥S) : G) • v c, ?_⟩
  have key : ∀ c : ↥S ⧸ P, (g : G) • (((Quotient.out c : ↥S) : G) • u)
      = (((Quotient.out (g • c) : ↥S) : G) • u)
        * (((Quotient.out (g • c) : ↥S) : G) • v c) ^ ℓ := by
    intro c
    rw [smul_smul, ← Subgroup.coe_mul,
      show g * Quotient.out c
          = Quotient.out (g • c) * ((Quotient.out (g • c))⁻¹ * (g * Quotient.out c)) from
        (mul_inv_cancel_left _ _).symm,
      Subgroup.coe_mul, ← smul_smul, hv c, smul_mul', smul_pow']
  rw [Finset.smul_prod', Finset.prod_congr rfl fun c (_ : c ∈ Finset.univ) => key c,
    Finset.prod_mul_distrib, Finset.prod_pow]
  congr 1
  exact Equiv.prod_comp (MulAction.toPerm g : Equiv.Perm (↥S ⧸ P))
    fun c => ((Quotient.out c : ↥S) : G) • u

variable [MulAction G X]

/-- **A unit of order one at a place and fixed modulo exponent-th powers under a subgroup of the
stabilizer of prime-to-the-exponent index is carried to one fixed under the whole stabilizer.**

The product along a transversal of the subgroup has order the index at the place, because every
representative fixes it, and order divisible by the exponent elsewhere, because the vector of orders
is equivariant and the places the factor has order at are carried among themselves.  Raising the
product to a power inverse to the index modulo the exponent brings the order at the place back to
one and leaves the invariance modulo exponent-th powers untouched. -/
theorem exists_forall_smul_eq_mul_pow {ℓ : ℕ} [Fact ℓ.Prime] (D : Additive A →+ (X →₀ ℤ))
    (hD : ∀ (σ : G) (a : A) (z : X),
      D (Additive.ofMul (σ • a)) z = D (Additive.ofMul a) (σ⁻¹ • z))
    (y : X) {S : Subgroup G} (hS : ∀ x : ↥S, (x : G) • y = y) (P : Subgroup ↥S)
    [Fintype (↥S ⧸ P)] (hidx : ¬ ℓ ∣ P.index) (u₁ : A)
    (hord : ∀ z : X, (ℓ : ℤ) ∣ D (Additive.ofMul u₁) z - Finsupp.single y 1 z)
    (hinv : ∀ σ : ↥S, σ ∈ P → ∃ v : A, (σ : G) • u₁ = u₁ * v ^ ℓ) :
    ∃ u : A, (∀ z : X, (ℓ : ℤ) ∣ D (Additive.ofMul u) z - Finsupp.single y 1 z) ∧
      ∀ σ : ↥S, ∃ v : A, (σ : G) • u = u * v ^ ℓ := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨u, hu⟩ : ∃ u : A, u = ∏ c : ↥S ⧸ P, ((Quotient.out c : ↥S) : G) • u₁ := ⟨_, rfl⟩
  set m : ℕ := Fintype.card (↥S ⧸ P) with hmdef
  have hmcard : m = P.index := Nat.card_eq_fintype_card.symm
  have hmne : ((m : ℕ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, hmcard]
    exact hidx
  set m' : ℕ := ((m : ZMod ℓ)⁻¹).val with hm'def
  have hmm' : (ℓ : ℤ) ∣ ((m' * m : ℕ) : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hm'def, ZMod.natCast_val, ZMod.cast_id, inv_mul_cancel₀ hmne, sub_self]
  have hordu : ∀ z : X, D (Additive.ofMul u) z
      = ∑ c : ↥S ⧸ P, D (Additive.ofMul u₁) (((Quotient.out c : ↥S) : G)⁻¹ • z) := by
    intro z
    rw [hu, _root_.ofMul_prod, map_sum, Finsupp.finset_sum_apply]
    exact Finset.sum_congr rfl fun c _ => hD _ _ _
  have hsingle : ∀ (c : ↥S ⧸ P) (z : X),
      (Finsupp.single y (1 : ℤ)) (((Quotient.out c : ↥S) : G)⁻¹ • z)
        = (Finsupp.single y (1 : ℤ)) z := by
    intro c z
    have hiff : (y = ((Quotient.out c : ↥S) : G)⁻¹ • z) ↔ (y = z) := by
      rw [eq_inv_smul_iff, hS]
    simp only [Finsupp.single_apply, hiff]
  have hordu' : ∀ z : X,
      (ℓ : ℤ) ∣ D (Additive.ofMul u) z - (m : ℤ) * (Finsupp.single y (1 : ℤ)) z := by
    intro z
    have hsum : ∑ c : ↥S ⧸ P, (D (Additive.ofMul u₁) (((Quotient.out c : ↥S) : G)⁻¹ • z)
          - (Finsupp.single y (1 : ℤ)) z)
        = D (Additive.ofMul u) z - (m : ℤ) * (Finsupp.single y (1 : ℤ)) z := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hordu z,
        ← hmdef]
    rw [← hsum]
    refine Finset.dvd_sum fun c _ => ?_
    have h1 := hord (((Quotient.out c : ↥S) : G)⁻¹ • z)
    rwa [hsingle c z] at h1
  have hpow : ∀ (n : ℕ) (z : X),
      D (Additive.ofMul (u ^ n)) z = (n : ℤ) * D (Additive.ofMul u) z := by
    intro n z
    rw [_root_.ofMul_pow, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  refine ⟨u ^ m', fun z => ?_, fun σ => ?_⟩
  · have h1 : (ℓ : ℤ) ∣ (m' : ℤ) * (D (Additive.ofMul u) z
        - (m : ℤ) * (Finsupp.single y (1 : ℤ)) z) := (hordu' z).mul_left _
    have h3 : (ℓ : ℤ) ∣ (((m' * m : ℕ) : ℤ) - 1) * (Finsupp.single y (1 : ℤ)) z :=
      hmm'.mul_right _
    have h4 := dvd_add h1 h3
    rw [hpow]
    refine dvd_trans h4 (dvd_of_eq ?_)
    push_cast
    ring
  · obtain ⟨w, hw⟩ := exists_pow_smul_prod_out P ℓ u₁ hinv σ
    rw [← hu] at hw
    refine ⟨w ^ m', ?_⟩
    rw [smul_pow', hw, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm ℓ m']

end Transversal

/-! ### The units, asked under a subgroup of order a prime power -/

section Units

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **The units the obstruction is bought with, asked under a subgroup of order a power of the
exponent.**

At each place of the hull of the named ones which some automorphism of order the exponent fixes, a
confined unit of order one at that place and none at the other places of the hull, each up to a
multiple of the exponent, whose class modulo exponent-th powers is fixed by a given subgroup of
order a power of the exponent inside the automorphisms fixing the place.  The subgroup is arbitrary
among those, so the demand is made of the Sylow subgroups of the decomposition group and of nothing
larger.  The place is asked to lie outside the set at which the radicand is kept inert, where an
order of one is impossible, and to have its order taken by an element the whole group of
automorphisms fixes. -/
def HasSylowConfinedUnits (ℓ : ℕ) (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ Xs₀ Tz : Set (HeightOneSpectrum (𝓞 ↥K)), Xs₀.Finite → Tz.Finite →
      ∀ (_ : Finite ↥(stableHull k ↥K Xs₀)) (y : ↥(stableHull k ↥K Xs₀)),
        (y : HeightOneSpectrum (𝓞 ↥K)) ∉ stableHull k ↥K Tz →
        IsBaseOrderPlace ℓ K (y : HeightOneSpectrum (𝓞 ↥K)) →
        (∃ σ : Gal(↥K/k), σ ≠ 1 ∧ σ ^ ℓ = 1 ∧ σ • y = y) →
        ∀ P : Subgroup Gal(↥K/k), IsPGroup ℓ ↥P → (∀ σ ∈ P, σ • y = y) →
        ∃ u : ↥(confinedUnits ↥K ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)),
          (∀ z : ↥(stableHull k ↥K Xs₀), (ℓ : ℤ) ∣
            confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) (stableHull k ↥K Xs₀)
              (Additive.ofMul u) z - Finsupp.single y 1 z) ∧
            ∀ σ ∈ P,
              ∃ v : ↥(confinedUnits ↥K ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)),
                σ • u = u * v ^ ℓ

/-- **A Sylow subgroup of the decomposition group is enough.**

The unit asked for under a Sylow subgroup of the automorphisms fixing the place is spread along a
transversal of that subgroup: the product of its translates is fixed modulo exponent-th powers by
every automorphism fixing the place, and its order there is the index of the Sylow subgroup, which
is prime to the exponent, so a power of the product has order one at the place.  Every
representative fixes the place, so the vector of orders of the product agrees at every place of the
hull with a multiple of the one asked for. -/
theorem hasStabilizerConfinedUnits_of_hasSylowConfinedUnits {ℓ : ℕ} [Fact ℓ.Prime]
    {K : IntermediateField k Ω} [NumberField ↥K] [FiniteDimensional k ↥K]
    (h : HasSylowConfinedUnits ℓ K) :
    HasStabilizerConfinedUnits ℓ K := by
  classical
  intro E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz hfin y hyTz hybase hy
  haveI := hfin
  haveI : Finite Gal(↥K/k) := Finite.of_fintype _
  obtain ⟨Q⟩ : Nonempty (Sylow ℓ ↥(stabilizer Gal(↥K/k) y)) := inferInstance
  haveI : Fintype (↥(stabilizer Gal(↥K/k) y) ⧸ (Q : Subgroup ↥(stabilizer Gal(↥K/k) y))) :=
    Fintype.ofFinite _
  obtain ⟨u₁, hord₁, hinv₁⟩ := h E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz hfin y hyTz hybase hy
    ((Q : Subgroup ↥(stabilizer Gal(↥K/k) y)).map (stabilizer Gal(↥K/k) y).subtype)
    (Q.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ _ Subtype.coe_injective))
    (by rintro σ ⟨x, _, rfl⟩; exact x.2)
  obtain ⟨u, hordu, hinvu⟩ :=
    exists_forall_smul_eq_mul_pow
      (confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) (stableHull k ↥K Xs₀))
      (confinedOrd_smul_apply ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)
        (stableHull k ↥K Xs₀))
      y (S := stabilizer Gal(↥K/k) y) (fun x => x.2)
      (Q : Subgroup ↥(stabilizer Gal(↥K/k) y)) Q.not_dvd_index u₁ hord₁
      fun σ hσ => hinv₁ _ (Subgroup.mem_map_of_mem _ hσ)
  exact ⟨u, hordu, fun σ hσ => hinvu ⟨σ, hσ⟩⟩

end Units

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

/-! ### The units under a prime-power subgroup, made of every level -/

/-- **Every finite Galois level of a number field inside an algebraic closure carrying a primitive
root of unity of the exponent carries the units the obstruction is bought with, asked under a
subgroup of order a power of the exponent.** -/
def SylowConfinedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K],
      (∃ ζ : ↥K, IsPrimitiveRoot ζ ℓ) → HasSylowConfinedUnits ℓ K

/-- **The units asked under a Sylow subgroup buy the units asked under the whole decomposition
group**, at every level. -/
theorem stabilizerConfinedUnitsEP_of_sylowConfinedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : SylowConfinedUnitsEP ℓ) : StabilizerConfinedUnitsEP ℓ := by
  intro k Ω _ _ _ _ _ _ K _ _ _ hζ
  exact hasStabilizerConfinedUnits_of_hasSylowConfinedUnits (h k Ω K hζ)

/-- **The step of the ladder over an odd prime**, in exchange for the units of the obstruction asked
under a subgroup of order a power of the prime and nothing else. -/
theorem genericLevelStepEPRoots_of_sylowConfinedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (hsyl : SylowConfinedUnitsEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_stabilizerConfinedUnitsEP ℓ hodd
    (stabilizerConfinedUnitsEP_of_sylowConfinedUnitsEP ℓ hsyl)

end Shafarevich
