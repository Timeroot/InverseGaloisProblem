/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicFamily
import InverseGalois.CFT.Units.CompletionUnits
import InverseGalois.CFT.Units.OrbitPlaces

/-!
# The finite part of the ideles fixed by the Galois group

A family of local units of the base field, one at each finite place, determines a family of local
units of the extension: at a prime of the extension take the image of the unit at the prime below.
This file shows that the families so obtained are exactly the families fixed by the Galois group.

One inclusion is the compatibility of the Galois transports between completions with the inclusion
of the completion of the base, which is checked on the dense image of the base field.  For the
other, a fixed family has its value at a prime fixed by the decomposition group there, hence coming
from the completion of the base; and the values at the other primes above the same prime of the
base are the transports of that one, so they are the images of the same element.

## Main definitions

* `InverseGalois.CFT.adicUnitsComapSections`: **a family of local units of the base field, viewed
  as a family of local units of the extension.**

## Main results

* `InverseGalois.CFT.adicCompletionGalEquiv_adicCompletionComap`: the Galois transports commute
  with the inclusion of the completion of the base.
* `InverseGalois.CFT.familyAut_adicUnitsComapSections`: the families coming from the base are
  fixed.
* `InverseGalois.CFT.adicUnitsComapSections_injective`: distinct families of the base give distinct
  families of the extension.
* `InverseGalois.CFT.mem_range_adicUnitsComapSections_iff`: **the families of local units fixed by
  the Galois group are exactly those coming from the base field.**
* `InverseGalois.CFT.eventually_unitVal_adicUnitsComapSections_eq_zero_iff`: a family coming from
  the base field satisfies the finiteness condition of the ideles exactly when the family below
  does.

## Tags

number field, idele, completion, Galois action, decomposition group
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section AdicFixed

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-! ### The transports commute with the inclusion of the base -/

/-- **The Galois transport between completions commutes with the inclusion of the completion of the
base field**, the two sides agreeing on the dense image of the base field. -/
theorem adicCompletionGalEquiv_adicCompletionComap (w : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k))
    (c : (primeUnder (𝓞 k) w).adicCompletion k) :
    adicCompletionGalEquiv w σ (adicCompletionComap (𝓞 k) w c)
      = adicCompletionComap (𝓞 k) (σ • w)
          (ringCast (fun p : HeightOneSpectrum (𝓞 k) => p.adicCompletion k)
            (primeUnder_smul_eq σ w).symm c) := by
  refine UniformSpace.Completion.induction_on c ?_ ?_
  · exact isClosed_eq
      ((continuous_adicCompletionGalEquiv w σ).comp (continuous_adicCompletionComap (𝓞 k) w))
      ((continuous_adicCompletionComap (𝓞 k) (σ • w)).comp (continuous_ringCast _ _))
  · intro x
    set y : k := WithVal.equiv ((primeUnder (𝓞 k) w).valuation k) x with hy
    have h1 : adicCompletionComap (𝓞 k) w (adicCoe y (primeUnder (𝓞 k) w))
        = adicCoe (algebraMap k K y) w := adicCompletionComap_coe (𝓞 k) w y
    have h2 : adicCompletionComap (𝓞 k) (σ • w) (adicCoe y (primeUnder (𝓞 k) (σ • w)))
        = adicCoe (algebraMap k K y) (σ • w) := adicCompletionComap_coe (𝓞 k) (σ • w) y
    show adicCompletionGalEquiv w σ
        (adicCompletionComap (𝓞 k) w (adicCoe y (primeUnder (𝓞 k) w)))
      = adicCompletionComap (𝓞 k) (σ • w)
        (ringCast _ (primeUnder_smul_eq σ w).symm (adicCoe y (primeUnder (𝓞 k) w)))
    rw [ringCast_adicCoe, h1, h2, adicCompletionGalEquiv_adicCoe, AlgEquiv.commutes]

/-! ### The families of local units coming from the base -/

variable (k) in
/-- **A family of local units of the base field, viewed as a family of local units of the
extension**: at a prime of the extension, the image of the unit at the prime below. -/
noncomputable def adicUnitsComapSections :
    (∀ v : HeightOneSpectrum (𝓞 k), Additive (v.adicCompletion k)ˣ) →+
      ∀ w : HeightOneSpectrum (𝓞 K), Additive (w.adicCompletion K)ˣ where
  toFun y w := adicUnitsComap k w (y (primeUnder (𝓞 k) w))
  map_zero' := funext fun w => map_zero (adicUnitsComap k w)
  map_add' _ _ := funext fun w => map_add (adicUnitsComap k w) _ _

variable (k) in
omit [IsGalois k K] in
@[simp]
theorem adicUnitsComapSections_apply
    (y : ∀ v : HeightOneSpectrum (𝓞 k), Additive (v.adicCompletion k)ˣ)
    (w : HeightOneSpectrum (𝓞 K)) :
    adicUnitsComapSections k (K := K) y w = adicUnitsComap k w (y (primeUnder (𝓞 k) w)) := rfl

variable (k) in
/-- **The transport of a local unit of the base field is the local unit of the base field at the
image prime.** -/
theorem unitsFamily_map_adicUnitsComap (w : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/k))
    (c : Additive ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
    (adicRingFamily (k := k) (K := K)).unitsFamily.map σ w (adicUnitsComap k w c)
      = adicUnitsComap k (σ • w)
          (famCast (fun p : HeightOneSpectrum (𝓞 k) => Additive (p.adicCompletion k)ˣ)
            (primeUnder_smul_eq σ w).symm c) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [famCast_units, coe_adicUnitsComap]
  show adicCompletionGalEquiv w σ
      ((Additive.toMul (adicUnitsComap k w c) : (w.adicCompletion K)ˣ) : w.adicCompletion K)
    = algebraMap ((primeUnder (𝓞 k) (σ • w)).adicCompletion k) ((σ • w).adicCompletion K)
        (ringCast (fun p : HeightOneSpectrum (𝓞 k) => p.adicCompletion k)
          (primeUnder_smul_eq σ w).symm
          ((Additive.toMul c : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
            (primeUnder (𝓞 k) w).adicCompletion k))
  rw [coe_adicUnitsComap, algebraMap_adicCompletion k w, algebraMap_adicCompletion k (σ • w)]
  exact adicCompletionGalEquiv_adicCompletionComap w σ _

variable (k) in
/-- **A family of local units coming from the base field is fixed by the Galois group.** -/
theorem familyAut_adicUnitsComapSections (σ : Gal(K/k))
    (y : ∀ v : HeightOneSpectrum (𝓞 k), Additive (v.adicCompletion k)ˣ) :
    (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ (adicUnitsComapSections k y)
      = adicUnitsComapSections k y := by
  refine FamilyAction.familyAut_eq_of_map _ σ _ _ fun w => ?_
  rw [adicUnitsComapSections_apply, unitsFamily_map_adicUnitsComap, adicUnitsComapSections_apply]
  exact congrArg (adicUnitsComap k (σ • w)) (famCast_apply_section _ _ y)

variable (k) in
omit [IsGalois k K] in
/-- **Distinct families of local units of the base field give distinct families of local units of
the extension.** -/
theorem adicUnitsComapSections_injective :
    Function.Injective (adicUnitsComapSections k (K := K)) := by
  intro y y' h
  funext v
  obtain ⟨w, hw⟩ := exists_primeUnder_eq (𝓞 k) (𝓞 K) v
  subst hw
  exact adicUnitsComap_injective k w (congrFun h w)

/-! ### The fixed families -/

variable (k K) in
/-- A chosen prime of the extension above a prime of the base field. -/
noncomputable def primeAbove (v : HeightOneSpectrum (𝓞 k)) : HeightOneSpectrum (𝓞 K) :=
  (exists_primeUnder_eq (𝓞 k) (𝓞 K) v).choose

variable (k K) in
omit [IsGalois k K] in
/-- The chosen prime above a prime of the base field does lie above it. -/
theorem primeUnder_primeAbove (v : HeightOneSpectrum (𝓞 k)) :
    primeUnder (𝓞 k) (primeAbove k K v) = v :=
  (exists_primeUnder_eq (𝓞 k) (𝓞 K) v).choose_spec

variable (k) in
omit [NumberField k] [IsGalois k K] in
/-- **The value of a fixed family at a prime is fixed by the decomposition group there.** -/
theorem smulUnitsAut_apply_of_familyAut_eq
    {x : ∀ w : HeightOneSpectrum (𝓞 K), Additive (w.adicCompletion K)ˣ}
    (hx : ∀ σ : Gal(K/k), (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ x = x)
    (w : HeightOneSpectrum (𝓞 K)) (σ : ↥(stabilizer Gal(K/k) w)) :
    smulUnitsAut σ (x w) = x w := by
  have hσ : (σ : Gal(K/k)) • w = w := mem_stabilizer_iff.mp σ.2
  have hmap : (adicRingFamily (k := k) (K := K)).unitsFamily.map (σ : Gal(K/k)) w (x w)
      = x ((σ : Gal(K/k)) • w) := by
    rw [← FamilyAction.familyAut_apply_smul, hx]
  have h := transport_adicUnitsFamily w (σ : Gal(K/k)) hσ (x w)
  rw [FamilyAction.transport_apply, hmap, famCast_apply_section] at h
  exact h.symm

variable (k) in
/-- **A fixed family is determined at every prime by its value at any one prime above the same
prime of the base.** -/
theorem adicUnitsComap_famCast_eq_of_familyAut_eq
    {x : ∀ w : HeightOneSpectrum (𝓞 K), Additive (w.adicCompletion K)ˣ}
    (hx : ∀ σ : Gal(K/k), (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ x = x)
    (W w : HeightOneSpectrum (𝓞 K)) (h : primeUnder (𝓞 k) W = primeUnder (𝓞 k) w)
    (c : Additive ((primeUnder (𝓞 k) W).adicCompletion k)ˣ) (hc : adicUnitsComap k W c = x W) :
    adicUnitsComap k w
        (famCast (fun p : HeightOneSpectrum (𝓞 k) => Additive (p.adicCompletion k)ˣ) h c)
      = x w := by
  haveI : IsGaloisGroup Gal(K/k) (𝓞 k) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing Gal(K/k) (𝓞 k) (𝓞 K) k K
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_primeUnder_eq (A := 𝓞 k) (G := Gal(K/k)) h
  have hmap : (adicRingFamily (k := k) (K := K)).unitsFamily.map σ W (x W) = x (σ • W) := by
    rw [← FamilyAction.familyAut_apply_smul, hx]
  rw [← hmap, ← hc, unitsFamily_map_adicUnitsComap]

variable (k) in
/-- **The families of local units fixed by the Galois group are exactly those coming from the base
field.** -/
theorem mem_range_adicUnitsComapSections_iff
    (x : ∀ w : HeightOneSpectrum (𝓞 K), Additive (w.adicCompletion K)ˣ) :
    x ∈ (adicUnitsComapSections k (K := K)).range ↔
      ∀ σ : Gal(K/k), (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ x = x := by
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩ σ
    exact familyAut_adicUnitsComapSections k σ y
  · haveI : IsGaloisGroup Gal(K/k) (𝓞 k) (𝓞 K) :=
      IsGaloisGroup.of_isFractionRing Gal(K/k) (𝓞 k) (𝓞 K) k K
    have hc : ∀ v : HeightOneSpectrum (𝓞 k),
        ∃ c : Additive ((primeUnder (𝓞 k) (primeAbove k K v)).adicCompletion k)ˣ,
          adicUnitsComap k (primeAbove k K v) c = x (primeAbove k K v) := fun v =>
      (mem_range_adicUnitsComap_iff k (primeAbove k K v) (x (primeAbove k K v))).mpr
        (smulUnitsAut_apply_of_familyAut_eq k hx (primeAbove k K v))
    choose c hcx using hc
    refine ⟨fun v => famCast (fun p : HeightOneSpectrum (𝓞 k) => Additive (p.adicCompletion k)ˣ)
      (primeUnder_primeAbove k K v) (c v), funext fun w => ?_⟩
    exact adicUnitsComap_famCast_eq_of_familyAut_eq k hx (primeAbove k K (primeUnder (𝓞 k) w)) w
      (primeUnder_primeAbove k K (primeUnder (𝓞 k) w)) _ (hcx _)

/-! ### The finiteness condition -/

variable (k) in
omit [IsGalois k K] in
/-- **A family coming from the base field is a unit of the valuation ring at a prime exactly when
the family below is one at the prime underneath.** -/
theorem unitVal_adicUnitsComapSections_eq_zero_iff
    (y : ∀ v : HeightOneSpectrum (𝓞 k), Additive (v.adicCompletion k)ˣ)
    (w : HeightOneSpectrum (𝓞 K)) :
    unitVal (adicUnitsComapSections k (K := K) y w) = 0 ↔
      unitVal (y (primeUnder (𝓞 k) w)) = 0 :=
  unitVal_adicUnitsComap_eq_zero_iff k w _

variable (k) in
/-- **A family coming from the base field satisfies the finiteness condition of the ideles exactly
when the family below does**: the two sets of bad primes correspond under passing to the prime
below, and the primes above a finite set of primes are finite in number. -/
theorem eventually_unitVal_adicUnitsComapSections_eq_zero_iff
    (y : ∀ v : HeightOneSpectrum (𝓞 k), Additive (v.adicCompletion k)ˣ) :
    (∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        unitVal (adicUnitsComapSections k (K := K) y w) = 0) ↔
      ∀ᶠ v : HeightOneSpectrum (𝓞 k) in Filter.cofinite, unitVal (y v) = 0 := by
  haveI : IsGaloisGroup Gal(K/k) (𝓞 k) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing Gal(K/k) (𝓞 k) (𝓞 K) k K
  rw [Filter.eventually_cofinite, Filter.eventually_cofinite]
  have hset : {w : HeightOneSpectrum (𝓞 K) |
        ¬ unitVal (adicUnitsComapSections k (K := K) y w) = 0}
      = primeUnder (𝓞 k) ⁻¹' {v : HeightOneSpectrum (𝓞 k) | ¬ unitVal (y v) = 0} :=
    Set.ext fun w => not_congr (unitVal_adicUnitsComapSections_eq_zero_iff k y w)
  rw [hset]
  exact finite_preimage_primeUnder_iff (𝓞 k) (𝓞 K) (G := Gal(K/k))

end AdicFixed

end InverseGalois.CFT
