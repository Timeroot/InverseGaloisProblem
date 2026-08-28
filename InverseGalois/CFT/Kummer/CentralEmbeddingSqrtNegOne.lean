/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CentralEmbedding
import InverseGalois.CFT.Units.ABHNFinite
import InverseGalois.CFT.Units.ABHNSqrtNegOneRamified

/-!
# Solving a central embedding problem over the rational numbers with no condition at infinity

The local-global criterion for a central Frattini embedding problem costs a hypothesis at the
archimedean places, and for a kernel of even order that hypothesis is not available.  Over the
rational numbers it costs nothing at all: the Albert-Brauer-Hasse-Noether theorem for a torsion
cocycle holds there with no condition at infinity, because a square root of minus one may always be
adjoined and the enlargement is invisible to the finite local conditions.  The criterion therefore
reads for an arbitrary kernel exactly as it does for an odd one.

The four forms of the criterion are restated in that setting, from the most flexible — the
obstruction is a coboundary at each ramified finite place — down to the congruence on the residue
characteristic that the Scholz-Reichardt construction verifies.

## Main results

* `InverseGalois.CFT.exists_surjective_hom_rat_of_forall_ramified`: **a central Frattini embedding
  problem over an extension of the rational numbers, whose obstruction is a coboundary at every
  ramified finite place, is solvable over a larger extension.**
* `InverseGalois.CFT.exists_surjective_hom_rat_of_forall_ramified_lift`: the same
  conclusion from a homomorphic lift over the decomposition group at each ramified finite place.
* `InverseGalois.CFT.exists_surjective_hom_rat_of_forall_ramified_pow`: the same
  conclusion from the roots of unity of the rational numbers being local powers there.
* `InverseGalois.CFT.exists_surjective_hom_rat_of_forall_ramified_primeResidue`: the
  same conclusion from a congruence on the residue characteristic at each ramified finite place
  with prime residue field.
* `InverseGalois.CFT.exists_surjective_hom_rat_of_forall_ramified_lift_or_primeResidue`:
  the same conclusion when each ramified finite place is discharged by either of the two.

## Tags

embedding problem, central extension, Frattini subgroup, Albert-Brauer-Hasse-Noether, square root
of minus one
-/

open IsDedekindDomain MulAction NumberField IntermediateField

namespace InverseGalois.CFT

/- An intermediate field of an extension of the rational numbers carries two structures of an
algebra over the rational numbers, the one it inherits from the ambient field and the one every
field of characteristic zero carries.  The first is the one the theory of embedding problems is
written in, so it is the one instance resolution is asked to prefer here. -/
attribute [local instance 0] DivisionRing.toRatAlgebra

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem over an extension of the rational numbers, whose
obstruction is a coboundary at every ramified finite place, is solvable over a larger extension.**
The factor set of a section of `f`, transported into the units of the rational numbers by the
identification of the kernel with the roots of unity, is a two-cocycle killed by the order of the
kernel; the Albert-Brauer-Hasse-Noether theorem over the rational numbers makes it a coboundary in
the units of the extension, with no condition at the archimedean places. -/
theorem exists_surjective_hom_rat_of_forall_ramified
    {n : ℕ} [NeZero n] {ζ : ℚ} (hζ : IsPrimitiveRoot ζ n)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = n)
    {K : IntermediateField ℚ Ω} [NumberField ↥K] [IsGalois ℚ ↥K]
    {π : Gal(↥K/ℚ) →* H} (hπ : Function.Surjective π)
    {χ : ↥f.ker →* ℚˣ} (hχinj : Function.Injective χ)
    (hχsurj : ∀ y : ℚˣ, y ^ n = 1 → ∃ z : ↥f.ker, χ z = y)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    (hram : ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
      ∃ c : ↥(stabilizer Gal(↥K/ℚ) v) → Additive (v.adicCompletion ↥K)ˣ,
      ∀ s u : ↥(stabilizer Gal(↥K/ℚ) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap ℚ ↥K : ℚ →* ↥K)
          (χ ⟨sectionFactorSet t (π s.1) (π u.1), sectionFactorSet_mem_ker f ht _ _⟩)))
          = smulUnitsAut s (c u) - c (s * u) + c s) :
    HasProperSolution K f π := by
  classical
  set a : Gal(↥K/ℚ) → Gal(↥K/ℚ) → ℚˣ := fun x y =>
    χ ⟨sectionFactorSet t (π x) (π y), sectionFactorSet_mem_ker f ht _ _⟩ with hadef
  have hapow : ∀ x y, a x y ^ n = 1 := by
    intro x y
    rw [hadef]
    exact charFactorSet_pow_eq_one f hcard ht χ π x y
  have hacoc : ∀ x y z : Gal(↥K/ℚ), a y z * a x (y * z) = a (x * y) z * a x y := by
    intro x y z
    rw [hadef]
    exact charFactorSet_cocycle f hZ ht χ π x y z
  obtain ⟨b, hb⟩ :=
    exists_isMulCoboundary_of_forall_ramified (K := ↥K) (NeZero.ne n) hapow hacoc hram
  exact exists_surjective_hom_of_isMulCoboundary hζ hZ hfr hcard hπ hχinj hχsurj ht hb

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem over an extension of the rational numbers which is
solvable over the decomposition group at every ramified finite place is solvable over a larger
extension.**  The only arithmetic input is a homomorphic lift of the restriction of `π` to each
such decomposition group. -/
theorem exists_surjective_hom_rat_of_forall_ramified_lift
    {n : ℕ} [NeZero n] {ζ : ℚ} (hζ : IsPrimitiveRoot ζ n)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = n)
    {K : IntermediateField ℚ Ω} [NumberField ↥K] [IsGalois ℚ ↥K]
    {π : Gal(↥K/ℚ) →* H} (hπ : Function.Surjective π)
    {χ : ↥f.ker →* ℚˣ} (hχinj : Function.Injective χ)
    (hχsurj : ∀ y : ℚˣ, y ^ n = 1 → ∃ z : ↥f.ker, χ z = y)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    (hlift : ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
      ∃ σ : ↥(stabilizer Gal(↥K/ℚ) v) →* G, ∀ s, f (σ s) = π s.1) :
    HasProperSolution K f π := by
  refine exists_surjective_hom_rat_of_forall_ramified hζ hZ hfr hcard hπ hχinj
    hχsurj ht (fun v hv => ?_)
  obtain ⟨σ, hσ⟩ := hlift v hv
  exact exists_local_coboundary_of_exists_lift (k := ℚ) (K := ↥K) hZ ht χ v hσ

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem over an extension of the rational numbers is solvable
over a larger extension as soon as, at every ramified finite place with cyclic decomposition group,
the roots of unity of the rational numbers are locally powers with exponent the order of that
group.** -/
theorem exists_surjective_hom_rat_of_forall_ramified_pow
    {n : ℕ} [NeZero n] {ζ : ℚ} (hζ : IsPrimitiveRoot ζ n)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = n)
    {K : IntermediateField ℚ Ω} [NumberField ↥K] [IsGalois ℚ ↥K]
    {π : Gal(↥K/ℚ) →* H} (hπ : Function.Surjective π)
    {χ : ↥f.ker →* ℚˣ} (hχinj : Function.Injective χ)
    (hχsurj : ∀ y : ℚˣ, y ^ n = 1 → ∃ z : ↥f.ker, χ z = y)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    (hram : ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
      ∃ g : ↥(stabilizer Gal(↥K/ℚ) v),
        (∀ x : ↥(stabilizer Gal(↥K/ℚ) v), x ∈ Subgroup.zpowers g) ∧
        ∀ z : ℚˣ, z ^ n = 1 → ∃ y : (v.adicCompletion ↥K)ˣ,
          (∀ σ : ↥(stabilizer Gal(↥K/ℚ) v), σ • (y : v.adicCompletion ↥K) = y) ∧
            y ^ Nat.card ↥(stabilizer Gal(↥K/ℚ) v)
              = adicUnitHom v (Units.map (algebraMap ℚ ↥K : ℚ →* ↥K) z)) :
    HasProperSolution K f π := by
  refine exists_surjective_hom_rat_of_forall_ramified hζ hZ hfr hcard hπ hχinj
    hχsurj ht (fun v hv => ?_)
  obtain ⟨g, hg, hroot⟩ := hram v hv
  refine exists_sub_add_eq_adicUnits_of_exists_pow (k := ℚ) (K := ↥K) (n := n)
    (a := fun x y => χ ⟨sectionFactorSet t (π x) (π y), sectionFactorSet_mem_ker f ht _ _⟩)
    v hg ?_ ?_ hroot
  · exact fun x y => charFactorSet_pow_eq_one f hcard ht χ π x y
  · exact fun x y z => charFactorSet_cocycle f hZ ht χ π x y z

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem over an extension of the rational numbers is solvable
over a larger extension as soon as every ramified finite place has cyclic decomposition group,
prime residue field, and residue characteristic congruent to one modulo the product of the order of
the kernel with the order of that group.**  This is the shape in which the Scholz-Reichardt
construction supplies the arithmetic, with no parity condition on the order of the kernel. -/
theorem exists_surjective_hom_rat_of_forall_ramified_primeResidue
    {n : ℕ} [NeZero n] {ζ : ℚ} (hζ : IsPrimitiveRoot ζ n)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = n)
    {K : IntermediateField ℚ Ω} [NumberField ↥K] [IsGalois ℚ ↥K]
    {π : Gal(↥K/ℚ) →* H} (hπ : Function.Surjective π)
    {χ : ↥f.ker →* ℚˣ} (hχinj : Function.Injective χ)
    (hχsurj : ∀ y : ℚˣ, y ^ n = 1 → ∃ z : ↥f.ker, χ z = y)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    (hram : ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
      IsCyclic ↥(stabilizer Gal(↥K/ℚ) v) ∧ ∃ p e : ℕ,
        HasResidueChar (v.adicCompletion ↥K) p e ∧
          (∀ x : v.adicCompletion ↥K, Valued.v x ≤ 1 →
            ∃ b : ℤ, Valued.v (x - (b : v.adicCompletion ↥K)) < 1) ∧
          n * Nat.card ↥(stabilizer Gal(↥K/ℚ) v) ∣ p - 1) :
    HasProperSolution K f π := by
  refine exists_surjective_hom_rat_of_forall_ramified_pow hζ hZ hfr hcard hπ hχinj
    hχsurj ht (fun v hv => ?_)
  obtain ⟨hcyc, p, e, h, hres, hnd⟩ := hram v hv
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(stabilizer Gal(↥K/ℚ) v))
  exact ⟨g, hg,
    fun z hz => exists_pow_eq_adicUnitHom_of_mul_dvd (k := ℚ) (K := ↥K) v h hres hnd z hz⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem over an extension of the rational numbers is solvable
over a larger extension as soon as each ramified finite place either carries a homomorphic lift
over its decomposition group or has cyclic decomposition group, prime residue field and residue
characteristic congruent to one modulo the product of the order of the kernel with the order of
that group.**  The congruence on the residue characteristic can never hold at the place above two,
so the two ways of discharging a place are allowed to be mixed, the place above two being handled
by a lift and the places the construction introduces by the congruence. -/
theorem exists_surjective_hom_rat_of_forall_ramified_lift_or_primeResidue
    {n : ℕ} [NeZero n] {ζ : ℚ} (hζ : IsPrimitiveRoot ζ n)
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = n)
    {K : IntermediateField ℚ Ω} [NumberField ↥K] [IsGalois ℚ ↥K]
    {π : Gal(↥K/ℚ) →* H} (hπ : Function.Surjective π)
    {χ : ↥f.ker →* ℚˣ} (hχinj : Function.Injective χ)
    (hχsurj : ∀ y : ℚˣ, y ^ n = 1 → ∃ z : ↥f.ker, χ z = y)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    (hram : ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
      (∃ σ : ↥(stabilizer Gal(↥K/ℚ) v) →* G, ∀ s, f (σ s) = π s.1) ∨
      (IsCyclic ↥(stabilizer Gal(↥K/ℚ) v) ∧ ∃ p e : ℕ,
        HasResidueChar (v.adicCompletion ↥K) p e ∧
          (∀ x : v.adicCompletion ↥K, Valued.v x ≤ 1 →
            ∃ b : ℤ, Valued.v (x - (b : v.adicCompletion ↥K)) < 1) ∧
          n * Nat.card ↥(stabilizer Gal(↥K/ℚ) v) ∣ p - 1)) :
    HasProperSolution K f π := by
  refine exists_surjective_hom_rat_of_forall_ramified hζ hZ hfr hcard hπ hχinj
    hχsurj ht (fun v hv => ?_)
  rcases hram v hv with ⟨σ, hσ⟩ | ⟨hcyc, p, e, h, hres, hnd⟩
  · exact exists_local_coboundary_of_exists_lift (k := ℚ) (K := ↥K) hZ ht χ v hσ
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(stabilizer Gal(↥K/ℚ) v))
    refine exists_sub_add_eq_adicUnits_of_exists_pow (k := ℚ) (K := ↥K) (n := n)
      (a := fun x y => χ ⟨sectionFactorSet t (π x) (π y), sectionFactorSet_mem_ker f ht _ _⟩)
      v hg (fun x y => charFactorSet_pow_eq_one f hcard ht χ π x y)
      (fun x y z => charFactorSet_cocycle f hZ ht χ π x y z)
      fun z hz => exists_pow_eq_adicUnitHom_of_mul_dvd (k := ℚ) (K := ↥K) v h hres hnd z hz

end InverseGalois.CFT
