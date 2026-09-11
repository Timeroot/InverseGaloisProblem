/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.GlobalPowRepresentatives
import InverseGalois.CFT.Profinite.CharacterRoot
import InverseGalois.CFT.Profinite.SymbolCyclic
import InverseGalois.CFT.Units.DecompositionClosed

/-!
# Every character of a decomposition subgroup is a Kummer character

The stabilizer of a prime of an algebraically closed extension of a number field is a closed
subgroup of the Galois group, so Hilbert's theorem ninety holds for it: a smooth character of it
with values in the roots of unity of the base is the coboundary of a single unit of the extension.
The power of that unit by the order of the roots of unity is then fixed by the stabilizer, and
finitely many units of the base field represent every power class of the elements fixed there, so
the unit differs from an `n`-th root of a unit of the base field by an element fixed by the
stabilizer.  Two `n`-th roots of the same unit have the same coboundary, so the character is the
Kummer character of that unit of the base field, along the whole stabilizer.

Nothing beyond Kummer theory and the finiteness of the power classes of a completion is spent: the
argument never leaves the decomposition subgroup and never names a completion, the passage to the
completion being hidden inside the statement that finitely many units of the base represent the
power classes fixed by the stabilizer.

## Main results

* `InverseGalois.CFT.exists_units_forall_kummerChar_eq_of_stabilizer` — **every smooth character of
  the stabilizer of a prime is the Kummer character of a unit of the base field.**
* `InverseGalois.CFT.exists_units_forall_kummerChar_eq_of_extends` — a character of a subgroup of a
  stabilizer which extends to the whole stabilizer is the Kummer character of a unit of the base
  field.

## Tags

Kummer theory, decomposition group, Hilbert's theorem 90, character, root of unity
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField groupCohomology

open scoped Pointwise

section CharStabilizer

variable {K : Type} {Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [IsAlgClosed Ω] {n : ℕ} [NeZero n] {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

/-- **Every smooth character of the stabilizer of a prime is the Kummer character of a unit of the
base field.**

The character is read in the units of the extension, where it becomes a smooth one cocycle of a
closed subgroup because its values lie in the base and are therefore fixed.  Hilbert's theorem
ninety for a closed subgroup makes it the coboundary of a unit of the extension, whose `n`-th power
the stabilizer fixes; a unit of the base field represents the power class of that power, and
dividing by the correcting factor leaves an `n`-th root of that unit with the same coboundary.  Two
`n`-th roots of the same unit have the same coboundary, so the coboundary of the chosen root is the
character one started with. -/
theorem exists_units_forall_kummerChar_eq_of_stabilizer
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥) (χ : ↥(stabilizer Gal(Ω/K) P) → ZMod n)
    (hχ : ∀ x y : ↥(stabilizer Gal(Ω/K) P), χ (x * y) = χ x + χ y)
    (hsm : ∃ N : Subgroup Gal(Ω/K), IsOpen (N : Set Gal(Ω/K)) ∧
      ∀ x : ↥(stabilizer Gal(Ω/K) P), (x : Gal(Ω/K)) ∈ N → χ x = 0) :
    ∃ a : Kˣ, ∀ x : ↥(stabilizer Gal(Ω/K) P), kummerChar h a (x : Gal(Ω/K)) = χ x := by
  have hAclosed : IsClosed ((stabilizer Gal(Ω/K) P : Subgroup Gal(Ω/K)) : Set Gal(Ω/K)) :=
    isClosed_stabilizer_ideal P
  -- the character, read in the units of the extension
  have hmul : ∀ x y : ↥(stabilizer Gal(Ω/K) P), Multiplicative.ofAdd (χ (x * y))
      = Multiplicative.ofAdd (χ x) * Multiplicative.ofAdd (χ y) := by
    intro x y
    rw [hχ, ofAdd_add]
  set χ' : ↥(stabilizer Gal(Ω/K) P) →* Multiplicative (ZMod n) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (χ x)) hmul with hχ'def
  set u : ↥(stabilizer Gal(Ω/K) P) →* Ωˣ := h.unitsHom.comp χ' with hudef
  have hu' : ∀ x : ↥(stabilizer Gal(Ω/K) P),
      u x = h.unitsHom (Multiplicative.ofAdd (χ x)) := fun _ => rfl
  have huapply : ∀ x : ↥(stabilizer Gal(Ω/K) P), u x
      = Units.map (algebraMap K Ω : K →* Ω)
        (zmodRootHom hζ (Multiplicative.ofAdd (χ x))) := fun _ => rfl
  have hufix : ∀ x y : ↥(stabilizer Gal(Ω/K) P), x • u y = u y := by
    intro x y
    rw [huapply]
    exact Units.ext ((x : Gal(Ω/K)).commutes _)
  have hupow : ∀ x : ↥(stabilizer Gal(Ω/K) P), u x ^ n = 1 := by
    intro x
    rw [hu']
    exact h.unitsHom_pow_eq_one _
  have hcoc : IsMulCocycle₁ (u : ↥(stabilizer Gal(Ω/K) P) → Ωˣ) := by
    intro x y
    rw [_root_.map_mul, hufix, mul_comm]
  have husm : IsSmooth₁ (u : ↥(stabilizer Gal(Ω/K) P) → Ωˣ) := by
    obtain ⟨N, hNopen, hN⟩ := hsm
    refine isSmooth₁_of_isOpenNormal_ker ⟨inferInstance, ?_⟩
    have hop : IsOpen ((N.subgroupOf (stabilizer Gal(Ω/K) P) :
        Subgroup ↥(stabilizer Gal(Ω/K) P)) : Set ↥(stabilizer Gal(Ω/K) P)) := by
      rw [Subgroup.coe_subgroupOf]
      exact hNopen.preimage continuous_subtype_val
    refine Subgroup.isOpen_mono (fun x hx => ?_) hop
    rw [MonoidHom.mem_ker, hu', hN x (Subgroup.mem_subgroupOf.1 hx), ofAdd_zero, _root_.map_one]
  obtain ⟨t, ht⟩ := isMulCoboundary₁_of_isMulCocycle₁_smooth_subgroup hAclosed hcoc husm
  -- the power of the unit the theorem produces is fixed by the stabilizer
  have htn : ∀ x : ↥(stabilizer Gal(Ω/K) P), (x : Gal(Ω/K)) ((t : Ω) ^ n) = (t : Ω) ^ n := by
    intro x
    have hx := ht x
    rw [div_eq_iff_eq_mul] at hx
    have h1 : (x : Gal(Ω/K)) (t : Ω) = ((u x : Ωˣ) : Ω) * (t : Ω) := congrArg Units.val hx
    have h2 : ((u x : Ωˣ) : Ω) ^ n = 1 := by
      have h3 := congrArg Units.val (hupow x)
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h3
    rw [_root_.map_pow, h1, mul_pow, h2, one_mul]
  have ht0 : (t : Ω) ^ n ≠ 0 := pow_ne_zero n t.ne_zero
  obtain ⟨b, c, hcfix, hbc⟩ :=
    exists_units_mul_pow_eq_of_forall_stabilizer_smul_eq (k := K) (NeZero.ne n) hP ht0 htn
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne n), mul_zero] at hbc
    exact ht0 hbc
  set γ : Ωˣ := Units.mk0 c hc0 with hγdef
  have hγval : (γ : Ω) = c := rfl
  have hγfix : ∀ x : ↥(stabilizer Gal(Ω/K) P), x • γ = γ := fun x => Units.ext (hcfix x)
  have hβpow : (t / γ) ^ n = Units.map (algebraMap K Ω : K →* Ω) b := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, hγval, div_pow, hbc, mul_div_assoc,
      div_self (pow_ne_zero n hc0), mul_one]
    rfl
  have hcancel : ∀ p q r : Ωˣ, p / r / (q / r) = p / q := div_div_div_cancel_right
  have hcob : ∀ x : ↥(stabilizer Gal(Ω/K) P), x • (t / γ) / (t / γ) = u x := by
    intro x
    rw [smul_div', hγfix, hcancel]
    exact ht x
  refine ⟨b, fun x => ?_⟩
  have hroot : (t / γ) ^ n = h.root b ^ n := by rw [hβpow, h.root_pow]
  have hkey : (x : Gal(Ω/K)) • h.root b / h.root b = u x :=
    (smul_div_eq_of_pow_eq hζ h.exists_ι_eq hroot (x : Gal(Ω/K))).symm.trans (hcob x)
  have hcs : h.unitsHom (h.cochain b (x : Gal(Ω/K))) = u x :=
    (h.cochain_spec b (x : Gal(Ω/K))).trans hkey
  have hvalχ : h.cochain b (x : Gal(Ω/K)) = Multiplicative.ofAdd (χ x) :=
    h.injective_unitsHom (hcs.trans (hu' x))
  rw [kummerChar_apply, hvalχ]
  rfl

/-- **A character of a subgroup of the stabilizer of a prime which extends to the whole stabilizer
is the Kummer character of a unit of the base field**, the extension being asked to be smooth. -/
theorem exists_units_forall_kummerChar_eq_of_extends
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥) {A : Subgroup Gal(Ω/K)}
    (hA : A ≤ stabilizer Gal(Ω/K) P) {χ : ↥A → ZMod n}
    {ψ : ↥(stabilizer Gal(Ω/K) P) → ZMod n}
    (hψ : ∀ x y : ↥(stabilizer Gal(Ω/K) P), ψ (x * y) = ψ x + ψ y)
    (hψsm : ∃ N : Subgroup Gal(Ω/K), IsOpen (N : Set Gal(Ω/K)) ∧
      ∀ x : ↥(stabilizer Gal(Ω/K) P), (x : Gal(Ω/K)) ∈ N → ψ x = 0)
    (hres : ∀ x : ↥A, χ x = ψ ⟨(x : Gal(Ω/K)), hA x.2⟩) :
    ∃ a : Kˣ, ∀ x : ↥A, kummerChar h a (x : Gal(Ω/K)) = χ x := by
  obtain ⟨a, ha⟩ := exists_units_forall_kummerChar_eq_of_stabilizer h hP ψ hψ hψsm
  exact ⟨a, fun x => (ha ⟨(x : Gal(Ω/K)), hA x.2⟩).trans (hres x).symm⟩

end CharStabilizer

end InverseGalois.CFT
