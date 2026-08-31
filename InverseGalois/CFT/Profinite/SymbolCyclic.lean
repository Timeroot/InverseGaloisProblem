/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.Cyclic
import InverseGalois.CFT.Profinite.Symbol

/-!
# The power symbol as a cyclic two cocycle

The symbol of two units of a base containing a primitive `n`-th root of unity is the cup product of
their Kummer classes.  The Kummer class of a unit is a character of the Galois group with values in
the residues modulo `n`, and the chosen `n`-th root of the first unit, raised to the character of
the second, is a one cochain in the units of the extension.  Its coboundary is the cup product of
the two Kummer cochains times an explicit two cocycle: the one taking the value the first unit
exactly when the character of the second at the two arguments adds up to at least `n`, and the
value one otherwise.

That two cocycle has exactly the shape of `InverseGalois.CFT.cyclicCocycle`, with the character of
the second unit in place of the discrete logarithm.  So in the second cohomology the symbol is the
inverse of the class of a cyclic two cocycle, which is what makes the symbol computable: its values
are read off from the norms of the corresponding cyclic extension.

## Main definitions

* `InverseGalois.CFT.kummerRootUnit`: a primitive `n`-th root of unity of the base, read in the
  units of the extension.
* `InverseGalois.CFT.kummerChar`: **the Kummer character of a unit of the base.**
* `InverseGalois.CFT.kummerCyclicCocycle`: **the cyclic two cocycle of a pair of units.**
* `InverseGalois.CFT.kummerCyclicCochain`: the one cochain comparing the symbol with the cyclic two
  cocycle.

## Main results

* `InverseGalois.CFT.isMulCocycle₂_kummerCyclicCocycle`: the cyclic two cocycle of a pair of units
  is a two cocycle.
* `InverseGalois.CFT.smul_root_eq_kummerRootUnit_pow`: an automorphism multiplies the chosen root
  of a unit by the root of unity that its Kummer character names.
* `InverseGalois.CFT.coboundary₂_kummerCyclicCochain`: **the coboundary of the comparison cochain
  is the cup product of the two Kummer cochains times the cyclic two cocycle.**
* `InverseGalois.CFT.kummerSymbolUnits_mul_smoothH2Mk_eq_one`: **the symbol of two units of the
  base is the inverse of the class of their cyclic two cocycle.**

## Tags

Hilbert symbol, norm residue symbol, Kummer theory, cup product, cyclic algebra, Galois cohomology
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### The carry in the exponent of a root -/

section Carry

/-- Dividing the power whose exponent is the sum of the values of two residues by the power whose
exponent is the value of their sum leaves the carry: nothing if the sum of the values is already
reduced, and the whole exponent otherwise. -/
theorem pow_val_add_div {A : Type*} [Group A] {n : ℕ} [NeZero n] (R : A) (x y : ZMod n) :
    R ^ (x.val + y.val) / R ^ (x + y).val = if x.val + y.val < n then 1 else R ^ n := by
  rcases Nat.lt_or_ge (x.val + y.val) n with hlt | hge
  · rw [ZMod.val_add_of_lt hlt, div_self', if_pos hlt]
  · rw [ZMod.val_add_of_le hge, if_neg (Nat.not_lt.2 hge)]
    calc R ^ (x.val + y.val) / R ^ (x.val + y.val - n)
        = R ^ (n + (x.val + y.val - n)) / R ^ (x.val + y.val - n) := by
          rw [Nat.add_sub_cancel' hge]
      _ = R ^ n := by rw [pow_add, mul_div_assoc, div_self', mul_one]

end Carry

/-! ### The Kummer character and the chosen root of unity -/

section SymbolCyclic

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {n : ℕ} [NeZero n]
  {ζ : k} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction

/-- The Galois group acts smoothly on the residues modulo `n`, the action being trivial. -/
local instance isSmoothAction_zmod : IsSmoothAction Gal(Ω/k) (Multiplicative (ZMod n)) :=
  ⟨⟨⊤, isOpenNormal_top, fun _ _ _ => rfl⟩⟩

variable (Ω hζ) in
/-- A primitive `n`-th root of unity of the base, read in the units of the extension. -/
noncomputable def kummerRootUnit : Ωˣ :=
  Units.map (algebraMap k Ω : k →* Ω) (primitiveRootUnit hζ)

omit [IsGalois k Ω] in
/-- The chosen root of unity of the extension is an `n`-th root of unity. -/
theorem kummerRootUnit_pow_eq_one : kummerRootUnit Ω hζ ^ n = 1 := by
  show Units.map (algebraMap k Ω : k →* Ω) (primitiveRootUnit hζ) ^ n = 1
  rw [← map_pow, (isPrimitiveRoot_primitiveRootUnit hζ).pow_eq_one, map_one]

variable (h : IsKummerData k Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

omit [IsGalois k Ω] in
/-- The coefficients of the Kummer situation are the powers of the chosen root of unity. -/
theorem unitsHom_eq_kummerRootUnit_pow (m : Multiplicative (ZMod n)) :
    h.unitsHom m = kummerRootUnit Ω hζ ^ m.toAdd.val := by
  rw [h.unitsHom_apply, zmodRootHom_apply, map_pow]
  rfl

/-- **The Kummer character of a unit of the base**: the value of its Kummer cochain, read as a
residue modulo `n`. -/
noncomputable def kummerChar (a : kˣ) (g : Gal(Ω/k)) : ZMod n := (h.cochain a g).toAdd

theorem kummerChar_apply (a : kˣ) (g : Gal(Ω/k)) :
    kummerChar h a g = (h.cochain a g).toAdd := rfl

/-- **The Kummer character is a character**, the Galois group acting trivially on the residues. -/
theorem kummerChar_mul (a : kˣ) (g g' : Gal(Ω/k)) :
    kummerChar h a (g * g') = kummerChar h a g + kummerChar h a g' := by
  have hc := h.cochain_isMulCocycle₁ a g g'
  rw [h.smul_eq] at hc
  rw [kummerChar_apply, kummerChar_apply, kummerChar_apply, hc, toAdd_mul]
  exact add_comm _ _

/-- **An automorphism multiplies the chosen root of a unit by the root of unity that its Kummer
character names.** -/
theorem smul_root_eq_kummerRootUnit_pow (a : kˣ) (g : Gal(Ω/k)) :
    g • h.root a = kummerRootUnit Ω hζ ^ (kummerChar h a g).val * h.root a := by
  have hspec := h.cochain_spec a g
  rw [zmodRootHom_apply, map_pow] at hspec
  exact div_eq_iff_eq_mul.mp hspec.symm

/-! ### The cyclic two cocycle of a pair of units -/

/-- **The cyclic two cocycle of a pair of units of the base**: it takes the value the first unit
exactly when the Kummer characters of the second at the two arguments add up to at least `n`, and
the value one otherwise. -/
noncomputable def kummerCyclicCocycle (a b : kˣ) : Gal(Ω/k) × Gal(Ω/k) → Ωˣ :=
  fun p => if (kummerChar h b p.1).val + (kummerChar h b p.2).val < n then 1
    else Units.map (algebraMap k Ω : k →* Ω) a

theorem kummerCyclicCocycle_apply (a b : kˣ) (g g' : Gal(Ω/k)) :
    kummerCyclicCocycle h a b (g, g')
      = if (kummerChar h b g).val + (kummerChar h b g').val < n then 1
        else Units.map (algebraMap k Ω : k →* Ω) a := rfl

/-- **The cyclic two cocycle of a pair of units is a two cocycle**, by the carrying identity for
the values of the residues. -/
theorem isMulCocycle₂_kummerCyclicCocycle (a b : kˣ) :
    IsMulCocycle₂ (kummerCyclicCocycle h a b) := by
  intro g g' g''
  have hfix : g • kummerCyclicCocycle h a b (g', g'')
      = kummerCyclicCocycle h a b (g', g'') := by
    rw [kummerCyclicCocycle_apply]
    split_ifs
    · exact smul_one g
    · exact smul_units_algebraMap g a
  rw [hfix]
  simp only [kummerCyclicCocycle_apply, kummerChar_mul]
  exact carry_identity _ _ _ _

/-- The cyclic two cocycle of a pair of units is smooth. -/
theorem isSmooth₂_kummerCyclicCocycle (a b : kˣ) : IsSmooth₂ (kummerCyclicCocycle h a b) := by
  obtain ⟨N, hN, hb⟩ := h.cochain_isSmooth₁ b
  refine ⟨N, hN, fun x y m hm m' hm' => ?_⟩
  have h1 : kummerChar h b (x * m) = kummerChar h b x := by
    rw [kummerChar_apply, kummerChar_apply, hb x m hm]
  have h2 : kummerChar h b (y * m') = kummerChar h b y := by
    rw [kummerChar_apply, kummerChar_apply, hb y m' hm']
  simp only [kummerCyclicCocycle_apply, h1, h2]

/-! ### The comparison of the symbol with the cyclic two cocycle -/

/-- The one cochain comparing the symbol with the cyclic two cocycle: the chosen `n`-th root of the
first unit, raised to the Kummer character of the second. -/
noncomputable def kummerCyclicCochain (a b : kˣ) : Gal(Ω/k) → Ωˣ :=
  fun g => h.root a ^ (kummerChar h b g).val

theorem kummerCyclicCochain_apply (a b : kˣ) (g : Gal(Ω/k)) :
    kummerCyclicCochain h a b g = h.root a ^ (kummerChar h b g).val := rfl

/-- The comparison cochain is smooth. -/
theorem isSmooth₁_kummerCyclicCochain (a b : kˣ) : IsSmooth₁ (kummerCyclicCochain h a b) := by
  obtain ⟨N, hN, hb⟩ := h.cochain_isSmooth₁ b
  refine ⟨N, hN, fun x m hm => ?_⟩
  have h1 : kummerChar h b (x * m) = kummerChar h b x := by
    rw [kummerChar_apply, kummerChar_apply, hb x m hm]
  rw [kummerCyclicCochain_apply, kummerCyclicCochain_apply, h1]

/-- **The coboundary of the comparison cochain is the cup product of the two Kummer cochains times
the cyclic two cocycle.**  The root of unity in the coboundary is the cup product, and the carry in
the exponent of the chosen root is the cyclic two cocycle. -/
theorem coboundary₂_kummerCyclicCochain (a b : kˣ) :
    coboundary₂ (kummerCyclicCochain h a b)
      = coeffMap₂ h.unitsHom (mulCup₁₁ (mulZMod n) (h.cochain a) (h.cochain b))
          * kummerCyclicCocycle h a b := by
  funext p
  obtain ⟨g, g'⟩ := p
  have hZ : kummerRootUnit Ω hζ ^ n = 1 := kummerRootUnit_pow_eq_one
  have hcup : coeffMap₂ h.unitsHom (mulCup₁₁ (mulZMod n) (h.cochain a) (h.cochain b)) (g, g')
      = kummerRootUnit Ω hζ ^ ((kummerChar h a g).val * (kummerChar h b g').val) := by
    rw [coeffMap₂_apply, mulCup₁₁_apply, h.smul_eq, mulZMod_apply,
      unitsHom_eq_kummerRootUnit_pow, toAdd_ofAdd, ← kummerChar_apply h a g,
      ← kummerChar_apply h b g', ZMod.val_mul, pow_mod_of_pow_eq_one hZ]
  have hcob : coboundary₂ (kummerCyclicCochain h a b) (g, g')
      = kummerRootUnit Ω hζ ^ ((kummerChar h a g).val * (kummerChar h b g').val)
        * (h.root a ^ ((kummerChar h b g).val + (kummerChar h b g').val)
            / h.root a ^ (kummerChar h b g + kummerChar h b g').val) := by
    rw [coboundary₂_apply]
    simp only [kummerCyclicCochain_apply, kummerChar_mul]
    rw [smul_pow', smul_root_eq_kummerRootUnit_pow, mul_pow, ← pow_mul, pow_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow]
    abel
  rw [Pi.mul_apply, hcup, hcob, pow_val_add_div, kummerCyclicCocycle_apply]
  congr 1
  split_ifs
  · rfl
  · exact h.root_pow a

/-- **The power symbol of two units of the base is the inverse of the class of their cyclic two
cocycle**, the comparison cochain interpolating between the two. -/
theorem kummerSymbolUnits_mul_smoothH2Mk_eq_one (a b : kˣ) :
    kummerSymbolUnits h (mulZMod n) a b
        * smoothH2Mk (kummerCyclicCocycle h a b) (isMulCocycle₂_kummerCyclicCocycle h a b)
          (isSmooth₂_kummerCyclicCocycle h a b) = 1 := by
  have hC : IsMulCocycle₂
      (coeffMap₂ h.unitsHom (mulCup₁₁ (mulZMod n) (h.cochain a) (h.cochain b))) :=
    isMulCocycle₂_coeffMap₂ h.unitsHom h.unitsHom_equivariant
      (isMulCocycle₂_mulCup₁₁ (mulZMod n) (h.equivariant (mulZMod n))
        (h.cochain_isMulCocycle₁ a) (h.cochain_isMulCocycle₁ b))
  have hS : IsSmooth₂
      (coeffMap₂ h.unitsHom (mulCup₁₁ (mulZMod n) (h.cochain a) (h.cochain b))) :=
    (isSmooth₂_mulCup₁₁ (mulZMod n) (h.cochain_isSmooth₁ a) (h.cochain_isSmooth₁ b)).coeffMap₂
      h.unitsHom
  have hsym : kummerSymbolUnits h (mulZMod n) a b
      = smoothH2Mk (coeffMap₂ h.unitsHom (mulCup₁₁ (mulZMod n) (h.cochain a) (h.cochain b)))
          hC hS := rfl
  rw [hsym, ← smoothH2Mk_mul hC hS (isMulCocycle₂_kummerCyclicCocycle h a b)
      (isSmooth₂_kummerCyclicCocycle h a b), smoothH2Mk_eq_one_iff]
  exact ⟨kummerCyclicCochain h a b, isSmooth₁_kummerCyclicCochain h a b,
    coboundary₂_kummerCyclicCochain h a b⟩

end SymbolCyclic

end InverseGalois.CFT
