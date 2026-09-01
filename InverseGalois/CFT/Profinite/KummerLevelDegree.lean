/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerLevel

/-!
# The degree of the level of a unit

Two automorphisms have the same restriction to the level of a unit exactly when the Kummer
character of the unit takes the same value on them, so the character descends to an *injective*
function on the Galois group of the level.  That function is a homomorphism to the residues modulo
`n`, whence the degree `m` of the level divides `n`.

The descended character therefore has exactly `m` values, each of them killed by `m` because the
group has order `m`; and the residues killed by `m` are exactly the multiples of `t := n / m`, of
which there are `m` as well.  The values are thus all of the multiples of `t`, so some automorphism
of the level has character exactly `t`.  Such an automorphism generates, and the character of an
arbitrary automorphism is `t` times its discrete logarithm to that generator.

This is what the comparison of the power symbol with a cyclic algebra needs, and it needs no
hypothesis on the unit: the carry of the character is the carry of the discrete logarithm, scaled
by `t` on both sides.

## Main results

* `InverseGalois.CFT.levelChar`: **the Kummer character read on the Galois group of the level**,
  injective by `InverseGalois.CFT.levelChar_injective`.
* `InverseGalois.CFT.card_gal_kummerLevel_dvd`: **the degree of the level divides `n`.**
* `InverseGalois.CFT.exists_generator_kummerLevel_index`: **the level of any unit is cyclic, and
  the Kummer character is the discrete logarithm to a suitable generator scaled by the index.**
* `InverseGalois.CFT.carry_iff_of_index`: **the carry condition of the discrete logarithm is the
  carry condition of the character.**

## Tags

Kummer theory, cyclic extension, discrete logarithm, Galois theory, class field theory
-/

namespace InverseGalois.CFT

open groupCohomology IntermediateField

section KummerLevelDegree

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {n : ℕ} [NeZero n]
  {ζ : k} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData k Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-! ### The character read on the Galois group of the level -/

/-- A chosen automorphism of the extension restricting to a given automorphism of the level. -/
noncomputable def levelPreimage (b : kˣ) (σ : Gal(↥(kummerLevel h b)/k)) : Gal(Ω/k) :=
  (restrictNormalHom_surjective_level (kummerLevel h b) σ).choose

/-- The chosen preimage really is a preimage. -/
theorem restrictNormalHom_levelPreimage (b : kˣ) (σ : Gal(↥(kummerLevel h b)/k)) :
    AlgEquiv.restrictNormalHom ↥(kummerLevel h b) (levelPreimage h b σ) = σ :=
  (restrictNormalHom_surjective_level (kummerLevel h b) σ).choose_spec

/-- **The Kummer character of a unit, read on the Galois group of the level of the unit.** -/
noncomputable def levelChar (b : kˣ) (σ : Gal(↥(kummerLevel h b)/k)) : ZMod n :=
  kummerChar h b (levelPreimage h b σ)

/-- The descended character computes the Kummer character. -/
theorem levelChar_restrictNormalHom (b : kˣ) (g : Gal(Ω/k)) :
    levelChar h b (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g) = kummerChar h b g :=
  (restrictNormalHom_kummerLevel_eq_iff h b _ g).mp (by rw [restrictNormalHom_levelPreimage])

/-- The descended character takes the value zero at the identity. -/
theorem levelChar_one (b : kˣ) : levelChar h b 1 = 0 := by
  rw [← map_one (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥(kummerLevel h b)),
    levelChar_restrictNormalHom, kummerChar_one]

/-- The descended character is additive. -/
theorem levelChar_mul (b : kˣ) (σ τ : Gal(↥(kummerLevel h b)/k)) :
    levelChar h b (σ * τ) = levelChar h b σ + levelChar h b τ := by
  obtain ⟨g, rfl⟩ := restrictNormalHom_surjective_level (kummerLevel h b) σ
  obtain ⟨g', rfl⟩ := restrictNormalHom_surjective_level (kummerLevel h b) τ
  rw [← map_mul, levelChar_restrictNormalHom, levelChar_restrictNormalHom,
    levelChar_restrictNormalHom, kummerChar_mul]

/-- The descended character multiplies by the exponent at a power. -/
theorem levelChar_pow (b : kˣ) (σ : Gal(↥(kummerLevel h b)/k)) (j : ℕ) :
    levelChar h b (σ ^ j) = j • levelChar h b σ := by
  induction j with
  | zero => rw [pow_zero, zero_smul, levelChar_one]
  | succ j ih => rw [pow_succ, levelChar_mul, ih, succ_nsmul]

/-- **The descended character is injective**, because two automorphisms of the extension have the
same restriction to the level exactly when the character agrees on them. -/
theorem levelChar_injective (b : kˣ) : Function.Injective (levelChar h b) := by
  intro σ τ hst
  rw [← restrictNormalHom_levelPreimage h b σ, ← restrictNormalHom_levelPreimage h b τ]
  exact (restrictNormalHom_kummerLevel_eq_iff h b _ _).mpr hst

variable (b : kˣ)

/-- The descended character as a homomorphism to the residues modulo `n`. -/
noncomputable def levelCharHom : Gal(↥(kummerLevel h b)/k) →* Multiplicative (ZMod n) where
  toFun σ := Multiplicative.ofAdd (levelChar h b σ)
  map_one' := congrArg Multiplicative.ofAdd (levelChar_one h b)
  map_mul' σ τ := congrArg Multiplicative.ofAdd (levelChar_mul h b σ τ)

variable {b}

/-- **The degree of the level of a unit divides `n`**, because the Galois group of the level embeds
in the residues modulo `n`. -/
theorem card_gal_kummerLevel_dvd (b : kˣ) : Nat.card Gal(↥(kummerLevel h b)/k) ∣ n := by
  have hinj : Function.Injective (levelCharHom h b) := fun σ τ hst => levelChar_injective h b hst
  have hd := Subgroup.card_dvd_of_injective (levelCharHom h b) hinj
  rwa [show Nat.card (Multiplicative (ZMod n)) = n from Nat.card_zmod n] at hd

/-- The degree of the level of a unit kills the Kummer character of that unit. -/
theorem card_nsmul_kummerChar (b : kˣ) (g : Gal(Ω/k)) :
    Nat.card Gal(↥(kummerLevel h b)/k) • kummerChar h b g = 0 := by
  rw [← levelChar_restrictNormalHom h b g, ← levelChar_pow, pow_card_eq_one', levelChar_one]

/-! ### The generator matching the character -/

/-- **The level of any unit is a cyclic extension of degree dividing `n`, generated by an
automorphism whose descended character is the index, and the Kummer character of the unit is the
discrete logarithm to that generator scaled by the index.** -/
theorem exists_generator_kummerLevel_index (b : kˣ) :
    ∃ (σ₀ : Gal(↥(kummerLevel h b)/k)) (t : ℕ),
      (∀ x : Gal(↥(kummerLevel h b)/k), x ∈ Subgroup.zpowers σ₀) ∧
      0 < t ∧
      Nat.card Gal(↥(kummerLevel h b)/k) * t = n ∧
      ∀ g : Gal(Ω/k),
        (kummerChar h b g).val
          = t * (dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)).val := by
  classical
  haveI : Fintype Gal(↥(kummerLevel h b)/k) := AlgEquiv.fintype k ↥(kummerLevel h b)
  set m := Nat.card Gal(↥(kummerLevel h b)/k) with hm
  have hmpos : 0 < m := Nat.card_pos
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmdvd : m ∣ n := card_gal_kummerLevel_dvd h b
  set t := n / m with ht
  have hmt : m * t = n := Nat.mul_div_cancel' hmdvd
  have htpos : 0 < t := Nat.div_pos (Nat.le_of_dvd hnpos hmdvd) hmpos
  have hlt : ∀ j : ℕ, j < m → j * t < n := fun j hj => by
    rw [← hmt]; exact (Nat.mul_lt_mul_right htpos).mpr hj
  -- every value of the descended character is a multiple of the index
  have hdvdval : ∀ σ : Gal(↥(kummerLevel h b)/k), t ∣ (levelChar h b σ).val := by
    intro σ
    have hcast : (((levelChar h b σ).val : ℕ) : ZMod n) = levelChar h b σ :=
      ZMod.natCast_rightInverse _
    have h0 : ((m * (levelChar h b σ).val : ℕ) : ZMod n) = 0 := by
      rw [Nat.cast_mul, hcast, ← nsmul_eq_mul, hm, ← levelChar_pow, pow_card_eq_one',
        levelChar_one]
    have h1 : m * t ∣ m * (levelChar h b σ).val := by
      rw [hmt]; exact (ZMod.natCast_eq_zero_iff _ _).mp h0
    exact (Nat.mul_dvd_mul_iff_left hmpos).mp h1
  -- the values of the descended character are exactly the multiples of the index
  set A : Finset (ZMod n) := Finset.image (levelChar h b) Finset.univ with hA
  set B : Finset (ZMod n) := Finset.image (fun j : ℕ => ((j * t : ℕ) : ZMod n)) (Finset.range m)
    with hB
  have hAcard : A.card = m := by
    rw [hA, Finset.card_image_of_injective _ (levelChar_injective h b), Finset.card_univ, hm,
      Nat.card_eq_fintype_card]
  have hBcard : B.card = m := by
    rw [hB]
    refine (Finset.card_image_of_injOn ?_).trans (Finset.card_range m)
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have hij' : ((i * t : ℕ) : ZMod n) = ((j * t : ℕ) : ZMod n) := hij
    have := congrArg ZMod.val hij'
    rw [ZMod.val_cast_of_lt (hlt i hi), ZMod.val_cast_of_lt (hlt j hj)] at this
    exact Nat.eq_of_mul_eq_mul_right htpos this
  have hAB : A ⊆ B := by
    intro x hx
    rw [hA, Finset.mem_image] at hx
    obtain ⟨σ, -, rfl⟩ := hx
    rw [hB, Finset.mem_image]
    refine ⟨(levelChar h b σ).val / t, Finset.mem_range.mpr ?_, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul htpos).mpr (by rw [hmt]; exact ZMod.val_lt _)
    · show (((levelChar h b σ).val / t * t : ℕ) : ZMod n) = levelChar h b σ
      rw [Nat.div_mul_cancel (hdvdval σ)]
      exact ZMod.natCast_rightInverse _
  have hABeq : A = B := Finset.eq_of_subset_of_card_le hAB (by rw [hAcard, hBcard])
  -- the index itself is such a value
  have htmem : ((t : ℕ) : ZMod n) ∈ A := by
    rw [hABeq, hB, Finset.mem_image]
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1 : t = n := by rw [← hmt, le_antisymm (by omega : m ≤ 1) hmpos, one_mul]
      refine ⟨0, Finset.mem_range.mpr hmpos, ?_⟩
      show ((0 * t : ℕ) : ZMod n) = ((t : ℕ) : ZMod n)
      rw [zero_mul, hm1, Nat.cast_zero, ZMod.natCast_self]
    · refine ⟨1, Finset.mem_range.mpr hm2, ?_⟩
      show ((1 * t : ℕ) : ZMod n) = ((t : ℕ) : ZMod n)
      rw [one_mul]
  rw [hA, Finset.mem_image] at htmem
  obtain ⟨σ₀, -, hσ₀⟩ := htmem
  -- it generates
  have hgen : ∀ x : Gal(↥(kummerLevel h b)/k), x ∈ Subgroup.zpowers σ₀ := by
    intro x
    have hxA : levelChar h b x ∈ A := by
      rw [hA]; exact Finset.mem_image_of_mem (levelChar h b) (Finset.mem_univ x)
    rw [hABeq, hB, Finset.mem_image] at hxA
    obtain ⟨j, -, hj⟩ := hxA
    have hj' : ((j * t : ℕ) : ZMod n) = levelChar h b x := hj
    have hxj : levelChar h b (σ₀ ^ j) = levelChar h b x := by
      rw [levelChar_pow, hσ₀, nsmul_eq_mul, ← Nat.cast_mul, hj']
    rw [← levelChar_injective h b hxj]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ₀) j
  refine ⟨σ₀, t, hgen, htpos, hmt, fun g => ?_⟩
  have hpow : σ₀ ^ (dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)).val
      = AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g := pow_val_dlog hgen _
  have hval : kummerChar h b g
      = (((dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)).val * t : ℕ) : ZMod n) := by
    rw [← levelChar_restrictNormalHom h b g]
    conv_lhs => rw [← hpow]
    rw [levelChar_pow, hσ₀, nsmul_eq_mul, Nat.cast_mul]
  rw [hval, ZMod.val_cast_of_lt (hlt _ (val_dlog_lt σ₀ _)), Nat.mul_comm]

/-! ### The carry condition -/

/-- **The carry condition of the discrete logarithm of a level is the carry condition of the Kummer
character**, as soon as the character is the discrete logarithm scaled by the index. -/
theorem carry_iff_of_index {b : kˣ} {σ₀ : Gal(↥(kummerLevel h b)/k)} {t : ℕ} (htpos : 0 < t)
    (hmt : Nat.card Gal(↥(kummerLevel h b)/k) * t = n)
    (hval : ∀ g : Gal(Ω/k), (kummerChar h b g).val
      = t * (dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)).val)
    (g g' : Gal(Ω/k)) :
    (dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g)).val
        + (dlog σ₀ (AlgEquiv.restrictNormalHom ↥(kummerLevel h b) g')).val
          < Nat.card Gal(↥(kummerLevel h b)/k) ↔
      (kummerChar h b g).val + (kummerChar h b g').val < n := by
  have key : ∀ M N T x y : ℕ, 0 < T → M * T = N → (x + y < M ↔ T * x + T * y < N) := by
    intro M N T x y hT hMN
    subst hMN
    rw [← Nat.mul_add, Nat.mul_comm M T]
    exact (Nat.mul_lt_mul_left hT).symm
  rw [hval g, hval g']
  exact key _ _ _ _ _ htpos hmt

end KummerLevelDegree

end InverseGalois.CFT
