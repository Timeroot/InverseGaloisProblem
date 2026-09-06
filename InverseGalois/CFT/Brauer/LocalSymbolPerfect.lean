/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.LocalSymbolNondegenerate
import InverseGalois.CFT.TateCohomology.Pontryagin

/-!
# The norm residue symbol of a local field is a perfect pairing

The symbol is trivial on the `n`-th powers in either argument, so it descends to a pairing of the
classes of a local field modulo `n`-th powers with themselves, valued in the rationals modulo the
integers; and it has no kernel on either side.  When the group of classes is **finite** that is
already enough for the pairing to be perfect, because a finite abelian group and its group of
characters have the same number of elements: an injection of the classes into their own character
group between two sets of the same finite size is a bijection.

So every character of the units of a local field which kills the `n`-th powers is the symbol
against a single element, and the element is unique modulo `n`-th powers.  This is local duality in
degree one for the roots of unity, read entirely through the symbol.

The finiteness of the group of classes is a hypothesis here rather than a conclusion, so that the
statement applies verbatim to a completion of a number field at either kind of place, where the
local index formula supplies it.

## Main results

* `InverseGalois.CFT.card_monoidHom_qModZ`: a finite abelian group and its group of characters
  have the same number of elements.
* `InverseGalois.CFT.ker_localSymbolDual`: an element pairs trivially with the whole group of
  classes exactly when it is an `n`-th power.
* `InverseGalois.CFT.injective_localSymbolQuotDual`: the classes inject into their own character
  group.
* `InverseGalois.CFT.surjective_localSymbolDual`,
  `InverseGalois.CFT.bijective_localSymbolQuotDual`: **every character of the classes is the symbol
  against an element.**
* `InverseGalois.CFT.localSymbolQuotEquivDual`: **the classes of a local field modulo `n`-th powers
  are isomorphic to their own character group, by the norm residue symbol.**
* `InverseGalois.CFT.exists_forall_localSymbol_eq`: **a character of the units killing the `n`-th
  powers is the symbol against a single element.**

## Tags

norm residue symbol, Hilbert symbol, local field, perfect pairing, local duality,
Pontryagin duality, class field theory
-/

namespace InverseGalois.CFT

open scoped Valued WithZero

/-! ### Characters of a finite abelian group -/

section Characters

variable {A : Type*} [CommGroup A] [Finite A]

/-- A finite abelian group and its group of characters valued in the rationals modulo the integers
have the same number of elements. -/
theorem card_monoidHom_qModZ : Nat.card (A →* Multiplicative QModZ) = Nat.card A := by
  rw [Nat.card_congr (MonoidHom.toAdditiveLeft (α := A) (β := QModZ))]
  rw [Nat.card_congr (Tate.intLinearEquiv (M := Additive A) (N := QModZ))]
  exact Tate.card_linearDual _

/-- The characters of a finite abelian group are themselves finite in number. -/
theorem finite_monoidHom_qModZ : Finite (A →* Multiplicative QModZ) := by
  have h : 0 < Nat.card (A →* Multiplicative QModZ) := by
    rw [card_monoidHom_qModZ (A := A)]
    exact Nat.card_pos
  exact (Nat.card_pos_iff.1 h).2

end Characters

/-! ### The symbol as a character of the classes modulo powers -/

section Perfect

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e n : ℕ} [NeZero n] {ζ : K}

/-- The symbol against a fixed element, read on the classes modulo `n`-th powers. -/
noncomputable def localSymbolLeftQuot (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (b : Kˣ) :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range →* Multiplicative QModZ :=
  QuotientGroup.lift _ ((localSymbol hres hm hζ).flip b) (by
    rintro _ ⟨c, rfl⟩
    exact localSymbol_eq_one_of_isPow_left hres hm hζ ⟨c, rfl⟩ b)

@[simp]
theorem localSymbolLeftQuot_mk (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (b a : Kˣ) :
    localSymbolLeftQuot hres hm hζ b (a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
      = localSymbol hres hm hζ a b := rfl

/-- The norm residue symbol, read as a map of the units into the characters of the classes modulo
`n`-th powers. -/
noncomputable def localSymbolDual (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) :
    Kˣ →* (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range →* Multiplicative QModZ) where
  toFun := localSymbolLeftQuot hres hm hζ
  map_one' := by
    ext a
    simp
  map_mul' b₁ b₂ := by
    ext a
    simp

/-- **An element pairs trivially with the whole group of classes exactly when it is an `n`-th
power**: the symbol is nondegenerate. -/
theorem ker_localSymbolDual (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) :
    (localSymbolDual hres hm hζ).ker = (powMonoidHom n : Kˣ →* Kˣ).range := by
  ext b
  rw [MonoidHom.mem_ker]
  constructor
  · intro hb
    refine (forall_localSymbol_eq_one_iff_isPow' hres hm hζ b).mp fun a => ?_
    have := congrArg (fun f => f (a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) hb
    simpa using this
  · rintro ⟨c, rfl⟩
    ext a
    simpa using localSymbol_eq_one_of_isPow_right hres hm hζ a ⟨c, rfl⟩

/-- The symbol, read as a map of the classes modulo `n`-th powers into their own character
group. -/
noncomputable def localSymbolQuotDual (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) :
    (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) →*
      ((Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) →* Multiplicative QModZ) :=
  QuotientGroup.lift _ (localSymbolDual hres hm hζ) fun x hx =>
    MonoidHom.mem_ker.mp (by rw [ker_localSymbolDual]; exact hx)

@[simp]
theorem localSymbolQuotDual_mk (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (b a : Kˣ) :
    localSymbolQuotDual hres hm hζ (b : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
      (a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = localSymbol hres hm hζ a b := rfl

/-- **The classes of a local field modulo `n`-th powers inject into their own character group**
under the norm residue symbol. -/
theorem injective_localSymbolQuotDual (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) : Function.Injective (localSymbolQuotDual hres hm hζ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | _ a =>
    rw [QuotientGroup.eq_one_iff, ← ker_localSymbolDual hres hm hζ, MonoidHom.mem_ker]
    exact hx

end Perfect

/-! ### Perfection, when the classes are finite -/

section Finite

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e n : ℕ} [NeZero n] {ζ : K}
  [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]

/-- **Every character of the classes modulo `n`-th powers is the norm residue symbol against a
single element.**  The symbol has no kernel, so the elements inject into the characters modulo
`n`-th powers, and the two groups have the same finite number of elements. -/
theorem surjective_localSymbolDual (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) : Function.Surjective (localSymbolDual hres hm hζ) := by
  haveI := finite_monoidHom_qModZ (A := Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
  rw [← MonoidHom.range_eq_top]
  refine Subgroup.eq_top_of_card_eq _ ?_
  have hq := Nat.card_congr
    (QuotientGroup.quotientKerEquivRange (localSymbolDual hres hm hζ)).toEquiv
  rw [ker_localSymbolDual] at hq
  rw [← hq, card_monoidHom_qModZ (A := Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]

/-- **The norm residue symbol identifies the classes modulo `n`-th powers with their own character
group.** -/
theorem bijective_localSymbolQuotDual (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) : Function.Bijective (localSymbolQuotDual hres hm hζ) := by
  refine ⟨injective_localSymbolQuotDual hres hm hζ, fun χ => ?_⟩
  obtain ⟨b, hb⟩ := surjective_localSymbolDual hres hm hζ χ
  exact ⟨(b : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range), hb⟩

/-- **The norm residue symbol of a local field is a perfect pairing**: the classes modulo `n`-th
powers are isomorphic to their own character group, by pairing against them. -/
noncomputable def localSymbolQuotEquivDual (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) :
    (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ≃*
      ((Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) →* Multiplicative QModZ) :=
  MulEquiv.ofBijective _ (bijective_localSymbolQuotDual hres hm hζ)

@[simp]
theorem localSymbolQuotEquivDual_apply (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (b a : Kˣ) :
    localSymbolQuotEquivDual hres hm hζ (b : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
      (a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = localSymbol hres hm hζ a b := rfl

/-- **A character of the units of a local field which kills the `n`-th powers is the norm residue
symbol against a single element.** -/
theorem exists_forall_localSymbol_eq (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (χ : Kˣ →* Multiplicative QModZ)
    (hχ : ∀ c : Kˣ, χ (c ^ n) = 1) :
    ∃ b : Kˣ, ∀ a : Kˣ, localSymbol hres hm hζ a b = χ a := by
  obtain ⟨b, hb⟩ := surjective_localSymbolDual hres hm hζ
    (QuotientGroup.lift _ χ (by rintro _ ⟨c, rfl⟩; exact hχ c))
  refine ⟨b, fun a => ?_⟩
  have := congrArg (fun f => f (a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) hb
  simpa [localSymbolDual] using this

end Finite

end InverseGalois.CFT
