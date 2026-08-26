import Mathlib
import InverseGalois.CFT.Brauer.SolvableBound
import InverseGalois.CFT.Tate.BrauerRelative

/-!
# The norm index bounds the relative Brauer group of a solvable extension

The relative Brauer group of a cyclic extension is the quotient of the base units by the norms, so
the hypothesis carried through the dévissage of a solvable extension can be stated without any
mention of algebras: it is the assertion that the index of the norm subgroup of a cyclic extension
is finite and at most the degree.  That assertion is the counting half of the first inequality of
class field theory, and for local fields it is where the whole computation of the Brauer group
begins.

## Main definitions

* `InverseGalois.CFT.HasCyclicNormIndexBound`: for every cyclic extension of a field of the class,
  the norm subgroup has finite index at most the degree.

## Main results

* `InverseGalois.CFT.hasCyclicBrauerBound_of_normIndex`: the norm index bound gives the bound on
  the relative Brauer group of a cyclic extension.
* `InverseGalois.CFT.card_relative_le_finrank_of_isSolvable_of_normIndex`: **the norm index bound
  for cyclic extensions bounds the relative Brauer group of every solvable extension by its
  degree.**

## Tags

Brauer group, relative Brauer group, norm index, solvable, class field theory
-/

open Module

namespace InverseGalois.CFT

/-- **The norm index bound** for the cyclic extensions of the fields of a class `P`: the norm
subgroup of such an extension has finite index, and that index is at most the degree. -/
def HasCyclicNormIndexBound (P : Type → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E],
    P F → IsCyclic (E ≃ₐ[F] E) →
      (normSubgroup F E).index ≠ 0 ∧ (normSubgroup F E).index ≤ finrank F E

variable {P : Type → Prop}

/-- **The relative Brauer group of a cyclic extension is the units modulo the norms**, so the norm
index bound is exactly the bound on that Brauer group. -/
theorem hasCyclicBrauerBound_of_normIndex (h : HasCyclicNormIndexBound P) :
    BrauerGroup.HasCyclicBrauerBound P := by
  intro F E _ _ _ _ _ hF hcyc
  haveI := hcyc
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  obtain ⟨hne, hle⟩ := h F E hF hcyc
  have hcard : Nat.card ↥(BrauerGroup.relative F E) = (normSubgroup F E).index :=
    card_brauerRelative_eq_index_normSubgroup hσ₀
  have hne' : Nat.card ↥(BrauerGroup.relative F E) ≠ 0 := by rw [hcard]; exact hne
  exact ⟨(Nat.card_ne_zero.mp hne').2, by rw [hcard]; exact hle⟩

/-- **The norm index bound for cyclic extensions bounds the relative Brauer group of a solvable
extension by its degree.**  This is the counting half of the computation of the Brauer group of a
local field: every Galois group of a local field is solvable, so the whole bound rests on the norm
index of a cyclic extension. -/
theorem card_relative_le_finrank_of_isSolvable_of_normIndex
    (hclosed : BrauerGroup.IsFiniteExtensionClosed P) (h : HasCyclicNormIndexBound P)
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hK : P K) (hsolv : IsSolvable (L ≃ₐ[K] L)) :
    Finite ↥(BrauerGroup.relative K L) ∧
      Nat.card ↥(BrauerGroup.relative K L) ≤ finrank K L :=
  BrauerGroup.card_relative_le_finrank_of_isSolvable hclosed
    (hasCyclicBrauerBound_of_normIndex h) K L hK hsolv

end InverseGalois.CFT
