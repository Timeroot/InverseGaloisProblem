/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.AdicUnramified
import InverseGalois.CFT.Brauer.UnramifiedRelative
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Local.CyclicNormIndex
import InverseGalois.CFT.Local.NormValued

/-!
# The relative Brauer group of a local field has the order of the degree

Every Brauer class over a field which is complete, discretely valued and locally compact is split
by a cyclic extension all of whose absolute values are absolute values of scalars.  Such an
extension is again complete, discretely valued and locally compact, for the valuation carried by
the field norm, and it is unramified over the base.  The relative Brauer group of an unramified
cyclic extension of local fields is the units of the base field modulo the norms, and that quotient
is the integers modulo the degree.

So every Brauer class over a local field lies in a relative Brauer group of exactly the order of
the degree of the extension: the local invariant map has a source of the expected size.

Unramifiedness is in fact not needed for the count.  The relative Brauer group of any cyclic
extension is the units of the base field modulo the norms, and the norm index of a cyclic extension
of a local field is the degree whatever the ramification is, so the relative Brauer group of an
arbitrary cyclic extension of a local field already has the order of the degree.

## Main results

* `InverseGalois.CFT.card_relative_eq_finrank_of_spectralNorm`: **the relative Brauer group of an
  unramified cyclic extension of a complete, discretely valued, locally compact field has the order
  of the degree.**
* `InverseGalois.CFT.card_relative_eq_finrank_local`: **the relative Brauer group of an arbitrary
  cyclic extension of such a field has the order of the degree**, with no condition on the
  ramification.
* `InverseGalois.CFT.exists_cyclic_relative_card_eq_finrank`: **every Brauer class over such a field
  lies in a relative Brauer group of the order of the degree.**
* `InverseGalois.CFT.exists_cyclic_relative_card_eq_finrank_adicCompletion`: the same for the
  completion of a number field at a finite place.

## Tags

Brauer group, relative Brauer group, local field, unramified extension, invariant map,
class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [Field L] [Algebra K L] [FiniteDimensional K L] {p e : ℕ}

/-! ### The order of a relative Brauer group -/

/-- **The relative Brauer group of an unramified cyclic extension of a complete, discretely valued,
locally compact field has the order of the degree.**  The extension inherits everything a local
field is asked for, so the units of the base field modulo the norms are the integers modulo the
degree. -/
theorem card_relative_eq_finrank_of_spectralNorm [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hres : HasResidueChar K p e)
    (hval : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖) :
    Nat.card ↥(BrauerGroup.relative K L) = finrank K L := by
  obtain ⟨u, hu0, hu1⟩ := Valuation.RankOne.nontrivial (Valued.v : Valuation K ℤᵐ⁰)
  have hnt : ∃ x : Kˣ, Valued.v (x : K) ≠ 1 :=
    ⟨Units.mk0 u fun h => hu0 (by rw [h, map_zero]), hu1⟩
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  obtain ⟨instV, instC, m, e', hv, hres', hgr, hur, hm⟩ :=
    exists_valued_of_spectralNorm K L hres hnt hval
  letI := instV
  haveI := instC
  exact card_relative_eq_finrank_of_unramified hv hres' hgr hur hm hσ₀

/-! ### An arbitrary cyclic extension -/

/-- **The relative Brauer group of a cyclic extension of a complete, discretely valued, locally
compact field has the order of the degree**, with no condition on the ramification.  The relative
Brauer group of a cyclic extension is the units of the base field modulo the norms, and the norm
index of a cyclic extension of a local field is the degree. -/
theorem card_relative_eq_finrank_local [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hres : HasResidueChar K p e) :
    Nat.card ↥(BrauerGroup.relative K L) = finrank K L := by
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  rw [← Nat.card_congr (cyclicBrauerEquiv hσ₀).toEquiv, ← Subgroup.index_eq_card,
    index_normSubgroup_eq_finrank_local K L hres]

/-! ### Every Brauer class -/

variable (K) in
/-- **Every Brauer class over a complete, discretely valued, locally compact field lies in a
relative Brauer group of the order of the degree.**  The class is split by a cyclic extension all
of whose absolute values are absolute values of scalars, and such an extension is unramified. -/
theorem exists_cyclic_relative_card_eq_finrank (hres : HasResidueChar K p e) (x : BrauerGroup K) :
    ∃ (M : Type) (_ : Field M) (_ : Algebra K M), FiniteDimensional K M ∧ IsGalois K M ∧
      IsCyclic (M ≃ₐ[K] M) ∧ x ∈ BrauerGroup.relative K M ∧
        Nat.card ↥(BrauerGroup.relative K M) = finrank K M := by
  obtain ⟨M, hMfield, hMalg, hMfin, hgal, hcyc, hval, hmem⟩ :=
    exists_cyclic_unramified_mem_relative K x
  letI : Field M := hMfield
  letI : Algebra K M := hMalg
  haveI : FiniteDimensional K M := hMfin
  haveI : IsGalois K M := hgal
  haveI : IsCyclic (M ≃ₐ[K] M) := hcyc
  exact ⟨M, hMfield, hMalg, hMfin, hgal, hcyc, hmem,
    card_relative_eq_finrank_of_spectralNorm hres hval⟩

/-! ### The completion of a number field at a finite place -/

section NumberField

open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

/-- **Every Brauer class over the completion of a number field at a finite place lies in a relative
Brauer group of the order of the degree.**  Such a completion is complete, discretely valued and
locally compact, and it has a residue characteristic. -/
theorem exists_cyclic_relative_card_eq_finrank_adicCompletion
    (x : BrauerGroup (w.adicCompletion F)) :
    ∃ (M : Type) (_ : Field M) (_ : Algebra (w.adicCompletion F) M),
      FiniteDimensional (w.adicCompletion F) M ∧ IsGalois (w.adicCompletion F) M ∧
        IsCyclic (M ≃ₐ[w.adicCompletion F] M) ∧
        x ∈ BrauerGroup.relative (w.adicCompletion F) M ∧
          Nat.card ↥(BrauerGroup.relative (w.adicCompletion F) M)
            = finrank (w.adicCompletion F) M := by
  obtain ⟨p, e, hres⟩ := exists_hasResidueChar_adicCompletion (K := F) w
  exact exists_cyclic_relative_card_eq_finrank _ hres x

end NumberField

end InverseGalois.CFT
