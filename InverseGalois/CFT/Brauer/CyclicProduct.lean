/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.BaseReciprocity
import InverseGalois.CFT.Brauer.PlaceCyclic
import InverseGalois.CFT.Brauer.RatCount
import InverseGalois.CFT.Brauer.SymbolCyclicAlgebra

/-!
# The product formula for the norm residue symbol

Global reciprocity says that the invariants of a Brauer class of a number field multiply to one
over all places.  Read on the classes that carry the arithmetic — the cyclic algebras, and the
power residue symbol whose Brauer class is a cyclic algebra — it becomes the product formula for
the norm residue symbol: the local symbols of a pair of units multiply to one over all places of
the base.  Only finitely many factors differ from one, so the statement can be read either as a
product with finite support over the finite places or as a product over any finite set of finite
places carrying the invariants, times the finitely many archimedean terms.

The same computation identifies the local factor.  The invariant at a finite place of a cyclic
algebra is the local invariant of the cyclic algebra of the decomposition group with the same
coefficient, and the Brauer class of a cyclic algebra is trivial exactly when its coefficient is a
norm.  So the invariant at a finite place vanishes exactly when the coefficient is a norm from the
completion of the splitting field there: the local factor of the product formula measures the
failure of the coefficient to be a local norm.

## Main results

* `InverseGalois.CFT.prod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one`: **the product
  formula**, over a finite set of finite places carrying the invariants.
* `InverseGalois.CFT.totalInvariant_cyclicBrauerHom`: the invariants of a cyclic algebra over a
  number field multiply to one.
* `InverseGalois.CFT.totalInvariant_smoothBrauerHom_kummerSymbolUnits`: **the product formula for
  the power residue symbol of two units of a number field.**
* `InverseGalois.CFT.placeInvariant_cyclicBrauerHom_eq_one_iff`: **the invariant at a finite place
  of a cyclic algebra vanishes exactly when its coefficient is a local norm there.**

## Tags

Brauer group, local invariant, global reciprocity, product formula, norm residue symbol, Hilbert
symbol, cyclic algebra, local norm, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### The product formula -/

section Product

variable (k : Type) [Field k] [NumberField k]

/-- **The product formula for the local invariants of a Brauer class of a number field**, read
over a finite set of finite places outside which they vanish. -/
theorem prod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one (x : BrauerGroup.{0, 0} k)
    (S : Finset (HeightOneSpectrum (𝓞 k))) (h : ∀ v ∉ S, placeInvariant k v x = 1) :
    (∏ v ∈ S, placeInvariant k v x) *
        ∏ u : InfinitePlace k, infinitePlaceInvariant k u x = 1 := by
  rw [← finprod_placeInvariant_eq_prod k x S h, ← totalInvariant_apply]
  exact totalInvariant_eq_one_base k x

/-- **The product formula for the local invariants of a Brauer class of a number field**, read as a
product with finite support over the finite places times the product over the infinite ones. -/
theorem finprod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one (x : BrauerGroup.{0, 0} k) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x) *
        ∏ u : InfinitePlace k, infinitePlaceInvariant k u x = 1 := by
  rw [← totalInvariant_apply]
  exact totalInvariant_eq_one_base k x

end Product

/-! ### The product formula for a cyclic algebra -/

section Cyclic

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

variable (k) in
/-- **The invariants of a cyclic algebra over a number field multiply to one over all places.** -/
theorem totalInvariant_cyclicBrauerHom {σ₀ : Gal(K/k)}
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) (a : kˣ) :
    totalInvariant k (cyclicBrauerHom hσ₀ a) = 1 :=
  totalInvariant_eq_one_base k _

variable (k) in
/-- **The product formula for a cyclic algebra over a number field**, read over a finite set of
finite places outside which the invariants vanish. -/
theorem prod_placeInvariant_mul_prod_infinitePlaceInvariant_cyclicBrauerHom {σ₀ : Gal(K/k)}
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) (a : kˣ)
    (S : Finset (HeightOneSpectrum (𝓞 k)))
    (h : ∀ v ∉ S, placeInvariant k v (cyclicBrauerHom hσ₀ a) = 1) :
    (∏ v ∈ S, placeInvariant k v (cyclicBrauerHom hσ₀ a)) *
        ∏ u : InfinitePlace k, infinitePlaceInvariant k u (cyclicBrauerHom hσ₀ a) = 1 :=
  prod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one k _ S h

end Cyclic

/-! ### The local factor is the obstruction to being a local norm -/

section LocalNorm

attribute [local instance] isGalois_adicCompletion

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

variable (k) in
/-- **The invariant at a finite place of a cyclic algebra vanishes exactly when its coefficient is
a norm from the completion of the splitting field there.**  Base change to the completion turns the
cyclic algebra into the cyclic algebra of the decomposition group with the same coefficient, and
the Brauer class of a cyclic algebra is trivial exactly when its coefficient is a norm. -/
theorem placeInvariant_cyclicBrauerHom_eq_one_iff (w : HeightOneSpectrum (𝓞 K)) {σ₀ : Gal(K/k)}
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) (a : kˣ) :
    placeInvariant k (primeUnder (𝓞 k) w) (cyclicBrauerHom hσ₀ a) = 1 ↔
      ∃ b : (w.adicCompletion K)ˣ,
        Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) (b : w.adicCompletion K)
          = algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (a : k) := by
  obtain ⟨σ, hσ, hres⟩ := exists_forall_mem_zpowers_restrictScalars_eq k w hσ₀
  rw [placeInvariant_eq_one_iff, BrauerGroup.relative, MonoidHom.mem_ker,
    baseChangeHom_cyclicBrauerHom_adicCompletion k w hσ₀ hσ hres a, ← MonoidHom.mem_ker,
    mem_ker_cyclicBrauerHom_iff hσ]
  rfl

end LocalNorm

/-! ### The product formula for the power residue symbol -/

section Symbol

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The invariants of the Brauer class of a smooth second cohomology class of a number field
multiply to one over all places. -/
theorem totalInvariant_smoothBrauerHom (z : SmoothH2 Gal(Ω/k) Ωˣ) :
    totalInvariant k (smoothBrauerHom z) = 1 :=
  totalInvariant_eq_one_base k _

variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M] {ι : M →* kˣ} {n : ℕ}
variable [NeZero n] [IsSmoothAction Gal(Ω/k) M]

/-- **The product formula for the power residue symbol of two units of a number field**: the local
invariants of its Brauer class multiply to one over all places. -/
theorem totalInvariant_smoothBrauerHom_kummerSymbolUnits (h : IsKummerData k Ω M ι n)
    (Φ : M →* M →* M) (a b : kˣ) :
    totalInvariant k (smoothBrauerHom (kummerSymbolUnits h Φ a b)) = 1 :=
  totalInvariant_eq_one_base k _

/-- **The product formula for the power residue symbol of two units of a number field**, read over
a finite set of finite places outside which the invariants vanish. -/
theorem prod_placeInvariant_mul_prod_infinitePlaceInvariant_kummerSymbolUnits
    (h : IsKummerData k Ω M ι n) (Φ : M →* M →* M) (a b : kˣ)
    (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hS : ∀ v ∉ S, placeInvariant k v (smoothBrauerHom (kummerSymbolUnits h Φ a b)) = 1) :
    (∏ v ∈ S, placeInvariant k v (smoothBrauerHom (kummerSymbolUnits h Φ a b))) *
        ∏ u : InfinitePlace k,
          infinitePlaceInvariant k u (smoothBrauerHom (kummerSymbolUnits h Φ a b)) = 1 :=
  prod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one k _ S hS

end Symbol

end InverseGalois.CFT
