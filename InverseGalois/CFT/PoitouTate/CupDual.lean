/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicProduct
import InverseGalois.CFT.PoitouTate.Dual

/-!
# The cup product of a class against a class with dual coefficients

Evaluation pairs a module with its Cartier dual, so cupping a one cocycle with values in the module
against a one cocycle with values in the dual gives a two cocycle with values in the coefficients.
This is the pairing that the duality theorems of global arithmetic are about, and it is the same
construction that produces the power residue symbol, with the two factors of the symbol replaced by
a class and a dual class.

Restriction to a subgroup commutes with the pairing, so a class that dies on a family of subgroups
pairs into classes that die on the same family: the pairing carries the everywhere locally trivial
classes of a module and of its dual into the everywhere locally trivial classes of the
coefficients.

Over a number field the coefficients embed in the units of a Galois extension, and there the second
cohomology is the Brauer group, whose invariants add up to zero.  So **the local invariants of the
pairing of a class with a dual class add up to zero over all places**: a product formula for the
pairing, of which the product formula for the power residue symbol is the case where the module and
its dual are both the roots of unity.

## Main definitions

* `InverseGalois.CFT.cupDual`: **the cup product of a class against a class with coefficients in
  the Cartier dual.**
* `InverseGalois.CFT.dualSymbolUnits`: the same pairing, read in the units of a Galois extension of
  a number field.

## Main results

* `InverseGalois.CFT.resH2_cupDual`: the pairing commutes with restriction to a subgroup.
* `InverseGalois.CFT.cupDual_mem_sha2_left`, `InverseGalois.CFT.cupDual_mem_sha2_right`: **the
  pairing of an everywhere locally trivial class is everywhere locally trivial.**
* `InverseGalois.CFT.totalInvariant_smoothBrauerHom_dualSymbolUnits`: **the local invariants of the
  pairing of a class with a dual class multiply to one over all places of a number field.**
* `InverseGalois.CFT.prod_placeInvariant_mul_prod_infinitePlaceInvariant_dualSymbolUnits`: the same,
  read over a finite set of finite places outside which the invariants vanish.

## Tags

Cartier dual, cup product, pairing, Brauer group, local invariant, product formula, duality
-/

namespace InverseGalois.CFT

open CartierDual IsDedekindDomain NumberField groupCohomology

/-! ### The pairing -/

section Pairing

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {A μ : Type*} [CommGroup A] [CommGroup μ]
variable [MulDistribMulAction G A] [MulDistribMulAction G μ]
variable [IsSmoothAction G A] [IsSmoothAction G μ]

variable (A μ) in
/-- **The cup product of a class against a class with coefficients in the Cartier dual**, taken
along evaluation. -/
def cupDual : SmoothH1 G A →* SmoothH1 G (CartierDual A μ) →* SmoothH2 G μ :=
  cupSmoothH1 (evalPairing A μ) fun g a f => evalPairing_smul g a f

/-- **The pairing is computed on cocycles.** -/
theorem cupDual_apply {u : G → A} (hu : IsMulCocycle₁ u) (hus : IsSmooth₁ u)
    {v : G → CartierDual A μ} (hv : IsMulCocycle₁ v) (hvs : IsSmooth₁ v) :
    cupDual A μ (smoothH1Mk u hu hus) (smoothH1Mk v hv hvs)
      = smoothH2Mk (mulCup₁₁ (evalPairing A μ) u v)
          (isMulCocycle₂_mulCup₁₁ _ (fun g a f => evalPairing_smul g a f) hu hv)
          (isSmooth₂_mulCup₁₁ _ hus hvs) := rfl

/-- **The pairing commutes with restriction to a subgroup.** -/
theorem resH2_cupDual (H : Subgroup G) (α : SmoothH1 G A) (β : SmoothH1 G (CartierDual A μ)) :
    resH2 H (cupDual A μ α β)
      = cupSmoothH1 (G := ↥H) (evalPairing A μ)
          (fun h a f => evalPairing_smul (h : G) a f) (resH1 H α) (resH1 H β) :=
  resH2_cupSmoothH1 (evalPairing A μ) (fun g a f => evalPairing_smul g a f) H α β

/-- **The pairing of an everywhere locally trivial class with any dual class is everywhere locally
trivial.** -/
theorem cupDual_mem_sha2_left {S : Set (Subgroup G)} {α : SmoothH1 G A} (hα : α ∈ sha1 A S)
    (β : SmoothH1 G (CartierDual A μ)) : cupDual A μ α β ∈ sha2 μ S :=
  cupSmoothH1_mem_sha2_left (evalPairing A μ) (fun g a f => evalPairing_smul g a f) hα β

/-- **The pairing of any class with an everywhere locally trivial dual class is everywhere locally
trivial.** -/
theorem cupDual_mem_sha2_right {S : Set (Subgroup G)} (α : SmoothH1 G A)
    {β : SmoothH1 G (CartierDual A μ)} (hβ : β ∈ sha1 (CartierDual A μ) S) :
    cupDual A μ α β ∈ sha2 μ S :=
  cupSmoothH1_mem_sha2_right (evalPairing A μ) (fun g a f => evalPairing_smul g a f) α hβ

end Pairing

/-! ### The product formula -/

section ProductFormula

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {A μ : Type} [CommGroup A] [CommGroup μ]
variable [MulDistribMulAction Gal(Ω/k) A] [MulDistribMulAction Gal(Ω/k) μ]
variable [IsSmoothAction Gal(Ω/k) A] [IsSmoothAction Gal(Ω/k) μ]
variable (ιμ : μ →* Ωˣ) (hιμ : ∀ (g : Gal(Ω/k)) (m : μ), ιμ (g • m) = g • ιμ m)

variable (A) in
include hιμ in
/-- **The pairing of a class with a dual class, read in the units of a Galois extension of a number
field.** -/
noncomputable def dualSymbolUnits :
    SmoothH1 Gal(Ω/k) A →* SmoothH1 Gal(Ω/k) (CartierDual A μ) →* SmoothH2 Gal(Ω/k) Ωˣ where
  toFun α := (coeffH2 ιμ hιμ).comp (cupDual A μ α)
  map_one' := by rw [map_one, MonoidHom.comp_one]
  map_mul' α α' := MonoidHom.ext fun β => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, map_mul, MonoidHom.mul_apply]

include hιμ in
/-- **The product formula for the pairing of a class with a dual class over a number field**: the
local invariants of its Brauer class multiply to one over all places. -/
theorem totalInvariant_smoothBrauerHom_dualSymbolUnits (α : SmoothH1 Gal(Ω/k) A)
    (β : SmoothH1 Gal(Ω/k) (CartierDual A μ)) :
    totalInvariant k (smoothBrauerHom (dualSymbolUnits A ιμ hιμ α β)) = 1 :=
  totalInvariant_eq_one_base k _

include hιμ in
/-- **The product formula for the pairing of a class with a dual class over a number field**, read
over a finite set of finite places outside which the invariants vanish. -/
theorem prod_placeInvariant_mul_prod_infinitePlaceInvariant_dualSymbolUnits
    (α : SmoothH1 Gal(Ω/k) A) (β : SmoothH1 Gal(Ω/k) (CartierDual A μ))
    (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hS : ∀ v ∉ S, placeInvariant k v (smoothBrauerHom (dualSymbolUnits A ιμ hιμ α β)) = 1) :
    (∏ v ∈ S, placeInvariant k v (smoothBrauerHom (dualSymbolUnits A ιμ hιμ α β))) *
        ∏ u : InfinitePlace k,
          infinitePlaceInvariant k u (smoothBrauerHom (dualSymbolUnits A ιμ hιμ α β)) = 1 :=
  prod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one k _ S hS

end ProductFormula

end InverseGalois.CFT
