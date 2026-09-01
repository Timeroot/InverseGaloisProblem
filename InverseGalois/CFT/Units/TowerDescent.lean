/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CoboundaryDescent
import InverseGalois.CFT.Units.ABHNCoboundary
import InverseGalois.CFT.Units.CompletionHilbert90
import InverseGalois.CFT.Units.IdeleNormTower
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.CFT.Units.TowerCoboundary

/-!
# Descending a local coboundary along a tower

Let `k ⊆ F ⊆ K` be a tower of number fields with `F` and `K` normal over `k`, let `a` be a family
of units of `k` indexed by pairs of automorphisms of `F` over `k`, and let `w` be a prime of the
integers of `K`.  Composing with the restriction map turns `a` into a family indexed by pairs of
automorphisms of `K` over `k`, and this file descends the local hypothesis of the
Albert-Brauer-Hasse-Noether theorem from `K` to `F`: if the inflated family is a coboundary in the
local units at `w`, then `a` itself is a coboundary in the local units at the prime below.

The descent has three ingredients.  The decomposition group at `w` maps onto the decomposition
group at the prime below, because the Galois group over the middle field already acts transitively
on the primes above a given one.  The local units of the middle field are exactly the local units
of the top field fixed by the kernel of that map, which is the decomposition group of the top field
over the middle one.  And Hilbert's theorem 90 for that kernel lets the trivialising cochain be
corrected so as to be constant on it.  A cochain constant on the kernel and trivialising an
inflated cocycle descends, which is the general descent of a two-coboundary along a surjection.

For relative Brauer groups this is the injectivity of inflation: a local class split by a larger
extension is already split by the smaller one.  It is the converse direction to the transport of
the local hypothesis upwards along the tower.

## Main definitions

* `InverseGalois.CFT.adicUnitsComapHom`: the local units of the base field inside the local units
  at a prime above, written multiplicatively.

## Main results

* `InverseGalois.CFT.stabilizerRestrictPlace_surjective`: **the decomposition group at a prime maps
  onto the decomposition group at the prime of the middle field below it.**
* `InverseGalois.CFT.exists_adicUnitsComapHom_eq_of_ker`: a local unit fixed by the decomposition
  group of the top field over the middle one comes from the completion of the middle field.
* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_descent`: **a family of units of the base field
  whose inflation is a local coboundary at a prime of the top field is a local coboundary at the
  prime of the middle field below it.**

## Tags

number field, tower, completion, decomposition group, two-cocycle, coboundary, inflation,
Hilbert ninety, relative Brauer group
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

open IsDedekindDomain MulAction NumberField groupCohomology

open scoped Pointwise

namespace InverseGalois.CFT

/-! ### The local units of the base field, written multiplicatively -/

section Generic

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

omit [NumberField k] [IsGalois k K] in
/-- **The action of the decomposition group on the units of the completion is the action carried
along the passage to additive notation.** -/
theorem toMul_smulUnitsAut_stabilizer (σ : ↥(stabilizer Gal(K/k) w))
    (u : Additive (w.adicCompletion K)ˣ) :
    Additive.toMul (smulUnitsAut σ u) = σ • Additive.toMul u :=
  Units.ext rfl

variable (k) in
omit [IsGalois k K] in
/-- **The units of the completion of the base field, viewed in the completion at a prime above**,
written multiplicatively. -/
noncomputable def adicUnitsComapHom :
    ((primeUnder (𝓞 k) w).adicCompletion k)ˣ →* (w.adicCompletion K)ˣ :=
  Units.map (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)).toMonoidHom

variable (k) in
omit [IsGalois k K] in
@[simp]
theorem coe_adicUnitsComapHom (u : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
    ((adicUnitsComapHom k w u : (w.adicCompletion K)ˣ) : w.adicCompletion K)
      = algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
        (u : (primeUnder (𝓞 k) w).adicCompletion k) := rfl

variable (k) in
omit [IsGalois k K] in
/-- The multiplicative and the additive readings of the local units of the base field agree. -/
theorem ofMul_adicUnitsComapHom (u : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
    Additive.ofMul (adicUnitsComapHom k w u) = adicUnitsComap k w (Additive.ofMul u) := rfl

variable (k) in
omit [IsGalois k K] in
/-- **The inclusion of the local units of the base field is injective.** -/
theorem adicUnitsComapHom_injective : Function.Injective (adicUnitsComapHom k w) := by
  intro u u' h
  refine Additive.ofMul.injective (adicUnitsComap_injective k w ?_)
  rw [← ofMul_adicUnitsComapHom, ← ofMul_adicUnitsComapHom, h]

end Generic

/-! ### The decomposition groups along a tower -/

section TowerDescent

variable {k F K : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
  [IsGalois k F] [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

omit [NumberField k] [NumberField F] [IsGalois k F] [IsGalois k K] in
/-- The automorphism of a completion attached to an automorphism over the middle field does not
depend on which base field the automorphism is read over. -/
theorem adicCompletionAut_restrictScalars (σ : Gal(K/F)) (hσ : σ • w = w)
    (hσ' : σ.restrictScalars k • w = w) (z : w.adicCompletion K) :
    adicCompletionAut w (σ.restrictScalars k) hσ' z = adicCompletionAut w σ hσ z := rfl

variable (F) in
omit [NumberField k] [NumberField F] in
/-- **The decomposition group at a prime maps onto the decomposition group at the prime of the
middle field below it.**  An automorphism of the middle field fixing the prime there lifts to the
top field; the lift moves the prime above to another prime above the same one, and the Galois group
of the top field over the middle one moves it back. -/
theorem stabilizerRestrictPlace_surjective :
    Function.Surjective (stabilizerRestrictPlace (k := k) F w) := by
  haveI : IsGalois F K := IsGalois.tower_top_of_isGalois k F K
  intro τ
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k)) :=
    AlgEquiv.restrictNormalHom_surjective K
  obtain ⟨σ₀, hσ₀⟩ := hsurj τ.1
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : (σ₀ • w).asIdeal.IsPrime := (σ₀ • w).isPrime
  have h2 := congrArg HeightOneSpectrum.asIdeal (mem_stabilizer_iff.mp τ.2)
  rw [asIdeal_smul, primeUnder_asIdeal] at h2
  have h1 : Ideal.under (𝓞 F) ((σ₀ • w).asIdeal) = Ideal.under (𝓞 F) w.asIdeal := by
    rw [asIdeal_smul, under_smul_ringOfIntegers F, hσ₀]
    exact h2
  obtain ⟨ρ₀, hρ₀⟩ :=
    exists_smul_eq_of_under_eq_ringOfIntegers (F := F) ((σ₀ • w).asIdeal) w.asIdeal h1
  have hstab : (ρ₀.restrictScalars k * σ₀) • w = w := by
    refine HeightOneSpectrum.ext ?_
    rw [asIdeal_smul, mul_smul]
    exact hρ₀.symm
  refine ⟨⟨ρ₀.restrictScalars k * σ₀, mem_stabilizer_iff.mpr hstab⟩, Subtype.ext ?_⟩
  rw [coe_stabilizerRestrict]
  show AlgEquiv.restrictNormalHom F (ρ₀.restrictScalars k * σ₀) = τ.1
  rw [map_mul, restrictNormalHom_restrictScalars k F ρ₀, one_mul, hσ₀]

variable (F) in
omit [NumberField k] in
/-- **A unit of the completion at a prime fixed by the decomposition group of the top field over
the middle field comes from the completion of the middle field at the prime below.**  The elements
of the completion fixed by the whole decomposition group over the middle field are the elements of
the completion of the middle field. -/
theorem exists_adicUnitsComapHom_eq_of_ker (x : (w.adicCompletion K)ˣ)
    (hx : ∀ n : ↥(stabilizerRestrictPlace (k := k) F w).ker,
      (n : ↥(stabilizer Gal(K/k) w)) • x = x) :
    ∃ b : ((primeUnder (𝓞 F) w).adicCompletion F)ˣ, adicUnitsComapHom F w b = x := by
  haveI : IsGalois F K := IsGalois.tower_top_of_isGalois k F K
  have hfix : ∀ σ : ↥(stabilizer Gal(K/F) w),
      smulUnitsAut σ (Additive.ofMul x) = Additive.ofMul x := by
    intro σ
    have hσ : σ.1 • w = w := mem_stabilizer_iff.mp σ.2
    have hσ' : (σ.1.restrictScalars k) • w = w := hσ
    have hker : (⟨σ.1.restrictScalars k, mem_stabilizer_iff.mpr hσ'⟩ :
        ↥(stabilizer Gal(K/k) w)) ∈ (stabilizerRestrictPlace (k := k) F w).ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext (restrictNormalHom_restrictScalars k F σ.1)
    have h : adicCompletionAut w (σ.1.restrictScalars k) hσ' (x : w.adicCompletion K)
        = (x : w.adicCompletion K) := congrArg Units.val (hx ⟨_, hker⟩)
    refine Additive.toMul.injective (Units.ext ?_)
    rw [coe_smulUnitsAut_apply, toMul_ofMul, stabilizer_smul_adicCompletion_def,
      ← adicCompletionAut_restrictScalars (k := k) w σ.1 hσ hσ']
    exact h
  obtain ⟨c, hc⟩ := (mem_range_adicUnitsComap_iff F w (Additive.ofMul x)).mpr hfix
  refine ⟨Additive.toMul c, Additive.ofMul.injective ?_⟩
  rw [ofMul_adicUnitsComapHom, ofMul_toMul]
  exact hc

variable (F) in
omit [NumberField k] [IsGalois k F] [IsGalois k K] in
/-- **A unit of the base field, read in the local units of the top field, is the image of its
reading in the local units of the middle field.** -/
theorem adicUnitsComapHom_adicUnitHom (q : kˣ) :
    adicUnitsComapHom F w (adicUnitHom (primeUnder (𝓞 F) w)
        (Units.map (algebraMap k F : k →* F) q))
      = adicUnitHom w (Units.map (algebraMap k K : k →* K) q) := by
  refine Additive.ofMul.injective ?_
  rw [ofMul_adicUnitsComapHom, adicUnitsComap_adicUnitHom F w, units_map_algebraMap_tower]

/-! ### The descent of the local hypothesis -/

variable (F) in
/-- **A family of units of the base field whose inflation is a local coboundary at a prime of the
top field is a local coboundary at the prime of the middle field below it.**  The decomposition
group above maps onto the decomposition group below, the local units below are the local units
above fixed by the kernel, and Hilbert's theorem 90 for the kernel makes the trivialising cochain
constant there, so the cochain descends. -/
theorem exists_sub_add_eq_adicUnits_descent {a : Gal(F/k) → Gal(F/k) → kˣ}
    (ha : ∀ x y z : Gal(F/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (h : ∃ c : ↥(stabilizer Gal(K/k) w) → Additive (w.adicCompletion K)ˣ,
        ∀ s t : ↥(stabilizer Gal(K/k) w),
          Additive.ofMul (adicUnitHom w (Units.map (algebraMap k K : k →* K)
              (a (AlgEquiv.restrictNormalHom F s.1) (AlgEquiv.restrictNormalHom F t.1))))
            = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ c : ↥(stabilizer Gal(F/k) (primeUnder (𝓞 F) w)) →
          Additive ((primeUnder (𝓞 F) w).adicCompletion F)ˣ,
      ∀ s t : ↥(stabilizer Gal(F/k) (primeUnder (𝓞 F) w)),
        Additive.ofMul (adicUnitHom (primeUnder (𝓞 F) w)
            (Units.map (algebraMap k F : k →* F) (a s.1 t.1)))
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  obtain ⟨c, hc⟩ := h
  -- the units of the base field are fixed by the decomposition group below
  have hfix : ∀ (s : ↥(stabilizer Gal(F/k) (primeUnder (𝓞 F) w))) (q : kˣ),
      s • adicUnitHom (primeUnder (𝓞 F) w) (Units.map (algebraMap k F : k →* F) q)
        = adicUnitHom (primeUnder (𝓞 F) w) (Units.map (algebraMap k F : k →* F) q) := by
    intro s q
    have h := congrArg Additive.toMul
      (smulUnitsAut_adicUnitHom_algebraMap (k := k) (primeUnder (𝓞 F) w) s q)
    rwa [toMul_smulUnitsAut_stabilizer, toMul_ofMul] at h
  -- the embedding of the units of the base field into the local units is multiplicative
  have hmul : ∀ x y : kˣ,
      adicUnitHom (primeUnder (𝓞 F) w) (Units.map (algebraMap k F : k →* F) x)
          * adicUnitHom (primeUnder (𝓞 F) w) (Units.map (algebraMap k F : k →* F) y)
        = adicUnitHom (primeUnder (𝓞 F) w) (Units.map (algebraMap k F : k →* F) (x * y)) := by
    intro x y
    rw [map_mul, map_mul]
  -- the family is a two-cocycle downstairs
  have hcoc : IsMulCocycle₂ (fun p : ↥(stabilizer Gal(F/k) (primeUnder (𝓞 F) w))
      × ↥(stabilizer Gal(F/k) (primeUnder (𝓞 F) w)) =>
        adicUnitHom (primeUnder (𝓞 F) w)
          (Units.map (algebraMap k F : k →* F) (a p.1.1 p.2.1))) := by
    intro g h j
    simp only [Subgroup.coe_mul]
    rw [hfix, hmul, hmul, ha g.1 h.1 j.1]
  -- the inclusion of the local units below intertwines the two actions
  have hjmap : ∀ (s : ↥(stabilizer Gal(K/k) w)) (b : ((primeUnder (𝓞 F) w).adicCompletion F)ˣ),
      s • adicUnitsComapHom F w b
        = adicUnitsComapHom F w (stabilizerRestrictPlace F w s • b) := by
    intro s b
    refine Units.ext ?_
    simp only [val_stabilizer_smul_units, coe_adicUnitsComapHom,
      stabilizer_smul_adicCompletion_def, algebraMap_adicCompletion F w]
    exact adicCompletionAut_adicCompletionComap_restrict F w s.1 (mem_stabilizer_iff.mp s.2) _
  -- the trivialising cochain upstairs, written multiplicatively
  have hcb : coboundary₂ (fun s : ↥(stabilizer Gal(K/k) w) => Additive.toMul (c s))
      = fun p : ↥(stabilizer Gal(K/k) w) × ↥(stabilizer Gal(K/k) w) =>
        adicUnitsComapHom F w (adicUnitHom (primeUnder (𝓞 F) w)
          (Units.map (algebraMap k F : k →* F)
            (a (stabilizerRestrictPlace F w p.1).1 (stabilizerRestrictPlace F w p.2).1))) := by
    funext p
    obtain ⟨s, t⟩ := p
    rw [coboundary₂_apply, adicUnitsComapHom_adicUnitHom F w, coe_stabilizerRestrict,
      coe_stabilizerRestrict]
    have h := congrArg Additive.toMul (hc s t)
    rw [toMul_ofMul, toMul_add, toMul_sub, toMul_smulUnitsAut_stabilizer] at h
    exact h.symm
  obtain ⟨d, hd⟩ := exists_coboundary₂_eq_of_comap
    (stabilizerRestrictPlace_surjective F w) (adicUnitsComapHom_injective F w) hjmap
    (exists_adicUnitsComapHom_eq_of_ker F w)
    (fun e he => isMulCoboundary₁_of_isMulCocycle₁_stabilizer k w _ e he) hcoc hcb
  refine ⟨fun q => Additive.ofMul (d q), fun s t => ?_⟩
  refine Additive.toMul.injective ?_
  rw [toMul_ofMul, toMul_add, toMul_sub, toMul_smulUnitsAut_stabilizer, toMul_ofMul, toMul_ofMul,
    toMul_ofMul]
  have h := congrFun hd (s, t)
  rw [coboundary₂_apply] at h
  exact h.symm

end TowerDescent

end InverseGalois.CFT
