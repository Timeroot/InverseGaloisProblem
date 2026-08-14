/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.MorseInertia

/-!
# Local monodromy of an equation is bounded by the multiplicities of its fibre

An inertia element at a place of a cover fixes every element of the integral model modulo that
place, so it permutes the roots of a defining equation *within a residue class*.  The roots sharing
a given residue are distinct roots of the equation, so the product of the corresponding linear
factors divides the equation; reducing that divisibility modulo the place exhibits a power of a
single linear factor inside the reduced equation.  The number of roots in a residue class is
therefore at most the multiplicity of that residue as a root of the fibre.

Pigeonholing the powers of an inertia element against that bound gives the main estimate: an inertia
element returns a root to itself after at most `m` steps, where `m` is the multiplicity of its
residue in the fibre.  Consequently, on a cover splitting the equation, an inertia element at a
place over a point whose fibre has all multiplicities at most `m` is killed by `m !`.

Two special cases are worth naming.  A place whose fibre is separable carries no inertia at all, and
a place whose fibre has only double points carries inertia of exponent two.  The second statement is
the branch-cycle input of the Morse theory with the hypothesis "*one* double point" relaxed to "only
double points": the branch cycle at such a point is a product of disjoint transpositions.

## Main results

* `Rigidity.RET.card_le_rootMultiplicity` — a set of roots sharing a residue is no larger than the
  multiplicity of that residue in the reduced equation.
* `Rigidity.RET.exists_pow_smul_eq_self` — an inertia element returns a root to itself in at most
  `rootMultiplicity` many steps.
* `Rigidity.RET.pow_factorial_eq_one_of_rootMultiplicity_le` — an inertia element at a place whose
  fibre has multiplicities at most `m` satisfies `σ ^ Nat.factorial m = 1`.
* `Rigidity.RET.eq_one_of_separable_fibre` — a place with separable fibre is unramified.
* `Rigidity.RET.sq_eq_one_of_rootMultiplicity_le_two` — a place whose fibre has only double points
  carries inertia of exponent two.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

-- the deck group commutes with the coordinate ring of the base on the integral model, so it acts
-- on the roots of an equation living there
attribute [local instance] Rigidity.RET.instSMulCommDeck

variable (L : LineCover) (f : Polynomial (Polynomial k))

/-! ### Counting the roots in a residue class -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **A set of roots of the equation sharing a residue at a place is no larger than the multiplicity
of that residue as a root of the reduced equation.**

The roots are distinct, so the product of the linear factors they cut out divides the equation in
the integral model; modulo the place that product becomes a power of a single linear factor. -/
theorem card_le_rootMultiplicity (hf : f.Monic) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    (s : Finset (Bring L.M)) (hs : ∀ b ∈ s, b ∈ f.rootSet (Bring L.M))
    (x : Bring L.M ⧸ Q) (hx : ∀ b ∈ s, Ideal.Quotient.mk Q b = x) :
    s.card ≤ (f.map (algebraMap (Polynomial k) (Bring L.M ⧸ Q))).rootMultiplicity x := by
  classical
  haveI : IsScalarTower (Polynomial k) (Bring L.M) (Bring L.M ⧸ Q) := inferInstance
  set ψ : Bring L.M →+* Bring L.M ⧸ Q := Ideal.Quotient.mk Q with hψ
  set fB : Polynomial (Bring L.M) := f.map (algebraMap (Polynomial k) (Bring L.M)) with hfB
  have hfB0 : fB ≠ 0 := (hf.map _).ne_zero
  have hD0 : f.map (algebraMap (Polynomial k) (Bring L.M ⧸ Q)) ≠ 0 := (hf.map _).ne_zero
  -- the roots in `s` are genuine roots of the equation in the integral model
  have hroots : ∀ b ∈ s, b ∈ fB.roots := by
    intro b hb
    refine (Polynomial.mem_roots hfB0).mpr ?_
    have h := (Polynomial.mem_rootSet'.mp (hs b hb)).2
    rwa [Polynomial.aeval_def, ← Polynomial.eval_map] at h
  have hle : s.val ≤ fB.roots := (Multiset.le_iff_subset s.nodup).mpr hroots
  -- so the product of their linear factors divides the equation
  have hdvd : (s.val.map fun a => X - C a).prod ∣ fB :=
    (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)).trans
      (Polynomial.prod_multiset_X_sub_C_dvd fB)
  have hmapdvd := Polynomial.map_dvd ψ hdvd
  -- modulo the place that product is a power of one linear factor
  have hLHS : ((s.val.map fun a => X - C a).prod).map ψ
      = (X - C x) ^ Multiset.card s.val := by
    rw [← Polynomial.coe_mapRingHom, map_multiset_prod, Multiset.map_map]
    have hconst : (s.val.map ((⇑(Polynomial.mapRingHom ψ)) ∘ fun a => X - C a))
        = Multiset.replicate (Multiset.card s.val) (X - C x) := by
      rw [← Multiset.map_const']
      refine Multiset.map_congr rfl fun a ha => ?_
      simp [hx a ha]
    rw [hconst, Multiset.prod_replicate]
  have hRHS : fB.map ψ = f.map (algebraMap (Polynomial k) (Bring L.M ⧸ Q)) := by
    rw [hfB, hψ, Polynomial.map_map, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  rw [hLHS, hRHS] at hmapdvd
  exact (Polynomial.le_rootMultiplicity_iff hD0).mpr hmapdvd

/-! ### Reading the multiplicity off the fibre over a point of the line -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The multiplicity of a residue coming from the base is the multiplicity of the corresponding
point in the fibre of the equation. -/
theorem rootMultiplicity_quotient (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] (y : k) :
    (f.map (algebraMap (Polynomial k) (Bring L.M ⧸ Q))).rootMultiplicity
        ((algebraMap (Polynomial k) (Bring L.M ⧸ Q)) (C y))
      = (f.map (evalRingHom t)).rootMultiplicity y := by
  set φ : k →+* Bring L.M ⧸ Q := (algebraMap (Polynomial k) (Bring L.M ⧸ Q)).comp C with hφ
  have hmapD : f.map (algebraMap (Polynomial k) (Bring L.M ⧸ Q))
      = (f.map (evalRingHom t)).map φ := by
    rw [Polynomial.map_map, hφ, ← algebraMap_quotient_eq_comp L t Q]
  rw [hmapD]
  exact (Polynomial.eq_rootMultiplicity_map (p := f.map (evalRingHom t)) φ.injective y).symm

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **Every root of the equation reduces to a point of the fibre.**  The fibre splits over the
algebraically closed base field, so the reduced equation has all its roots among the constants. -/
theorem exists_residue_eq (hf : f.Monic) (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] {b : Bring L.M} (hb : b ∈ f.rootSet (Bring L.M)) :
    ∃ y : k, (f.map (evalRingHom t)).IsRoot y ∧
      (algebraMap (Polynomial k) (Bring L.M ⧸ Q)) (C y) = Ideal.Quotient.mk Q b := by
  classical
  haveI : IsScalarTower (Polynomial k) (Bring L.M) (Bring L.M ⧸ Q) := inferInstance
  set φ : k →+* Bring L.M ⧸ Q := (algebraMap (Polynomial k) (Bring L.M ⧸ Q)).comp C with hφ
  set fib : Polynomial k := f.map (evalRingHom t) with hfib
  have hmapD : f.map (algebraMap (Polynomial k) (Bring L.M ⧸ Q)) = fib.map φ := by
    rw [hfib, Polynomial.map_map, hφ, ← algebraMap_quotient_eq_comp L t Q]
  have hfibmonic : fib.Monic := hf.map _
  -- the residue of the root is a root of the reduced equation
  have hroot : (fib.map φ).IsRoot (Ideal.Quotient.mk Q b) := by
    have h := (Polynomial.mem_rootSet'.mp hb).2
    rw [Polynomial.aeval_def, ← Polynomial.eval_map] at h
    have hmap : (f.map (algebraMap (Polynomial k) (Bring L.M))).map (Ideal.Quotient.mk Q)
        = fib.map φ := by
      rw [Polynomial.map_map, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
        hmapD]
    rw [Polynomial.IsRoot, ← hmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, h, map_zero]
  -- and the roots of the reduced equation are the images of the roots of the fibre
  have hsplit : fib.Splits := IsAlgClosed.splits fib
  have hroots : (fib.map φ).roots = fib.roots.map φ := hsplit.roots_map_of_injective φ.injective
  have hmem : Ideal.Quotient.mk Q b ∈ (fib.map φ).roots :=
    (Polynomial.mem_roots (hfibmonic.map φ).ne_zero).mpr hroot
  rw [hroots] at hmem
  obtain ⟨y, hy, hyb⟩ := Multiset.mem_map.mp hmem
  exact ⟨y, (Polynomial.mem_roots hfibmonic.ne_zero).mp hy, hyb⟩

/-! ### Inertia moves a root inside its residue class -/

set_option synthInstance.maxHeartbeats 800000 in
/-- An inertia element at a place does not change residues there. -/
theorem mk_smul_eq (Q : Ideal (Bring L.M)) {σ : L.deck} (hσ : σ ∈ geomInertia L.M Q)
    (x : Bring L.M) : Ideal.Quotient.mk Q (σ • x) = Ideal.Quotient.mk Q x := by
  rw [← sub_eq_zero, ← RingHom.map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hσ x)

set_option synthInstance.maxHeartbeats 800000 in
/-- Every power of an inertia element preserves residues. -/
theorem mk_pow_smul_eq (Q : Ideal (Bring L.M)) {σ : L.deck} (hσ : σ ∈ geomInertia L.M Q)
    (x : Bring L.M) (i : ℕ) : Ideal.Quotient.mk Q ((σ ^ i) • x) = Ideal.Quotient.mk Q x := by
  induction i with
  | zero => rw [pow_zero, one_smul]
  | succ i ih => rw [pow_succ', mul_smul, mk_smul_eq L Q hσ, ih]

/-- The deck group permutes the roots of the equation inside the integral model. -/
theorem smul_mem_rootSet {σ : L.deck} {b : Bring L.M} (hb : b ∈ f.rootSet (Bring L.M)) :
    σ • b ∈ f.rootSet (Bring L.M) := by
  have h := (σ • (⟨b, hb⟩ : f.rootSet (Bring L.M))).2
  rwa [Polynomial.rootSet.coe_smul] at h

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **An inertia element returns a root to itself in at most `rootMultiplicity` many steps.**

The powers of the element carry the root to roots with the same residue, of which there are at most
`rootMultiplicity` many; two of the first `rootMultiplicity + 1` powers therefore agree on it. -/
theorem exists_pow_smul_eq_self (hf : f.Monic) (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] {σ : L.deck} (hσ : σ ∈ geomInertia L.M Q)
    {b : Bring L.M} (hb : b ∈ f.rootSet (Bring L.M)) {y : k}
    (hy : (algebraMap (Polynomial k) (Bring L.M ⧸ Q)) (C y) = Ideal.Quotient.mk Q b) :
    ∃ p, 0 < p ∧ p ≤ (f.map (evalRingHom t)).rootMultiplicity y ∧ (σ ^ p) • b = b := by
  classical
  set m := (f.map (evalRingHom t)).rootMultiplicity y with hm
  set T : Finset (Bring L.M) := (Finset.range (m + 1)).image (fun i => (σ ^ i) • b) with hT
  have hTroot : ∀ c ∈ T, c ∈ f.rootSet (Bring L.M) := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    exact smul_mem_rootSet L f hb
  have hTres : ∀ c ∈ T, Ideal.Quotient.mk Q c = Ideal.Quotient.mk Q b := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    exact mk_pow_smul_eq L Q hσ b i
  have hcard : T.card ≤ m := by
    have h := card_le_rootMultiplicity L f hf Q T hTroot (Ideal.Quotient.mk Q b) hTres
    rwa [← hy, rootMultiplicity_quotient L f t Q y] at h
  have hlt : T.card < (Finset.range (m + 1)).card := by
    rw [Finset.card_range]; omega
  have hmaps : Set.MapsTo (fun i : ℕ => (σ ^ i) • b) ↑(Finset.range (m + 1)) ↑T := by
    intro i hi
    have hi' : i ∈ Finset.range (m + 1) := hi
    have hmem : (σ ^ i) • b ∈ T := by rw [hT]; exact Finset.mem_image_of_mem _ hi'
    exact hmem
  obtain ⟨i, hi, j, hj, hij, hgij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (f := fun i : ℕ => (σ ^ i) • b) hlt hmaps
  rw [Finset.mem_range] at hi hj
  -- the two agreeing powers differ by a nonzero exponent at most `m`
  have key : ∀ u v : ℕ, u < v → v ≤ m → (σ ^ u) • b = (σ ^ v) • b →
      ∃ p, 0 < p ∧ p ≤ m ∧ (σ ^ p) • b = b := by
    intro u v huv hvm h
    refine ⟨v - u, by omega, by omega, ?_⟩
    have hsplit : σ ^ v = σ ^ u * σ ^ (v - u) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_smul] at h
    exact (MulAction.injective (σ ^ u)) h.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h (by omega) hgij
  · exact key j i h (by omega) hgij.symm

/-! ### Killing the inertia group -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **An inertia element at a place whose fibre has all multiplicities at most `m` is killed by
`m !`.** -/
theorem pow_factorial_eq_one_of_rootMultiplicity_le (hf : f.Monic)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly f)]
    (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP t)]
    (m : ℕ) (hm : ∀ y : k, (f.map (evalRingHom t)).rootMultiplicity y ≤ m)
    {σ : L.deck} (hσ : σ ∈ geomInertia L.M Q) : σ ^ Nat.factorial m = 1 := by
  classical
  refine toPermHom_injective L f hf (Equiv.ext fun b => ?_)
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply]
  refine Subtype.ext ?_
  rw [Polynomial.rootSet.coe_smul, one_smul]
  obtain ⟨y, _, hy⟩ := exists_residue_eq L f hf t Q b.2
  obtain ⟨p, hp0, hpm, hpb⟩ := exists_pow_smul_eq_self L f hf t Q hσ b.2 hy
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hp0 (hpm.trans (hm y))
  have hpow : ∀ r : ℕ, ((σ ^ p) ^ r) • (b : Bring L.M) = (b : Bring L.M) := by
    intro r
    induction r with
    | zero => rw [pow_zero, one_smul]
    | succ r ih => rw [pow_succ, mul_smul, hpb, ih]
  rw [hq, pow_mul]
  exact hpow q

set_option maxHeartbeats 400000 in
/-- **A place whose fibre is separable is unramified.** -/
theorem eq_one_of_separable_fibre (hf : f.Monic)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly f)]
    (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP t)]
    (hm : ∀ y : k, (f.map (evalRingHom t)).rootMultiplicity y ≤ 1)
    {σ : L.deck} (hσ : σ ∈ geomInertia L.M Q) : σ = 1 := by
  have h := pow_factorial_eq_one_of_rootMultiplicity_le L f hf t Q 1 hm hσ
  rwa [Nat.factorial_one, pow_one] at h

set_option maxHeartbeats 400000 in
/-- **A place whose fibre has only double points carries inertia of exponent two**: the branch cycle
there is a product of disjoint transpositions. -/
theorem sq_eq_one_of_rootMultiplicity_le_two (hf : f.Monic)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly f)]
    (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP t)]
    (hm : ∀ y : k, (f.map (evalRingHom t)).rootMultiplicity y ≤ 2)
    {σ : L.deck} (hσ : σ ∈ geomInertia L.M Q) : σ * σ = 1 := by
  have h := pow_factorial_eq_one_of_rootMultiplicity_le L f hf t Q 2 hm hσ
  rwa [show Nat.factorial 2 = 2 from rfl, pow_two] at h

set_option maxHeartbeats 400000 in
/-- **The order of an inertia element divides `m !`** when the fibre has all multiplicities at most
`m`. -/
theorem orderOf_dvd_factorial_of_rootMultiplicity_le (hf : f.Monic)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly f)]
    (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP t)]
    (m : ℕ) (hm : ∀ y : k, (f.map (evalRingHom t)).rootMultiplicity y ≤ m)
    {σ : L.deck} (hσ : σ ∈ geomInertia L.M Q) : orderOf σ ∣ Nat.factorial m :=
  orderOf_dvd_of_pow_eq_one (pow_factorial_eq_one_of_rootMultiplicity_le L f hf t Q m hm hσ)

set_option maxHeartbeats 400000 in
/-- **The inertia group at such a place has order dividing `m !`.**  Geometric inertia groups are
cyclic, so the bound on a generator bounds the whole group. -/
theorem card_geomInertia_dvd_factorial (hf : f.Monic)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly f)]
    (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP t)]
    (m : ℕ) (hm : ∀ y : k, (f.map (evalRingHom t)).rootMultiplicity y ≤ m) :
    Nat.card (geomInertia L.M Q) ∣ Nat.factorial m := by
  obtain ⟨g, hg⟩ := (isCyclic_geomInertia L.M t Q).exists_generator
  have htop : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' _).mpr hg
  have hcard : Nat.card (geomInertia L.M Q) = orderOf g := by
    rw [← Nat.card_zpowers g, htop, Subgroup.card_top]
  have hord : orderOf (g : L.deck) ∣ Nat.factorial m :=
    orderOf_dvd_factorial_of_rootMultiplicity_le L f hf t Q m hm g.2
  rwa [hcard, ← Subgroup.orderOf_coe g]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **An inertia element fixes every root lying over a simple point of the fibre.** -/
theorem smul_eq_self_of_rootMultiplicity_eq_one (hf : f.Monic) (t : k) (Q : Ideal (Bring L.M))
    [Q.IsMaximal] [Q.LiesOver (placeP t)] {σ : L.deck} (hσ : σ ∈ geomInertia L.M Q)
    {b : Bring L.M} (hb : b ∈ f.rootSet (Bring L.M)) {y : k}
    (hy : (algebraMap (Polynomial k) (Bring L.M ⧸ Q)) (C y) = Ideal.Quotient.mk Q b)
    (hmult : (f.map (evalRingHom t)).rootMultiplicity y ≤ 1) : σ • b = b := by
  obtain ⟨p, hp0, hpm, hpb⟩ := exists_pow_smul_eq_self L f hf t Q hσ hb hy
  have hp1 : p = 1 := by omega
  rwa [hp1, pow_one] at hpb

end Rigidity.RET

end
