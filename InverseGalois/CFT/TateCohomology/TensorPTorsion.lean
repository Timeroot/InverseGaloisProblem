/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TensorTrivial

/-!
# Tensoring with coefficients killed by a prime

A tensor product one of whose factors is killed by a natural number is killed by that number,
because the number may be moved onto that factor.  If the number is prime to the order of the
group then the complete cohomology is killed both by it and by the order of the group, so it
vanishes; only the Sylow subgroup for that prime can carry anything.

Reducing a representation modulo a natural number becomes an isomorphism after tensoring with a
representation killed by that number: the reduction map stays surjective because tensoring is
right exact, and its kernel is the image of multiplication by the number, which is zero on the
tensor product.  So a representation tensored with coefficients killed by a prime is its reduction
modulo that prime tensored with the same coefficients, and the reduction is killed by the prime;
on the Sylow subgroup for that prime the vanishing of the first cohomology of the reduction is
therefore all that is needed.

When the prime acts without torsion the reduction sits in a short exact sequence whose two other
terms are the representation itself, so a representation with no complete cohomology has a
reduction with no first cohomology and the criterion is met.  Feeding the outcome into the
connecting map of the tensored extension gives the theorem of Tate and Nakayama for coefficients
killed by a prime.

## Main definitions

* `InverseGalois.CFT.Tate.isoOfBijective`: a map of representations with a bijective underlying
  map, as an isomorphism.
* `InverseGalois.CFT.Tate.tensorModNsmulIso`: the reduction modulo a natural number, tensored with
  a representation killed by that number.

## Main results

* `InverseGalois.CFT.Tate.nsmul_tensorObj_eq_zero`: **a tensor product one of whose factors is
  killed by a natural number is killed by that number.**
* `InverseGalois.CFT.Tate.isZero_tateModule_of_nsmul_eq_zero_coprime`: **a representation killed
  by a natural number prime to the order of the group has no complete cohomology.**
* `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj_of_coprime`,
  `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj_of_coprime'`: **a tensor product one of whose
  factors is killed by a natural number prime to the order of the group has no complete
  cohomology.**
* `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj_of_nsmul`: **a representation killed by a
  prime whose restriction to a Sylow subgroup for that prime has no first cohomology has no
  complete cohomology after tensoring with any representation.**
* `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj_of_nsmul_eq_zero`: **a representation whose
  reduction modulo a prime has no first cohomology on a Sylow subgroup for that prime has no
  complete cohomology after tensoring with a representation killed by that prime.**
* `InverseGalois.CFT.Tate.tateNakayamaPTorsionEquiv`: **the theorem of Tate and Nakayama** for
  coefficients killed by a prime.

## Tags

Tate cohomology, cohomologically trivial, tensor product, torsion, Tate-Nakayama
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### Torsion in a tensor product -/

section Torsion

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

omit [Finite G] in
/-- **A tensor product one of whose factors is killed by a natural number is killed by that
number.** -/
theorem nsmul_tensorObj_eq_zero (A M : Rep k G) (m : ℕ) (hM : ∀ v : ↥M.V, m • v = 0) :
    ∀ t : ↥(tensorObj A M).V, m • t = 0 := by
  have h : ∀ t : ↥A.V ⊗[k] ↥M.V, m • t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact smul_zero m
    | tmul a v =>
      rw [← Nat.cast_smul_eq_nsmul k m (a ⊗ₜ[k] v), TensorProduct.smul_tmul',
        TensorProduct.smul_tmul, Nat.cast_smul_eq_nsmul k m v, hM v, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  exact h

omit [Finite G] in
/-- **A tensor product whose first factor is killed by a natural number is killed by that
number.** -/
theorem nsmul_tensorObj_eq_zero' (A M : Rep k G) (m : ℕ) (hA : ∀ v : ↥A.V, m • v = 0) :
    ∀ t : ↥(tensorObj A M).V, m • t = 0 := by
  have h : ∀ t : ↥A.V ⊗[k] ↥M.V, m • t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact smul_zero m
    | tmul a v =>
      rw [← Nat.cast_smul_eq_nsmul k m (a ⊗ₜ[k] v), TensorProduct.smul_tmul',
        Nat.cast_smul_eq_nsmul k m a, hA a, TensorProduct.zero_tmul]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  exact h

/-- **A representation killed by a natural number prime to the order of the group has no complete
cohomology.** -/
theorem isZero_tateModule_of_nsmul_eq_zero_coprime (A : Rep k G) {m : ℕ}
    (hA : ∀ v : ↥A.V, m • v = 0) (hcop : Nat.Coprime m (Nat.card G)) (n : ℤ) :
    Limits.IsZero (tateModule A n) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  have hzero : nsmulHom A m = 0 := by
    ext v
    simpa using hA v
  have h1 : m • x = 0 := by
    rw [← tateMap_nsmulHom_apply A m n x, hzero, tateMap_zero]
    simp
  have h2 : Nat.card G • x = 0 := card_nsmul_eq_zero_tateModule A n x
  have hb : (1 : ℤ) = m * Nat.gcdA m (Nat.card G) + Nat.card G * Nat.gcdB m (Nat.card G) := by
    have h := Nat.gcd_eq_gcd_ab m (Nat.card G)
    rwa [hcop, Nat.cast_one] at h
  refine (one_smul ℤ x).symm.trans ?_
  rw [hb, add_smul, mul_comm (m : ℤ), mul_comm (Nat.card G : ℤ), mul_smul, mul_smul,
    natCast_zsmul, natCast_zsmul, h1, h2, smul_zero, smul_zero, add_zero]

/-- **A tensor product whose second factor is killed by a natural number prime to the order of the
group has no complete cohomology.** -/
theorem isZero_tateModule_tensorObj_of_coprime (A M : Rep k G) {m : ℕ}
    (hM : ∀ v : ↥M.V, m • v = 0) (hcop : Nat.Coprime m (Nat.card G)) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj A M) n) :=
  isZero_tateModule_of_nsmul_eq_zero_coprime _ (nsmul_tensorObj_eq_zero A M m hM) hcop n

/-- **A tensor product whose first factor is killed by a natural number prime to the order of the
group has no complete cohomology.**  This is the vanishing of a local contribution at a place whose
decomposition group has order prime to the exponent of the module sitting there. -/
theorem isZero_tateModule_tensorObj_of_coprime' (A M : Rep k G) {m : ℕ}
    (hA : ∀ v : ↥A.V, m • v = 0) (hcop : Nat.Coprime m (Nat.card G)) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj A M) n) :=
  isZero_tateModule_of_nsmul_eq_zero_coprime _ (nsmul_tensorObj_eq_zero' A M m hA) hcop n

end Torsion

/-! ### The reduction modulo a natural number after tensoring -/

section ModNsmul

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **A map of representations with a bijective underlying map, as an isomorphism.** -/
def isoOfBijective {A B : Rep k G} (Φ : A ⟶ B) (h : Function.Bijective Φ.hom.hom) : A ≅ B :=
  Action.mkIso (LinearEquiv.ofBijective Φ.hom.hom h).toModuleIso fun g =>
    ModuleCat.hom_ext (LinearMap.ext fun a => LinearMap.congr_fun (hom_equivariant Φ g) a)

omit [Finite G] in
/-- **Reducing modulo a natural number stays bijective after tensoring with a representation
killed by that number.** -/
theorem bijective_tensorHomLeft_nsmulSeq_g (A M : Rep k G) (m : ℕ)
    (hM : ∀ v : ↥M.V, m • v = 0) :
    Function.Bijective (tensorHomLeft M (nsmulSeq A m).g).hom.hom := by
  have hex : Function.Exact (nsmulLinear k m ↥A.V)
      (LinearMap.range (nsmulLinear k m ↥A.V)).mkQ :=
    LinearMap.exact_iff.2 (Submodule.ker_mkQ _)
  refine ⟨fun x y hxy => ?_, LinearMap.rTensor_surjective _ (Submodule.mkQ_surjective _)⟩
  have hsub : (tensorHomLeft M (nsmulSeq A m).g).hom.hom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ :=
    (rTensor_exact ↥M.V hex (Submodule.mkQ_surjective _) (x - y)).1 hsub
  have hz' : LinearMap.rTensor ↥M.V (nsmulLinear k m ↥A.V) z = m • z := by
    have hcon := congrArg (fun Φ : tensorObj A M ⟶ tensorObj A M => Φ.hom.hom z)
      (tensorHomLeft_nsmulHom A M m)
    simpa using hcon
  rw [hz', nsmul_tensorObj_eq_zero A M m hM z] at hz
  exact sub_eq_zero.1 hz.symm

/-- **The reduction modulo a natural number, tensored with a representation killed by that
number.** -/
def tensorModNsmulIso (A M : Rep k G) (m : ℕ) (hM : ∀ v : ↥M.V, m • v = 0) :
    tensorObj A M ≅ tensorObj (modNsmul A m) M :=
  isoOfBijective (tensorHomLeft M (nsmulSeq A m).g) (bijective_tensorHomLeft_nsmulSeq_g A M m hM)

omit [Finite G] in
/-- **Restriction to a subgroup commutes with reduction modulo a natural number.** -/
theorem resObj_modNsmul (H : Subgroup G) (A : Rep k G) (m : ℕ) :
    resObj H (modNsmul A m) = modNsmul (resObj H A) m := rfl

/-- **The reduction modulo a natural number acting without torsion has no first cohomology as soon
as the representation has no complete cohomology in the two matching degrees.** -/
theorem isZero_H1_modNsmul (A : Rep k G) (m : ℕ) (htf : ∀ v : ↥A.V, m • v = 0 → v = 0)
    (h1 : Limits.IsZero (tateModule A 1)) (h2 : Limits.IsZero (tateModule A (1 + 1))) :
    Limits.IsZero (groupCohomology (modNsmul A m) 1) :=
  isZero_tateModule_X₃ (nsmulSeq_shortExact A m htf) 1 h1 h2

end ModNsmul

/-! ### Coefficients killed by a prime -/

section PTorsion

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

/-- **A representation over the integers killed by a prime whose restriction to a Sylow subgroup
for that prime has no first cohomology has no complete cohomology after tensoring with any
representation.** -/
theorem isZero_tateModule_tensorObj_of_nsmul (N M : Rep ℤ G) (hN : ∀ v : ↥N.V, p • v = 0)
    (h : ∀ P : Sylow p G, Limits.IsZero (groupCohomology (resObj (P : Subgroup G) N) 1))
    (n : ℤ) : Limits.IsZero (tateModule (tensorObj N M) n) := by
  have key : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, ∀ m : ℤ,
      Limits.IsZero (tateModule (resObj (P : Subgroup G) (tensorObj N M)) m) := by
    intro q hq P m
    haveI : Fact q.Prime := ⟨hq⟩
    rw [resObj_tensorObj]
    rcases eq_or_ne q p with rfl | hne
    · exact isZero_tateModule_tensorObj_of_isZero_H1_int P.isPGroup'
        (resObj (P : Subgroup G) N) hN (h P) (resObj (P : Subgroup G) M) m
    · have hp : p.Prime := Fact.out
      refine isZero_tateModule_of_nsmul_eq_zero_coprime _
        (nsmul_tensorObj_eq_zero' (resObj (P : Subgroup G) N)
          (resObj (P : Subgroup G) M) p hN) ?_ m
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := q)).1 P.isPGroup'
      rw [ha]
      exact Nat.Coprime.pow_right a ((Nat.coprime_primes hp hq).2 (Ne.symm hne))
  exact isZero_tateModule_of_sylow (tensorObj N M)
    (fun q hq P => ⟨0, key q hq P 0, key q hq P 1⟩) n

/-- **A representation over the integers whose reduction modulo a prime has no first cohomology on
a Sylow subgroup for that prime has no complete cohomology after tensoring with a representation
killed by that prime.** -/
theorem isZero_tateModule_tensorObj_of_nsmul_eq_zero (E M : Rep ℤ G)
    (hM : ∀ v : ↥M.V, p • v = 0)
    (hE : ∀ P : Sylow p G,
      Limits.IsZero (groupCohomology (resObj (P : Subgroup G) (modNsmul E p)) 1)) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj E M) n) :=
  isZero_tateModule_of_iso (tensorModNsmulIso E M p hM) n
    (isZero_tateModule_tensorObj_of_nsmul (modNsmul E p) M (nsmul_modNsmul_eq_zero E p) hE n)

/-- **A representation over the integers without torsion at a prime whose restriction to a Sylow
subgroup for that prime has no complete cohomology has none after tensoring with a representation
killed by that prime.** -/
theorem isZero_tateModule_tensorObj_of_torsionFree_nsmul (E M : Rep ℤ G)
    (hM : ∀ v : ↥M.V, p • v = 0) (htf : ∀ v : ↥E.V, p • v = 0 → v = 0)
    (hE : ∀ P : Sylow p G, ∀ i : ℤ,
      Limits.IsZero (tateModule (resObj (P : Subgroup G) E) i)) (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj E M) n) :=
  isZero_tateModule_tensorObj_of_nsmul_eq_zero E M hM
    (fun P => by
      rw [resObj_modNsmul]
      exact isZero_H1_modNsmul (resObj (P : Subgroup G) E) p htf (hE P 1) (hE P (1 + 1))) n

/-- **The theorem of Tate and Nakayama**: for coefficients killed by a prime, the complete
cohomology of a representation in a degree is the complete cohomology of its tensor product with a
representation two degrees higher, as soon as the reduction modulo that prime of the extension
attached to a class in degree two has no first cohomology on a Sylow subgroup for that prime. -/
def tateNakayamaPTorsionEquiv (A : Rep ℤ G) (α : tateModule A 2) (M : Rep ℤ G)
    (hM : ∀ v : ↥M.V, p • v = 0)
    (hE : ∀ P : Sylow p G, Limits.IsZero (groupCohomology (resObj (P : Subgroup G)
      (modNsmul (cocycleObj (shiftObj A) (tateTwoCocycle A α)) p)) 1)) (n : ℤ) :
    tateModule M n ≃ₗ[ℤ] tateModule (tensorObj A M) (n + 1 + 1) :=
  tateNakayamaTwoEquiv A α M
    (fun m => isZero_tateModule_tensorObj_of_nsmul_eq_zero _ M hM hE m) n

end PTorsion

end

end InverseGalois.CFT.Tate
