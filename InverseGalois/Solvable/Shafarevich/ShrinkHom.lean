/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.Generic
import InverseGalois.Solvable.Shafarevich.LayerWord

/-!
# Shrinking a free operator group

The counting step of Shafarevich's construction compares the relatively free operator group on
`r * n` letters with the one on `n` letters.  Reading the large basis as `r` blocks of `n` letters,
a vector of exponents `a : Fin r → ℕ` determines a homomorphism sending the letter in position `i`
of block `k` to the `a k`-th power of the letter `i`.  It commutes with the operator action because
it leaves the operator coordinate of a letter untouched, and it is the map along which a solution
found upstairs is transported downstairs.

Such a homomorphism is surjective as soon as one of the exponents is prime to `ℓ`: in an `ℓ`-group
an element is recovered from a power of itself by taking a further power, so a subgroup containing
the `a k`-th powers of a generating set is already the whole group.  That is the elementary
substitute for the Frattini argument.

## Main definitions

* `InverseGalois.Shafarevich.shrinkHom` — the homomorphism
  `OperatorFree U (r * n) →* OperatorFree U n` attached to a vector of exponents.
* `InverseGalois.Shafarevich.genericShrink` — the homomorphism it induces between the generic
  operator groups.

## Main results

* `InverseGalois.Shafarevich.shrinkHom_comp_freeAut` and
  `InverseGalois.Shafarevich.genericShrink_comp_genericAut` — both homomorphisms are equivariant.
* `InverseGalois.Shafarevich.eq_top_of_pow_mem_coprime` — in an `ℓ`-group, a subgroup containing
  the `m`-th powers of a generating set, with `m` prime to `ℓ`, is everything.
* `InverseGalois.Shafarevich.genericShrink_surjective` — **the shrinking homomorphism between
  generic operator groups is surjective** as soon as one of the exponents is prime to `ℓ`.

## Tags

Shafarevich's theorem, embedding problem, relatively free group, shrinking
-/

namespace InverseGalois.Shafarevich

/-! ### Recovering an element from a power of it -/

section PGroup

variable {P : Type*} [Group P] {ℓ m : ℕ}

/-- In an `ℓ`-group, a subgroup containing an `m`-th power with `m` prime to `ℓ` contains the
element itself. -/
theorem mem_of_pow_mem_coprime (hP : IsPGroup ℓ P) (hm : ℓ.Coprime m) {K : Subgroup P} {g : P}
    (hg : g ^ m ∈ K) : g ∈ K := by
  have key : (hP.powEquiv hm).symm (hP.powEquiv hm g) = g := (hP.powEquiv hm).symm_apply_apply g
  rw [IsPGroup.powEquiv_apply, IsPGroup.powEquiv_symm_apply] at key
  exact key ▸ zpow_mem hg _

/-- In an `ℓ`-group, a subgroup containing the `m`-th powers of a generating set, with `m` prime to
`ℓ`, is the whole group. -/
theorem eq_top_of_pow_mem_coprime (hP : IsPGroup ℓ P) (hm : ℓ.Coprime m) {K : Subgroup P}
    {X : Set P} (hX : Subgroup.closure X = ⊤) (h : ∀ x ∈ X, x ^ m ∈ K) : K = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← hX]
  exact (Subgroup.closure_le K).mpr fun x hx => mem_of_pow_mem_coprime hP hm (h x hx)

end PGroup

/-! ### The shrinking homomorphism -/

section Shrink

variable (U : Type) [Group U] (r n : ℕ)

/-- **The shrinking homomorphism.**  Reading the `r * n` letters as `r` blocks of `n`, it sends the
letter in position `i` of block `k` to the `a k`-th power of the letter `i`, leaving the operator
coordinate alone. -/
def shrinkHom (a : Fin r → ℕ) : OperatorFree U (r * n) →* OperatorFree U n :=
  FreeGroup.lift fun z =>
    FreeGroup.of ((finProdFinEquiv.symm z.1).2, z.2) ^ a (finProdFinEquiv.symm z.1).1

omit [Group U] in
@[simp]
theorem shrinkHom_of (a : Fin r → ℕ) (z : Fin (r * n) × U) :
    shrinkHom U r n a (FreeGroup.of z)
      = FreeGroup.of ((finProdFinEquiv.symm z.1).2, z.2) ^ a (finProdFinEquiv.symm z.1).1 :=
  FreeGroup.lift_apply_of

omit [Group U] in
/-- The value of the shrinking homomorphism on a letter named by its block and its position. -/
theorem shrinkHom_of_block (a : Fin r → ℕ) (k : Fin r) (i : Fin n) (g : U) :
    shrinkHom U r n a (FreeGroup.of (finProdFinEquiv (k, i), g)) = FreeGroup.of (i, g) ^ a k := by
  simp

/-- The shrinking homomorphism is equivariant for the operator action. -/
theorem shrinkHom_comp_freeAut (a : Fin r → ℕ) (u : U) :
    (shrinkHom U r n a).comp
        (freeAut U (r * n) u : OperatorFree U (r * n) →* OperatorFree U (r * n))
      = (freeAut U n u : OperatorFree U n →* OperatorFree U n).comp (shrinkHom U r n a) :=
  FreeGroup.ext_hom _ _ fun z => by simp [map_pow]

/-! ### The induced map on the generic groups -/

variable (S : Type) [Group S]

omit [Group U] in
theorem shrinkHom_ker_le (a : Fin r → ℕ) :
    (testPi U (r * n) S).ker ≤ Subgroup.comap (shrinkHom U r n a) (testPi U n S).ker := by
  intro x hx
  rw [Subgroup.mem_comap, mem_testPi_ker]
  exact fun f => (mem_testPi_ker U (r * n) S).mp hx (f.comp (shrinkHom U r n a))

/-- **The shrinking homomorphism between the generic operator groups.** -/
def genericShrink (a : Fin r → ℕ) : Generic U (r * n) S →* Generic U n S :=
  QuotientGroup.map _ _ (shrinkHom U r n a) (shrinkHom_ker_le U r n S a)

omit [Group U] in
@[simp]
theorem genericShrink_mk (a : Fin r → ℕ) (x : OperatorFree U (r * n)) :
    genericShrink U r n S a (QuotientGroup.mk x) = QuotientGroup.mk (shrinkHom U r n a x) := rfl

/-- The induced homomorphism is equivariant for the operator action. -/
theorem genericShrink_comp_genericAut (a : Fin r → ℕ) (u : U) :
    (genericShrink U r n S a).comp (genericAut U (r * n) S u).toMonoidHom
      = (genericAut U n S u).toMonoidHom.comp (genericShrink U r n S a) := by
  refine MonoidHom.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | _ y =>
    show (QuotientGroup.mk (shrinkHom U r n a (freeAut U (r * n) u y)) : Generic U n S)
      = QuotientGroup.mk (freeAut U n u (shrinkHom U r n a y))
    exact congrArg QuotientGroup.mk (DFunLike.congr_fun (shrinkHom_comp_freeAut U r n a u) y)

/-! ### Surjectivity -/

omit [Group U] in
/-- The classes of the letters generate the generic operator group. -/
theorem closure_range_mk_of :
    Subgroup.closure
        (Set.range fun z : Fin n × U => (QuotientGroup.mk (FreeGroup.of z) : Generic U n S))
      = ⊤ := by
  have h : (fun z : Fin n × U => (QuotientGroup.mk (FreeGroup.of z) : Generic U n S))
      = QuotientGroup.mk' (testPi U n S).ker ∘ FreeGroup.of := rfl
  rw [h, Set.range_comp, ← MonoidHom.map_closure, FreeGroup.closure_range_of,
    ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)

omit [Group U] in
/-- **The shrinking homomorphism between the generic operator groups is surjective** as soon as one
of the exponents is prime to `ℓ`. -/
theorem genericShrink_surjective [Finite U] [Finite S] {ℓ : ℕ} (hS : IsPGroup ℓ S)
    (a : Fin r → ℕ) (k : Fin r) (hk : ℓ.Coprime (a k)) :
    Function.Surjective (genericShrink U r n S a) := by
  rw [← MonoidHom.range_eq_top]
  refine eq_top_of_pow_mem_coprime (isPGroup_generic U n S hS) hk (closure_range_mk_of U n S) ?_
  rintro _ ⟨z, rfl⟩
  exact ⟨QuotientGroup.mk (FreeGroup.of (finProdFinEquiv (k, z.1), z.2)), by simp⟩

end Shrink

end InverseGalois.Shafarevich
