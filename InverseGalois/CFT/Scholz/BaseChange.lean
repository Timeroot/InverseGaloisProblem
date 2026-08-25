/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CompositumBase
import InverseGalois.CFT.CyclotomicCompositum

/-!
# Adjoining the roots of unity without disturbing the Galois group

The local criterion for solving a central embedding problem with kernel of order `n` needs a
primitive `n`-th root of unity in the base field, so the Scholz-Reichardt construction cannot run
over `ℚ`: it runs over `k = ℚ(μ_ℓ)` and descends at the end.  The base change costs nothing on the
Galois side, because the degree of `k` over `ℚ` is `ℓ - 1` while the field being extended has
degree a power of `ℓ`: the two are coprime, so the compositum has the Galois group of the original
field over `k`.

This module fixes the ambient algebraic closure of `ℚ`, takes `k` to be the cyclotomic subfield
`cycSubfield n`, and records the data the criterion asks of its base field: an algebraic closure
above it, and a primitive `n`-th root of unity inside it.

## Main definitions

* `InverseGalois.CFT.cycRootBase`: a primitive `n`-th root of unity in the cyclotomic subfield.
* `InverseGalois.CFT.cycBaseChange`: the compositum of a subfield with the cyclotomic subfield,
  viewed as an extension of the latter.
* `InverseGalois.CFT.galEquivCycBase`: the isomorphism of Galois groups produced by the base
  change.

## Main results

* `InverseGalois.CFT.isAlgClosure_cycSubfield`: the fixed algebraic closure of `ℚ` is one of the
  cyclotomic subfield as well.
* `InverseGalois.CFT.cycRootBase_spec`: the chosen element is a primitive `n`-th root of unity.
* `InverseGalois.CFT.coprime_pow_totient`: **a power of a prime is coprime to the degree of the
  cyclotomic field of that prime**, which is what makes the base change harmless.

## Tags

cyclotomic field, base change, roots of unity, Galois group
-/

namespace InverseGalois.CFT

open Module IntermediateField NumberField

variable (n : ℕ) [NeZero n]

/-! ### The cyclotomic subfield as a base field -/

/-- The fixed algebraic closure of `ℚ` is an algebraic closure of the cyclotomic subfield. -/
instance isAlgClosure_cycSubfield : IsAlgClosure ↥(cycSubfield n) (AlgebraicClosure ℚ) where
  isAlgClosed := inferInstance
  isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ℚ) _

/-- A primitive `n`-th root of unity inside the `n`-th cyclotomic subfield: the generator of that
subfield, viewed as one of its own elements. -/
noncomputable def cycRootBase : ↥(cycSubfield n) :=
  ⟨cycRoot n, IntermediateField.subset_adjoin ℚ {cycRoot n} rfl⟩

/-- The chosen element of the cyclotomic subfield is a primitive `n`-th root of unity. -/
theorem cycRootBase_spec : IsPrimitiveRoot (cycRootBase n) n :=
  IsPrimitiveRoot.of_map_of_injective
    (f := (algebraMap ↥(cycSubfield n) (AlgebraicClosure ℚ)).toMonoidHom)
    (cycRoot_spec n) (algebraMap ↥(cycSubfield n) (AlgebraicClosure ℚ)).injective

/-! ### The base change -/

variable (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ A] [FiniteDimensional ℚ A]

/-- **The compositum of `A` with the `n`-th cyclotomic subfield, viewed as an extension of the
latter.**  This is the field over which the embedding problem posed by `A` is solved. -/
noncomputable abbrev cycBaseChange : IntermediateField ↥(cycSubfield n) (AlgebraicClosure ℚ) :=
  supOver A (cycSubfield n)

instance numberField_cycBaseChange : NumberField ↥(cycBaseChange n A) := ⟨⟩

/-- **Adjoining the roots of unity does not disturb the Galois group**, provided the degree of `A`
is coprime to the degree of the cyclotomic field. -/
noncomputable def galEquivCycBase (hcop : Nat.Coprime (finrank ℚ A) (Nat.totient n)) :
    Gal(↥(cycBaseChange n A)/↥(cycSubfield n)) ≃* Gal(A/ℚ) :=
  galEquivBaseOfCoprime A (cycSubfield n) (by rwa [finrank_cycSubfield])

/-! ### Coprimality -/

/-- **A power of a prime is coprime to the degree of the cyclotomic field of that prime.**  The
degree is `ℓ - 1`, which is coprime to `ℓ`. -/
theorem coprime_pow_totient {ℓ : ℕ} (hℓ : ℓ.Prime) (N : ℕ) :
    Nat.Coprime (ℓ ^ N) (Nat.totient ℓ) := by
  rw [Nat.totient_prime hℓ]
  exact Nat.Coprime.pow_left N
    ((Nat.coprime_self_sub_right hℓ.one_le).mpr (Nat.coprime_one_right ℓ))

end InverseGalois.CFT
