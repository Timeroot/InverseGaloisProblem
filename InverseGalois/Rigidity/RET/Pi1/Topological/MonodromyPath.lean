/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.Monodromy

/-!
# Moving the basepoint of the monodromy representation

The monodromy representation of a covering map is attached to a basepoint: it acts on the fibre
over that point.  A path between two basepoints identifies the two representations, because
transport along the path is a bijection of the fibres and conjugating a loop by the path is an
isomorphism of the fundamental groups; the two identifications are compatible, since transport
along a concatenation is transport along the pieces in turn.

The consequence used downstream is that nothing about the monodromy *group* depends on the
basepoint: the two readings of a loop are conjugate permutations, so they have the same order, and
an exponent for one is an exponent for the other.

## Main definitions

* `IsCoveringMap.fibreEquiv` — transport along a homotopy class of paths, as an equivalence of
  fibres.
* `FundamentalGroup.transport` — conjugation of loops by a homotopy class of paths, as an
  isomorphism of fundamental groups.

## Main results

* `IsCoveringMap.monodromyHom_transport` — the two monodromy representations differ by conjugation
  with the transport of fibres.
* `IsCoveringMap.orderOf_monodromyHom_transport` — the order of the monodromy of a loop does not
  depend on the basepoint it is read at.
-/

open CategoryTheory

noncomputable section

namespace FundamentalGroup

variable {X : Type*} [TopologicalSpace X]

/-- **Conjugation by a path**, as an isomorphism of the fundamental groups at its endpoints. -/
def transport {x y : X} (q : Path.Homotopic.Quotient x y) :
    FundamentalGroup X x ≃* FundamentalGroup X y :=
  ((Groupoid.isoEquivHom _ _).symm q).conj

theorem transport_mk {x y : X} (r : Path x y) :
    transport (Path.Homotopic.Quotient.mk r) = fundamentalGroupMulEquivOfPath r := rfl

end FundamentalGroup

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (cov : IsCoveringMap p)

/-! ### Transport of fibres -/

/-- **Transport along a path**, as an equivalence of the fibres over its endpoints. -/
def fibreEquiv {x y : X} (q : Path.Homotopic.Quotient x y) : p ⁻¹' {x} ≃ p ⁻¹' {y} :=
  Equiv.ofBijective _ (cov.monodromy_bijective q)

@[simp] theorem fibreEquiv_apply {x y : X} (q : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    cov.fibreEquiv q e = cov.monodromy q e := rfl

/-! ### Compatibility of the two transports -/

/-- **The monodromy representations at two basepoints differ by conjugation.**  Transporting the
fibre along a path intertwines the monodromy of a loop with the monodromy of its conjugate. -/
theorem monodromyHom_transport {x y : X} (q : Path.Homotopic.Quotient x y)
    (γ : FundamentalGroup X x) :
    cov.monodromyHom y (FundamentalGroup.transport q γ)
      = Equiv.permCongrHom (cov.fibreEquiv q) (cov.monodromyHom x γ) := by
  classical
  set α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk y :=
    (Groupoid.isoEquivHom _ _).symm q with hα
  have hhom : α.hom = q := rfl
  -- transporting a fibre point back along the path undoes the transport
  have hback : ∀ e : p ⁻¹' {x}, cov.monodromy α.inv (cov.monodromy q e) = e := by
    intro e
    rw [← cov.monodromy_trans_apply]
    show cov.monodromy (α.hom ≫ α.inv) e = e
    rw [α.hom_inv_id]
    show cov.monodromy (Path.Homotopic.Quotient.refl _) e = e
    rw [cov.monodromy_refl]
    rfl
  refine Equiv.ext fun e' => ?_
  obtain ⟨e, rfl⟩ := (cov.fibreEquiv q).surjective e'
  have hR : Equiv.permCongrHom (cov.fibreEquiv q) (cov.monodromyHom x γ) (cov.fibreEquiv q e)
      = cov.fibreEquiv q (cov.monodromyHom x γ e) := by
    show cov.fibreEquiv q (cov.monodromyHom x γ ((cov.fibreEquiv q).symm (cov.fibreEquiv q e)))
      = cov.fibreEquiv q (cov.monodromyHom x γ e)
    rw [Equiv.symm_apply_apply]
  rw [hR]
  show cov.monodromy (α.inv.trans (γ.toPath.trans α.hom)) (cov.monodromy q e)
    = cov.monodromy q (cov.monodromy γ.toPath e)
  rw [cov.monodromy_trans_apply, cov.monodromy_trans_apply, hback e, hhom]

/-- **The order of the monodromy of a loop does not depend on the basepoint.** -/
theorem orderOf_monodromyHom_transport {x y : X} (q : Path.Homotopic.Quotient x y)
    (γ : FundamentalGroup X x) :
    orderOf (cov.monodromyHom y (FundamentalGroup.transport q γ))
      = orderOf (cov.monodromyHom x γ) := by
  rw [cov.monodromyHom_transport q γ]
  exact orderOf_injective (Equiv.permCongrHom (cov.fibreEquiv q)).toMonoidHom
    (Equiv.permCongrHom (cov.fibreEquiv q)).injective _

/-- **The exponents of the monodromy of a loop are the same at every basepoint.** -/
theorem monodromyHom_transport_pow_eq_one_iff {x y : X} (q : Path.Homotopic.Quotient x y)
    (γ : FundamentalGroup X x) {n : ℕ} :
    cov.monodromyHom y (FundamentalGroup.transport q γ) ^ n = 1
      ↔ cov.monodromyHom x γ ^ n = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one,
    cov.orderOf_monodromyHom_transport q γ]

/-- **An exponent for the monodromy at one basepoint is an exponent at any other.** -/
theorem monodromyHom_transport_pow_eq_one {x y : X} (q : Path.Homotopic.Quotient x y)
    (γ : FundamentalGroup X x) {n : ℕ} (h : cov.monodromyHom x γ ^ n = 1) :
    cov.monodromyHom y (FundamentalGroup.transport q γ) ^ n = 1 :=
  (cov.monodromyHom_transport_pow_eq_one_iff q γ).mpr h

end IsCoveringMap

end
