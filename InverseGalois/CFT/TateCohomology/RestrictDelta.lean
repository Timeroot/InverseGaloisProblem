/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DeltaNatural
import InverseGalois.CFT.TateCohomology.RestrictNatural

/-!
# The connecting map in degree minus one against restriction and corestriction

In degree minus one the connecting map of a short exact sequence is the snake of the ladder of the
norms: a class of the quotient killed by the norm is the class of a vector of the middle whose norm
comes from the sub, and the connecting map sends it to the class of the vector of the sub that
witnesses the norm.  Restriction to a subgroup in that degree is the opposite transfer, the sum of
the actions of the inverses of the representatives of the cosets, and restriction in degree zero is
the inclusion of the invariants of the group into those of the subgroup; corestriction is the
transfer and the sum over the cosets.

The comparison of either with the snake is a computation with a single vector.  The norm of a
group is the norm of a subgroup applied to the opposite transfer, so the opposite transfer of a
vector whose norm comes from the sub has the same witness in the sub; the two classes attached to
it, in degree minus one of the quotient and in degree zero of the sub, are exactly the restrictions
of the classes attached to the original vector.  Dually the norm of a group is the transfer of the
norm of a subgroup, so a vector whose norm for the subgroup comes from the sub also has its norm for
the group coming from the sub, with the witness transferred; that is the statement for
corestriction.

These are the two squares that the recursive definitions of restriction and corestriction leave
open, since the recursion in a nonnegative degree and the recursion in a degree below minus one each
assert their own square by construction.

## Main results

* `InverseGalois.CFT.Tate.deltaMid_res`: **the connecting map in degree minus one commutes with
  restriction to a subgroup.**
* `InverseGalois.CFT.Tate.deltaMid_cor`: **the connecting map in degree minus one commutes with
  corestriction from a subgroup.**
* `InverseGalois.CFT.Tate.tateRes_tateδ_negOne`, `InverseGalois.CFT.Tate.tateCor_tateδ_negOne`: the
  same two squares written for the complete cohomology.

## Tags

Tate cohomology, connecting homomorphism, restriction, corestriction, transfer
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (H : Subgroup G)

/-! ### Restriction -/

/-- The opposite transfer of a vector of the middle whose norm comes from the sub is a vector whose
norm for the subgroup comes from the sub. -/
theorem mem_normSource_transferRight (b : ↥(normSource X.X₂.ρ X.f.hom.hom)) :
    transferRight H X.X₂.ρ (b : X.X₂)
      ∈ normSource (resSeq H X).X₂.ρ (resSeq H X).f.hom.hom := by
  obtain ⟨a, ha⟩ := mem_normSource_iff.1 b.2
  exact mem_normSource_iff.2 ⟨a, ha.trans (normMap_eq_transferRight H X.X₂.ρ (b : X.X₂))⟩

/-- The vectors of the middle whose norm comes from the sub, read on a subgroup. -/
def normSourceRes (b : ↥(normSource X.X₂.ρ X.f.hom.hom)) :
    ↥(normSource (resSeq H X).X₂.ρ (resSeq H X).f.hom.hom) :=
  ⟨transferRight H X.X₂.ρ (b : X.X₂), mem_normSource_transferRight H b⟩

/-- The class in degree minus one attached to such a vector is restricted along with it. -/
theorem toHm1_normSourceRes (b : ↥(normSource X.X₂.ρ X.f.hom.hom)) :
    resm1 H X.X₃.ρ (toHm1 X.f.hom.hom X.g.hom.hom (hom_equivariant X.g)
        (shortExact_range_eq_ker hX) b)
      = toHm1 (resSeq H X).f.hom.hom (resSeq H X).g.hom.hom (hom_equivariant (resSeq H X).g)
        (shortExact_range_eq_ker (resSeq_shortExact hX H)) (normSourceRes H b) := by
  refine Subtype.ext ?_
  rw [resm1_coe, toHm1_coe, toHm1_coe, resCoinvariants_mk]
  exact congrArg (Coinvariants.mk (restrictRep H X.X₃.ρ)) (hom_transferRight H X.g (b : X.X₂))

/-- The vector of the sub witnessing the norm is unchanged by the opposite transfer. -/
theorem normDescent_normSourceRes (b : ↥(normSource X.X₂.ρ X.f.hom.hom)) :
    normDescent (resSeq H X).f.hom.hom (shortExact_injective (resSeq_shortExact hX H))
        (normSourceRes H b)
      = normDescent X.f.hom.hom (shortExact_injective hX) b := by
  refine shortExact_injective hX ?_
  have h1 : X.f.hom.hom (normDescent (resSeq H X).f.hom.hom
        (shortExact_injective (resSeq_shortExact hX H)) (normSourceRes H b))
      = normMap (restrictRep H X.X₂.ρ) (transferRight H X.X₂.ρ (b : X.X₂)) :=
    f_normDescent _ _ _
  have h2 : X.f.hom.hom (normDescent X.f.hom.hom (shortExact_injective hX) b)
      = normMap X.X₂.ρ (b : X.X₂) :=
    f_normDescent _ _ _
  rw [h1, h2]
  exact (normMap_eq_transferRight H X.X₂.ρ (b : X.X₂)).symm

/-- The class in degree zero attached to such a vector is restricted along with it. -/
theorem toH0_normSourceRes (b : ↥(normSource X.X₂.ρ X.f.hom.hom)) :
    res0 H X.X₁.ρ (toH0 X.f.hom.hom (hom_equivariant X.f) (shortExact_injective hX) b)
      = toH0 (resSeq H X).f.hom.hom (hom_equivariant (resSeq H X).f)
        (shortExact_injective (resSeq_shortExact hX H)) (normSourceRes H b) := by
  rw [toH0_apply, res0_H0mk, toH0_apply]
  refine congrArg (H0mk (restrictRep H X.X₁.ρ)) (Subtype.ext ?_)
  rw [resInvariants_coe, normDescentInv_coe, normDescentInv_coe]
  exact (normDescent_normSourceRes hX H b).symm

/-- **The connecting map in degree minus one commutes with restriction to a subgroup.** -/
theorem deltaMid_res (u : Hm1 X.X₃.ρ) :
    res0 H X.X₁.ρ (deltaMid hX u) = deltaMid (resSeq_shortExact hX H) (resm1 H X.X₃.ρ u) := by
  obtain ⟨b, rfl⟩ := toHm1_surjective X.f.hom.hom X.g.hom.hom (hom_equivariant X.g)
    (shortExact_surjective hX) (shortExact_range_eq_ker hX) u
  rw [deltaMid_toHm1 hX b, toHm1_normSourceRes hX H b,
    deltaMid_toHm1 (resSeq_shortExact hX H) (normSourceRes H b), toH0_normSourceRes hX H b]

/-! ### Corestriction -/

/-- A vector of the middle whose norm for the subgroup comes from the sub has its norm for the group
coming from the sub as well. -/
theorem mem_normSource_of_res
    (b : ↥(normSource (resSeq H X).X₂.ρ (resSeq H X).f.hom.hom)) :
    (b : (resSeq H X).X₂) ∈ normSource X.X₂.ρ X.f.hom.hom := by
  obtain ⟨a, ha⟩ := mem_normSource_iff.1 b.2
  have ha' : X.f.hom.hom a = normMap (restrictRep H X.X₂.ρ) (b : (resSeq H X).X₂) := ha
  refine mem_normSource_iff.2 ⟨transferLeft H X.X₁.ρ a, ?_⟩
  calc X.f.hom.hom (transferLeft H X.X₁.ρ a)
      = transferLeft H X.X₂.ρ (X.f.hom.hom a) := (hom_transferLeft H X.f a).symm
    _ = transferLeft H X.X₂.ρ (normMap (restrictRep H X.X₂.ρ) (b : (resSeq H X).X₂)) := by
        rw [ha']
    _ = normMap X.X₂.ρ (b : (resSeq H X).X₂) :=
        (normMap_eq_transferLeft H X.X₂.ρ (b : (resSeq H X).X₂)).symm

/-- The vectors of the middle whose norm for a subgroup comes from the sub, read on the group. -/
def normSourceCor (b : ↥(normSource (resSeq H X).X₂.ρ (resSeq H X).f.hom.hom)) :
    ↥(normSource X.X₂.ρ X.f.hom.hom) :=
  ⟨(b : (resSeq H X).X₂), mem_normSource_of_res H b⟩

/-- The class in degree minus one attached to such a vector is corestricted along with it. -/
theorem toHm1_normSourceCor (b : ↥(normSource (resSeq H X).X₂.ρ (resSeq H X).f.hom.hom)) :
    corm1 H X.X₃.ρ (toHm1 (resSeq H X).f.hom.hom (resSeq H X).g.hom.hom
        (hom_equivariant (resSeq H X).g) (shortExact_range_eq_ker (resSeq_shortExact hX H)) b)
      = toHm1 X.f.hom.hom X.g.hom.hom (hom_equivariant X.g) (shortExact_range_eq_ker hX)
        (normSourceCor H b) := by
  refine Subtype.ext ?_
  show corCoinvariants H X.X₃.ρ
      (Coinvariants.mk (restrictRep H X.X₃.ρ) (X.g.hom.hom (b : (resSeq H X).X₂)))
    = Coinvariants.mk X.X₃.ρ (X.g.hom.hom (b : (resSeq H X).X₂))
  rw [corCoinvariants_mk]

/-- The vector of the sub witnessing the norm is transferred. -/
theorem normDescent_normSourceCor (b : ↥(normSource (resSeq H X).X₂.ρ (resSeq H X).f.hom.hom)) :
    normDescent X.f.hom.hom (shortExact_injective hX) (normSourceCor H b)
      = transferLeft H X.X₁.ρ (normDescent (resSeq H X).f.hom.hom
        (shortExact_injective (resSeq_shortExact hX H)) b) := by
  refine shortExact_injective hX ?_
  have h1 : X.f.hom.hom (normDescent X.f.hom.hom (shortExact_injective hX) (normSourceCor H b))
      = normMap X.X₂.ρ (b : (resSeq H X).X₂) :=
    f_normDescent _ _ _
  have h2 : X.f.hom.hom (normDescent (resSeq H X).f.hom.hom
        (shortExact_injective (resSeq_shortExact hX H)) b)
      = normMap (restrictRep H X.X₂.ρ) (b : (resSeq H X).X₂) :=
    f_normDescent _ _ _
  rw [h1, ← hom_transferLeft H X.f, h2]
  exact normMap_eq_transferLeft H X.X₂.ρ (b : (resSeq H X).X₂)

/-- The class in degree zero attached to such a vector is corestricted along with it. -/
theorem toH0_normSourceCor (b : ↥(normSource (resSeq H X).X₂.ρ (resSeq H X).f.hom.hom)) :
    cor0 H X.X₁.ρ (toH0 (resSeq H X).f.hom.hom (hom_equivariant (resSeq H X).f)
        (shortExact_injective (resSeq_shortExact hX H)) b)
      = toH0 X.f.hom.hom (hom_equivariant X.f) (shortExact_injective hX) (normSourceCor H b) := by
  show H0mk X.X₁.ρ (corInvariants H X.X₁.ρ
      (normDescentInv (resSeq H X).f.hom.hom (hom_equivariant (resSeq H X).f)
        (shortExact_injective (resSeq_shortExact hX H)) b))
    = H0mk X.X₁.ρ (normDescentInv X.f.hom.hom (hom_equivariant X.f) (shortExact_injective hX)
        (normSourceCor H b))
  refine congrArg (H0mk X.X₁.ρ) (Subtype.ext ?_)
  rw [corInvariants_coe, normDescentInv_coe, normDescentInv_coe]
  exact (normDescent_normSourceCor hX H b).symm

/-- **The connecting map in degree minus one commutes with corestriction from a subgroup.** -/
theorem deltaMid_cor (v : Hm1 (restrictRep H X.X₃.ρ)) :
    cor0 H X.X₁.ρ (deltaMid (resSeq_shortExact hX H) v) = deltaMid hX (corm1 H X.X₃.ρ v) := by
  obtain ⟨b, rfl⟩ := toHm1_surjective (resSeq H X).f.hom.hom (resSeq H X).g.hom.hom
    (hom_equivariant (resSeq H X).g) (shortExact_surjective (resSeq_shortExact hX H))
    (shortExact_range_eq_ker (resSeq_shortExact hX H)) v
  rw [deltaMid_toHm1 (resSeq_shortExact hX H) b, toHm1_normSourceCor hX H b,
    deltaMid_toHm1 hX (normSourceCor H b), toH0_normSourceCor hX H b]

/-! ### The two squares for the complete cohomology -/

/-- **Restriction to a subgroup commutes with the connecting map of the complete cohomology in
degree minus one.** -/
theorem tateRes_tateδ_negOne (w : ↥(tateModule X.X₃ (Int.negSucc 0))) :
    tateRes H X.X₁ (Int.negSucc 0 + 1) (tateδ hX (Int.negSucc 0) w)
      = tateδ (resSeq_shortExact hX H) (Int.negSucc 0) (tateRes H X.X₃ (Int.negSucc 0) w) :=
  deltaMid_res hX H w

/-- **Corestriction from a subgroup commutes with the connecting map of the complete cohomology in
degree minus one.** -/
theorem tateCor_tateδ_negOne (w : ↥(tateModule (resSeq H X).X₃ (Int.negSucc 0))) :
    tateCor H X.X₁ (Int.negSucc 0 + 1) (tateδ (resSeq_shortExact hX H) (Int.negSucc 0) w)
      = tateδ hX (Int.negSucc 0) (tateCor H X.X₃ (Int.negSucc 0) w) :=
  deltaMid_cor hX H w

end

end InverseGalois.CFT.Tate
