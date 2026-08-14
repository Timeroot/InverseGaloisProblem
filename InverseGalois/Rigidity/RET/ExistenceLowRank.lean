/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.KummerCover
import InverseGalois.Rigidity.RET.KummerInertia
import InverseGalois.Rigidity.RET.Pi1.Topological.SphereBaseCase

/-!
# The existence direction of the covers correspondence, for at most two branch points

`riemann_existence_cover_mpr` (`RET.Existence`) asserts that a surjection `Γ_r ↠ G` from a sphere
group — a monodromy representation with `r` prescribed branch points — is realized by a finite
Galois extension of `ℚ̄(T)` with group `G`.  For `r ≤ 2` that assertion is a **theorem**, with no
geometric input at all, and this file proves it.

The reason is that the sphere groups of rank at most two are cyclic: `Γ_0` and `Γ_1` are trivial
(`sphereGroup_zero_subsingleton`, `sphereGroup_one_subsingleton`) and `Γ_2 ≅ ℤ`
(`sphereGroup_two_mulEquiv_int`), so a quotient of one of them is a finite cyclic group — and the
finite cyclic groups are realized explicitly by the Kummer covers `yⁿ = T`
(`isGeometricGaloisCover_of_isCyclic`).  Geometrically this is the classical picture: a cover of the
line branched over at most two points is, after a Möbius change of coordinate, `y ↦ yⁿ`.

The bound is sharp in the sense that it is exactly the range in which the group theory forces the
answer: `Γ_r` is free of rank `r - 1` (`sphereGroup_mulEquiv_free`), so from `r = 3` on its finite
quotients are all the two-generated finite groups, and no explicit construction covers them.

The same range is reached in the sharper form the rigidity method consumes — branch points named
on the line, and each branch cycle required to *generate* the inertia group of a place above its
point (`GeomRET.exists_cover`) — by the two-point Kummer cover
`wⁿ = (T - t₀)(T - t₁)^{n-1}` of `RET/KummerInertia.lean`: it is totally ramified over `t₀` and
over `t₁`, and unramified at every other point of the line and at infinity.

## Main results

* `Rigidity.RET.isGeometricGaloisCover_of_sphereGroup_surjective_of_le_two` — a monodromy
  representation with at most two branch points is realized by a geometric Galois cover.
* `Rigidity.RET.trivialCover` — the line itself, as a cover of itself.
* `Rigidity.RET.exists_cover_of_le_two` — the existence direction of `GeomRET`, with the branch
  points and the distinguished-inertia clause, for at most two branch points.
-/

namespace Rigidity.RET

/-- **A sphere group with at most two punctures is cyclic.**  `Γ_0` and `Γ_1` are trivial, and
`Γ_2 ≅ ℤ` is the fundamental group of the twice-punctured sphere `ℂˣ`. -/
theorem isCyclic_sphereGroup_of_le_two {r : ℕ} (hr : r ≤ 2) : IsCyclic (SphereGroup r) := by
  interval_cases r
  · infer_instance
  · infer_instance
  · exact isCyclic_of_surjective sphereGroup_two_mulEquiv_int.symm
      sphereGroup_two_mulEquiv_int.symm.surjective

/-- **The existence direction of the covers correspondence, for at most two branch points.**

A surjection `Γ_r ↠ G` with `r ≤ 2` is realized by a finite Galois extension of `ℚ̄(T)` with group
`G`: such a `G` is a finite cyclic group, hence the group of a Kummer cover `yⁿ = T`.  This is the
special case of `riemann_existence_cover_mpr` in which the branch data is small enough that the
geometry is forced — the general statement needs the Riemann Existence Theorem. -/
theorem isGeometricGaloisCover_of_sphereGroup_surjective_of_le_two {G : Type} [Group G] [Finite G]
    {r : ℕ} (hr : r ≤ 2) (φ : SphereGroup r →* G) (hφ : Function.Surjective φ) :
    IsGeometricGaloisCover G := by
  haveI := isCyclic_sphereGroup_of_le_two hr
  haveI : IsCyclic G := isCyclic_of_surjective φ hφ
  exact isGeometricGaloisCover_of_isCyclic G

/-! ## Naming the branch points -/

section BranchPoints

open Polynomial GeomAKLB

noncomputable section

/-- A generator is carried to a generator by an isomorphism. -/
theorem zpowers_symm_eq_top {A B : Type*} [Group A] [Group B] (e : A ≃* B) {x : B}
    (hx : Subgroup.zpowers x = ⊤) : Subgroup.zpowers (e.symm x) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro y
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hx ▸ Subgroup.mem_top (e y))
  exact Subgroup.mem_zpowers_iff.mpr ⟨m, by rw [← map_zpow, hm, e.symm_apply_apply]⟩

/-! ### The trivial cover -/

/-- **The trivial cover of the line**: the line itself, with trivial deck group. -/
def trivialCover : LineCover := LineCover.of (RatFunc k)

instance : Subsingleton trivialCover.deck :=
  ⟨fun a b => AlgEquiv.ext fun x => (a.commutes x).trans (b.commutes x).symm⟩

theorem trivialCover_isUnramifiedOutside (S : Set k) : trivialCover.IsUnramifiedOutside S :=
  fun _ _ σ _ => Subsingleton.elim σ 1

theorem trivialCover_isUnramifiedAtInfinity : trivialCover.IsUnramifiedAtInfinity := by
  intro τ _
  set σ : trivialCover.M ≃ₐ[RatFunc k] trivialCover.M := Twist.unaut τ with hσdef
  have hσ1 : σ = 1 := Subsingleton.elim _ _
  have hτaut : τ = Twist.aut σ := AlgEquiv.ext fun _ => rfl
  rw [hτaut, hσ1]
  exact AlgEquiv.ext fun _ => rfl

theorem trivialCover_isInertiaGenAt (t : k) (σ : trivialCover.deck) :
    trivialCover.IsInertiaGenAt t σ := by
  obtain ⟨Q, hQmax, hQover⟩ := exists_Q_over_placeP trivialCover.M t
  refine ⟨Q, hQmax, hQover, ?_⟩
  have hbot : ∀ K : Subgroup trivialCover.deck, K = ⊥ := by
    intro K
    rw [Subgroup.eq_bot_iff_forall]
    intro x _
    exact Subsingleton.elim x 1
  rw [hbot (geomInertia trivialCover.M Q), hbot (Subgroup.zpowers σ)]

/-! ### The existence direction for at most two branch points -/

/-- **The existence direction of the covers correspondence for at most two branch points**, with
the distinguished-inertia clause. -/
theorem exists_cover_of_le_two {r : ℕ} (hr : r ≤ 2) (t : Fin r → k) (ht : Function.Injective t)
    {H : Type} [Group H] [Finite H] (h : Fin r → H)
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : LineCover) (e : L.deck ≃* H),
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i)) := by
  interval_cases r
  -- no branch points: the group is trivial and the cover is the line
  · have hbot : (⊥ : Subgroup H) = ⊤ := by
      rw [← htop, Set.range_eq_empty h, Subgroup.closure_empty]
    haveI : Subsingleton H :=
      ⟨fun a b => by
        have ha : a ∈ (⊥ : Subgroup H) := hbot ▸ Subgroup.mem_top a
        have hb : b ∈ (⊥ : Subgroup H) := hbot ▸ Subgroup.mem_top b
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]⟩
    exact ⟨trivialCover, mulEquivOfSubsingleton, trivialCover_isUnramifiedOutside _,
      trivialCover_isUnramifiedAtInfinity, fun i => absurd i.2 (by omega)⟩
  -- one branch point: the single branch cycle is trivial, so the group is
  · have h0 : h 0 = 1 := by simpa using hprod
    have hr1 : Set.range h = {1} := by
      ext x; simp [Set.mem_range, Fin.exists_fin_one, h0, eq_comm]
    have hbot : (⊥ : Subgroup H) = ⊤ := by
      rw [← htop, hr1, Subgroup.closure_singleton_one]
    haveI : Subsingleton H :=
      ⟨fun a b => by
        have ha : a ∈ (⊥ : Subgroup H) := hbot ▸ Subgroup.mem_top a
        have hb : b ∈ (⊥ : Subgroup H) := hbot ▸ Subgroup.mem_top b
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]⟩
    exact ⟨trivialCover, mulEquivOfSubsingleton, trivialCover_isUnramifiedOutside _,
      trivialCover_isUnramifiedAtInfinity, fun i => trivialCover_isInertiaGenAt _ _⟩
  -- two branch points: the group is cyclic, and the cover is the two-point Kummer cover
  · have h01 : t 0 ≠ t 1 := fun hh => by simpa using ht hh
    have hp : h 0 * h 1 = 1 := by simpa using hprod
    have h1eq : h 1 = (h 0)⁻¹ := (inv_eq_of_mul_eq_one_right hp).symm
    have hrange : Set.range h = {h 0, h 1} := by
      ext x; simp [Fin.exists_fin_two, eq_comm]
    have hclos : Subgroup.closure ({h 0, (h 0)⁻¹} : Set H) = Subgroup.closure {h 0} := by
      refine le_antisymm ?_ (Subgroup.closure_mono (by simp))
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure rfl
      · exact inv_mem (Subgroup.subset_closure rfl)
    have hgen0 : Subgroup.zpowers (h 0) = ⊤ := by
      rw [Subgroup.zpowers_eq_closure, ← hclos, ← h1eq, ← hrange, htop]
    have hgen1 : Subgroup.zpowers (h 1) = ⊤ := by rw [h1eq, Subgroup.zpowers_inv, hgen0]
    haveI : IsCyclic H :=
      ⟨⟨h 0, fun x => by
        show x ∈ Subgroup.zpowers (h 0)
        rw [hgen0]; exact Subgroup.mem_top x⟩⟩
    haveI : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
    set n : ℕ := Nat.card H with hn
    set a : RatFunc k := algebraMap (Polynomial k) (RatFunc k) (kummerA n (t 0) (t 1)) with ha
    have Hirr : Irreducible ((X : (RatFunc k)[X]) ^ n - C a) :=
      irreducible_kummerA (NeZero.ne n) h01
    obtain ⟨ζ₀, hζ₀⟩ := exists_primitiveRoot_k n
    have hζ : IsPrimitiveRoot (algebraMap k (RatFunc k) ζ₀) n :=
      hζ₀.map_of_injective (algebraMap k (RatFunc k)).injective
    have hprim : (primitiveRoots n (RatFunc k)).Nonempty :=
      ⟨_, (mem_primitiveRoots (NeZero.pos n)).mpr hζ⟩
    let M := ((X : (RatFunc k)[X]) ^ n - C a).SplittingField
    haveI : IsGalois (RatFunc k) M := isGalois_of_isSplittingField_X_pow_sub_C hprim Hirr M
    haveI : FiniteDimensional (RatFunc k) M :=
      IsSplittingField.finiteDimensional M ((X : (RatFunc k)[X]) ^ n - C a)
    let L : LineCover := LineCover.of M
    haveI : IsSplittingField (RatFunc k) L.M ((X : (RatFunc k)[X]) ^ n - C a) :=
      inferInstanceAs (IsSplittingField (RatFunc k) M ((X : (RatFunc k)[X]) ^ n - C a))
    refine ⟨L, (autEquivZmod Hirr M hζ).trans (zmodCyclicMulEquiv (inferInstance : IsCyclic H)),
      ?_, ?_, ?_⟩
    · have hset : Set.range t = {t 0, t 1} := by
        ext x
        simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
        exact ⟨fun hx => hx.imp Eq.symm Eq.symm, fun hx => hx.imp Eq.symm Eq.symm⟩
      rw [hset]
      exact isUnramifiedOutside_kummerCover n (t 0) (t 1) h01 L
    · exact isUnramifiedAtInfinity_kummerCover n h01 L
    · intro i
      fin_cases i
      · exact isInertiaGenAt_kummerCover n h01 L (zpowers_symm_eq_top _ hgen0)
      · exact isInertiaGenAt_kummerCover' n h01 L (zpowers_symm_eq_top _ hgen1)

end

end BranchPoints

end Rigidity.RET
