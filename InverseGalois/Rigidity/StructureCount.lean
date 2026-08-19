/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.StructureConstant

/-!
# Counting a rigidity certificate through a single structure constant

The expensive field of a `RigidityCertificate` is
`rigid : Nat.card (rigidTuples C) = Nat.card G`, and `rigidTuples` carries a *generation*
condition `Subgroup.closure (Set.range g) = ⊤`.  Deciding generation for every product-one tuple
in the prescribed classes is what makes the condition unusable for a group of any size.

This file replaces that global count by **one classical structure constant**.  Write
`prodOneTuples C` for the tuples in the prescribed classes whose product is `1`, with **no**
generation requirement, and — for a triple of classes and a *fixed* element `z` of the last one —
write `prodOneFibre C₀ C₁ z` for the set of first entries `x` of the product-one triples ending
in `z`.  The second entry is then forced, `y = x⁻¹z⁻¹`, so this really is a set of group elements,
and it is the classical structure constant `n(C₀, C₁, C₃)`.

The counting theorem is:

> if **one** triple `(x₀, x₀⁻¹z⁻¹, z)` in the classes generates `G`, and the fibre through `z` has
> at most `|C_G(z)|` elements, then all the product-one triples in the classes form a single
> simultaneous-conjugacy orbit — so the certificate's count holds.

An upper bound suffices because the matching lower bound is automatic: the centralizer of `z`
already moves `x₀` to `|C_G(z)|` distinct points of the fibre.

The reason is orbit–stabilizer, applied twice.  Conjugating by the centralizer of `z` moves `x₀`
inside the fibre and, because `x₀` and `z` already generate `G`, does so with trivial stabilizer;
the orbit therefore has `|C_G(z)|` elements and, by the count, exhausts the fibre.  A general
product-one triple is conjugated so that its last entry is `z`, and is then caught by that orbit.

This is what makes a certificate for a large group finitely checkable: instead of `|G|`-many
tuples one enumerates a **single conjugacy class** — the smallest of the three — and tests each of
its elements for membership in one other class.

Rationality is likewise cheap: `IsRationalClass` quantifies over every element of the class, but
conjugation commutes with taking powers, so it suffices to check a **single representative**.

## Main results

* `Rigidity.rigid_of_card_prodOneTuples` — the generation-free form of the rigidity count.
* `Rigidity.prodOneTuples_eq_orbit_of_card_prodOneFibre` — the product-one triples are the orbit
  of the distinguished one.
* `Rigidity.rigid_of_card_prodOneFibre` — rigidity from the single structure constant.
* `Rigidity.RigidityCertificate.ofStructureConstant` — the certificate built from that count.
* `Rigidity.isRationalClass_mk_of_rep` — rationality from one representative.
-/

open scoped BigOperators

open MulAction Subgroup

namespace Rigidity

variable {G : Type*} [Group G]

/-- If `a` commutes with `b` then it commutes with `b⁻¹`. -/
theorem mul_inv_comm_of_comm {a b : G} (h : a * b = b * a) : a * b⁻¹ = b⁻¹ * a := by
  calc a * b⁻¹ = b⁻¹ * (b * a) * b⁻¹ := by group
    _ = b⁻¹ * (a * b) * b⁻¹ := by rw [h]
    _ = b⁻¹ * a := by group

/-! ### Rationality from a single representative -/

/-- **Rationality of a conjugacy class only has to be checked at one representative.**
Conjugation is an automorphism, so it commutes with `g ↦ g ^ k` and preserves orders; a power
condition verified at `z` therefore propagates to every conjugate of `z`. -/
theorem isRationalClass_mk_of_rep {z : G}
    (h : ∀ k : ℕ, Nat.Coprime k (orderOf z) → ConjClasses.mk (z ^ k) = ConjClasses.mk z) :
    IsRationalClass (ConjClasses.mk z) := by
  intro g hg k hk
  rw [ConjClasses.mk_eq_mk_iff_isConj] at hg
  obtain ⟨c, hc⟩ := hg
  -- `hc : SemiconjBy ↑c g z`, so `g` and `z` have the same order and `g ^ k` is conjugate to `z ^ k`
  have horder : orderOf g = orderOf z := by
    have hmap : MulAut.conj (c : G) g = z := by
      have h : (c : G) * g = z * (c : G) := hc
      simp only [MulAut.conj_apply]
      rw [h]; group
    rw [← hmap, MulEquiv.orderOf_eq]
  have hpow : IsConj (g ^ k) (z ^ k) := ⟨c, hc.pow_right k⟩
  rw [← ConjClasses.mk_eq_mk_iff_isConj] at hpow
  rw [hpow]
  exact h k (horder ▸ hk)

/-! ### Product-one tuples, with no generation condition -/

/-- The tuples `(g₁, …, g_r)` with `gᵢ` in the prescribed class `Cᵢ` and `∏ gᵢ = 1`.  This is
`rigidTuples` with the generation condition dropped, so it is a superset, and — crucially for a
concrete group — counting it needs no subgroup-closure computation. -/
def prodOneTuples {r : ℕ} (C : Fin r → ConjClasses G) : Set (Fin r → G) :=
  { g | (∀ i, ConjClasses.mk (g i) = C i) ∧ (List.ofFn g).prod = 1 }

theorem rigidTuples_subset_prodOneTuples {r : ℕ} {C : Fin r → ConjClasses G} :
    rigidTuples C ⊆ prodOneTuples C := fun _ hg => ⟨hg.1, hg.2.1⟩

/-- Simultaneous conjugation preserves the product-one tuples, exactly as it preserves the rigid
ones (`smul_mem_rigidTuples`): it fixes conjugacy classes and is multiplicative. -/
theorem smul_mem_prodOneTuples {r : ℕ} {C : Fin r → ConjClasses G} {g : Fin r → G}
    (hg : g ∈ prodOneTuples C) (x : ConjAct G) : x • g ∈ prodOneTuples C := by
  obtain ⟨hclass, hprod⟩ := hg
  set c := ConjAct.ofConjAct x with hc
  set f : G →* G := (MulAut.conj c).toMonoidHom with hf
  have hφ : ∀ i, (x • g) i = f (g i) := fun i => by
    rw [Pi.smul_apply, ConjAct.smul_eq_mulAut_conj]; rfl
  have hfun : (x • g) = f ∘ g := funext hφ
  refine ⟨fun i => ?_, ?_⟩
  · rw [hφ i, ← hclass i, ConjClasses.mk_eq_mk_iff_isConj]
    simp only [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact isConj_iff.mpr ⟨c⁻¹, by group⟩
  · have hlist : List.ofFn (x • g) = (List.ofFn g).map f := by rw [List.map_ofFn, ← hfun]
    rw [hlist, ← map_list_prod f, hprod, map_one]

/-- **The rigidity count, with generation tested only once.**  For a centerless finite group, if
the product-one tuples in the prescribed classes number exactly `|G|` and at least one of them
generates, then the certificate's count `Nat.card (rigidTuples C) = Nat.card G` holds.

The generating tuple's simultaneous-conjugacy orbit already has `|G|` elements and sits inside
`prodOneTuples C`, which has `|G|` elements; so the orbit is everything, and every product-one
tuple in the classes is a conjugate of the generating one — hence itself generating. -/
theorem rigid_of_card_prodOneTuples {r : ℕ} {C : Fin r → ConjClasses G} [Finite G]
    (hZ : Subgroup.center G = ⊥) (hne : (rigidTuples C).Nonempty)
    (hcard : Nat.card (prodOneTuples C) = Nat.card G) :
    Nat.card (rigidTuples C) = Nat.card G := by
  obtain ⟨g₀, hg₀⟩ := hne
  set O := MulAction.orbit (ConjAct G) g₀ with hO
  have hOR : O ⊆ rigidTuples C := by rintro _ ⟨x, rfl⟩; exact smul_mem_rigidTuples hg₀ x
  have hRP : rigidTuples C ⊆ prodOneTuples C := rigidTuples_subset_prodOneTuples
  have hcardO : O.ncard = Nat.card G := by
    rw [← Nat.card_coe_set_eq]; exact card_orbit_conjAct hg₀.2.2 hZ
  have hcardP : (prodOneTuples C).ncard = Nat.card G := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  have hPfin : (prodOneTuples C).Finite := Set.toFinite _
  have hOP : O = prodOneTuples C :=
    Set.eq_of_subset_of_ncard_le (hOR.trans hRP) (hcardP.trans hcardO.symm).le hPfin
  have : rigidTuples C = O := (hOP ▸ hRP).antisymm hOR
  rw [this, Nat.card_coe_set_eq, hcardO]

/-! ### The structure constant of a triple of classes -/

/-- The **structure constant set** of a triple of classes at a fixed `z`: the first entries `x` of
the product-one triples `(x, y, z)` with `x` in `C₀` and `y` in `C₁`.  The middle entry is forced
to be `y = x⁻¹z⁻¹`, so the triple is determined by `x` alone. -/
def prodOneFibre (C₀ C₁ : ConjClasses G) (z : G) : Set G :=
  { x | ConjClasses.mk x = C₀ ∧ ConjClasses.mk (x⁻¹ * z⁻¹) = C₁ }

/-- The distinguished triple attached to a point of a structure-constant fibre. -/
def fibreTriple (x z : G) : Fin 3 → G := ![x, x⁻¹ * z⁻¹, z]

theorem prod_fibreTriple (x z : G) : (List.ofFn (fibreTriple x z)).prod = 1 := by
  simp [fibreTriple, List.ofFn_succ, mul_assoc]

/-- The product of a triple, written out. -/
theorem prod_ofFn_three (f : Fin 3 → G) : (List.ofFn f).prod = f 0 * (f 1 * f 2) := by
  simp [List.ofFn_succ]

/-- In a product-one triple the middle entry is determined by the other two. -/
theorem mid_of_prod_one {f : Fin 3 → G} (hf : (List.ofFn f).prod = 1) :
    f 1 = (f 0)⁻¹ * (f 2)⁻¹ := by
  rw [prod_ofFn_three] at hf
  calc f 1 = (f 0)⁻¹ * (f 0 * (f 1 * f 2)) * (f 2)⁻¹ := by group
    _ = (f 0)⁻¹ * (f 2)⁻¹ := by rw [hf]; group

theorem range_fibreTriple (x z : G) :
    Set.range (fibreTriple x z) = {x, x⁻¹ * z⁻¹, z} := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- The distinguished triple is a product-one triple in the prescribed classes. -/
theorem fibreTriple_mem_prodOneTuples {C : Fin 3 → ConjClasses G} {x z : G}
    (hx : x ∈ prodOneFibre (C 0) (C 1) z) (hz : ConjClasses.mk z = C 2) :
    fibreTriple x z ∈ prodOneTuples C := by
  refine ⟨fun i => ?_, prod_fibreTriple x z⟩
  fin_cases i
  · exact hx.1
  · exact hx.2
  · exact hz

/-- The distinguished triple is a *rigid* tuple as soon as `x` and `z` generate. -/
theorem fibreTriple_mem_rigidTuples {C : Fin 3 → ConjClasses G} {x z : G}
    (hx : x ∈ prodOneFibre (C 0) (C 1) z) (hz : ConjClasses.mk z = C 2)
    (hgen : Subgroup.closure ({x, z} : Set G) = ⊤) :
    fibreTriple x z ∈ rigidTuples C := by
  obtain ⟨hclass, hprod⟩ := fibreTriple_mem_prodOneTuples hx hz
  refine ⟨hclass, hprod, ?_⟩
  refine eq_top_iff.2 ?_
  rw [← hgen]
  refine Subgroup.closure_mono ?_
  rw [range_fibreTriple]
  intro w hw
  rcases hw with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

/-- Conjugating by the centralizer of `z` keeps a structure-constant fibre inside itself. -/
theorem conj_mem_prodOneFibre {C₀ C₁ : ConjClasses G} {x z c : G}
    (hx : x ∈ prodOneFibre C₀ C₁ z) (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    c * x * c⁻¹ ∈ prodOneFibre C₀ C₁ z := by
  have hcz : c * z = z * c := (Subgroup.mem_centralizer_singleton_iff).1 hc
  have hcz' : c * z⁻¹ = z⁻¹ * c := mul_inv_comm_of_comm hcz
  have hcz'' : c⁻¹ * z⁻¹ = z⁻¹ * c⁻¹ := (mul_inv_comm_of_comm hcz'.symm).symm
  refine ⟨?_, ?_⟩
  · rw [← hx.1, ConjClasses.mk_eq_mk_iff_isConj]
    exact isConj_iff.mpr ⟨c⁻¹, by group⟩
  · have hrw : (c * x * c⁻¹)⁻¹ * z⁻¹ = c * (x⁻¹ * z⁻¹) * c⁻¹ := by
      calc (c * x * c⁻¹)⁻¹ * z⁻¹ = c * x⁻¹ * (c⁻¹ * z⁻¹) := by group
        _ = c * x⁻¹ * (z⁻¹ * c⁻¹) := by rw [hcz'']
        _ = c * (x⁻¹ * z⁻¹) * c⁻¹ := by group
    rw [hrw, ← hx.2, ConjClasses.mk_eq_mk_iff_isConj]
    exact isConj_iff.mpr ⟨c⁻¹, by group⟩

/-- **The structure-constant fibre is one centralizer orbit.**  If `x₀` together with `z`
generates the centerless group `G`, then conjugation by `C_G(z)` moves `x₀` injectively, so its
orbit already has `|C_G(z)|` elements inside the fibre; an upper bound of `|C_G(z)|` on the fibre
therefore makes the orbit *equal* to the fibre.

Only the upper bound is a hypothesis, because the matching lower bound is exactly the orbit that
the conclusion produces. -/
theorem prodOneFibre_eq_image_of_card [Finite G] {C₀ C₁ : ConjClasses G} {x₀ z : G}
    (hZ : Subgroup.center G = ⊥) (hgen : Subgroup.closure ({x₀, z} : Set G) = ⊤)
    (hx₀ : x₀ ∈ prodOneFibre C₀ C₁ z)
    (hcard : Nat.card (prodOneFibre C₀ C₁ z)
        ≤ Nat.card (Subgroup.centralizer ({z} : Set G))) :
    prodOneFibre C₀ C₁ z
      = (fun c : G => c * x₀ * c⁻¹) '' (Subgroup.centralizer ({z} : Set G) : Set G) := by
  set Cz : Set G := (Subgroup.centralizer ({z} : Set G) : Set G) with hCz
  set F := prodOneFibre C₀ C₁ z with hF
  -- the conjugation map is injective on `C_G(z)`, since a fixed point centralizes `x₀` and `z`
  have hinj : Set.InjOn (fun c : G => c * x₀ * c⁻¹) Cz := by
    intro c₁ h₁ c₂ h₂ heq
    simp only at heq
    set d := c₂⁻¹ * c₁ with hd
    have hdmem : d ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ h₂) h₁
    have hdx : d * x₀ = x₀ * d := by
      have : c₂⁻¹ * (c₁ * x₀ * c₁⁻¹) * c₂ = c₂⁻¹ * (c₂ * x₀ * c₂⁻¹) * c₂ := by rw [heq]
      rw [hd]
      have h1 : c₂⁻¹ * (c₂ * x₀ * c₂⁻¹) * c₂ = x₀ := by group
      rw [h1] at this
      calc c₂⁻¹ * c₁ * x₀ = c₂⁻¹ * (c₁ * x₀ * c₁⁻¹) * (c₁) := by group
        _ = x₀ * (c₂⁻¹ * c₁) := by
              rw [show c₂⁻¹ * (c₁ * x₀ * c₁⁻¹) * c₁
                    = (c₂⁻¹ * (c₁ * x₀ * c₁⁻¹) * c₂) * (c₂⁻¹ * c₁) by group, this]
    have hdcent : d ∈ Subgroup.center G := by
      rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← hgen, Subgroup.centralizer_closure]
      rw [Subgroup.mem_centralizer_iff]
      rintro h (rfl | rfl)
      · exact hdx.symm
      · exact ((Subgroup.mem_centralizer_singleton_iff).1 hdmem).symm
    rw [hZ, Subgroup.mem_bot] at hdcent
    have : c₂⁻¹ * c₁ = 1 := hdcent
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hsub : (fun c : G => c * x₀ * c⁻¹) '' Cz ⊆ F := by
    rintro _ ⟨c, hc, rfl⟩
    exact conj_mem_prodOneFibre hx₀ hc
  have hFfin : F.Finite := Set.toFinite _
  have hcardimg : ((fun c : G => c * x₀ * c⁻¹) '' Cz).ncard = Cz.ncard :=
    Set.InjOn.ncard_image hinj
  have hcardF : F.ncard ≤ Cz.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]; exact hcard
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcardimg]; exact hcardF) hFfin).symm

/-- **All product-one triples are conjugate to the distinguished one.**  This is the geometric
content of rigidity: the last entry can be conjugated onto `z`, and the resulting first entry lies
in the structure-constant fibre, which is a single `C_G(z)`-orbit. -/
theorem prodOneTuples_eq_orbit_of_card_prodOneFibre [Finite G] {C : Fin 3 → ConjClasses G}
    {x₀ z : G} (hZ : Subgroup.center G = ⊥) (hgen : Subgroup.closure ({x₀, z} : Set G) = ⊤)
    (hx₀ : x₀ ∈ prodOneFibre (C 0) (C 1) z) (hz : ConjClasses.mk z = C 2)
    (hcard : Nat.card (prodOneFibre (C 0) (C 1) z)
        ≤ Nat.card (Subgroup.centralizer ({z} : Set G))) :
    prodOneTuples C = MulAction.orbit (ConjAct G) (fibreTriple x₀ z) := by
  have himg := prodOneFibre_eq_image_of_card hZ hgen hx₀ hcard
  apply Set.Subset.antisymm
  · intro g hg
    -- move the last entry onto `z`
    have hconj : IsConj z (g 2) := by
      rw [← ConjClasses.mk_eq_mk_iff_isConj, hz]; exact (hg.1 2).symm
    obtain ⟨c, hcc⟩ := hconj
    have hcz : (c : G) * z * (c : G)⁻¹ = g 2 := by
      have h : (c : G) * z = g 2 * (c : G) := hcc
      rw [h]; group
    set u : ConjAct G := ConjAct.toConjAct ((c : G)⁻¹) with hu
    have hug : u • g ∈ prodOneTuples C := smul_mem_prodOneTuples hg u
    have hcoord : ∀ i, (u • g) i = (c : G)⁻¹ * g i * (c : G) := by
      intro i
      rw [Pi.smul_apply, ConjAct.smul_def, hu, ConjAct.ofConjAct_toConjAct, inv_inv]
    have hu2 : (u • g) 2 = z := by rw [hcoord 2, ← hcz]; group
    have h1 : (u • g) 1 = ((u • g) 0)⁻¹ * z⁻¹ := by
      rw [mid_of_prod_one hug.2, hu2]
    -- the first entry now lies in the fibre
    have hu0 : (u • g) 0 ∈ prodOneFibre (C 0) (C 1) z := by
      refine ⟨hug.1 0, ?_⟩
      rw [← h1]; exact hug.1 1
    rw [himg] at hu0
    obtain ⟨d, hd, hdx⟩ := hu0
    -- and is a `C_G(z)`-conjugate of `x₀`, so the whole triple is
    have hdz : (d : G) * z = z * (d : G) := (Subgroup.mem_centralizer_singleton_iff).1 hd
    have hdzi : d * z⁻¹ = z⁻¹ * d := mul_inv_comm_of_comm hdz
    have hdz' : d⁻¹ * z⁻¹ * d = z⁻¹ := by
      calc d⁻¹ * z⁻¹ * d = d⁻¹ * (z⁻¹ * d) := by group
        _ = d⁻¹ * (d * z⁻¹) := by rw [hdzi]
        _ = z⁻¹ := by group
    have hd0 : (u • g) 0 = d * x₀ * d⁻¹ := hdx.symm
    have heq : u • g = (ConjAct.toConjAct d) • fibreTriple x₀ z := by
      have hsm : ∀ j : Fin 3, ((ConjAct.toConjAct d) • fibreTriple x₀ z) j
          = d * fibreTriple x₀ z j * d⁻¹ := fun j => by
        rw [Pi.smul_apply, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
      funext i
      fin_cases i
      · rw [hsm]
        show (u • g) 0 = d * x₀ * d⁻¹
        exact hd0
      · rw [hsm]
        show (u • g) 1 = d * (x₀⁻¹ * z⁻¹) * d⁻¹
        rw [h1, hd0]
        calc (d * x₀ * d⁻¹)⁻¹ * z⁻¹ = d * x₀⁻¹ * (d⁻¹ * z⁻¹ * d) * d⁻¹ := by group
          _ = d * x₀⁻¹ * z⁻¹ * d⁻¹ := by rw [hdz']
          _ = d * (x₀⁻¹ * z⁻¹) * d⁻¹ := by group
      · rw [hsm]
        show (u • g) 2 = d * z * d⁻¹
        rw [hu2, hdz]; group
    refine ⟨u⁻¹ * ConjAct.toConjAct d, ?_⟩
    show (u⁻¹ * ConjAct.toConjAct d) • fibreTriple x₀ z = g
    rw [mul_smul, ← heq, ← mul_smul, inv_mul_cancel, one_smul]
  · rintro _ ⟨x, rfl⟩
    exact smul_mem_prodOneTuples (fibreTriple_mem_prodOneTuples hx₀ hz) x

/-- **Rigidity from a single structure constant.**  For a centerless finite group: if `x₀` and `z`
generate `G`, the triple `(x₀, x₀⁻¹z⁻¹, z)` lies in the prescribed classes, and the structure
constant `#{x ∈ C₀ : x⁻¹z⁻¹ ∈ C₁}` equals `|C_G(z)|`, then
`Nat.card (rigidTuples C) = Nat.card G`. -/
theorem rigid_of_card_prodOneFibre [Finite G] {C : Fin 3 → ConjClasses G} {x₀ z : G}
    (hZ : Subgroup.center G = ⊥) (hgen : Subgroup.closure ({x₀, z} : Set G) = ⊤)
    (hx₀ : x₀ ∈ prodOneFibre (C 0) (C 1) z) (hz : ConjClasses.mk z = C 2)
    (hcard : Nat.card (prodOneFibre (C 0) (C 1) z)
        ≤ Nat.card (Subgroup.centralizer ({z} : Set G))) :
    Nat.card (rigidTuples C) = Nat.card G := by
  have hgen' : Subgroup.closure (Set.range (fibreTriple x₀ z)) = ⊤ :=
    (fibreTriple_mem_rigidTuples hx₀ hz hgen).2.2
  refine rigid_of_card_prodOneTuples hZ ⟨_, fibreTriple_mem_rigidTuples hx₀ hz hgen⟩ ?_
  rw [prodOneTuples_eq_orbit_of_card_prodOneFibre hZ hgen hx₀ hz hcard,
    Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact card_orbit_conjAct hgen' hZ

/-- **A rigidity certificate from one structure constant.**  Everything except the rationality of
the three classes is paid for by a single conjugacy-class enumeration. -/
def RigidityCertificate.ofStructureConstant [Finite G] (C : Fin 3 → ConjClasses G) {x₀ z : G}
    (hZ : Subgroup.center G = ⊥) (hrat : ∀ i, IsRationalClass (C i))
    (hgen : Subgroup.closure ({x₀, z} : Set G) = ⊤)
    (hx₀ : x₀ ∈ prodOneFibre (C 0) (C 1) z) (hz : ConjClasses.mk z = C 2)
    (hcard : Nat.card (prodOneFibre (C 0) (C 1) z)
        ≤ Nat.card (Subgroup.centralizer ({z} : Set G))) :
    RigidityCertificate G where
  r := 3
  C := C
  center_triv := fun g hg => by rw [hZ, Subgroup.mem_bot] at hg; exact hg
  rational := hrat
  gen := ⟨_, fibreTriple_mem_rigidTuples hx₀ hz hgen⟩
  rigid := rigid_of_card_prodOneFibre hZ hgen hx₀ hz hcard

end Rigidity
