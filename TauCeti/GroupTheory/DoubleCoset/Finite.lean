/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index

/-!
# Finiteness of the double-coset quotient

A double coset `HgK` is a union of left cosets of `K`, so the double cosets `H \ G / K` are a
quotient of `G ⧸ K`: the map `gK ↦ HgK` is well defined and surjective
(`TauCeti.doubleCosetMk_out_mk` is the well-definedness, in the form the surjection uses).
Consequently `H \ G / K` is finite as soon as `K` has finite index, with no finiteness assumption
on `G` itself.

This is the instance that lets a sum be taken over `H \ G / K`; the Mackey decomposition
(`TauCeti.RepresentationTheory.Induction.Mackey.Basic`) uses it, where the index of the subgroup
being induced from is the only finiteness available.

The double cosets partition `G`, so their sizes add up to the order of `G`
(`Subgroup.sum_card_quotToDoubleCoset`).

## Main statements

* `TauCeti.finite_doubleCosetQuotient`: `H \ G / K` is finite when `K` has finite index in `G`.
* `Subgroup.sum_card_quotToDoubleCoset`: the sizes of the double cosets add up to `|G|`.
* `Subgroup.sum_card_quotToDoubleCoset_div_card_eq_index`: the numbers `|HgK| / |H|` add up
  to the index of `H`.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- Replacing an element by the chosen representative of its left `K`-coset does not change its
double coset. -/
theorem doubleCosetMk_out_mk (H K : Subgroup G) (g : G) :
    DoubleCoset.mk H K (QuotientGroup.mk g : G ⧸ K).out = DoubleCoset.mk H K g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  rw [hk, DoubleCoset.mk_mul_mem]

/-- **The double cosets `H \ G / K` are finite when `K` has finite index**: they are the image of
the finite set `G ⧸ K` under `gK ↦ HgK`. -/
instance finite_doubleCosetQuotient (H K : Subgroup G) [K.FiniteIndex] :
    Finite (DoubleCoset.Quotient (H : Set G) (K : Set G)) :=
  Finite.of_surjective (fun t : G ⧸ K => DoubleCoset.mk H K t.out) fun d =>
    ⟨QuotientGroup.mk d.out, (doubleCosetMk_out_mk H K d.out).trans (DoubleCoset.out_eq' d)⟩

end TauCeti

namespace Subgroup

variable {G : Type*} [Group G]

/-- **The double cosets partition the group**: the sizes of the double cosets `HgK` add up to the
order of `G`. For infinite `G` both sides are `0`: a finite double coset forces `H` and `K` to be
finite, and then `G`, a finite union of finite double cosets, would be finite. -/
theorem sum_card_quotToDoubleCoset (H K : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (K : Set G))] :
    ∑ q, Nat.card (DoubleCoset.quotToDoubleCoset H K q) = Nat.card G := by
  by_cases hG : Finite G
  · rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (DoubleCoset.mk H K)), Nat.card_sigma]
    exact Fintype.sum_congr _ _ fun q =>
      Nat.card_congr (Equiv.subtypeEquivRight fun a => DoubleCoset.mem_quotToDoubleCoset_iff q a)
  have hGi : Infinite G := not_finite_iff_infinite.1 hG
  rw [Nat.card_eq_zero_of_infinite]
  -- the double coset of `q` consists of the products `h * a * k`, for any representative `a`
  have hmem (q : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
      ∃ a : G, ∀ x : G, x ∈ DoubleCoset.quotToDoubleCoset H K q ↔
        ∃ h ∈ H, ∃ k ∈ K, x = h * a * k := by
    obtain ⟨a, rfl⟩ : ∃ a, DoubleCoset.mk H K a = q := ⟨q.out, DoubleCoset.out_eq' q⟩
    refine ⟨a, fun x ↦ ?_⟩
    rw [DoubleCoset.mem_quotToDoubleCoset_iff, eq_comm, DoubleCoset.eq]
  by_cases hHK : Finite H ∧ Finite K
  · -- every double coset is finite, so `G`, their union, would be finite
    obtain ⟨hH, hK⟩ := hHK
    refine absurd ?_ hG
    have hfin (q : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
        (DoubleCoset.quotToDoubleCoset H K q).Finite := by
      obtain ⟨a, ha⟩ := hmem q
      refine (Set.finite_range fun p : H × K ↦ (p.1 : G) * a * p.2).subset fun x hx ↦ ?_
      obtain ⟨h, hh, k, hk, rfl⟩ := (ha x).1 hx
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
    have hall : (Set.univ : Set G).Finite := by
      rw [← DoubleCoset.iUnion_quotToDoubleCoset H K]
      exact Set.finite_iUnion hfin
    exact Set.finite_univ_iff.1 hall
  · -- some factor is infinite, and each double coset contains a translate of it
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    obtain ⟨a, ha⟩ := hmem q
    rw [not_and_or, not_finite_iff_infinite, not_finite_iff_infinite] at hHK
    have : Infinite (DoubleCoset.quotToDoubleCoset H K q) := by
      rcases hHK with hH | hK
      · exact Infinite.of_injective (fun h : H ↦ (⟨(h : G) * a,
          (ha _).2 ⟨h, h.2, 1, K.one_mem, by simp⟩⟩ : DoubleCoset.quotToDoubleCoset H K q))
          fun h h' hh ↦ Subtype.ext (mul_right_cancel (congrArg Subtype.val hh))
      · exact Infinite.of_injective (fun k : K ↦ (⟨a * k,
          (ha _).2 ⟨1, H.one_mem, k, k.2, by simp⟩⟩ : DoubleCoset.quotToDoubleCoset H K q))
          fun k k' hk ↦ Subtype.ext (mul_left_cancel (congrArg Subtype.val hk))
    exact Nat.card_eq_zero_of_infinite

/-- **The double cosets count the right cosets**: each double coset `HsK` of a finite group is a
union of `|HsK| / |H|` right cosets of `H`, and these numbers add up, over `H \ G / K`, to the
index of `H`. -/
theorem sum_card_quotToDoubleCoset_div_card_eq_index [Finite G] (H K : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (K : Set G))] :
    ∑ q, Nat.card (DoubleCoset.quotToDoubleCoset H K q) / Nat.card H = H.index := by
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H)) ?_
  rw [Finset.sum_mul, Subgroup.index_mul_card, ← sum_card_quotToDoubleCoset H K]
  refine Finset.sum_congr rfl fun q _ => Nat.div_mul_cancel ?_
  -- Inversion turns right cosets of `H` into left cosets, counted by Mathlib's formula.
  rw [DoubleCoset.quotToDoubleCoset, DoubleCoset.doubleCoset,
    ← Nat.card_image_of_injective inv_injective, Set.image_inv_eq_inv]
  simp only [mul_inv_rev, inv_coe_set, ← mul_assoc]
  rw [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient]
  exact dvd_mul_right _ _

end Subgroup
