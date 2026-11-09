/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
public import TauCeti.Data.Rat.CastArith
public import TauCeti.Order.Monotone.LtAddOne

/-!
# Integrality data of a window of rising heights

For a list `D` and weights `f`, `g` of its entries, where the partial sums of `fⱼ gⱼ` rise strictly
at an entry `k` with `0 ≤ fₖ`, we get `0 < gₖ`
(`List.pos_of_sum_take_map_mul_lt_sum_take_succ_map_mul`). For a list `D` of pairs `(τ, d)` of
durations and a weight `c τ`, suppose the integer weights `c(τₖ)` give heights
`hₖ = ∑_{j<k} dⱼ c(τⱼ)` that start at an integer `z` at `k₀`, satisfy `hₖ < hₖ₊₁` for
`k₀ ≤ k ≤ j₁`, and reach `z + 1` at the positive fraction `θ` of the entry `j₁`, and suppose the
heights are congruent modulo integers to the break times `aₖ` times the weights. Then `aₖ c(τₖ)`
is not an integer for `k₀ < k ≤ j₁`, `c(τₖ) ≤ 0` just before the window if the height there is at
least `z`, and `(a_{j₁} + θ d_{j₁}) c(τ_{j₁})` is an integer
(`List.not_exists_intCast_and_nonpos_and_exists_intCast_of_sum_take_map_mul`).
-/

public section

namespace List

variable {α : Type*}

/-- Where the partial sums of `fⱼ gⱼ` rise strictly at an entry `k` with `0 ≤ fₖ`, the weight `gₖ`
of that entry is positive. -/
theorem pos_of_sum_take_map_mul_lt_sum_take_succ_map_mul {R : Type*} [Semiring R] [LinearOrder R]
    [IsStrictOrderedRing R] (f g : α → R) (D : List α) {k : ℕ} (hk : k < D.length)
    (hd : 0 ≤ f D[k])
    (h : ((D.take k).map fun a ↦ f a * g a).sum <
      ((D.take (k + 1)).map fun a ↦ f a * g a).sum) :
    0 < g D[k] := by
  rw [List.map_take, List.map_take, List.sum_take_succ _ _ (by simpa using hk),
    List.getElem_map] at h
  have h' : 0 < f D[k] * g D[k] := by simpa using h
  exact pos_of_mul_pos_right h' hd

/-- **The integrality data of a window.** Let `D` be a list of pairs `(τ, d)` of positive durations
and integer weights `c τ`, and write `hₖ = ∑_{j<k} dⱼ c(τⱼ)` for the heights. Suppose `hₖ₀ = z` is
an integer, `hₖ < hₖ₊₁` for `k₀ ≤ k ≤ j₁` with `c(τₖ) > 0`, the height reaches `z + 1` at the
fraction `θ` of the entry `j₁`, and `hₖ` is congruent modulo integers to `aₖ c(τₖ)` at the break
`aₖ = ∑_{j<k} dⱼ`. Then `aₖ c(τₖ)` is not an integer for `k₀ < k ≤ j₁`, `c(τₖ) ≤ 0` for the entry
just before the window provided the height there is at least `z` (the hypothesis `hmin`), and
`(a_{j₁} + θ d_{j₁}) c(τ_{j₁})` is an integer. -/
theorem not_exists_intCast_and_nonpos_and_exists_intCast_of_sum_take_map_mul
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c : α → ℤ) (D : List (α × K)) {k₀ j₁ : ℕ}
    (hdpos : ∀ k (hk : k < D.length), 0 < D[k].2)
    (hpos : ∀ k (hk : k < D.length), k₀ ≤ k → k ≤ j₁ → 0 < c D[k].1) (hk₀j₁ : k₀ ≤ j₁)
    (hj₁ : j₁ < D.length) {z : ℤ}
    (hk₀ : ((D.take k₀).map fun p ↦ p.2 * (c p.1 : K)).sum = z)
    (hrise : ∀ k, k₀ ≤ k → k ≤ j₁ →
      ((D.take k).map fun p ↦ p.2 * (c p.1 : K)).sum <
        ((D.take (k + 1)).map fun p ↦ p.2 * (c p.1 : K)).sum)
    (hmin : ∀ k, k + 1 = k₀ → (z : K) ≤ ((D.take k).map fun p ↦ p.2 * (c p.1 : K)).sum)
    (hcong : ∀ k (hk : k < D.length), ∃ m : ℤ,
      ((D.take k).map fun p ↦ p.2 * (c p.1 : K)).sum -
        ((D.take k).map Prod.snd).sum * (c D[k].1 : K) = m)
    {θ : K} (hθpos : 0 < θ)
    (hθd : θ * (D[j₁].2 * (c D[j₁].1 : K)) =
      z + 1 - ((D.take j₁).map fun p ↦ p.2 * (c p.1 : K)).sum) :
    (∀ k (hk : k < D.length), k₀ < k → k ≤ j₁ →
      ¬∃ m : ℤ, ((D.take k).map Prod.snd).sum * (c D[k].1 : K) = m) ∧
    (∀ k (hk : k < D.length), k + 1 = k₀ → c D[k].1 ≤ 0) ∧
    ∃ m : ℤ, (((D.take j₁).map Prod.snd).sum + θ * D[j₁].2) * (c D[j₁].1 : K) = m := by
  have hdH : 0 < D[j₁].2 * (c D[j₁].1 : K) :=
    mul_pos (hdpos j₁ hj₁) (by exact_mod_cast hpos j₁ hj₁ hk₀j₁ le_rfl)
  refine ⟨fun k hk hk₀' hkj ↦ ?_, fun k hk hkk ↦ ?_, ?_⟩
  · have hlt := TauCeti.lt_and_lt_of_lt_add_one (u := (z : K) + 1) hrise hk₀
      (by nlinarith [mul_pos hθpos hdH]) hk₀' hkj
    exact TauCeti.not_exists_intCast_of_lt_of_lt_add_one (hcong k hk) hlt.1 hlt.2
  · have hle := hmin k hkk
    have hsucc : ((D.take (k + 1)).map fun p ↦ p.2 * (c p.1 : K)).sum =
        ((D.take k).map fun p ↦ p.2 * (c p.1 : K)).sum + D[k].2 * (c D[k].1 : K) := by
      rw [List.map_take, List.map_take, List.sum_take_succ _ _ (by simpa using hk),
        List.getElem_map]
    rw [hkk, hk₀] at hsucc
    have : (c D[k].1 : K) ≤ 0 := nonpos_of_mul_nonpos_right (by linarith) (hdpos k hk)
    exact_mod_cast this
  · obtain ⟨m, hm⟩ := hcong j₁ hj₁
    refine ⟨z + 1 - m, ?_⟩
    push_cast
    linear_combination hθd - hm

end List
