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

For a list `D` of pairs `(τ, d)` of positive durations and an integer weight `c τ`, the rational
heights `∑_{j<k} dⱼ c(τⱼ)` rising strictly on a window force `c(τₖ) > 0` there
(`List.pos_of_rise_sum_take_map_mul`). If moreover the heights are congruent modulo integers to the
break times `aₖ` times the weights, then the products `aₖ c(τₖ)` at the interior breaks of the
window are not integers (`List.window_facts_of_sum_take_map_mul`).
-/

public section

namespace List

/-- Along a window where the rational heights `∑ dₖ c(τₖ)` rise strictly, the integers `c(τₖ)` are
positive, as the durations `dₖ` are. -/
theorem pos_of_rise_sum_take_map_mul {α : Type*} (c : α → ℤ) (D : List (α × ℚ))
    (hdpos : ∀ k (hk : k < D.length), 0 < D[k].2) {k₀ j₁ : ℕ} (hgt : ℕ → ℚ)
    (hhgt : ∀ k, hgt k = ((D.take k).map fun p ↦ p.2 * (c p.1 : ℚ)).sum)
    (hrise : ∀ k, k₀ ≤ k → k ≤ j₁ → hgt k < hgt (k + 1)) :
    ∀ k (hk : k < D.length), k₀ ≤ k → k ≤ j₁ → 0 < c D[k].1 := fun k hk hk₀ hkj ↦ by
  have := hrise k hk₀ hkj
  have hsucc : ((D.take (k + 1)).map fun p : α × ℚ ↦ p.2 * (c p.1 : ℚ)).sum =
      ((D.take k).map fun p : α × ℚ ↦ p.2 * (c p.1 : ℚ)).sum + D[k].2 * (c D[k].1 : ℚ) := by
    rw [List.map_take, List.map_take, List.sum_take_succ _ _ (by simpa using hk),
      List.getElem_map]
  rw [hhgt, hhgt, hsucc] at this
  have h : (0 : ℚ) < c D[k].1 := pos_of_mul_pos_right (by linarith) (hdpos k hk).le
  exact_mod_cast h

/-- **The integrality data of a window.** Let the rational heights `hgt k = ∑_{j<k} dⱼ c(τⱼ)` of a
list `D` start at the integer `z` at `k₀`, rise strictly up to `j₁`, and reach `z + 1` at the
fraction `θ` of the entry `j₁`, and let them be congruent modulo integers to `aₖ c(τₖ)` at the
break `aₖ`. Then `aₖ c(τₖ)` is not an integer strictly inside the window, `c(τₖ) ≤ 0` for the
entry just before the window provided the height there is at most `z` (the hypothesis `hmin`), and
`(a_{j₁} + θ d_{j₁}) c(τ_{j₁})` is an integer. -/
theorem window_facts_of_sum_take_map_mul {α : Type*} (c : α → ℤ) (D : List (α × ℚ))
    (hdpos : ∀ k (hk : k < D.length), 0 < D[k].2) {k₀ j₁ : ℕ} (hk₀j₁ : k₀ ≤ j₁)
    (hj₁ : j₁ < D.length) (hgt : ℕ → ℚ)
    (hhgt : ∀ k, hgt k = ((D.take k).map fun p ↦ p.2 * (c p.1 : ℚ)).sum) {z : ℤ}
    (hk₀ : hgt k₀ = z) (hrise : ∀ k, k₀ ≤ k → k ≤ j₁ → hgt k < hgt (k + 1))
    (hmin : ∀ k, k + 1 = k₀ → (z : ℚ) ≤ hgt k)
    (hcong : ∀ k (hk : k < D.length),
      ∃ m : ℤ, hgt k - ((D.take k).map Prod.snd).sum * (c D[k].1 : ℚ) = m)
    {θ : ℚ} (hθpos : 0 < θ) (hθd : θ * (D[j₁].2 * (c D[j₁].1 : ℚ)) = z + 1 - hgt j₁) :
    (∀ k (hk : k < D.length), k₀ < k → k ≤ j₁ →
      ¬∃ m : ℤ, ((D.take k).map Prod.snd).sum * (c D[k].1 : ℚ) = m) ∧
    (∀ k (hk : k < D.length), k + 1 = k₀ → c D[k].1 ≤ 0) ∧
    ∃ m : ℤ, (((D.take j₁).map Prod.snd).sum + θ * D[j₁].2) * (c D[j₁].1 : ℚ) = m := by
  have hpos := pos_of_rise_sum_take_map_mul c D hdpos hgt hhgt hrise
  have hdH : 0 < D[j₁].2 * (c D[j₁].1 : ℚ) :=
    mul_pos (hdpos j₁ hj₁) (by exact_mod_cast hpos j₁ hj₁ hk₀j₁ le_rfl)
  refine ⟨fun k hk hk₀' hkj ↦ ?_, fun k hk hkk ↦ ?_, ?_⟩
  · have hlt := TauCeti.lt_and_lt_of_lt_succ (u := (z : ℚ) + 1) hrise hk₀
      (by nlinarith [mul_pos hθpos hdH]) hk₀' hkj
    exact TauCeti.not_exists_intCast_of_lt_of_lt_add_one (hcong k hk) hlt.1 hlt.2
  · have := hmin k hkk
    have hsucc : ((D.take (k + 1)).map fun p : α × ℚ ↦ p.2 * (c p.1 : ℚ)).sum =
        ((D.take k).map fun p : α × ℚ ↦ p.2 * (c p.1 : ℚ)).sum + D[k].2 * (c D[k].1 : ℚ) := by
      rw [List.map_take, List.map_take, List.sum_take_succ _ _ (by simpa using hk),
        List.getElem_map]
    rw [← hhgt, ← hhgt, hkk, hk₀] at hsucc
    have : (c D[k].1 : ℚ) ≤ 0 := nonpos_of_mul_nonpos_right (by linarith) (hdpos k hk)
    exact_mod_cast this
  · obtain ⟨m, hm⟩ := hcong j₁ hj₁
    refine ⟨z + 1 - m, ?_⟩
    push_cast
    linear_combination hθd - hm

end List
