/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.List.Basic

/-!
# Subdividing an entry of a list of durations

Cutting the entry `(τ, d)` of a list of pairs into the two entries `(τ, θ d)` and
`(τ, (1 - θ) d)` leaves the earlier entries and partial sums of durations unchanged
(`List.subdivide_getElem_and_sum_take`).
-/

public section

namespace List

/-- Entries and partial sums of durations of the list obtained by subdividing the entry
`l[j₁] = (τ, d)` at the fraction `θ`: before the cut they are those of `l`, the entry at `j₁` is
`(τ, θ d)` and the one after it is `(τ, (1 - θ) d)`. -/
theorem subdivide_getElem_and_sum_take {α : Type*} {l : List (α × ℚ)} {j₁ : ℕ}
    (hj₁ : j₁ < l.length) {τ : α} {d : ℚ} (hτd : l[j₁] = (τ, d)) (θ : ℚ)
    {Dp : List (α × ℚ)}
    (hDp : Dp = l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1)) :
    Dp.length = l.length + 1 ∧
      (∀ k (hk : k < Dp.length) (hk' : k < l.length), k < j₁ → Dp[k] = l[k]) ∧
      (∀ h : j₁ < Dp.length, Dp[j₁] = (τ, θ * d)) ∧
      (∀ h : j₁ + 1 < Dp.length, Dp[j₁ + 1] = (τ, (1 - θ) * d)) ∧
      (∀ k (hk : k < Dp.length) (hk' : k < l.length), k ≤ j₁ → Dp[k].1 = l[k].1) ∧
      (∀ k ≤ j₁, ((Dp.take k).map Prod.snd).sum = ((l.take k).map Prod.snd).sum) ∧
      ((Dp.take (j₁ + 1)).map Prod.snd).sum = ((l.take j₁).map Prod.snd).sum + θ * d := by
  subst hDp
  have hlen_take : (l.take j₁).length = j₁ := by simp; omega
  have hlt : ∀ k (hk : k < (l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1)).length)
      (hk' : k < l.length), k < j₁ →
      (l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1))[k] = l[k] := by
    intro k hk hk' hkj
    rw [List.getElem_append_left (by rw [hlen_take]; omega), List.getElem_take]
  have hj : ∀ h : j₁ < (l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1)).length,
      (l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1))[j₁] = (τ, θ * d) := by
    intro h
    rw [List.getElem_append_right (by omega)]
    simp [hlen_take]
  refine ⟨by simp; omega, hlt, hj, fun h ↦ ?_, fun k hk hk' hkj ↦ ?_, fun k hk ↦ ?_, ?_⟩
  · rw [List.getElem_append_right (by omega)]
    simp [hlen_take]
  · rcases hkj.lt_or_eq with hkj | rfl
    · rw [hlt k hk hk' hkj]
    · rw [hj hk, hτd]
  · rw [List.take_append_of_le_length (by omega), List.take_take, min_eq_left hk]
  · rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show j₁ + 1 - j₁ = 1 by omega]
    simp

end List
