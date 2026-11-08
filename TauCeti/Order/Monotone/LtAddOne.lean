/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Order.Monotone.Basic

/-!
# Values of a sequence rising strictly on a window

If a rational sequence rises strictly on a window `[k₀, j₁]`, starts at `z` and stays below `z + 1`
at `j₁`, its values strictly inside the window lie strictly between `z` and `z + 1`
(`lt_and_lt_add_one_of_lt_succ`).
-/

public section

/-- If a sequence rises strictly on the window `[k₀, j₁]`, starts at `z` there and stays below
`z + 1` at `j₁`, then its values strictly inside the window lie strictly between `z` and
`z + 1`. -/
theorem lt_and_lt_add_one_of_lt_succ {hgt : ℕ → ℚ} {k₀ j₁ : ℕ} {z : ℚ}
    (hrise : ∀ k, k₀ ≤ k → k ≤ j₁ → hgt k < hgt (k + 1)) (hk₀ : hgt k₀ = z)
    (hj₁ : hgt j₁ < z + 1) {k : ℕ} (hk₀k : k₀ < k) (hkj : k ≤ j₁) : z < hgt k ∧ hgt k < z + 1 := by
  have hsm : StrictMonoOn hgt (Set.Icc k₀ j₁) :=
    strictMonoOn_of_lt_add_one Set.ordConnected_Icc fun m _ hm hm' ↦
      hrise m hm.1 (by simp only [Set.mem_Icc] at hm'; omega)
  refine ⟨?_, ?_⟩
  · rw [← hk₀]
    exact hsm ⟨le_rfl, by omega⟩ ⟨hk₀k.le, hkj⟩ hk₀k
  · exact (hsm.monotoneOn ⟨hk₀k.le, hkj⟩ ⟨by omega, le_rfl⟩ hkj).trans_lt hj₁
