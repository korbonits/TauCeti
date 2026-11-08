/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# Integrality arguments for rational numbers

A rational strictly between two consecutive integers, congruent modulo integers to `c`, shows that
`c` is not an integer (`TauCeti.not_exists_intCast_of_lt_of_lt_add_one`), and a relation
`x + θ y = z + 1` with `x`, `y` rational determines `θ` as a rational number
(`TauCeti.eq_cast_div_of_add_mul_eq`).
-/

public section

namespace TauCeti

/-- A rational strictly between two consecutive integers, congruent modulo integers to `c`, shows
that `c` is not an integer. -/
theorem not_exists_intCast_of_lt_of_lt_add_one {x c : ℚ} {z : ℤ}
    (hx : ∃ m : ℤ, x - c = m) (h₁ : (z : ℚ) < x) (h₂ : x < z + 1) : ¬∃ m : ℤ, c = m := by
  rintro ⟨m, rfl⟩
  obtain ⟨m', hm'⟩ := hx
  have hk' : x = ((m' + m : ℤ) : ℚ) := by
    push_cast
    linarith
  rw [hk'] at h₁ h₂
  have h₁' : z < m' + m := by exact_mod_cast h₁
  have h₂' : m' + m < z + 1 := by exact_mod_cast h₂
  omega

/-- If `x + θ y = z + 1` in a field `𝕜` of characteristic zero, with `x`, `y` rational and `y`
nonzero, then `θ` is the rational number `(z + 1 - x) / y`. -/
theorem eq_cast_div_of_add_mul_eq {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {x y : ℚ} {z : ℤ} {θ : 𝕜}
    (hy : y ≠ 0) (h : (x : 𝕜) + θ * y = z + 1) : θ = (((z + 1 - x) / y : ℚ) : 𝕜) := by
  push_cast
  rw [eq_div_iff (by exact_mod_cast hy)]
  linear_combination h

end TauCeti
