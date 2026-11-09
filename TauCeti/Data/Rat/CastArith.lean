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
# Integrality arguments in ordered rings and fields

An element of an ordered ring strictly between two consecutive integers, congruent modulo integers
to `c`, shows that `c` is not an integer (`TauCeti.not_exists_intCast_of_lt_of_lt_add_one`), and a
relation `x + θ y = r` with `x`, `y`, `r` rational and `y` nonzero determines `θ` as a rational
number (`TauCeti.eq_ratCast_div_of_add_mul_eq`). Only the latter lemma involves rational numbers;
the former holds in any ordered ring.
-/

public section

namespace TauCeti

/-- An element of an ordered ring strictly between two consecutive integers, congruent modulo
integers to `c`, shows that `c` is not an integer. -/
theorem not_exists_intCast_of_lt_of_lt_add_one {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {x c : R} {z : ℤ}
    (hx : ∃ m : ℤ, x - c = m) (h₁ : (z : R) < x) (h₂ : x < z + 1) : ¬∃ m : ℤ, c = m := by
  rintro ⟨m, rfl⟩
  obtain ⟨m', hm'⟩ := hx
  have hk' : x = ((m' + m : ℤ) : R) := by
    push_cast
    linarith
  rw [hk'] at h₁ h₂
  have h₁' : z < m' + m := by exact_mod_cast h₁
  have h₂' : m' + m < z + 1 := by exact_mod_cast h₂
  omega

/-- If `x + θ y = r` in a field `𝕜` of characteristic zero, with `x`, `y`, `r` rational and `y`
nonzero, then `θ` is the rational number `(r - x) / y`. -/
theorem eq_ratCast_div_of_add_mul_eq {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {x y r : ℚ} {θ : 𝕜}
    (hy : y ≠ 0) (h : (x : 𝕜) + θ * y = r) : θ = (((r - x) / y : ℚ) : 𝕜) := by
  push_cast
  rw [eq_div_iff (by exact_mod_cast hy)]
  linear_combination h

end TauCeti
