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
`k₀ ≤ k ≤ j₁`, and stay below `z + 1` at `j₁`, and suppose the
heights are congruent modulo integers to the break times `aₖ` times the weights. Then `aₖ c(τₖ)`
is not an integer for `k₀ < k ≤ j₁`
(`List.not_exists_intCast_sum_take_map_snd_mul`), and `(a_{j₁} + θ d_{j₁}) c(τ_{j₁})` is an
integer (`List.exists_intCast_sum_take_map_snd_add_mul`). Moreover `c(τₖ) ≤ 0` for the entry just
before the window if the height there is at least `z`
(`List.nonpos_of_sum_take_map_mul_eq`). The step `List.sum_take_succ_map_get` computes the height
after an entry.
-/

public section

namespace List

variable {α : Type*}

/-- The partial sum of `g` through an entry is the partial sum before it plus the entry's own
term. -/
theorem sum_take_succ_map_get {M : Type*} [AddMonoid M] (g : α → M) (D : List α) {k : ℕ}
    (hk : k < D.length) :
    ((D.take (k + 1)).map g).sum = ((D.take k).map g).sum + g D[k] := by
  rw [List.map_take, List.map_take, List.sum_take_succ _ _ (by simpa using hk),
    List.getElem_map]

/-- Where the partial sums of `fⱼ gⱼ` rise strictly at an entry `k` with `0 ≤ fₖ`, the weight `gₖ`
of that entry is positive. -/
theorem pos_of_sum_take_map_mul_lt_sum_take_succ_map_mul {R : Type*} [Semiring R] [LinearOrder R]
    [IsStrictOrderedRing R] (f g : α → R) (D : List α) {k : ℕ} (hk : k < D.length)
    (hd : 0 ≤ f D[k])
    (h : ((D.take k).map fun a ↦ f a * g a).sum <
      ((D.take (k + 1)).map fun a ↦ f a * g a).sum) :
    0 < g D[k] := by
  have h' : 0 < f D[k] * g D[k] := by
    rw [sum_take_succ_map_get (fun a ↦ f a * g a) D hk] at h
    simpa using h
  exact pos_of_mul_pos_right h' hd

/-- **Non-integrality in a window.** Let `D` be a list of pairs `(τ, d)` of durations and integer
weights `c τ`, and write `hₖ = ∑_{j<k} dⱼ c(τⱼ)` for the heights. Suppose `hₖ₀ = z` is
an integer, `hₖ < hₖ₊₁` for `k₀ ≤ k ≤ j₁` (that is, `dₖ c(τₖ) > 0` there), the height `hⱼ₁` is
below `z + 1`, and `hₖ` is congruent modulo integers to
`aₖ c(τₖ)` at the break `aₖ = ∑_{j<k} dⱼ`. Then `aₖ c(τₖ)` is not an integer for
`k₀ < k ≤ j₁`. -/
theorem not_exists_intCast_sum_take_map_snd_mul
    {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    (c : α → ℤ) (D : List (α × K)) {k₀ j₁ : ℕ} {z : ℤ}
    (hk₀ : ((D.take k₀).map fun p ↦ p.2 * (c p.1 : K)).sum = z)
    (hrise : ∀ k, k₀ ≤ k → k ≤ j₁ →
      ((D.take k).map fun p ↦ p.2 * (c p.1 : K)).sum <
        ((D.take (k + 1)).map fun p ↦ p.2 * (c p.1 : K)).sum)
    (hcong : ∀ k (hk : k < D.length), ∃ m : ℤ,
      ((D.take k).map fun p ↦ p.2 * (c p.1 : K)).sum -
        ((D.take k).map Prod.snd).sum * (c D[k].1 : K) = m)
    (hj₁z : ((D.take j₁).map fun p ↦ p.2 * (c p.1 : K)).sum < z + 1) :
    ∀ k (hk : k < D.length), k₀ < k → k ≤ j₁ →
      ¬∃ m : ℤ, ((D.take k).map Prod.snd).sum * (c D[k].1 : K) = m := by
  intro k hk hk₀' hkj
  have hlt := TauCeti.lt_and_lt_of_lt_add_one (u := (z : K) + 1) hrise hk₀ hj₁z hk₀' hkj
  exact TauCeti.not_exists_intCast_of_lt_of_lt_add_one (hcong k hk) hlt.1 hlt.2

/-- **The weight before a window is nonpositive.** If the height `hₖ = ∑_{j<k} dⱼ c(τⱼ)` before an
entry `k` of positive duration is at least `z` and the height after it is `z`, then `c(τₖ) ≤ 0`. -/
theorem nonpos_of_sum_take_map_mul_eq {K : Type*} [CommRing K] [LinearOrder K]
    [IsStrictOrderedRing K] (c : α → ℤ) (D : List (α × K)) {k : ℕ} (hk : k < D.length)
    (hd : 0 < D[k].2) {z : ℤ}
    (hmin : (z : K) ≤ ((D.take k).map fun p ↦ p.2 * (c p.1 : K)).sum)
    (hz : ((D.take (k + 1)).map fun p ↦ p.2 * (c p.1 : K)).sum = z) : c D[k].1 ≤ 0 := by
  rw [sum_take_succ_map_get (fun p : α × K ↦ p.2 * (c p.1 : K)) D hk] at hz
  have : (c D[k].1 : K) ≤ 0 := nonpos_of_mul_nonpos_right (by linarith) hd
  exact_mod_cast this

/-- **Integrality at the cut.** If the height `hₖ = ∑_{j<k} dⱼ c(τⱼ)` is congruent modulo integers
to `aₖ c(τₖ)` at the break `aₖ = ∑_{j<k} dⱼ` of an entry `j₁`, and the height reaches the integer
`z + 1` at the fraction `θ` of that entry, then `(a_{j₁} + θ d_{j₁}) c(τ_{j₁})` is an integer. -/
theorem exists_intCast_sum_take_map_snd_add_mul
    {K : Type*} [CommRing K] (c : α → ℤ) (D : List (α × K)) {j₁ : ℕ} (hj₁ : j₁ < D.length)
    (hcong : ∃ m : ℤ, ((D.take j₁).map fun p ↦ p.2 * (c p.1 : K)).sum -
      ((D.take j₁).map Prod.snd).sum * (c D[j₁].1 : K) = m)
    {z : ℤ} {θ : K}
    (hθd : θ * (D[j₁].2 * (c D[j₁].1 : K)) =
      z + 1 - ((D.take j₁).map fun p ↦ p.2 * (c p.1 : K)).sum) :
    ∃ m : ℤ, (((D.take j₁).map Prod.snd).sum + θ * D[j₁].2) * (c D[j₁].1 : K) = m := by
  obtain ⟨m, hm⟩ := hcong
  refine ⟨z + 1 - m, ?_⟩
  push_cast
  linear_combination hθd - hm

end List
