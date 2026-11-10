/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Basic properties of homotopy groups

A pointed space is path connected if and only if its zeroth homotopy set is a subsingleton.
This follows from Mathlib's equivalence between the zeroth homotopy set and path components.

For an infinite index set the boundary of the cube is dense, so a generalized loop into a
Hausdorff space is determined by its boundary values and the homotopy set is trivial
(`HomotopyGroup.subsingleton_of_infinite`).
-/

public section

open scoped Topology Topology.Homotopy
open HomotopyGroup Topology.Homotopy

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- A pointed space is path connected if and only if its zeroth homotopy set `π_ 0 X x` is a
subsingleton. -/
theorem pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (x : X) :
    PathConnectedSpace X ↔ Subsingleton (π_ 0 X x) := by
  rw [pathConnectedSpace_iff_zerothHomotopy]
  have hne : Nonempty (ZerothHomotopy X) := ⟨ZerothHomotopy.mk x⟩
  simp only [hne, true_and]
  exact (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x).symm.subsingleton_congr

end TauCeti

open scoped unitInterval

/-- **The boundary of a cube indexed by an infinite set is dense**: a basic open set constrains
only finitely many coordinates, so it meets the boundary through a free coordinate set to `0`. -/
theorem Cube.dense_boundary (N : Type*) [Infinite N] : Dense (Cube.boundary N) := fun y ↦ by
  rw [mem_closure_iff]
  intro U hU hyU
  obtain ⟨s, u, hu, hsU⟩ := isOpen_pi_iff.1 hU y hyU
  classical
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset s
  refine ⟨Function.update y i 0, hsU fun a ha ↦ ?_, i, Or.inl (by simp)⟩
  rw [Function.update_of_ne (by rintro rfl; exact hi (Finset.mem_coe.1 ha))]
  exact (hu a ha).2

/-- **Homotopy sets indexed by an infinite set are trivial** for Hausdorff spaces: two generalized
loops agree on the dense boundary of the cube, hence everywhere. -/
theorem HomotopyGroup.subsingleton_of_infinite {N X : Type*} [Infinite N] [TopologicalSpace X]
    [T2Space X] (x : X) : Subsingleton (HomotopyGroup N X x) := by
  refine ⟨Quotient.ind₂ fun f g ↦ congrArg _ (GenLoop.ext f g (congrFun
    (Continuous.ext_on (Cube.dense_boundary N) (map_continuous f) (map_continuous g)
      fun y hy ↦ (GenLoop.boundary f y hy).trans (GenLoop.boundary g y hy).symm)))⟩
