/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# Basic properties of homotopy groups

A pointed space is path connected if and only if its zeroth homotopy set is a subsingleton.
This follows from Mathlib's equivalence between the zeroth homotopy set and path components.

For an infinite index set the boundary of the cube is dense (`Cube.dense_boundary`), so a
generalized loop into a `T1` space is constant: there is only one generalized loop and the
homotopy set is trivial. Both facts are instances (`GenLoop.subsingleton_of_infinite`,
`HomotopyGroup.subsingleton_of_infinite`).
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

open scoped unitInterval in
/-- **Generalized loops indexed by an infinite set are constant** in a `T1` space: such a loop is
the base point on the dense boundary of the cube, and the fiber over the base point is closed. -/
instance GenLoop.subsingleton_of_infinite {N X : Type*} [Infinite N] [TopologicalSpace X]
    [T1Space X] {x : X} : Subsingleton (Ω^ N X x) :=
  have hconst (f : Ω^ N X x) (y : I^N) : f y = x :=
    closure_minimal (s := Cube.boundary N) (t := ⇑f ⁻¹' {x})
      (fun y hy ↦ GenLoop.boundary f y hy) (isClosed_singleton.preimage (map_continuous f))
      ((Cube.dense_boundary N) y)
  ⟨fun f g ↦ GenLoop.ext f g fun y ↦ (hconst f y).trans (hconst g y).symm⟩

/-- **Homotopy sets indexed by an infinite set are trivial** for `T1` spaces, since there is
only one generalized loop (`GenLoop.subsingleton_of_infinite`). -/
instance HomotopyGroup.subsingleton_of_infinite {N X : Type*} [Infinite N] [TopologicalSpace X]
    [T1Space X] {x : X} : Subsingleton (HomotopyGroup N X x) :=
  inferInstanceAs (Subsingleton (Quotient (GenLoop.Homotopic.setoid N x)))
