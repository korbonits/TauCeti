/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Bounded operators on a finite-dimensional space

A bounded operator on a finite-dimensional normed space is just a linear map, so its spectrum is
the finite set of eigenvalues. This holds over every field of scalars acting compatibly, for
instance over `ℝ` for an operator on a complex space.

Bounded operators out of a finite-dimensional space are determined by the images of a basis,
with operator norm controlled by the norms of those images. Hence such operators into `E` are
approximated in operator norm by operators factoring through any operator `g : F →L[𝕜] E` of
dense range. On a finite-dimensional real domain, strict pointwise norm bounds are equivalent
to strict operator-norm bounds.

Bounded operators between finite-dimensional spaces form a finite-dimensional space over every
finite extension of the scalars acting compatibly on the codomain, for instance over `ℂ` for
real-linear operators into a complex space.

## Main results

* `ContinuousLinearMap.finite_spectrum`: a bounded operator on a finite-dimensional normed space
  has finite spectrum, also over subfields of the scalars such as `ℝ ⊆ ℂ`.
* `ContinuousLinearMap.isUnit_of_isUnit_toLinearMap`: on a finite-dimensional normed space over a
  nontrivially normed field, a continuous linear map invertible as a linear map is invertible as a
  continuous linear map, without completeness of the scalars.
* `ContinuousLinearMap.denseRange_comp`: on operators out of a finite-dimensional space,
  postcomposition with an operator of dense range has dense range.
* `ContinuousLinearMap.opNorm_lt_iff`: a strict norm bound can be checked on
  every nonzero vector of a finite-dimensional real domain.
* `ContinuousLinearMap.finiteDimensional_of_isScalarTower`: `E →L[𝕜] F` is finite-dimensional
  over a finite extension `𝕜'` of `𝕜` acting on a finite-dimensional codomain `F`.
* `IsCompact.isCompact_setOfPred_mapsTo`: out of a finite-dimensional space over a complete field,
  the operators sending a neighbourhood of `0` into a compact set form a compact set.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

omit [CompleteSpace 𝕜] in
/-- On a finite-dimensional normed space, a continuous linear map that is invertible as a linear
map is invertible as a continuous linear map: its inverse is a polynomial in it, by the
minimal polynomial, so no completeness of the scalar field is needed. -/
theorem isUnit_of_isUnit_toLinearMap {u : V →L[𝕜] V} (hu : IsUnit (u : Module.End 𝕜 V)) :
    IsUnit u := by
  let φ : (V →L[𝕜] V) →ₐ[𝕜] Module.End 𝕜 V :=
    { toFun := fun f ↦ (f : Module.End 𝕜 V)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  have hφ : Function.Injective φ := fun f g h ↦ ContinuousLinearMap.coe_injective h
  have hinj : Function.Injective (u : Module.End 𝕜 V) := (Module.End.isUnit_iff _).1 hu |>.1
  have hc := LinearMap.minpoly_coeff_zero_of_injective hinj
  set p := minpoly 𝕜 (u : Module.End 𝕜 V)
  have hp : Polynomial.aeval u p = 0 := by
    apply hφ
    rw [map_zero]
    exact (Polynomial.aeval_algHom_apply φ u p).symm.trans (minpoly.aeval 𝕜 _)
  rw [← Polynomial.divX_mul_X_add p, map_add, map_mul, Polynomial.aeval_X,
    Polynomial.aeval_C] at hp
  set g := Polynomial.aeval u (Polynomial.divX p)
  have hcomm : u * g = g * u := by
    have : Polynomial.aeval u (Polynomial.X * Polynomial.divX p) =
        Polynomial.aeval u (Polynomial.divX p * Polynomial.X) := by rw [mul_comm]
    simpa only [map_mul, Polynomial.aeval_X] using this
  have h1 : g * u = (-(algebraMap 𝕜 (V →L[𝕜] V) (p.coeff 0))) := eq_neg_of_add_eq_zero_left hp
  rw [isUnit_iff_exists]
  refine ⟨(-(p.coeff 0)⁻¹) • g, ?_, ?_⟩
  · rw [mul_smul_comm, hcomm, h1, smul_neg, neg_smul, neg_neg, Algebra.smul_def, ← map_mul,
      inv_mul_cancel₀ hc, map_one]
  · rw [smul_mul_assoc, h1, smul_neg, neg_smul, neg_neg, Algebra.smul_def, ← map_mul,
      inv_mul_cancel₀ hc, map_one]

omit [CompleteSpace 𝕜] in
/-- A bounded operator on a finite-dimensional normed space has finite spectrum over any field
`S` of scalars acting compatibly, for instance over `ℝ` for an operator on a complex space. -/
theorem finite_spectrum (S : Type*) [Field S] [Algebra S 𝕜] [Algebra S (V →L[𝕜] V)]
    [IsScalarTower S 𝕜 (V →L[𝕜] V)] (T : V →L[𝕜] V) : (spectrum S T).Finite := by
  have hsub : spectrum 𝕜 T ⊆ spectrum 𝕜 (T : Module.End 𝕜 V) := fun μ hμ ↦ by
    rw [spectrum.mem_iff] at hμ ⊢
    exact fun hu ↦ hμ (isUnit_of_isUnit_toLinearMap hu)
  rw [← spectrum.preimage_algebraMap 𝕜]
  exact ((Module.End.finite_spectrum _).subset hsub).preimage (algebraMap S 𝕜).injective.injOn

/-- On continuous linear maps out of a finite-dimensional space, postcomposition with a
continuous linear map of dense range has dense range: each `T : V →L[𝕜] E` is approximated in
operator norm by maps `g.comp U` with `U : V →L[𝕜] F`. -/
theorem denseRange_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {g : F →L[𝕜] E} (hg : DenseRange g) :
    DenseRange (g.comp : (V →L[𝕜] F) → V →L[𝕜] E) := by
  rw [Metric.denseRange_iff]
  intro T r hr
  -- Approximate the images of a basis of `V` by points of the range of `g`.
  let v := Module.finBasis 𝕜 V
  obtain ⟨C, hC, hv⟩ := v.exists_opNorm_le (F := E)
  have hrC : 0 < r / (2 * C) := by positivity
  choose y hy using fun i ↦ Metric.denseRange_iff.1 hg (T (v i)) _ hrC
  refine ⟨v.constrL y, ?_⟩
  rw [dist_eq_norm]
  calc ‖T - g.comp (v.constrL y)‖ ≤ C * (r / (2 * C)) :=
        hv hrC.le fun i ↦ by
          simpa [Module.Basis.constrL_basis, ← dist_eq_norm] using (hy i).le
    _ = r / 2 := by field_simp
    _ < r := half_lt_self hr

section StrictNorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- On a finite-dimensional real domain, a strict pointwise operator bound gives a strict
operator-norm bound. The positivity assumption includes the zero-dimensional domain. -/
theorem opNorm_lt_iff (A : E →L[ℝ] F) {c : ℝ} (hc : 0 < c) :
    ‖A‖ < c ↔ ∀ x ≠ 0, ‖A x‖ < c * ‖x‖ := by
  refine ⟨fun h x hx ↦ (A.le_opNorm x).trans_lt ?_, fun h ↦ ?_⟩
  · exact mul_lt_mul_of_pos_right h (norm_pos_iff.mpr hx)
  · cases subsingleton_or_nontrivial E
    · simpa only [Subsingleton.elim A 0, norm_zero] using hc
    · obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn
        (NormedSpace.sphere_nonempty.mpr zero_le_one) A.continuous.norm.continuousOn
      have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      have hxne : x ≠ 0 := by
        intro hx0
        simp [hx0] at hxnorm
      calc
        ‖A‖ ≤ ‖A x‖ := A.opNorm_le_of_unit_norm (norm_nonneg _) fun y hy ↦
          hmax (mem_sphere_zero_iff_norm.mpr hy)
        _ < c := by simpa only [hxnorm, mul_one] using h x hxne

end StrictNorm

section ScalarExtension

variable {𝕜 𝕜' E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [FiniteDimensional 𝕜 𝕜']
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [IsScalarTower 𝕜 𝕜' F]
  [FiniteDimensional 𝕜' F]

/-- Bounded `𝕜`-linear operators between finite-dimensional spaces form a finite-dimensional
space over a finite extension `𝕜'` of `𝕜` acting compatibly on the codomain, for instance over
`ℂ` for real-linear operators into a finite-dimensional complex space. -/
theorem finiteDimensional_of_isScalarTower : FiniteDimensional 𝕜' (E →L[𝕜] F) := by
  have : FiniteDimensional 𝕜 F := Module.Finite.trans 𝕜' F
  exact Module.Finite.of_restrictScalars_finite 𝕜 𝕜' (E →L[𝕜] F)

end ScalarExtension

end ContinuousLinearMap

section MapsTo

open Filter Set Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Out of a finite-dimensional normed space over a complete field, the operators sending a
neighbourhood `s` of `0` into a compact set `K` form a compact set. -/
theorem IsCompact.isCompact_setOfPred_mapsTo {K : Set F} (hK : IsCompact K) {s : Set E}
    (hs : s ∈ 𝓝 (0 : E)) : IsCompact {T : E →L[𝕜] F | MapsTo T s K} := by
  -- An operator is determined by its values on a basis contained in `s`, and these values lie
  -- in `K`.
  let v := Module.finBasis 𝕜 E
  -- Some nonzero multiple `a • v` of a basis lies in `s`.
  have hev : ∀ᶠ a in 𝓝[≠] (0 : 𝕜), ∀ i, a • v i ∈ s := eventually_all.2 fun i ↦
    nhdsWithin_le_nhds <| (continuous_id.smul continuous_const).tendsto' 0 (0 : E)
      (zero_smul 𝕜 _) hs
  obtain ⟨a, hav, ha : a ≠ 0⟩ := (hev.and self_mem_nhdsWithin).exists
  -- Operators out of `E` are identified with their values on the basis `w = a • v` inside `s`.
  let w := v.map (LinearEquiv.smulOfNeZero 𝕜 E a ha)
  let e : (E →L[𝕜] F) ≃L[𝕜] (Fin _ → F) :=
    (w.equivFunL.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing _)
  refine (e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ ↦ hK)).of_isClosed_subset
    (hK.isClosed.setOfPred_mapsTo fun x _ ↦ continuous_eval_const x) fun T hT ↦ ?_
  simp only [mem_preimage, mem_univ_pi]
  intro i
  -- `piRing` evaluates at `Pi.single i 1`, the coordinate vector of `w i`; the inverse of
  -- `equivFunL` is that of `equivFun` by definition.
  have hwi : w.equivFunL.symm (Pi.single i 1) = w i := Basis.equivFun_symm_single w i
  have hw : w i = a • v i := by simp [w]
  change T (w.equivFunL.symm (Pi.single i 1)) ∈ K
  exact hwi ▸ hw ▸ hT (hav i)

end MapsTo
