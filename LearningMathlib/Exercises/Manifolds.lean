import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic



variable
  (n : WithTop ℕ∞)
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]


open Metric Function Set Real ContDiff

/-
  Recap differentiable functions
-/
section

example : Differentiable ℝ fun x => sin x * exp x := by
  apply Differentiable.mul
  . apply differentiable_sin
  . apply differentiable_exp

example : Differentiable ℝ fun x => cos (sin x) * exp x := by
  simp_all only [differentiable_sin, Differentiable.cos, differentiable_exp, Differentiable.mul]

example : Differentiable ℝ fun x => cos (sin x) * exp x := by
  apply Differentiable.mul
  . apply Differentiable.cos
    . apply differentiable_sin
  . apply differentiable_exp

-- Just the identity to warm up
example : ContDiff ℝ ∞ (fun x : ℝ => x) := by
  exact contDiff_id

-- Proof that x ↦ x * x is differentiable everywhere
example : ContDiff ℝ ∞ (fun x : ℝ => x * x) := by
  apply ContDiff.mul
  . exact contDiff_id
  . exact contDiff_id

-- Proof that x ↦ x * x + 7 * x is differentiable everywhere
example : ContDiff ℝ ∞ (fun x : ℝ => x * x + 7 * x) := by
  apply ContDiff.add
  . apply ContDiff.mul
    . apply contDiff_id
    . apply contDiff_id
  . apply ContDiff.mul
    . apply contDiff_const
    . apply contDiff_id

-- 1 / x is differentiable on positive numbers
example : ContDiffOn ℝ ∞ (fun x : ℝ => 1 / x) (Set.Ioi 0) := by
  apply ContDiffOn.div
  . apply contDiffOn_const
  . apply contDiffOn_id
  sorry


-- Proof that x ↦ exp x is differentiable everywhere
example : ContDiff ℝ ∞ (fun x => Real.exp x) := by
  apply Real.contDiff_exp


example : ContDiffOn ℝ ∞ (fun x => Real.exp (1 / x)) (Set.Ioi 0) := by
  apply ContDiffOn.exp
  apply ContDiffOn.div
  . apply contDiffOn_const
  . apply contDiffOn_id
  sorry


example : ContDiffOn ℝ ∞ (fun x => (Real.cos x, Real.sin x)) (Set.Icc 0 1) := by
  apply ContDiffOn.prodMk
  sorry
  sorry


end




section Spheres


-- Proof that (-1, 0) and (cos 2, sin 2) are points on the "sphere" in ℝ^2, which is the unit circle.
def u := (!₂[-1, 0] : EuclideanSpace ℝ (Fin 2))
example : u ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one), mem_setOf]
  simp [u]

noncomputable def v := (!₂[Real.cos 2, Real.sin 2] : EuclideanSpace ℝ (Fin 2))
example : v ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one), mem_setOf]
  simp [v]

-- And the same in the two sphere in ℝ^3

def u3 := (!₂[-1, 0, 0] : EuclideanSpace ℝ (Fin 3))
theorem g3 : u3 ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)]
  rw [mem_setOf]
  simp [u3]
  sorry -- WHY?


def c : ℝ → EuclideanSpace ℝ (Fin 3) := fun t => !₂[t, t, t]

theorem isCurveInSphere (t: ℝ): (c t ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  sorry

end Spheres
