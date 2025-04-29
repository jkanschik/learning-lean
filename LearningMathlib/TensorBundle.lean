import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket



open Manifold Bundle TensorProduct




-- structure MultilinearMap (R : Type uR) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [Semiring R]
--   [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂] where
--   /-- The underlying multivariate function of a multilinear map. -/
--   toFun : (∀ i, M₁ i) → M₂
--   /-- A multilinear map is additive in every argument. -/
--   map_update_add' :
--     ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i),
--       toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
--   /-- A multilinear map is compatible with scalar multiplication in every argument. -/
--   map_update_smul' :
--     ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i),
--       toFun (update m i (c • x)) = c • toFun (update m i x)

structure Tensor (R: Type*)  (i_cov i_contra : Nat) (M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] where
  toFun: MultilinearMap R (fun _ : Fin i_cov => M) R


section

variable
  (ι : Type*)
  (R : Type*) [CommSemiring R]
  (M : Type*) [AddCommMonoid M] [Module R M]


#check TensorProduct R M M -- The tensor product of two module
variable
  (f : TensorProduct R M M)
#check 2 • f + f

#check M ⊗ M
variable
  (f : M ⊗[R] M)
#check 2 • f + f


#check MultilinearMap R (fun _ : Fin 5 => M) M
#check @MultilinearMap R (Fin 5) (fun _ : Fin 5 => M) M

variable
  (f : MultilinearMap R (fun _ : Fin 5 => M) R)
  (m : M)


#check f (fun _ : Fin 5 => m)

#check (f : ((i : Fin 5) → M) → R)
variable
  (f : ((i : Fin 5) → M) → R)
#check f

#check Fin 5 → M


def my_map (X Y Z : M) : Fin 3 → M
| 0 => X
| 1 => Y
| 2 => Z

#check my_map M m m m

end



section

variable
  (n : WithTop ℕ∞)
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]

variable
  (x : M)
  (v : E)

#check TangentSpace I x
#check Tensor 𝕜 2 3 E
#check Tensor 𝕜 2 3 (TangentSpace I x)

variable
  (T : Tensor 𝕜 2 3 E)
#check T.toFun (fun _ : Fin 2 => v)

#check ⨂[𝕜]^3 (TangentSpace I x)

#check (∀ x:M, TangentSpace I x)
#check (∀ x:M, Tensor 𝕜 2 3 (TangentSpace I x))
#check (∀ x:M, (TangentSpace I x) ⊗ (TangentSpace I x))
#check (∀ x:M, ⨂[𝕜]^3 (TangentSpace I x))
#check (∀ x:M, TangentSpace I x →[𝕜] 𝕜)

variable
  -- A vector is a (0 1) tensor
  (X : Π(x:M), Tensor 𝕜 0 1 (TangentSpace I x))
  -- A linear form is a (1 0) tensor
  (α : Π(x:M), Tensor 𝕜 1 0 (TangentSpace I x))
  -- A metric (no matter whether pseudo or Riemannian) is a (2 0) tensor
  (g : Π(x:M), Tensor 𝕜 2 0 (TangentSpace I x))
  -- The Ricci curvature
  (Ricci : Π(x:M), Tensor 𝕜 2 0 (TangentSpace I x))
  -- The torsion of a connnection
  (Torsion : Π(x:M), Tensor 𝕜 2 1 (TangentSpace I x))
  -- The Riemann cuvature tensor
  (Curvature : Π(x:M), Tensor 𝕜 3 1 (TangentSpace I x))

-- We want to write
-- g x v w = g_x(v,w) for v w : TangentSpace I x
#check (g x).toFun 

end
