import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Manifolds in matlib

## Differentiable manifolds and their tangent bundles

In this file we want to describe the basic machinery for manifolds in matlib.

First of all, we look at the definition of a manifold. This includes
- the field over which the manifold is defined, i.e. R or C
- the "ModelWithCorners", which defines the underlying model. This is defined in `Mathlib.Geometry.Manifold.IsManifold.Basic`


  `variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {I : ModelWithCorners ℝ E E} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]`

On a differentiable manifold `M`, we have the tangent bundle `TM`
and for each point `x ∈ M` we have the associated tangent space `T_xM`of `M` at `x`.
The tangent space and tangent bundle are defined in `Mathlib.Geometry.Manifold.IsManifold.Basic`.

The tangent space at `x` on a manifold modelled on `I` is denoted by `TangentSpace I x`.
The tangent bundle on a manifold is `TangentBundle`.


## Functions between manifolds

Differentiable functions between manifolds are treated in
`Mathlib.Geometry.Manifold.ContMDiffMap`. It defines the notation `C^n⟮I, M; I', M'⟯`
for differentiable maps between manifolds `M`and `M'`
as well as the shorter notation  `C^n⟮I, M; 𝕜⟯` for differentiable functions on manifolds, i.e. the special case where `M' = 𝕜`.

The same file also defines typical differentiable functions on manifolds, namely:
* the identity on a manifold `ContMDiffMap.id : C^n⟮I, M; I, M⟯`
* the constant function from a manifold to `𝕜` : `ContMDiffMap.const : C^n⟮I, M; 𝕜⟯`
* the composition of two functions (as differentiable functions): `ContMDiffMap.comp`
* the projections from a product of manifolds to the first and second factor:
  `ContMDiffMap.fst : C^n⟮I', M × M'; I, M⟯` and `ContMDiffMap.fst : C^n⟮I', M × M'; I, M⟯`
* the product `x ↦ (f x, g x)` of two functions: `ContMDiffMap.prodMk :  C^n⟮I', M × M'; I, M⟯`

## Differentiability

Differentiability is defined in `Mathlib.Geometry.Manifold.MFDeriv.Defs` in terms of the
underlying chart (since a manifold `M` is a `ChartedSpace`).

Let `f: M → M'` be a differential function, i.e. of type `C^n⟮I, M; I', M'⟯`.
Then the derivative of `f` at a point `x` is a `𝕜`-linear function
between the corresponding tangent spaces, i.e. the map `TangentSpace I x →L[𝕜] TangentSpace I' f x`

The following two defs indicate that a function `f` has the derivative `f'`
HasMFDerivAt
HasFDerivWithinAt
This used to prove that a given function is the derivative of another function, so both must already be defined.

We can also retrieve the differential of a given function by using `mfderiv`and `mfderivWithin`:
for a differentiable function `f`, `mfderiv I I' f x` is the derivative of `f` at `x`

MDifferentiableOn
MDifferentiable

mfderivWithin
mfderiv

tangentMap
tangentMapWithin

## Vector field

Vector fields can be described as sections in the tangent bundle,
i.e. a map `X: M → TM` such that `π ∘ X = id` where `π` is
the projection of the bundle onto the base manifold `M`.

In Mathlib, there is no specific type for vector fields.
Currently, there are only two files which work with vector fields on differentiable manifolds:
`Mathlib.Geometry.Manifold.VectorField.LieBracket` and `Mathlib.Geometry.Manifold.VectorField.Pullback`

In both files, vector fields are described using a Sigma type:
`V : Π (x : M), TangentSpace I x`

Copied:
Note that a smoothness assumption for a vector field is written by seeing the vector field as
a function from `M` to its tangent bundle through a coercion, as in:
`MDifferentiableWithinAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) s x`.

-/

-- The field we are working over
variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]

  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']

  {f f₀ f₁ : M → M'} {x : M} {s t : Set M}
  {g : M' → M''} {u : Set M'}

  {f' f₀' f₁' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)}
  {g' : TangentSpace I' (f x) →L[𝕜] TangentSpace I'' (g (f x))}




#check f
#check g ∘ f
#check HasMFDerivAt I I' f x



variable (h : M → M'')
variable (h' : TangentSpace I x →L[𝕜] TangentSpace I'' (h x))

#check h
#check mfderiv I I'' h x

example (hg: HasMFDerivAt I' I'' g (f x) g') (hf : HasMFDerivAt I I' f x f') : HasMFDerivAt I I'' (g ∘ f) x (g'.comp f'):= by
  apply HasMFDerivAt.comp x hg hf


example (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableAt I I' f x) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) := by
  apply HasMFDerivAt.mfderiv
  exact HasMFDerivAt.comp x hg.hasMFDerivAt hf.hasMFDerivAt


open Manifold

variable (n : WithTop ℕ∞)
variable (f: C^n⟮I, M; I', M'⟯)
variable (g h: C^n⟮I, M; 𝕜⟯)
variable (X : TangentSpace I x)
variable (k : 𝕜)

#check ContMDiffMap.id x
#check ContMDiffMap.const 5 x
#check g x + ContMDiffMap.const k x
#check (g • ContMDiffMap.const k) x


def const3 : C^n⟮I, M; 𝕜⟯ := ContMDiffMap.const 3
instance myid : C^n⟮I, M; I, M⟯ := ContMDiffMap.id

#check const3 I n
#check mfderiv I 𝓘(𝕜, 𝕜) (const3 I n) x X
#check mfderiv I I (myid I n) x
#check g x

example (X : M): mfderiv I 𝓘(𝕜, 𝕜) (const3 I n) x = 0 := by
  -- hasMFDerivAt_const
  sorry

-- theorem hasMFDerivAt_const (c : M') (x : M) :
--     HasMFDerivAt I I' (fun _ : M => c) x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) := by
--   refine ⟨continuous_const.continuousAt, ?_⟩
--   simp only [writtenInExtChartAt, Function.comp_def, hasFDerivWithinAt_const]

example (c : 𝕜) : HasMFDerivAt I 𝓘(𝕜, 𝕜) (fun _ : M => c) x (0 : TangentSpace I x →L[𝕜] TangentSpace 𝓘(𝕜, 𝕜) c) := by
  apply hasMFDerivAt_const




#check f
#check mfderiv I I' f x X
#check mfderiv I (modelWithCornersSelf 𝕜 𝕜) g x X
#check 2 • mfderiv I 𝓘(𝕜, 𝕜) g x X + mfderiv I 𝓘(𝕜, 𝕜) h x X
#check (mfderiv I 𝓘(𝕜, 𝕜) g x X) + 0

#check fun x ↦ g x + h x

#check mfderiv I 𝓘(𝕜, 𝕜) (fun x ↦ g x + h x) x

-- g,h : M → ℝ, g+h : M → ℝ, D g+h x = D g x + D h x

example (g h: C^n⟮I, M; 𝕜⟯) : mfderiv I 𝓘(𝕜, 𝕜) (fun x ↦ g x + h x) x = mfderiv I 𝓘(𝕜, 𝕜) h x := by sorry

variable (g h : M → 𝕜)
#check g+h

variable (k : 𝕜)
variable (T : TangentSpace 𝓘(𝕜, 𝕜) k)
#check T
