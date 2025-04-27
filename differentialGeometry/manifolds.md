# Manifolds in Mathlb

We will discuss how manifolds can be described in Mathlib. To do this, let's dive straight in and define the manifold \\( M \\) and don't worry, we will dissect it:

```
import Mathlib.Geometry.Manifold.IsManifold.Basic

variable
  (n : WithTop ℕ∞)
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M] [CompleteSpace E]

#check M
```
[Open in Lean 4 Web](https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0BxAUwhAJigE8dkA7YAMwnQBMcBJAZxvsZYCEl2wAMYAoEQDckUYEizoCIuHAAU1OAC44AdWBoAKhDBxAqISA8IgCUiuAG9ArBuAdXY1w95MAQBUAXzgBtAHIQ1GTA4jLo6OQBUCRMAGLABMxwDgC6VtYAEk4ubl6+BpDoEADmwkjoAMpgSEIEcBlpStYAotmuHt7+0DEAgkxMAMLEIHhQEACuRs0pvlExVTV1DnDT6axOCBBMiTpoQ1DUBFDsyY6tGZ7pCG25nQWMJWWV1bWIMz4DqFIwBEwLr1kEO8OFwGEl1mogb4huB5D9/nVViIAMRCVAEIQAa0QIiAA)

Let's go through the different variables that are defined here:
* `(n : WithTop ℕ∞)`
is the a smoothness parameter. It can vary from `n = 0` for a topological manifold, i.e. no differentiable structure to `n = ∞` for a smooth manifold and `n = ω` for an analytic manifold.

* `{𝕜 : Type*} [NontriviallyNormedField 𝕜]`
is the field over which we work, i.e. the real or complex numbers. All statements about manifolds should work with an arbitrary nontrivial, normed field as long as possible since most concepts can be used for the reals and complex numbers.

* `{H : Type*} [TopologicalSpace H]`

* `{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]`

* `{I : ModelWithCorners 𝕜 E H}`

* `{M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M] [CompleteSpace E]`
To start with, `M` is a [`TopologicalSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html#TopologicalSpace), which means we have a proper topology.
The type class `ChartedSpace` defines an atlas on the topological space, i.e. a set of homoemorphisms from `M` to the model space such that the domains cover the whole space. This doesn't define a manifold structure yet. To do so, we need the type class `IsManifold`, which states that the coordinate transformations of the charted space form a groupoid of differentiable maps.



**TODO** Do we really need `[CompleteSpace E]`? It states that Cauchy sequences converge. Can this be deduced from the other type classes?


When working with several manifolds at the time, it's best to call them `M`, `M'`, or `M''` or use subscripts `M₁`, `M₂`, etc. and use the same convention for the underlying objects like `I`, `I' and so on. Otherwise it's easy to loose track of the dependencies, causing weird errors.

## The tangent space of manifolds

Based on the differentiable structure given by `IsManifold`, we can define the tangent bundle of `M`.

## Maps between manifolds

We now consider maps between manifolds. Unless we demand differentiability, these are just functions between types: \\( f: M \to M'\\) is defined as
```
variable (F: M → M')
```

To state that the map is differentiable, we have different possibilities:
*

ContMDiffMap and notations


File [MFDeriv.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#HasMFDerivAt)

- [ ] asdasd

asasdasd
: asdasd

[HasMFDerivWithinAt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#HasMFDerivWithinAt)


[HasMFDerivAt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#HasMFDerivAt)
: `HasMFDerivAt I I' f x f'` indicates that the function f between manifolds has, at the point x, the derivative f'.



[mfderivWithin](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#mfderivWithin)
: `mfderivWithin I I' f s x` is the derivative of f at x within the set s

[mfderiv](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#mfderiv)
:  `mfderiv I I' f x` is the derivative of f at x


[tangentMapWithin](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#tangentMapWithin)


[tangentMap](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#tangentMap)




## Examples

Real vector space and subspaces: Instances.Real
curves and homotopies => geodesic variations

Spheres. Instances.Sphere


For products and disjoint union, see IsManifold.Basic

TODOs:
* Can we put n in {}?
