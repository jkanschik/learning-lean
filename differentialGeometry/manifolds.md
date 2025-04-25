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
* `(n : WithTop ℕ∞)` is the a smoothness parameter. It can vary from `n = 0` for a topological manifold, i.e. no differentiable structure to `n = ∞` for a smooth manifold and `n = ω` for an analytic manifold.

* `{𝕜 : Type*} [NontriviallyNormedField 𝕜]` is the field over which we work, i.e. the real or complex numbers. All statements about manifolds should work with an arbitrary nontrivial, normed field as long as possible since most concepts can be used for the reals and complex numbers.

* `{H : Type*} [TopologicalSpace H]`
* `{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]`
* `{I : ModelWithCorners 𝕜 E H}`
* `{M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M] [CompleteSpace E]`




TODOs:
* Can we put n in {}?
