# Vector bundles and tensor fields

## Vector bundles

### Topological fibre bundles

Vector bundles are special types of topological fiber bundles, so it makes sense to look at fiber bundles first. We define a fiber bundle as follows:

```

```

[`Mathlib.Topology.FiberBundle.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/FiberBundle/Basic.html)
: Basic definitions of a fibre bundle `F → E → B`

[`Mathlib.Topology.FiberBundle.Constructions`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/FiberBundle/Constructions.html)
: Construction of important fibre bundles, namely
* the fiber bundle structure `Bundle.Trivial.fiberBundle` on the trivial bundle and homeomorphism to `F → F × B → B`
* the fiber bundle structure on the fibre wise product of two fiber bundles
* the pullback of the fiber bundle structure `F → E → B` by a function `f: B' → B`.






## Sections in vector bundles

## Vector fields as sections

## Vector field

Vector fields can be described as sections in the tangent bundle, i.e. a map `X: M → TM` such that `π ∘ X = id` where `π` is the projection of the bundle onto the base manifold `M`.

In Mathlib, there is no specific type for vector fields.
Currently, there are only two files which work with vector fields on differentiable manifolds:
`Mathlib.Geometry.Manifold.VectorField.LieBracket` and `Mathlib.Geometry.Manifold.VectorField.Pullback`

In both files, vector fields are described using a Sigma type:
`V : Π (x : M), TangentSpace I x`

Copied:
Note that a smoothness assumption for a vector field is written by seeing the vector field as
a function from `M` to its tangent bundle through a coercion, as in:
`MDifferentiableWithinAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) s x`.




https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorField/Pullback.html#ContMDiffWithinAt.mpullbackWithin_vectorField_inter

Hypothesis hV say V is a C^n VF



## Tensor bundles

About multilinear maps vs. tensors: https://math.stackexchange.com/questions/2138459/understanding-the-definition-of-tensors-as-multilinear-maps

https://en.wikipedia.org/wiki/Tensor_field

Quote from some comment: a vector is a [1,0] tensor (but a [1,0] tensor is not necessarily a vector unless V
 has finite dimension)

https://cseweb.ucsd.edu/~gill/CILASite/Resources/15Chap11.pdf



As an example, explain correspondence between vectors and multilinear map on dual.
* scalar as a (0,0) tensor
* vector
* dual form
* metric
* curvature tensor


For any given vector bundle F -> E -> M, we define the tensor bundle of E:

Fiber: MultilinearMap k (M i) k
where M0 to Mk are F, M(k+1) to M(l) are Dual of F.

Construct a VectorBundleCore.


See https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Multilinear/Basic.html



# Open issues

- [ ] Learn how to use MultiLinearMaps. This probably is the correct fiber.
- [ ] What exactly is the difference between the notation `Π (x : M), TangentSpace I x` and simply `(s : ∀ x, E x)`





Example of a theorem involving sections (see [Bundle.contMDiffAt_section](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorBundle/Basic.html#Bundle.contMDiffAt_section)):

```
/-- Characterization of `C^n` sections of a vector bundle. -/
theorem contMDiffAt_section (s : ∀ x, E x) (x₀ : B) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x₀ ↔
      ContMDiffAt IB 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F E x₀ ⟨x, s x⟩).2) x₀ := by
  simp_rw [contMDiffAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffAt_id
```

Topics to cover
* vector field as `Π (x : M), TangentSpace I x`
* sections in `E` as `Π (x : M), E x`
