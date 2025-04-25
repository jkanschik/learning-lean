import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.VectorField.LieBracket

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (n : WithTop ℕ∞)



open Manifold ContDiff


/-!

# Vector fields

The set of VF...

# (Global) Affine Connections

An affine connection `𝓓` is a map $𝓓: 𝓧(M) → 𝓧(M) → 𝓧(M)$, such that

1. ("C^n linearity"): For any two differentiable functions `f₁ f₂ : C^n⟮I M; 𝕜⟯` and vector fields `X Y₁ Y₂ : 𝓧(M)` we have
    $𝓓 X (f₁ • Y₁ + f₂ • Y₂) = f₁ • 𝓓 X Y₁ + f₂ • 𝓓 X Y₂ $
2. ("𝕜 linearity"): For any two scalars `c₁ c₂ : 𝕜` and vector fields `X₁ X₂ Y : 𝓧(M)` we have
    `𝓓 (c₁ • X₁ + c₂ • X₂) Y = c₁ • 𝓓 X₁ Y + c₂ • 𝓓 X₂ Y`
3. ("product rule"): For a differentiably function `f : C^n⟮I M; 𝕜⟯` and vector fields `X Y : 𝓧(M)` we have
    `𝓓 (f • X) Y = d_Yf • X + f • 𝓓 X Y`


`𝓓 X` is the covariant derivative of the vector field `X`,  which is `𝕜`-linear map of vector fields.
This derivative can be applied to another vector field `Y`, yielding the vector field `𝓓 X Y`,
which can then be evaluated at a point `x₀` like `𝓓 X Y x₀`.

Please note that `𝓓` is a global concept as it works on global vector fields.

## Local interpretation of connections

Due to the condition (1) of the definition of an affine connection,
it can be shown that $𝓓_YX_{|x₀}$ or `𝓓 X Y x₀` only depends on the value `Y x₀`.
Hence we can also apply the connection to vectors in the tangent space, analogous to the classical derivation.
However, the while the derivation is defined as a local concept and then extended to global functions,
connections are defined globally and by virtue of (?) interpreted locally.

This is described by `D.at X x₀: TangentSpace I x₀ → TangentSpace I x₀`

## Implementation note

The connection of the vector field only depends on the direction at the point. we could define
𝓓 X v = 𝓓_vX for a vector v, but then we couldn't easily define R or second order derivatives in general.

## Torsion

The torsion `T` of a connection `𝓓` is defined as
$ T: 𝓧(M) × 𝓧(M) → 𝓧(M)$, $T(X, Y) = 𝓓_YX - 𝓓_XY$

`T X Y = 𝓓 X Y - 𝓓 Y X`


# Curves

## Differentiable Curves in M

In Riemannian geometry, we often want to describe differentiable curves, i.e. differentiable maps $γ : 𝕜 → M$.

The derivative of $γ$ is usually denoted with $γ': 𝕜 → TM$ and for any $t₀ ∈ 𝕜$ we consider $γ'(t₀)$ to be a vector in $T_{γ(t₀)} M$.

Formally, this is not correct, because the (formally correct) derivative of $γ$ at $t₀$ is a 𝕜-linear map $T_{t₀} 𝕜 → T_{γ(t₀)} M$.
Instead, we evaluate the derivate of γ on the unit section of $T 𝕜$;
in other words we apply the derivative implicitly to $1 ∈ T_t₀ 𝕜$by identifying $T_t₀ 𝕜$ with $𝕜$.

Im Mathlib, we can describe a differentiable curve as `γ : C^n⟮𝓘(𝕜, 𝕜), 𝕜; I M⟯`. The derivative ofthis curve at $t₀$ can be determined as
`mfderiv 𝓘(𝕜, 𝕜) I γ t`, which is of type `TangentSpace 𝓘(𝕜, 𝕜) t →L[𝕜] TangentSpace I (γ t)`.

TODO: we would like to interpret this as a vector in `TangentSpace I (γ t)`. A naive approach is to write `mfderiv 𝓘(𝕜, 𝕜) I γ t 1`,
i.e. try to apply the derivative to 1, but we would need to define an appopriate coercion.
Maybe we can even coerce linear maps `𝕜 → V` to `V` in category of vector spaces or modules?

## Vector fields along curves

A vector field $X$ along the curve $γ$ is a map $X: 𝕜 → TM$ such that $X(t) ∈ T_{γ(t)}M$.
An important example is the tangent vector of γ: $γ': 𝕜 → TM$ is a vector field along γ.

How wold we properly define $\frac{𝓓}{dt}X$ ? For example to describe geodesics, for which we have $\frac{𝓓}{dt}γ'(t) = 0$.

## Piecewise differentiable curves in M

It would also be useful to describe piecewise differentiable curves,`γ : C^n⟮𝓘(𝕜, 𝕜), 𝕜; I M⟯` won't help here...

For example this would be used in the statement that a length minimizing piecewise smooth curve is a geodesic and smooth everywhere.


# Open questions...

* Understand the relationship between sections in TM and sections in vector bundles. Can we describe vector fields as setions in TM?
* If so, should we reformulate lie brackets? Do we have pullbacks of sections?

* Define 𝓧 as the set of vector fields on M. Maybe similar to the definition of ContMDiffMap? ContDiffVectorField?
* Coerce multiplication of diff. functions M→𝕜 with vector fields; I want to write f ⬝ X to create the vector field x ↦ f x • X x
* Prove that 𝓧 is a module of the ring of differentiable functions.

* Is there a notion of piecewise differentiable vector fields? I have only seen differentiable vector fields, somehow restricted to an open set.
If we have such a situation, we could extend the VF using a bump function to a global VF, diff. everywhere.

Oopsie, what exactly is a differentiable vector field? And where do we actually need the condition "differentiable"?

The formal definition of a connection doesn't need it. Or does it??

-/

noncomputable section


variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (n : WithTop ℕ∞)
variable [IsManifold I 2 M] [CompleteSpace E]


variable (I M) in
/--
The affine connection on the manifold M.

This is ...
-/
structure AffineConnection where
  /-- The connection, applied to an vector field on M maps another vector (the direction) -/
  protected toFun: (Π (x : M), TangentSpace I x) → (Π (x : M), TangentSpace I x) → (Π (x : M), TangentSpace I x)
  /- The connection D is 𝕜 linear in the first component. -/
  protected linear1 : ∀ (x: M) (X₁ X₂ Y : Π (x : M), TangentSpace I x) (c₁ c₂: 𝕜),
    toFun (fun y ↦ c₁ • X₁ y + c₂ • X₂ y) Y x = c₁ • toFun X₁ Y x + c₂ • toFun X₂ Y x
  /- The connection D is C^n - linear in the direction of the derivative (the second component in our notation) -/
  protected linear2 : ∀ (x: M) (X Y₁ Y₂ : Π (x : M), TangentSpace I x) (f₁ f₂: C^n⟮I, M; 𝕜⟯),
    toFun X (fun y ↦ f₁ y • Y₁ y + f₂ y • Y₂ y) x = f₁ x • toFun X Y₁ x + f₂ x • toFun X Y₂ x
  /- Leibnix rule or Product rule 𝓓 (f•X) = df • X + f • 𝓓 X, where d is the normal differentiation on manifolds -/
  protected prodRule: ∀ (x₀: M) (X Y : Π (x : M), TangentSpace I x) (f : C^n⟮I, M; 𝕜⟯),
    toFun (fun y ↦ f y • X y) Y x₀ = (mfderiv I 𝓘(𝕜, 𝕜) f x₀) (Y x₀) • X x₀ + f x₀ • toFun X Y x₀
    /- For any two vector fields X and Y which are differentiable at x₀ in M,
      the vector field 𝓓 X Y must be differentiable at x₀ -/
  protected smooth : ∀ (X Y : Π (x : M), TangentSpace I x) (x₀ : M),
    MDifferentiableAt I I.tangent (fun x => (toFun X Y x : TangentBundle I M)) x₀



namespace AffineConnection

/-
In this section, we prove general properties of affine connections.

In particular, we prove that the affine connection of a vector field "behaves tensorial" in the direction of the derivative.
In other words, for two vector fields Y₁ and Y₂ and a point x₀ with Y₁ x₀ = Y₂ x₀,
the derivative 𝓓 X Y₁ x₀ and 𝓓 X Y₂ x₀ are identical.
Hence we can evaulate 𝓓 X v where v : TangentSpace x₀

-/
section

def evaluateAt
  (𝓓 : AffineConnection I M n) (X : Π (x : M), TangentSpace I x) {x₀ : M} (v : TangentSpace I x₀) :
  Π (x : M), TangentSpace I x :=
  sorry



end


section Torsion

/-- The torsion of a connection 𝓓 is the skew-symmetric tensor field T(X Y) := 𝓓 X Y - 𝓓 Y X -/
def torsion
    (𝓓 : AffineConnection I M n) (X Y : Π (x : M), TangentSpace I x) :
    (Π (x : M), TangentSpace I x) :=
    𝓓.toFun X Y - 𝓓.toFun Y X - VectorField.mlieBracket I X Y

def torsionWithin
    (𝓓 : AffineConnection I M n) (X Y : Π (x : M), TangentSpace I x) (s : Set M) (x₀ : M):
    TangentSpace I x₀ :=
    𝓓.toFun X Y x₀ - 𝓓.toFun Y X x₀ - VectorField.mlieBracketWithin I X Y s x₀

/- Proof that the torsion is indeed skew symmetric. -/
lemma torsion_isSkewSymm
    (𝓓 : AffineConnection I M n) (X Y : Π (x : M), TangentSpace I x) :
    𝓓.torsion n X Y = - 𝓓.torsion n Y X :=
    sorry

end Torsion

section Curvature

/--
The curvature tensor of a connection 𝓓 is given by
$$ R(X, Y)Z = \Nabla_X \Nabla Y Z - \Nabla Y \Nabla X Z - \Nabla_[X, Y] $$
 -/
def curvatureTensor_forFields
  (𝓓 : AffineConnection I M n) (X Y Z : Π (x : M), TangentSpace I x) :
  (Π (x : M), TangentSpace I x) :=
  𝓓.toFun (𝓓.toFun Z Y) X - 𝓓.toFun (𝓓.toFun Z X) Y - 𝓓.toFun Z (VectorField.mlieBracket I X Y)


end Curvature

end AffineConnection



variable (X Y : Π (x : M), TangentSpace I x)
variable (𝓓 : AffineConnection I M n)
#check 𝓓
#check 𝓓.toFun X
#check 𝓓.torsion n X


end





open Bundle Filter Function

open scoped Bundle Manifold ContDiff


-- variable (F: Type) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace E V)]
  -- `V` vector bundle
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle E V]
  (x: M)


#check ContMDiffVectorBundle

#check Bundle.TotalSpace E (TangentSpace I : M → Type _)

#check (TangentBundle I M)
variable (T : TangentBundle I M)
#check T.proj
#check T.snd

#check E
-- #check F
#check V
variable (v : V x)
#check v

variable (v : TangentSpace I x)
#check v


-- Triviales Bündel über M mit Faser E
-- Das Bündel ist "nur" eine Abbildung M → Type*
#check Bundle.Trivial M E
-- t ist ein Element in dem Bündel
variable (t : Bundle.TotalSpace E (Bundle.Trivial M E))
-- t kann auf die Basis projeziert werden, das gibt ein Element in M:
#check t.proj
-- die Faser, in der t liegt: Trivial M E t.proj
-- "Trivial M E" ist das Bündel, also die Abbildung M → Type*
-- t.proj ist der Basispunkt in M, also ist "Trivial M E t.proj" die Faser, quasi "Type*"
#check t.snd

#check TotalSpace E (Bundle.Trivial M E)
#check Bundle.TotalSpace.trivialSnd M E
-- die kanonische Projection auf die Faser F bildet t auf ein Element in F ab
#check (Bundle.TotalSpace.trivialSnd M E) t



-- Jetzt mit dem TangentBundle:
-- TangentBundle ist der Bundle.TotalSpace E (TangentSpace I : M → Type _)
variable (v : TangentBundle I M)
-- v liegt in der Faser über v.proj, also in T_{v.proj}M
#check v.proj
-- v.snd ist die Faser, also T_{v.proj}M
#check v.snd

variable
  (x: M)
  (X : Π (x:M), TangentSpace I x)

-- Erzeugt ein Element in TM über x mit Wert X_x; hier ist die Faser nicht spezifiziert, ?m.99999
#check TotalSpace.mk x (X x)
-- Projection auf M
#check (TotalSpace.mk x (X x)).proj
-- Quasi TangentSpace I x
#check (TotalSpace.mk x (X x)).snd

#check (TotalSpace.mk' E x (X x)).proj
#check (TotalSpace.mk' E x (X x)).snd


variable (X : Π (x : M), TangentSpace I x)
#check X
#check Π (x : M), TangentSpace I x
#check (Π (x : M), TangentSpace I x)


-- V ist vom Typ M → Type u_11
#check V
-- TangentSpace I ist vom Typ ?m.9999 → Type u_3
#check TangentSpace I

#check FiberBundle E V

variable (s : Cₛ^n⟮I; E, V⟯)
#check s
#check s x
