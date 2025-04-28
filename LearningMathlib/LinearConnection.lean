import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket


open Manifold Bundle

variable
  (n : WithTop ℕ∞)
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]


variable
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {I' : ModelWithCorners 𝕜 F H}
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*)
  [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]





variable (I M) in
/--
The linear connection on the vector bundle `V` over the manifold `M`.

We want the connection to map C^n sections to C^(n-1) sections
which is in line with the product rule, which contains the term df • s,
i.e. a product of C^(n-1) and the section.

The differentiability requirement uses "ContMDiffWithinAt",
which allows us to apply the connection even to sections which are not everywhere differentiable.

TODO: also reformulate cn_linear and product rule to "...WithinAt"
-/
structure LinearConnection where
  /-- The connection, applied to a section is a map from vector fields to sections. -/
  protected toFun: (Π (x : M), V x) → (Π (x : M), TangentSpace I x) → (Π (x : M), V x)
  /- The connection D is 𝕜 linear for sections (the first component). -/
  protected k_linear : ∀ (x: M) (s₁ s₂ : Π (x : M), V x) (c₁ c₂: 𝕜) (X : Π (x : M), TangentSpace I x),
    toFun (c₁ • s₁ + c₂ • s₂) X x = c₁ • toFun s₁ X x + c₂ • toFun s₂ X x
  /- The connection D is C^n - linear in the direction of the derivative (the second component in our notation) -/
  protected cn_linear : ∀ (x: M) (s : Π (x : M), V x) (Y₁ Y₂ : Π (x : M), TangentSpace I x) (f₁ f₂: C^n⟮I, M; 𝕜⟯),
    toFun s (fun y ↦ f₁ y • Y₁ y + f₂ y • Y₂ y) x = f₁ x • toFun s Y₁ x + f₂ x • toFun s Y₂ x
  /- Leibnix rule or Product rule 𝓓 (f•s) = df • s + f • 𝓓 s, where d is the Fréchet differentiation on manifolds -/
  protected prodRule: ∀ (x₀: M) (s : Π (x : M), V x) (X : Π (x : M), TangentSpace I x) (f : C^n⟮I, M; 𝕜⟯),
    toFun (fun y ↦ f y • s y) X x₀ = (by exact mfderiv I 𝓘(𝕜, 𝕜) f x₀ : TangentSpace I x₀ →L[𝕜] 𝕜) (X x₀) • (s x₀) + f x₀ • toFun s X x₀
    /- For any two vector fields X and Y which are differentiable at x₀ in M,
      the vector field 𝓓 X Y must be differentiable at x₀ -/
  protected smooth : ∀ (s : Π (x : M), V x)
    (X : Π (x : M), TangentSpace I x) (u : Set M) (x₀ : M)
    (hs: ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) u x₀),
    -- TODO hypothesis for X
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (toFun s X x)) u x₀



namespace LinearConnection

noncomputable section Curvature

/--
The curvature tensor of a connection 𝓓 is defined by
$$ R(X, Y)s = \Nabla_X \Nabla Y s - \Nabla Y \Nabla X s - \Nabla_[X, Y] s $$
 -/
def curvature
  (𝓓 : LinearConnection I M F n V) (s : Π (x : M), V x) (X Y : Π (x : M), TangentSpace I x) :
  (Π (x : M), V x) :=
  𝓓.toFun (𝓓.toFun s Y) X - 𝓓.toFun (𝓓.toFun s X) Y - 𝓓.toFun s (VectorField.mlieBracket I X Y)

/--
The curvature tensor is skew-symmetric in the first two components.
-/
lemma curvature_skew (𝓓 : LinearConnection I M F n V)
  (s : Π (x : M), V x)
  (X Y : Π (x : M), TangentSpace I x) : curvature F n V 𝓓 s X Y = curvature F n V 𝓓 s Y X := by
  sorry

end Curvature


end LinearConnection
