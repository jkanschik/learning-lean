# Vector bundles and tensor fields

## Vector bundles

## Sections in vector bundles

## Vector fields as sections


# Open issues

- [ ] What exactly is the difference between the notation 





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
