# Learning Mathlib




## Creating the documentation

Link to doc-gen4: https://github.com/leanprover/doc-gen4

Creating the documentation:
- Go to directory `docbuild`
- Execute `lake build LearningMathlib:docs`

Serve files locally:
- Go to directory `docbuild/.lake/build/doc`
- Execute `py -m http.server`
- Open http:/localhost:8000

## Latex works that easy?

Inline \(2+2 = 4\) works maybe also

And a paragraph

\[ \tfrac{\Nabla}{dt}\gamma' = 0 \]
