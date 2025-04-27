# Learning Mathlib

## Notes on how to use Mathlib differential geometry

[Manifolds in MathLib](/differentialGeometry/manifolds.md)

[Exercises](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fjkanschik%2Flearning-lean%2Frefs%2Fheads%2Fmain%2FLearningMathlib%2Fexercise%2Fmanifolds.lean)

Tactics Cheat Sheet: https://github.com/PatrickMassot/GlimpseOfLean/blob/master/tactics.pdf

## Creating the documentation

Link to doc-gen4: https://github.com/leanprover/doc-gen4

Creating the documentation:
- Go to directory `docbuild`
- Execute `lake build LearningMathlib:docs`

Serve files locally:
- Go to directory `docbuild/.lake/build/doc`
- Execute `py -m http.server`
- Open http:/localhost:8000

## Add MathJax to the Jekyll template

To add MathJax to the Jekyll template, the Javascript libraries need to be loaded in the HTML header.
This can be done by creating a file `_includes/head-custom.html` which contains

```html
<!-- MathJax -->
<script type="text/javascript"
    src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.3/MathJax.js?config=TeX-AMS-MML_HTMLorMML">
</script>
```

When this is done, the Javascript will be loaded and we can use MathJax anywhere in the Markdown files.

Please note that inline statements need to start / end with ``\\( \\)`` while block statements use ``\\[ ... \\]``

Example: A function between `M` and `N`is \\( f: M \to N \\).

And a block statement:

\\[ \tfrac{\nabla}{dt}\gamma' = 0 \\]
