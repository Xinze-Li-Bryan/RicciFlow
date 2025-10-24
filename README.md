# Ricci Flow Formalization in Lean 4

A formal verification project for Ricci Flow theory using the Lean 4 proof assistant.

[![Lean 4](https://img.shields.io/badge/Lean-4-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-latest-blue)](https://github.com/leanprover-community/mathlib4)
[![Blueprint](https://img.shields.io/badge/blueprint-online-blue)](https://xinze-li-bryan.github.io/RicciFlow/)

## Overview

Ricci Flow is a fundamental geometric evolution equation introduced by Richard Hamilton in 1982, which has profound applications including Perelman's proof of the Poincaré conjecture. This project aims to formalize the mathematical foundations of Ricci Flow theory in Lean 4, providing machine-checked proofs of key theorems.

The formalization includes:
- Riemannian manifold structures
- Ricci curvature tensor definitions
- The Ricci Flow equation
- Short-time existence theorem (in progress)

## Project Structure

```
RicciFlow/
├── RicciFlow/
│   ├── Basic.lean              # Fundamental lemmas (real numbers, topology)
│   ├── RiemannianManifold.lean # Riemannian metric and inner products
│   ├── RicciCurvature.lean     # Ricci tensor and scalar curvature
│   └── Flow.lean               # Ricci Flow equation and theorems
├── blueprint/                   # LaTeX blueprint for the formalization
│   └── src/
│       ├── content.tex         # Main mathematical content
│       └── web.tex             # Blueprint configuration
├── docs/                        # Generated API documentation (doc-gen4)
├── lakefile.lean               # Lake build configuration
└── leanblueprint.toml          # Blueprint configuration
```

## Getting Started

### Prerequisites

- **Lean 4**: Install via [elan](https://github.com/leanprover/elan)
- **Lake**: Lean's package manager (comes with Lean 4)
- **Python 3** (for blueprint): With `plastex` and `leanblueprint` packages

### Installation

1. **Clone the repository**:
   ```bash
   git clone https://github.com/Xinze-Li-Bryan/RicciFlow.git
   cd RicciFlow
   ```

2. **Build the project**:
   ```bash
   lake build
   ```
   This will download Mathlib and compile all dependencies.

3. **Generate API documentation** (optional):
   ```bash
   lake -R -Kenv=dev build RicciFlow:docs
   ```
   The documentation will be generated in the `docs/` directory.

4. **View the blueprint** (optional):
   ```bash
   pip install leanblueprint plastex
   cd blueprint
   leanblueprint web
   leanblueprint serve
   ```
   Then visit `http://localhost:8000` to view the interactive blueprint.

## Documentation

### Blueprint

The [Blueprint](blueprint/src/content.tex) provides a comprehensive overview of the formalization roadmap, including:
- Mathematical definitions and theorems
- Dependency graphs
- Links to corresponding Lean code
- Formalization status tracking

**Features**:
- Interactive web interface with dependency visualization
- Direct links from math statements to Lean declarations
- Proof completion tracking with `\leanok` markers

### API Documentation

The project uses [doc-gen4](https://github.com/leanprover/doc-gen4) to generate API documentation. After building the docs, you can:

1. Start a local HTTP server:
   ```bash
   cd docs && python3 -m http.server 8001
   ```

2. Visit `http://localhost:8001` to browse the documentation

## Current Status

### Completed ✓
- **Basic lemmas**: Real number properties, topological foundations
- **Riemannian manifolds**: Metric structure with symmetry and positive-definiteness
- **Inner products**: Tangent vector inner products and norms
- **Ricci curvature**: Simplified tensor representation and scalar curvature
- **Project infrastructure**: Blueprint, doc-gen4, dependency tracking

### In Progress 🚧
- **Short-time existence theorem**: Framework established, proof incomplete
- **Full tensor formalization**: Current implementation uses simplified types

### Future Work 📋
- Complete Ricci Flow short-time existence proof
- Maximum principles for Ricci Flow
- Normalized Ricci Flow
- Perelman's monotonicity formulas
- Long-time behavior and convergence results
- Full tangent bundle and Riemann tensor implementation

## Mathematical Background

### Ricci Flow Equation

The Ricci Flow is a geometric evolution equation that deforms a Riemannian metric `g` on a manifold `M` according to:

```
∂g/∂t = -2 Ric(g)
```

where `Ric(g)` is the Ricci curvature tensor. This equation can be viewed as a nonlinear heat equation for metrics, smoothing out irregularities in the geometry.

### Key Results

1. **Short-Time Existence** (Hamilton, 1982): For any smooth compact Riemannian manifold `(M, g₀)`, there exists `T > 0` and a smooth solution `g(t)` to the Ricci Flow for `t ∈ [0, T)` with initial condition `g(0) = g₀`.

2. **Scalar Curvature**: The trace of the Ricci tensor, measuring the "total curvature" at a point:
   - `R > 0`: positive curvature (sphere-like)
   - `R < 0`: negative curvature (hyperbolic)
   - `R = 0`: flat (Euclidean)

## Implementation Notes

### Current Simplifications

The implementation uses a **simplified type-theoretic approach** for pedagogical clarity and faster prototyping:

1. **Abstract tangent spaces**: Uses type parameter `V` instead of dependent `TangentSpace ℝ M x`
2. **Stored scalar curvature**: Directly stores trace value instead of computing from tensor components
3. **Axiomatized Ricci Flow equation**: Core PDE structure is axiomatized

### Future Extension Path

**Phase 1** (Current): Simplified types with abstract vector spaces
```lean
structure RiemannianMetric (M : Type*) (V : Type*) where
  toFun : M → (V → V → ℝ)
```

**Phase 2** (Intermediate): Dependent tangent spaces
```lean
def RiemannianMetric (M : Type*) :=
  ∀ x : M, TangentSpace ℝ M x → TangentSpace ℝ M x → ℝ
```

**Phase 3** (Complete): Full tensor field formalization
```lean
def RiemannianMetric (M : Type*) :=
  SmoothSection (SymmetricPositive (⊗² T*M))
```

## Contributing

Contributions are welcome! Areas where help is needed:

- **Proofs**: Complete sorry'd theorems, especially short-time existence
- **Tensor calculus**: Implement full Riemann tensor and contraction operations
- **Documentation**: Improve docstrings and blueprint explanations
- **Testing**: Add more lemmas and sanity checks

Please open an issue or pull request on GitHub.

## References

### Mathematical References
- Hamilton, R. S. (1982). "Three-manifolds with positive Ricci curvature". *J. Differential Geom.*
- Perelman, G. (2002). "The entropy formula for the Ricci flow and its geometric applications". arXiv:math/0211159
- Lee, J. M. (1997). *Riemannian Manifolds: An Introduction to Curvature*
- Do Carmo, M. P. (1992). *Riemannian Geometry*

### Lean 4 Resources
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)

### Related Formalizations
- [Sphere Eversion Project](https://github.com/leanprover-community/sphere-eversion): Convex integration in Lean
- [Lean Liquid Project](https://github.com/leanprover-community/lean-liquid): Condensed mathematics
- [Carleson Theorem](https://github.com/fpvandoorn/carleson): Harmonic analysis formalization

## License

This project is available under the [Apache 2.0 License](LICENSE).

## Author

**Xinze Li**
GitHub: [@Xinze-Li-Bryan](https://github.com/Xinze-Li-Bryan)

## Acknowledgments

- The Lean community for developing Lean 4 and Mathlib
- Patrick Massot for the leanblueprint tool
- The sphere-eversion project for inspiration on project structure
- Richard Hamilton and Grigori Perelman for the beautiful mathematics

---

*Last updated: October 2024*
