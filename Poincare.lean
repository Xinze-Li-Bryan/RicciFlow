-- Poincare.lean
-- Top-level module for the Poincaré Program

import Poincare.Final
import Poincare.Core.TopologyInput
import Poincare.Perelman.KappaSolutionClassification
import Poincare.Perelman.PoincareFromPerelman
import Poincare.Dev.Audit
import Poincare.Dev.Notes

/-!
# Poincaré Conjecture via Ricci Flow

This is the top-level module for the Poincaré Program.

## Main Goal

Formalize the proof of the Poincaré Conjecture using Perelman's
Ricci Flow with surgery approach.

**Theorem**: Every simply-connected, closed 3-manifold is homeomorphic to S³.

## Structure

- `Poincare.Final`: Main theorem statements
- `Poincare.Core.TopologyInput`: Topological prerequisites
- `Poincare.Perelman.Package`: Perelman's toolkit
- `Poincare.Perelman.Entropy`: W-entropy, F-functional, ν-entropy
- `Poincare.Perelman.KappaSolutions`: κ-solution theory
- `Poincare.Perelman.KappaSolutionClassification`: κ-solution classification (Phase 4)
- `Poincare.Perelman.GeometricSurgery`: Surgery framework
- `Poincare.Perelman.PoincareFromPerelman`: Proof derivation
- `Poincare.Dev.Audit`: Axiom auditing
- `Poincare.Dev.Notes`: Development notes

## Status

**Phase 0-4 Progress** (October 2024):
- ✅ Phase 0: Architecture setup
- ✅ Phase 1: Topology foundations
- ✅ Phase 2: Perelman entropy functionals
- ✅ Phase 3: κ-solutions and geometric surgery
- ✅ Phase 4: κ-solution classification (NEW)

**Next**: Phase 5 (Surgery theory and extinction)

## Dependencies

This layer builds on the complete `RicciFlow` library (0 sorry).
-/
