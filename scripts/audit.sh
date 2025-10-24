#!/usr/bin/env bash
# audit.sh - Axiom auditing script for the Poincaré Program

set -e

echo "============================================"
echo "Axiom Audit for Poincaré via Ricci Flow"
echo "============================================"
echo ""

# Build the project first
echo "Step 1: Building project..."
lake build
echo "✅ Build complete"
echo ""

# Audit Poincare layer
echo "Step 2: Auditing Poincare layer..."
echo ""
echo "Running: lake env lean Poincare/Dev/Audit.lean"
echo "-------------------------------------------"
lake env lean Poincare/Dev/Audit.lean 2>&1 | tee audit_output.txt
echo ""

# Summary
echo "============================================"
echo "Audit Summary"
echo "============================================"
echo ""
echo "Full output saved to: audit_output.txt"
echo ""
echo "Expected axioms in Poincare layer:"
echo "  - Topological placeholders (Is3Manifold, SimplyConnected, etc.)"
echo "  - Perelman theory (WEntropy, w_entropy_monotone, etc.)"
echo "  - Proof derivation (assign_riemannian_metric, etc.)"
echo ""
echo "Expected axioms in RicciFlow layer:"
echo "  - ricciNaturalityOn (only geometric axiom)"
echo ""
echo "Standard Lean axioms (acceptable):"
echo "  - Quot.sound, propext, Classical.choice, funext"
echo ""
echo "✅ Audit complete!"
echo ""
echo "To review the output, run:"
echo "  cat audit_output.txt"
