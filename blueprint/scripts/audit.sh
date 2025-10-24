#!/usr/bin/env bash
# audit.sh - Axiom auditing script for the Poincaré Program

set -e

echo "============================================"
echo "Axiom Audit for Poincaré via Ricci Flow"
echo "============================================"
echo ""

# Audit Poincare layer
echo "Auditing main theorems..."
echo ""
lake env lean --run Poincare/Dev/Audit.lean 2>&1 | grep -A 100 "axioms" | head -50

echo ""
echo "✅ Audit complete!"
