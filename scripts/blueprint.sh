#!/usr/bin/env bash
# Script to generate the Lean blueprint

set -e

echo "Generating Lean blueprint..."

# Navigate to project root
cd "$(dirname "$0")/.."

# Run leanblueprint
leanblueprint build

echo "Blueprint generated successfully!"
echo "View it by opening: blueprint/web/index.html"
