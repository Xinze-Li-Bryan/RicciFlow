#!/usr/bin/env bash
# Script to regenerate the blueprint after code changes

set -e

echo "🔄 Updating RicciFlow Blueprint"
echo "================================"
echo ""

echo "1️⃣  Building Lean project..."
cd /Users/lixinze/RicciFlow
lake build

echo ""
echo "2️⃣  Regenerating blueprint..."
cd /Users/lixinze
leanblueprint web

echo ""
echo "✅ Blueprint updated successfully!"
echo "📁 View at: /Users/lixinze/blueprint/web/index.html"
echo "🚀 Or run: ./view-blueprint.sh"
