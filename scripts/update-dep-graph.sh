#!/usr/bin/env bash
# Script to update the dependency graph

set -e

echo "🔄 Updating Dependency Graph"
echo "============================"
echo ""

# Navigate to project root
cd "$(dirname "$0")/.."

echo "1️⃣  Generating module import graph..."
lake exe graph

echo ""
echo "2️⃣  Converting to SVG..."
if [ -f "import_graph.dot" ]; then
    dot -Tsvg import_graph.dot -o blueprint/web/import_graph.svg
    echo "   ✅ Module import graph created"
fi

echo ""
echo "3️⃣  Generating blueprint dependency graph..."
if [ -f "blueprint/src/dep_graph.dot" ]; then
    dot -Tsvg blueprint/src/dep_graph.dot -o /Users/lixinze/blueprint/web/dep_graph.svg
    cp /Users/lixinze/blueprint/web/dep_graph.svg blueprint/web/
    echo "   ✅ Blueprint dependency graph created"
fi

echo ""
echo "4️⃣  Regenerating blueprint..."
cd /Users/lixinze
leanblueprint web

echo ""
echo "5️⃣  Fixing HTML to include graph..."
cd /Users/lixinze/RicciFlow
if grep -q '<div class="centered">  </div>' /Users/lixinze/blueprint/web/index.html; then
    sed -i.bak 's|<div class="centered">  </div>|<div class="centered">\n<img src="dep_graph.svg" alt="Dependency Graph" style="max-width: 100%; height: auto;">\n</div>|g' /Users/lixinze/blueprint/web/index.html
    echo "   ✅ HTML fixed"
fi

echo ""
echo "✅ Dependency graph updated!"
echo "📁 View at: /Users/lixinze/blueprint/web/index.html"
echo "🚀 Or run: ./view-blueprint.sh"
