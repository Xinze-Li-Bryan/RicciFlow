#!/usr/bin/env bash
# Rebuild the RicciFlow blueprint
# This script regenerates the HTML and dependency graph

set -e

echo "🔨 Rebuilding RicciFlow Blueprint"
echo "================================="
echo ""

# Step 1: Generate HTML with plastex
echo "📝 Step 1: Generating HTML with PlasTeX..."
cd blueprint/src
plastex --renderer=HTML5 web.tex
mv web ../
cd ../..

# Step 2: Generate dependency graph
echo "📊 Step 2: Generating dependency graph..."
python3 generate_dep_graph.py

# Step 3: Copy dep_graph.html template
echo "📄 Step 3: Creating dep_graph.html page..."
if [ ! -f "blueprint/web/dep_graph.html" ]; then
  cp blueprint-templates/dep_graph.html blueprint/web/ 2>/dev/null || echo "Template not found, will create on next run"
fi

# Step 4: Add Lean code links
echo "🔗 Step 4: Adding Lean code links..."
for file in blueprint/web/sect*.html blueprint/web/chap-*.html; do
  # Add links to Basic.lean declarations
  sed -i '' 's|RicciFlow\.pos_mul_pos|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/Basic.lean#L21" class="lean-link">RicciFlow.pos_mul_pos</a>|g' "$file"
  sed -i '' 's|RicciFlow\.square_pos_of_ne_zero|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/Basic.lean#L26" class="lean-link">RicciFlow.square_pos_of_ne_zero</a>|g' "$file"
  sed -i '' 's|RicciFlow\.exists_pos_real|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/Basic.lean#L31" class="lean-link">RicciFlow.exists_pos_real</a>|g' "$file"
  sed -i '' 's|RicciFlow\.inv_pos_of_pos|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/Basic.lean#L37" class="lean-link">RicciFlow.inv_pos_of_pos</a>|g' "$file"
  sed -i '' 's|RicciFlow\.continuousAt_iff_continuousWithinAt|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/Basic.lean#L48" class="lean-link">RicciFlow.continuousAt_iff_continuousWithinAt</a>|g' "$file"

  # Add links to RiemannianManifold.lean
  sed -i '' 's|RicciFlow\.RiemannianMetric|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/RiemannianManifold.lean#L60" class="lean-link">RicciFlow.RiemannianMetric</a>|g' "$file"
  sed -i '' 's|RicciFlow\.innerProduct<|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/RiemannianManifold.lean#L94" class="lean-link">RicciFlow.innerProduct</a><|g' "$file"
  sed -i '' 's|RicciFlow\.normSq<|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/RiemannianManifold.lean#L104" class="lean-link">RicciFlow.normSq</a><|g' "$file"
  sed -i '' 's|RicciFlow\.innerProduct_symm|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/RiemannianManifold.lean#L111" class="lean-link">RicciFlow.innerProduct_symm</a>|g' "$file"
  sed -i '' 's|RicciFlow\.normSq_pos|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/RiemannianManifold.lean#L116" class="lean-link">RicciFlow.normSq_pos</a>|g' "$file"

  # Add links to RicciCurvature.lean and Flow.lean
  sed -i '' 's|RicciFlow\.RicciTensor|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/RicciCurvature.lean#L38" class="lean-link">RicciFlow.RicciTensor</a>|g' "$file"
  sed -i '' 's|RicciFlow\.scalarCurvature<|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/RicciCurvature.lean#L74" class="lean-link">RicciFlow.scalarCurvature</a><|g' "$file"
  sed -i '' 's|RicciFlow\.scalarCurvature_eq_traceValue|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/RicciCurvature.lean#L82" class="lean-link">RicciFlow.scalarCurvature_eq_traceValue</a>|g' "$file"
  sed -i '' 's|RicciFlow\.ricci_flow_equation|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/Flow.lean#L14" class="lean-link">RicciFlow.ricci_flow_equation</a>|g' "$file"
  sed -i '' 's|RicciFlow\.short_time_existence|<a href="file:///Users/lixinze/RicciFlow/RicciFlow/Flow.lean#L17" class="lean-link">RicciFlow.short_time_existence</a>|g' "$file"
done

# Step 5: Update HTML files with dep_graph links
echo "📊 Step 5: Adding dependency graph links to sidebar..."
for file in blueprint/web/index.html blueprint/web/chap-*.html blueprint/web/sect*.html; do
  if [ -f "$file" ] && ! grep -q "dep_graph.html" "$file"; then
    sed -i '' '/<\/ul>/i\
<li class="">\
  <a href="dep_graph.html"><span class="toc_ref">📊</span> <span class="toc_entry">Dependency Graph</span></a>\
 </li>
' "$file"
  fi
done

echo ""
echo "✅ Blueprint rebuilt successfully!"
echo ""
echo "📁 Files generated:"
echo "   - blueprint/web/*.html (8 pages)"
echo "   - blueprint/web/dep_graph.svg"
echo "   - blueprint/web/dep_graph.dot"
echo ""
echo "🌐 To view: ./view-blueprint.sh"
