#!/usr/bin/env python3
"""
Add Lean code links to generated HTML files.
Maps Lean declarations to their source files.
"""
from pathlib import Path
import re

# Mapping of Lean declarations to file paths and approximate line numbers
LEAN_DECLS = {
    'RicciFlow.pos_mul_pos': ('RicciFlow/Basic.lean', 21),
    'RicciFlow.square_pos_of_ne_zero': ('RicciFlow/Basic.lean', 26),
    'RicciFlow.exists_pos_real': ('RicciFlow/Basic.lean', 31),
    'RicciFlow.inv_pos_of_pos': ('RicciFlow/Basic.lean', 37),
    'RicciFlow.continuousAt_iff_continuousWithinAt': ('RicciFlow/Basic.lean', 48),
    'RicciFlow.RiemannianMetric': ('RicciFlow/RiemannianManifold.lean', 60),
    'RicciFlow.innerProduct': ('RicciFlow/RiemannianManifold.lean', 94),
    'RicciFlow.normSq': ('RicciFlow/RiemannianManifold.lean', 104),
    'RicciFlow.innerProduct_symm': ('RicciFlow/RiemannianManifold.lean', 111),
    'RicciFlow.normSq_pos': ('RicciFlow/RiemannianManifold.lean', 116),
    'RicciFlow.RicciTensor': ('RicciFlow/RicciCurvature.lean', 38),
    'RicciFlow.scalarCurvature': ('RicciFlow/RicciCurvature.lean', 74),
    'RicciFlow.scalarCurvature_eq_traceValue': ('RicciFlow/RicciCurvature.lean', 82),
    'RicciFlow.ricci_flow_equation': ('RicciFlow/Flow.lean', 14),
    'RicciFlow.short_time_existence': ('RicciFlow/Flow.lean', 17),
}

def add_lean_links_to_html(html_path):
    """Add Lean code links to an HTML file."""
    content = html_path.read_text()
    modified = False

    for decl_name, (file_path, line_num) in LEAN_DECLS.items():
        # Create link to local file (VSCode can open these)
        lean_link = f'<a href="../../{file_path}#L{line_num}" class="lean-decl-link" title="View in Lean source">📄 {decl_name}</a>'

        # Find where this declaration appears (usually right after the definition/lemma/theorem heading)
        # Look for the declaration name in code or text
        pattern = rf'<code>{re.escape(decl_name)}</code>'
        if pattern in content:
            # Add link after the code element
            replacement = f'<code>{decl_name}</code> {lean_link}'
            content = content.replace(f'<code>{decl_name}</code>', replacement, 1)
            modified = True

    if modified:
        html_path.write_text(content)
        return True
    return False

# Process all HTML files
html_dir = Path('blueprint/web')
for html_file in html_dir.glob('*.html'):
    if html_file.name != 'dep_graph.html':  # Skip dep_graph for now
        if add_lean_links_to_html(html_file):
            print(f"Added Lean links to {html_file.name}")

print("\n✅ Lean code links added to HTML files!")
print("\nNote: Links point to local Lean files. They will open in your editor if clicked.")
