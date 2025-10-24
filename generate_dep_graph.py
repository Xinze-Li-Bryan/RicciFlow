#!/usr/bin/env python3
"""
Manually generate dependency graph from blueprint content.tex
"""
import re
from pathlib import Path

# Read content.tex
content_file = Path("blueprint/src/content.tex")
content = content_file.read_text()

# Parse all theorems/definitions with their labels, lean tags, uses, and leanok status
items = []

# Pattern to match theorem environments
pattern = r'\\begin\{(definition|lemma|theorem|proposition|corollary)\}(?:\[(.*?)\])?(.*?)\\end\{\1\}'

for match in re.finditer(pattern, content, re.DOTALL):
    env_type = match.group(1)
    title = match.group(2) or ""
    body = match.group(3)

    # Extract label
    label_match = re.search(r'\\label\{([^}]+)\}', body)
    if not label_match:
        continue
    label = label_match.group(1)

    # Extract lean tag
    lean_match = re.search(r'\\lean\{([^}]+)\}', body)
    lean_tag = lean_match.group(1) if lean_match else ""

    # Check if leanok
    leanok = r'\leanok' in body

    # Extract uses
    uses_match = re.search(r'\\uses\{([^}]+)\}', body)
    uses = []
    if uses_match:
        uses_str = uses_match.group(1)
        uses = [u.strip() for u in uses_str.split(',')]

    items.append({
        'type': env_type,
        'title': title,
        'label': label,
        'lean': lean_tag,
        'leanok': leanok,
        'uses': uses
    })

print(f"Found {len(items)} items")
for item in items:
    print(f"  {item['label']}: {item['type']} - {item['title']} (leanok: {item['leanok']}, uses: {item['uses']})")

# Generate GraphViz DOT format
dot_lines = ['digraph dependencies {']
dot_lines.append('  rankdir=BT;')
dot_lines.append('  node [fontname="Arial"];')
dot_lines.append('')

# Add nodes
for item in items:
    # Determine shape: box for definitions, ellipse for lemmas/theorems
    shape = 'box' if item['type'] == 'definition' else 'ellipse'

    # Determine color: green if leanok, yellow otherwise
    fillcolor = 'lightgreen' if item['leanok'] else 'lightyellow'

    # Create node label
    node_label = item['label'].replace('_', '\\_').replace('-', '\\-')

    dot_lines.append(f'  "{item["label"]}" [shape={shape}, style=filled, fillcolor={fillcolor}, label="{node_label}"];')

dot_lines.append('')

# Add edges
for item in items:
    for dep in item['uses']:
        dot_lines.append(f'  "{dep}" -> "{item["label"]}";')

dot_lines.append('}')

# Write DOT file
dot_file = Path("blueprint/web/dep_graph.dot")
dot_file.write_text('\n'.join(dot_lines))
print(f"\nGenerated {dot_file}")

# Generate SVG using Graphviz
import subprocess
try:
    result = subprocess.run([
        'dot', '-Tsvg',
        'blueprint/web/dep_graph.dot',
        '-o', 'blueprint/web/dep_graph.svg'
    ], capture_output=True, text=True)
    if result.returncode == 0:
        print("Successfully generated blueprint/web/dep_graph.svg")
    else:
        print(f"Error generating SVG: {result.stderr}")
except FileNotFoundError:
    print("Graphviz 'dot' command not found. Please install Graphviz.")
    print("You can install it with: brew install graphviz")
