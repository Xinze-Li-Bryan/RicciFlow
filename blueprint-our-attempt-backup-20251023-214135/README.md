# RicciFlow Blueprint

This directory contains the blueprint for the Ricci Flow formalization project.

## Structure

```
blueprint/
├── src/                    # Source files
│   ├── web.tex            # Main web configuration
│   ├── print.tex          # Print version configuration
│   ├── content.tex        # Mathematical content
│   ├── blueprint.sty      # Blueprint package (local override)
│   └── macros/
│       └── common.tex     # Shared LaTeX macros
└── web/                   # Generated HTML files
    ├── *.html             # Chapter and section pages
    ├── dep_graph.svg      # Dependency graph (SVG)
    ├── dep_graph.dot      # Dependency graph (GraphViz)
    └── dep_graph.html     # Interactive dependency graph page
```

## Viewing the Blueprint

From the repository root:

```bash
./view-blueprint.sh
```

Then open http://localhost:8000 in your browser.

## Rebuilding the Blueprint

After editing `src/content.tex`:

```bash
./rebuild-blueprint.sh
```

This will:
1. Regenerate HTML files with PlasTeX
2. Generate dependency graph from `\uses{}` declarations
3. Update all pages with navigation links

## Editing Content

Edit `blueprint/src/content.tex` to add new:
- Definitions: `\begin{definition}...\end{definition}`
- Lemmas: `\begin{lemma}...\end{lemma}`
- Theorems: `\begin{theorem}...\end{theorem}`

### Required Tags

For each declaration:

```latex
\begin{definition}[Title]
\label{unique-label}           % Required: unique reference
\lean{Lean.DeclarationName}    % Required: Lean identifier
\leanok                        % Optional: mark as formalized
\uses{label1, label2}          % Optional: dependencies
Definition content here...
\end{definition}
```

### Examples

```latex
\begin{definition}[Riemannian Metric]
\label{def:riemannian-metric}
\lean{RicciFlow.RiemannianMetric}
\leanok
\uses{def:manifold-type, lem:pos-mul-pos}
A Riemannian metric is a smooth, symmetric, positive-definite $(0,2)$-tensor.
\end{definition}
```

## Dependency Graph

The dependency graph shows:
- **Boxes (□)**: Definitions
- **Ellipses (○)**: Lemmas and Theorems
- **Green nodes**: Fully formalized (\leanok)
- **Yellow nodes**: Not yet formalized
- **Arrows**: A → B means "B depends on A"

## Current Statistics

- **Total declarations**: 13
- **Definitions**: 5
- **Lemmas**: 6
- **Theorems**: 2
- **Formalized**: 11 (85%)
- **Work in progress**: 2 (15%)

## Files to Edit

- `src/content.tex` - Add mathematical content
- `src/macros/common.tex` - Add LaTeX macros
- `src/web.tex` - Modify web configuration (rarely needed)

## Files NOT to Edit Manually

- `web/*.html` - Generated automatically
- `web/dep_graph.svg` - Generated automatically
- `web/dep_graph.dot` - Generated automatically

## Troubleshooting

### PlasTeX errors

If `leanblueprint web` fails with Jinja2 errors, use the rebuild script instead:
```bash
./rebuild-blueprint.sh
```

This uses PlasTeX directly and manually generates the dependency graph.

### Missing dependency graph

Run:
```bash
python3 generate_dep_graph.py
```

### Broken links

Make sure all `\label{}` references are unique and match the `\uses{}` dependencies.

## Resources

- [leanblueprint documentation](https://github.com/PatrickMassot/leanblueprint)
- [PlasTeX documentation](https://plastex.github.io/plastex/)
- [Example blueprints](https://github.com/PatrickMassot/leanblueprint/wiki)
