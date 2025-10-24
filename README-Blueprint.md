# Ricci Flow Blueprint

This document explains how to use and maintain the Lean Blueprint for the RicciFlow project.

## What is a Blueprint?

A **Lean Blueprint** is a powerful documentation system that:
- Visualizes the dependency graph of definitions and theorems
- Tracks which parts are formalized (✓ green) vs. incomplete (✗ red)
- Generates beautiful web and PDF documentation
- Links mathematical statements to their Lean code

## Directory Structure

```
RicciFlow/
├── blueprint/
│   ├── src/              # LaTeX source files
│   │   ├── blueprint.tex # Main document (for PDF)
│   │   ├── web.tex       # Web version
│   │   ├── macros.tex    # Custom LaTeX macros
│   │   ├── blueprint.sty # Blueprint style package
│   │   ├── plastex.cfg   # Web generation config
│   │   └── web.paux      # PlasTeX auxiliary file
│   └── web/              # Generated HTML files
├── scripts/
│   └── blueprint.sh      # Helper script
└── leanblueprint.toml    # Blueprint configuration
```

## Prerequisites

All dependencies are already installed on your system:
- ✅ Python 3.12.0
- ✅ leanblueprint 0.0.18
- ✅ Graphviz 14.0.0
- ✅ LaTeX (TeX Live 2023)

## Generating the Blueprint

### Option 1: Generate Web Version (Recommended)

```bash
cd /Users/lixinze
leanblueprint web
```

This generates HTML files in `blueprint/web/`

### Option 2: Generate PDF Version

```bash
cd /Users/lixinze
leanblueprint pdf
```

This generates a PDF in `blueprint/print/blueprint.pdf`

### Option 3: Generate Everything

```bash
cd /Users/lixinze
leanblueprint all
```

This generates both web and PDF versions.

## Viewing the Blueprint

### View Web Version Locally

```bash
cd /Users/lixinze
leanblueprint serve
```

Then open your browser to: **http://localhost:8000**

The server will keep running until you press Ctrl+C.

### View Web Files Directly

Open the file: `/Users/lixinze/blueprint/web/index.html` in your browser.

## Blueprint Structure

The blueprint is organized into chapters:

### Chapter 1: Introduction
Overview of the Ricci Flow formalization project.

### Chapter 2: Basic Definitions
- **Definition 2.1**: Manifold Type (`RicciFlow.Basic`)
  - Status: ✓ Complete
  - Defines the base type `M` with topological and charted space structures

### Chapter 3: Riemannian Manifolds
- **Definition 3.1**: Riemannian Metric (`RicciFlow.RiemannianMetric`)
  - Status: ⚠️ Partial (structure defined, properties pending)
  - Depends on: Definition 2.1

### Chapter 4: Ricci Curvature
- **Definition 4.1**: Ricci Tensor (`RicciFlow.RicciTensor`)
  - Status: ⚠️ Partial (structure defined)
  - Depends on: Definition 3.1

- **Definition 4.2**: Scalar Curvature (`RicciFlow.scalarCurvature`)
  - Status: ✗ Incomplete (uses `sorry`)
  - Depends on: Definition 4.1

### Chapter 5: Ricci Flow
- **Definition 5.1**: Ricci Flow Equation (`RicciFlow.ricci_flow_equation`)
  - Status: ⚠️ Axiom (not proven)
  - Depends on: Definitions 3.1, 4.1

- **Theorem 5.1**: Short-Time Existence (`RicciFlow.short_time_existence`)
  - Status: ✗ Incomplete (uses `sorry`)
  - Depends on: Definition 5.1
  - This is the main theorem!

## Tracking Progress

The blueprint automatically detects:
- **Green (✓)**: Definitions and theorems that are complete
- **Yellow (⚠️)**: Partial implementations or axioms
- **Red (✗)**: Declarations that use `sorry`

To update the status tracking:

```bash
cd /Users/lixinze/RicciFlow
lake build  # Build your Lean project
cd /Users/lixinze
leanblueprint checkdecls  # Check which declarations exist
leanblueprint web  # Regenerate with updated status
```

## Editing the Blueprint

### To Add New Definitions

Edit `/Users/lixinze/blueprint/src/blueprint.tex` (or `web.tex`):

```latex
\begin{definition}[Your Definition Name]
\label{def:your-label}
\lean{YourModule.yourDefinition}
\uses{def:dependency1, def:dependency2}
Your mathematical description here.
\end{definition}
```

### To Add New Theorems

```latex
\begin{theorem}[Your Theorem Name]
\label{thm:your-label}
\lean{YourModule.yourTheorem}
\uses{def:definition-it-uses}
Statement of the theorem.
\end{theorem}

\begin{proof}
\leanok  % Add this if the proof is complete in Lean
Proof sketch or full proof.
\end{proof}
```

### Key Commands

- `\lean{Name}`: Links to Lean declaration
- `\leanok`: Marks as complete (green ✓)
- `\notready`: Marks as incomplete (red ✗)
- `\uses{labels}`: Declares dependencies

## Regenerating After Changes

After editing the blueprint:

```bash
cd /Users/lixinze
leanblueprint web
leanblueprint serve
```

## Advanced Features

### Dependency Graph

The blueprint can generate a dependency graph showing how definitions and theorems relate. This is automatically included in the PDF version.

### Custom Macros

Edit `/Users/lixinze/blueprint/src/macros.tex` to add your own LaTeX macros:

```latex
\newcommand{\mycommand}{...}
```

### Deployment

To deploy the blueprint to GitHub Pages or a web server, simply copy the entire `blueprint/web/` directory.

## Troubleshooting

### Issue: "No such file or directory" errors

**Solution**: Make sure you run commands from `/Users/lixinze` (not the RicciFlow subdirectory), because `leanblueprint` looks for the `blueprint/` folder in the parent of your current directory.

### Issue: Blueprint doesn't show correct status

**Solution**:
1. Make sure your Lean project builds: `cd /Users/lixinze/RicciFlow && lake build`
2. Regenerate the blueprint: `cd /Users/lixinze && leanblueprint web`

### Issue: LaTeX compilation errors

**Solution**: Check `/Users/lixinze/blueprint/src/blueprint.tex` for syntax errors.

## Quick Reference

```bash
# Generate web version
cd /Users/lixinze && leanblueprint web

# Generate PDF version
cd /Users/lixinze && leanblueprint pdf

# Generate both
cd /Users/lixinze && leanblueprint all

# Start local server
cd /Users/lixinze && leanblueprint serve

# Check declaration status
cd /Users/lixinze && leanblueprint checkdecls
```

## Next Steps

1. **Complete the definitions**: Remove `sorry` from the Lean code
2. **Update the blueprint**: Add more theorems and lemmas as you formalize them
3. **Regenerate regularly**: Keep the blueprint in sync with your code
4. **Share it**: Deploy the web version so others can follow your progress!

---

**Blueprint Homepage**: View at `/Users/lixinze/blueprint/web/index.html`
**Blueprint Server**: `leanblueprint serve` → http://localhost:8000
