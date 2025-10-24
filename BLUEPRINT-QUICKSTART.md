# Blueprint Quick Start Guide

## 🎯 What You Have

Your RicciFlow project now has a **Lean Blueprint** - a beautiful documentation system that:
- ✅ Shows your project structure visually
- ✅ Tracks which theorems are proven (green) vs. incomplete (red)
- ✅ Links math statements to Lean code
- ✅ Generates web pages and PDFs

## 📂 Where Everything Is

```
RicciFlow/
├── blueprint/src/     # LaTeX source files (edit these)
├── blueprint/web/     # Generated HTML (view in browser)
├── view-blueprint.sh  # 🚀 Quick viewer script
└── update-blueprint.sh # 🔄 Regenerate after changes
```

## ⚡ Quick Commands

### View the Blueprint (Easiest Way)

```bash
cd /Users/lixinze/RicciFlow
./view-blueprint.sh
```

Then open: **http://localhost:8000**

### Or Open HTML Directly

```bash
open /Users/lixinze/blueprint/web/index.html
```

### Update After Code Changes

```bash
cd /Users/lixinze/RicciFlow
./update-blueprint.sh
```

### Manual Commands

```bash
# From /Users/lixinze (parent directory):
leanblueprint web      # Generate HTML
leanblueprint pdf      # Generate PDF
leanblueprint serve    # Start web server
leanblueprint all      # Generate everything
```

## ✏️ Editing the Blueprint

### Add a New Definition

Edit `blueprint/src/blueprint.tex` or `blueprint/src/web.tex`:

```latex
\begin{definition}[Name]
\label{def:mylabel}
\lean{ModuleName.definitionName}
\uses{def:other-definition}
Description here...
\end{definition}
```

### Add a New Theorem

```latex
\begin{theorem}[Name]
\label{thm:mylabel}
\lean{ModuleName.theoremName}
\uses{def:dependency}
Statement here...
\end{theorem}

\begin{proof}
\leanok  % ← Add this if proven!
Proof sketch...
\end{proof}
```

### After Editing

```bash
cd /Users/lixinze/RicciFlow
./update-blueprint.sh
```

## 🎨 Current Blueprint Structure

Your blueprint documents:

1. **Chapter 2: Basic Definitions**
   - Manifold type with topology and charts

2. **Chapter 3: Riemannian Manifolds**
   - RiemannianMetric structure

3. **Chapter 4: Ricci Curvature**
   - RicciTensor structure
   - scalarCurvature function

4. **Chapter 5: Ricci Flow**
   - ricci_flow_equation (the main PDE)
   - short_time_existence theorem ⭐

## 🎯 Blueprint Tags

- `\lean{Name}` - Links to Lean declaration
- `\leanok` - Marks as complete (green ✓)
- `\notready` - Marks as incomplete (red ✗)
- `\uses{labels}` - Shows dependencies

## 🔍 Status Tracking

The blueprint automatically detects:
- **Green (✓)**: Complete definitions/theorems
- **Yellow (⚠️)**: Partial or axioms
- **Red (✗)**: Uses `sorry`

## 💡 Tips

1. **Keep it updated**: Run `./update-blueprint.sh` after each coding session
2. **Edit both files**: Update both `blueprint.tex` (PDF) and `web.tex` (HTML)
3. **Watch progress**: See your green ✓ count grow as you complete proofs!
4. **Share it**: The `blueprint/web/` folder can be deployed anywhere

## 🐛 Troubleshooting

**Problem**: "No such file or directory"
**Solution**: Make sure to run `leanblueprint` commands from `/Users/lixinze`

**Problem**: Blueprint doesn't update
**Solution**:
```bash
cd /Users/lixinze/RicciFlow
lake clean
lake build
cd /Users/lixinze
leanblueprint web
```

## 📚 Full Documentation

See [README-Blueprint.md](README-Blueprint.md) for complete details.

---

**View Now**: Run `./view-blueprint.sh` and visit http://localhost:8000
