# Blueprint Documentation

This directory contains the blueprint documentation for the Ricci Flow formalization project.

## Building the Blueprint

### Web Version (Recommended)

To build the interactive web version with dependency graphs:

```bash
cd blueprint
leanblueprint web
```

The output will be in the `web/` directory.

### PDF Version

To build the PDF version:

```bash
cd blueprint/src
latexmk print.tex
```

The PDF will be generated in the `print/` directory.

## Important Notes

- **DO NOT** try to compile `web.tex` directly with LaTeX. This file is used by the `leanblueprint` tool and requires special processing.
- Only `print.tex` should be compiled with standard LaTeX tools.
- The `web.tex` file is processed by plasTeX via the `leanblueprint web` command.

## Files

- `src/content.tex` - Main content (shared between web and print)
- `src/print.tex` - Entry point for PDF generation
- `src/web.tex` - Entry point for web generation (used by leanblueprint)
- `src/macros_common.tex` - Common macros
- `src/macros_print.tex` - Print-specific macros
- `src/macros_web.tex` - Web-specific macros
- `lean_decls` - List of Lean declarations to link
- `web/` - Generated web output
- `print/` - Generated PDF output

## Updating the Blueprint

After adding new Lean declarations:

1. Update `lean_decls` with the new declaration names (with `RicciFlow.` prefix)
2. Update `src/content.tex` with documentation and `\lean{}` tags
3. Run `lake exe checkdecls blueprint/lean_decls` to verify declarations exist
4. Run `leanblueprint web` to regenerate the web version
