---
name: lean-lsp-mcp
description: Use when working in this Lean 4 repository and Codex needs diagnostics, proof goals, hovers, declarations, code actions, verification, local Lean search, or build feedback for `.lean` files. Prefer the configured `lean-lsp` MCP server tools from `lean-lsp-mcp` whenever they are available; fall back to `lake`/`lean` shell commands only when MCP tools are unavailable or insufficient.
---

# Lean LSP MCP

This skill is specific to the `provable_computation` Lean repository. The configured MCP server is named `lean-lsp` and is expected to run `uvx lean-lsp-mcp` with `LEAN_PROJECT_PATH=/home/ji/projects/provable_computation`.

## Workflow

1. Before editing Lean code or proofs, inspect the relevant file through the Lean LSP MCP tools if they are exposed in the current Codex session.
2. Use project-relative file paths such as `ProvableComputation/LinearAlgebra/GaussianElimination/Rref.lean`.
3. Prefer `lean_file_outline` to understand imports and declarations before making structural changes.
4. Prefer `lean_diagnostic_messages` for current errors and warnings in the file under edit.
5. Prefer `lean_goal` or `lean_term_goal` at the proof location before changing tactics or terms.
6. Prefer `lean_hover_info`, `lean_declaration_file`, and `lean_references` when the type, source, or callers of a declaration are unclear.
7. Prefer `lean_code_actions` for "try this" suggestions, then apply only suggestions that fit the surrounding proof style.
8. Prefer `lean_verify` or file diagnostics after edits; run `lean_build` or `lake build` after nontrivial cross-module changes.
9. Use `lean_local_search`, `lean_loogle`, or related theorem-search tools for Lean facts; use `rg` for plain text search in repository files.

## Fallback

If MCP tools are not available in the current session, say so briefly and use the normal Lean toolchain:

- `lake env lean <file>` for a single file.
- `lake build` for project-level validation.
- `uvx lean-lsp-mcp --version` and `codex mcp list` when checking whether the server is installed and configured.

After adding or changing MCP configuration, expect existing Codex sessions to require restart before new MCP tools appear.
