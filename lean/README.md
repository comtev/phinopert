# Lean formalisation

The final target is
[`Phinopert.actual_phinopert_no_proper_shadow_fit`](ActualPhinopertNoProperShadowFit.lean)
of type `NoProperShadowFit`. The retained complete verification passed on
16 November 2026; see the [verification report](../docs/VERIFICATION.md).

## Why these files are kept

Of the original 157 files in this directory, **153 lie in the final theorem's
transitive source import closure**. The other four (`*NegativeControls.lean`)
are regression controls and remain useful for review. They are not obsolete
proof drafts. Removing this small source collection would make the mathematical
definitions and reductions harder to inspect without materially reducing size.

The final theorem, all-root assembly and root-coverage bridge have been added
unchanged from the verified run. Individual earlier files may correctly describe
their own result as a conditional lemma or a partial milestone. The final theorem
supplies the missing hypotheses; those historical source comments have not been
rewritten, preserving source identity.

## Building

Toolchain: **Lean 4.19.0**. mathlib: commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (tag `v4.19.0`).

This directory is the small, browsable portion of the formalisation, not a
standalone Lake project. The complete import closure contains **169,583 project
modules**, including generated certificates and assembly lemmas. Its source
archive has its own pinned Lake configuration, inventory and bounded replay
script. See [release assets](../docs/RELEASE_ASSETS.md) and
[reproduction](../docs/REPRODUCING.md).

Neither the completion JSON nor a successful source-inventory check is a fresh
Lean proof. The portable distribution must complete a clean rebuild and final
axiom audit before that stronger reproducibility claim is made. Compiled objects,
local caches and toolchains are not included in this Git tree.
