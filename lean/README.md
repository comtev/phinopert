# Lean source snapshot

These 157 files are the original geometric/algebraic modules and the
small generated input tables needed by their imports. Source bytes are
preserved and identified in the release manifest. Toolchain: **Lean 4.19.0**.

This is not the full generated certificate replay, a clean-room rebuild or a
completed end-to-end proof. There is deliberately no misleading `lake build`
quick start: the historical drivers depend on frozen result bundles and
locally installed dependencies which this repository does not include.
Their thousands of generated leaf proofs and compiled objects are omitted.
No source file alone establishes a completed theorem or an axiom audit.

Read the repository proof-status and reproduction notes before interpreting
these modules. The two projects use different Lean/mathlib versions and should
not share a build directory. A portable, fully pinned end-to-end Lean release
remains a publication task after the current replay is reviewed.
