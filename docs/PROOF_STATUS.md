# Proof status

Updated 17 November 2026. The completed research run is `phinopert-global-final-v129`,
finished **16 November 2026 at 11:30:40 UTC**.

| Layer | Status |
| --- | --- |
| Exact body and 180 exposed vertices | Exact small checks included and runnable |
| Historical Python certificate chain | Recorded completed audit, 432/432 original roots |
| Full Lean non-Rupertness theorem | **Completed and audited in the research environment** |
| Final Lean assembly | 1,146/1,146 modules; 432/432 root exclusions |
| Final axiom audit | `propext`, `Classical.choice`, `Quot.sound` only |
| Core sources and final evidence | Included in this repository |
| Portable source distribution | See [release assets](RELEASE_ASSETS.md); packaging and successful rebuilding are different checks |
| Fresh end-to-end build of the portable distribution | Intentionally not performed for this candidate |
| Independent human review | Not claimed |

The exact final declaration is
[`Phinopert.actual_phinopert_no_proper_shadow_fit`](../lean/ActualPhinopertNoProperShadowFit.lean),
of type `NoProperShadowFit`. It rules out strict orthogonal-shadow containment
for every nonzero viewing direction, both proper rotations and every translation.
The [theorem map](THEOREM_MAP.md) expands the definitions and explains the relation
to the paper's straight-passage formulation.

The 1,146 count describes the **final assembly stage**, not the entire Lean
dependency closure. Of these, 1,144 were authenticated from completed earlier
compilations and two were compiled in the final native run. The dependency
audits examined 172,548 original and 172,546 packed imported files. Those are
file counts, not additional original roots or independent proofs.

The October snapshot's unfinished Lean status is superseded by this result.
The historical Python total of 29,673 geometric records includes controls,
other bodies and alternative branches. It is not the number of Phinopert roots.
Incomplete experiments for other bodies are not premises of this theorem.

Completion records establish what the retained run checked. They do not make
the small checkout a standalone proof package or replace a fresh verifier run.
See [verification and trust](VERIFICATION.md) and [reproduction](REPRODUCING.md).
