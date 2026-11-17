# Formal verification report

## Result and evidence

The retained run `phinopert-global-final-v129` finished on 16 November 2026 at
11:30:40 UTC. Its [summary](../verification/v129/summary.json) and
[final audit](../verification/v129/final-audit.json) report completion and success:

| Measure | Recorded result |
| --- | ---: |
| Final assembly modules | 1,146 / 1,146 |
| Authenticated completed prefix | 1,144 |
| Final native kernel compilations | 2 |
| Original roots excluded | 432 / 432 |
| Original imported files audited | 172,548 |
| Packed imported files audited | 172,546 |
| Final run elapsed time | 13,092.63 seconds (about 3 h 38 min) |

The final run duration is not a clean-build estimate: it reused a large
authenticated proof corpus. Module counts from different stages must not be
added to infer a completion percentage.

The final declaration has type `NoProperShadowFit`, with no certificate
hypothesis. Its retained [axiom log](../verification/v129/ActualPhinopertNoProperShadowFit.log)
reports exactly `propext`, `Classical.choice` and `Quot.sound`. There is no
`sorryAx` or extra problem-specific axiom in that reported dependency set.

Final-audit SHA-256:

```text
3bded0dcd6bb6eb7099f96aee5b5faf7bd3516be210b1e90337f20bd8166cf20
```

The two final sources and their small logs are included unchanged. Receipt
extracts explicitly identify the fields retained; they are not represented
as the original full receipts. `scripts/check_evidence.py` checks the included
record relationships. It does **not** reconstruct the full historical audit.

## What the original audits checked

- **Statements and coverage:** actual geometric root exclusions, exact root
  identities and attachments, all 432 roots and the global no-fit statement.
- **Compilation and axioms:** successful kernel compilation; dependency
  traversal admitting only the three axioms named above; retained compiler
  outputs, source/object/log hashes and receipt bindings.
- **Upstream dependencies:** pinned sources, original compiled artifacts and
  completed earlier receipts were reauthenticated before and after the final
  assembly. Successful generation alone was not accepted as a proof.
- **Packed imports:** the original and compacted import files were checked
  before and after use, preserving proof/type payloads. Metadata normalization
  had a kernel-checked justification and negative controls.
- **Axiom traversal cache:** only authenticated, previously audited upstream
  theorems were eligible. Current-stage declarations and definitions were not
  accepted through that cache. The original certificates were reconstructed
  against the imported artifact registry before and after use.
- **Failure controls:** false-proof and forbidden-axiom examples, changed
  inputs and malformed cache entries were checked by the retained controls.
  Guard failures stopped work rather than being reclassified as proofs.
- **Operational guards:** one Lean worker, advisory locks, a 1,200-second
  module cap including imports and axiom traversal, bounded audit children,
  a controller deadline and an 8 GiB disk reserve.

The final before/after server-audit hashes agree. See the final-audit JSON for
the exact compiler, packing, import inventory and audit digests.

## Trust boundary and reproduction

The mathematical trust includes Lean's kernel and foundational axioms, its
implementation/toolchain and the hardware executing it. The historical audit
also relies on the correctness of the import normalization, provenance and
axiom-traversal tooling described above. Hashes bind bytes; they do not by
themselves prove a mathematical statement or authenticate an author.

The compact checkout contains evidence of the completed run. A third party
should rebuild the supplied source closure in a fresh pinned environment,
then audit the final theorem's dependencies. That portable rebuild must pass
before advertising the release as independently reproduced. The packaging
checks and CI are deliberately labelled separately from a full proof replay.

The earlier Python certificate replay is another verification layer. It shares
arithmetic libraries within that implementation and is not an independent
formal kernel. Neither it nor assistant-generated checks constitute external
human peer review. [The theorem map](THEOREM_MAP.md) identifies the remaining
human statement-correspondence review.
