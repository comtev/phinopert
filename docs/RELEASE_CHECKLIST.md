# Release preparation

The research proof is complete. Preparing a portable, independently runnable
release is a separate task. This checklist does not authorize publication.

## Included in the candidate

- [x] Exact body data, printable mesh and figures.
- [x] Core Lean sources and the exact final declaration.
- [x] Updated proof status and retained final-audit evidence.
- [x] Paper-to-Lean theorem map and explicit trust boundaries.
- [x] Updated manuscript source; PDF build and visual check documented with the candidate.
- [x] MIT for original software; CC BY 4.0 for original research material.
- [x] Citation metadata without invented DOI or arXiv identifiers.
- [x] Small integrity/geometry/evidence checks and CI configuration.
- [x] Manifest-based repository archive builder and bounded source-replay tooling.

## Additional review and optional independent reproduction

- [ ] Full clean build of the portable source archive, using the pinned environment (intentionally skipped for this candidate at the author's request).
- [ ] Final theorem and axiom audit from that clean build; archive its logs and environment.
- [ ] Human review of the exact body and statement correspondence in `THEOREM_MAP.md`.
- [ ] External mathematical/software scrutiny; record its scope without implying endorsement.

The candidate can be released with this limitation stated explicitly. It must
not be described as a fully reproduced portable distribution. The original
completed research verification remains the proof evidence.

The full rebuild needs substantial disk space; the recorded final-stage runtime
is not a clean-rebuild estimate. A requested pilot checkpoint is not a completed
proof replay. Keep the historical proof evidence and new distribution checks separate.

## Publication steps requiring the author's final review

1. Review the final PDF, source archive inventory, licensing, attribution and metadata.
2. Choose a release version and approve the exact commit and asset digests.
3. Upload the large source asset to a durable archive; add its verified download
   URL to `release-assets.json`. Keep generated bulk data out of Git history.
4. Tag the reviewed commit and publish release notes linking the paper and assets.
5. Archive that version and its assets with a DOI provider; update `CITATION.cff`
   only after an identifier is assigned. An arXiv submission is a separate action.

The familiar pattern is a readable repository, a paper, precise formal targets,
pinned build instructions, checks, and versioned citable artifacts. See the
[PFR formalisation](https://github.com/teorth/pfr) for an example and
[GitHub's citation/archive guidance](https://docs.github.com/en/repositories/archiving-a-github-repository/referencing-and-citing-content).
A full interactive blueprint is optional; the theorem map serves as the compact
entry point here.

The historical Python review archive is not bundled in the Lean source asset.
If it is distributed later, resolve the exact upstream licence/permission
record identified in [THIRD_PARTY.md](../THIRD_PARTY.md). No source archive,
toolchain, original output or backup should be deleted to make a release fit.
