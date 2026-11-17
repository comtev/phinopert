# Release assets

This is an **unpublished release candidate**. Exact asset identities are in
[`release-assets.json`](../release-assets.json). A missing download URL means
that no public deposit is being claimed.

| Material | Contents | Distribution |
| --- | --- | --- |
| Compact repository | Paper PDF/TeX, exact geometry, model, core Lean sources, theorem map, final audit evidence, small checks | Git and deterministic repository ZIP |
| `phinopert-proof-sources-v2.tar.gz` | Complete project source import closure; 169,583 Lean modules, pinned Lake files, inventory and bounded replay driver | Separate large asset; prepared privately |
| Historical Python review archive | Original full certificate lineage and Python replay | Separately retained; not part of this release candidate |

## Lean source asset

- Archive size: **456,546,752 bytes** (456.5 MB; about 435.4 MiB).
- Project Lean source size: **5,869,302,374 bytes** (5.87 GB), before tar overhead
  and the source manifest. Allow at least 7 GB for extraction.
- Project modules: **169,583**, selected by following imports from the final theorem.
- SHA-256:

```text
c6e59cb1c1962f3c3cdaf52572ddb8cc3014465020915dec213d684e81e9ccc4
```

The archive contains original source bytes, project-relative provenance, all
project imports, a topological build order, pinned Lean 4.19.0/mathlib dependencies,
licences, instructions and a guarded stock-Lean replay script. The small Git
checkout intentionally retains only the browsable core and final declarations.

No project compiled objects, packed import copies, axiom memo, toolchain,
third-party source tree or historical Python archive is bundled. Dependencies
are downloaded separately using the supplied lock. This is a complete **project
source** archive, not a fully offline compiler-and-dependencies appliance.

The source-selection and packaging checks do not repeat the original kernel
audit. See `verification/distribution-checks.json` for exactly which new
checks have run. A clean full replay is intentionally skipped for this candidate at the
author's request. It would be required before claiming that the portable
distribution has been independently reproduced.

## Working resources

A compressed source download is much smaller than a proof build. The retained objects selected by this project import closure total
484,592,204,880 bytes (451.3 GiB), before toolchain and other dependencies.
Retaining both original and packed research copies used roughly 1 TB. The portable driver conservatively requires 600 GiB
free for a full fresh replay and preserves an 8 GiB reserve. This is a guard,
not a measured minimal requirement. Memory and full clean-build duration
remain to be measured. A small requested checkpoint needs less disk and must
not be reported as a completed replay.

## Depositing a release

The proof-source archive is a **GitHub Release asset**, separate from the Git
tree. Its filename, size and SHA-256 are committed in `release-assets.json`.
The local `dist/` directory stages files for upload and is intentionally ignored
by Git: committing the 456.5 MB binary would exceed GitHub's ordinary file limit.

Prepare both repository and proof-source artifacts with:

```bash
python3 -B scripts/package_release.py \
  --out dist/phinopert-repository.zip \
  --proof-source dist/phinopert-proof-sources-v2.tar.gz
```

Supply an existing copy of the source archive for `--proof-source`. The command
checks its size and SHA-256 against committed metadata, stages it alongside the
repository ZIP and writes checksum sidecars. It refuses to replace different
existing files. The archive is not nested inside the repository ZIP.

Attach these four files to the repository's draft GitHub Release:

- `phinopert-proof-sources-v2.tar.gz`
- `phinopert-proof-sources-v2.tar.gz.sha256`
- `phinopert-repository.zip`
- `phinopert-repository.zip.sha256`

Upload through the GitHub release editor, or use `gh release upload` after
authenticating GitHub CLI. Do not use `--clobber`: a changed asset needs a new
version. An upload has not happened until GitHub returns an asset record; local
staging alone does not provide a download URL. Draft assets remain restricted
according to GitHub's draft-release permissions.

Deposit the reviewed repository ZIP, source archive and checksum sidecars
under a durable versioned record.
Update the asset URL and citation DOI only after the deposit exists. The
manifest-based ZIP builder excludes local caches and unpublished workspace data.
Use [the release checklist](RELEASE_CHECKLIST.md) before tagging or publishing.
