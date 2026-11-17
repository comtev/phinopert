# Reproducing Phinopert

## What this repository can check on its own

Python 3.10 or later, standard library only:

```bash
python3 scripts/check_release.py
python3 scripts/check_geometry.py
python3 scripts/check_evidence.py
python3 -B -m unittest discover -s tests -v
```

The release checker verifies the manifest and file hashes. The evidence checker
checks included completion records; the tests exercise failure guards. Neither
executes a new Lean proof. CI runs these same small checks.

Compare the manifest
or ZIP digest against a separately trusted copy before executing downloaded
code. Hashes do not authenticate the author and do not prove the theorem.

The geometry checker uses exact rational arithmetic in Q(sqrt(5)). It verifies
the frozen shape-record digest, distinct vertices, central symmetry, a
nonzero three-dimensional determinant, strict exposing normals and the
incidences of every listed supporting plane. It does not prove completeness
of the facet enumeration and is not a non-Rupertness checker.

The paper is a standalone LaTeX source with an embedded TikZ figure. With a
suitable TeX installation, run `pdflatex phinopert.tex` twice from `paper/`.
The checked PDF is included at [paper/phinopert.pdf](../paper/phinopert.pdf).
Alternatively, build using `tectonic --outdir paper paper/phinopert.tex` from
the repository root. The release PDF was rendered and visually checked on all
eight pages; its build had no LaTeX warnings or overflow reports. The geometry
figure and printable STL are available without compiling the paper.

## Full exact non-Rupertness replay

The historical replay package is separately retained as
`ico-union-review-v1-for-review.zip`, SHA-256
`b531aefeac102379ed42cc9d200de844ce9dfd4e8e76907421c36627f679c3c2`.
It contains 21 historical review archives and 187 frozen source files. It is
not a minimal candidate-only certificate and is **not included** here.
See [THIRD_PARTY.md](../THIRD_PARTY.md) for the outstanding distribution record.

Once that exact archive has been obtained through an authorised distribution,
follow its own README. In outline, from its extracted package folder:

```bash
python3 check_package.py verify
python3 check_package.py unpack --dest ../phinopert-review-workspace
```

The destination must not already exist. Inside the restored workspace, use its
pinned Python 3.12.14 and requirements, then run:

```bash
.venv/bin/python -m review_package.run --workers 4
```

This is a substantial resumable exact replay, not a search. Require both
`complete: true` and `candidate_certificate_chain_passed: true`, with 432/432
candidate roots and all 29,673 corpus records replayed. Geometry checks,
historical receipts and smoke tests alone cannot substitute for that replay.
Do not relax pinned requirements or edit old manifests to make checks pass.

## Lean source distribution

Read [lean/README.md](../lean/README.md) and [release assets](RELEASE_ASSETS.md).
The final theorem was completed in the retained research run. The separate
source asset contains its complete project import closure, a file manifest,
pinned Lean/mathlib configuration and the bounded replay script.

After checking the asset digest and extracting into a new directory:

```bash
cd phinopert-proof-sources-v2
python3 -B replay_lean.py verify
lake exe cache get
python3 -B replay_lean.py build --out ../phinopert-pilot --limit 3
```

The pilot is a requested checkpoint, **not** a full proof. For a full rebuild,
use a host with at least 600 GiB free working space and omit `--limit`:

```bash
python3 -B replay_lean.py build --out ../phinopert-full-replay
```

That conservative disk guard is not a measured portable-build requirement.
At the author's request, a full clean build is intentionally skipped for this
candidate; it has not been certified. Memory and total runtime
remain to be measured; the historical final-stage time of 3 h 38 min reused
previously checked proofs and is not a full-build estimate.

The script enforces one worker, locking, per-module time limits, disk reserve,
source/dependency identity and axiom-output checks. It runs stock Lean and does
not consume the research run's packed objects or axiom memo. Never disable
these guards to get past a failure. A stock-compiler resource failure is a
packaging/reproduction blocker, not evidence against the original completed
run and not permission to claim a new success.

Require `complete: true`, `passed: true`, all selected modules checked and 432
roots in the new summary. Retain the final axiom log, receipts and environment.
A stopped audit or partially built archive is not a completed replay.

## Rebuild the compact repository archive

After updating and reviewing the release inventory:

```bash
python3 -B scripts/package_release.py --out ../phinopert-repository.zip
```

This writes a deterministic ZIP and SHA-256 sidecar using only manifest-listed
files. It refuses to overwrite an existing archive. No `.git` directory,
private workspace data or local build cache is included. This archive is
separate from the much larger Lean source asset.
