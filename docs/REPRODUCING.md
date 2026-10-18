# Reproducing Phinopert

## What this repository can check on its own

Python 3.10 or later, standard library only:

```bash
python3 scripts/check_release.py
python3 scripts/check_geometry.py
```

The release checker verifies the manifest and file hashes. Compare the manifest
or ZIP digest against a separately trusted copy before executing downloaded
code. Hashes do not authenticate the author and do not prove the theorem.

The geometry checker uses exact rational arithmetic in Q(sqrt(5)). It verifies
the frozen shape-record digest, distinct vertices, central symmetry, a
nonzero three-dimensional determinant, strict exposing normals and the
incidences of every listed supporting plane. It does not prove completeness
of the facet enumeration and is not a non-Rupertness checker.

The paper is a standalone LaTeX source with an embedded TikZ figure. With a
suitable TeX installation, run `pdflatex phinopert.tex` twice from `paper/`.
No exported PDF is included in this snapshot. The geometry figure and printable
STL are available without compiling the paper.

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

## Lean

Read [lean/README.md](../lean/README.md). The source snapshot does not contain
the entire generated leaf corpus, cached dependencies or a portable full-proof
build. Its presence is not a proof of the final non-Rupert theorem.
