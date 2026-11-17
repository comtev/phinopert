# Reviewing and contributing

Start with the [theorem map](docs/THEOREM_MAP.md) and
[reproduction guide](docs/REPRODUCING.md). Report whether an observation concerns
the mathematical statement, a proof, a dependency, the packaging or the exposition.
Include the repository revision, source-asset digest and relevant command/log.

Run the documented small checks for repository changes. They do not replace a
full Lean replay. Changes to mathematical definitions, generated certificates,
compiler settings or proof tooling require renewed proof and axiom checks.
Keep historical evidence immutable and put new run evidence under a new name.

Do not add generated build objects, toolchains, private paths, credentials or
large experimental archives to Git. Preserve the original attribution and the
applicable MIT/CC BY 4.0 or third-party terms. A successful CI badge describes
only its listed checks and should never be labelled a full proof replay.
