# Attribution and third-party material

## Prior mathematical work

Steininger and Yurkevich established algorithmic foundations and the
Noperthedron counterexample. Bence Hervay's rhombicosidodecahedron work supplies
an important symmetry-reduction and exact-certificate precedent. Subsequent
work by Oscar Smith, Gihyo Jung and Tom Murphy VII is acknowledged in the paper.
The particular Phinopert construction and its body-specific certificates should
not be presented as new general principles of symmetry or support separation.

## Historical replay dependency

The frozen full-chain replay uses Hervay's
[`audit/model.py`](https://github.com/bence-hervay/nopert-rid/blob/802a3ded09535c4a99cef1371ce0d0277c433fa8/audit/model.py)
at revision `802a3ded09535c4a99cef1371ce0d0277c433fa8`, SHA-256
`4ac089da8ad99be0b3d8962886328a30da1454a01fe45ac1b253e4dd452cae6a`.
It also contains upstream README text and archived copies of the model.

**Those files and the nested historical archives are not shipped in this
repository snapshot.** Before distributing the full archive, retain an
applicable licence or permission record covering those exact files and add
the required notices. The older review located MIT declarations for upstream
Rust packages and CC BY 4.0 for the deposited paper, but did not establish the
scope for the separate Python model and root README. This is a release-record
gap, not an assertion that reuse is prohibited.

The owner's choice of MIT and CC BY 4.0 for original contributions does not
relicense upstream files. This snapshot therefore does not imply that the
full historical replay is already publicly redistributable or self-contained.

## External dependencies

Lean, mathlib and Python dependencies are obtained separately under their own
licences. No compiler, mathlib checkout, virtual environment, external paper
PDF or third-party source repository is vendored here. Mathematical data and
formal proofs derived from cited constructions retain the relevant scholarly
attribution; the project does not claim authorship of those constructions.
