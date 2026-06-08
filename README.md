# DenseMatrix Poster, UW 2026 Spring

Public artifact repository for the UW Math AI Lab Spring 2026 DenseMatrix
poster.

## Contents

- `densematrix-poster-2026sp.pdf`: poster PDF.
- `index.html`: poster and benchmark overview page.
- `artifact.html`: public artifact file index.
- `densematrix-benchmark-bundle-20260605/`: complete extracted benchmark bundle.
- `data/poster-data.json`: compact web data derived from the bundle.
- `REPRODUCE.md`: smoke and full reproduction commands.
- `SHA256SUMS`: integrity hashes for tracked artifact files.

## Benchmark Snapshot

- Records: 266
- Measured samples: 13,300
- Paired checksum mismatches: 0
- Max size: n=2048
- Full run time: 30.85 hours
- Main claim: DenseMatrix has 20.93x median square-multiplication speedup over
  mathlib Matrix in this benchmark, with 19.17x speedup at n=2048.

See `densematrix-benchmark-bundle-20260605/README.md` for the benchmark bundle
and `REPRODUCE.md` for reproduction commands.
