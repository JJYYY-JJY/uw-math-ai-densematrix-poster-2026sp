# DenseMatrix Spring 2026 Poster Artifact

This repository is the public export for the UW Math AI Lab Spring 2026
DenseMatrix poster. It contains the poster PDF, static web pages, a compact
site-data JSON file, and the full extracted benchmark bundle from
`densematrix-benchmark-bundle-20260605.zip`.

## Data Scope

- Bundle: `densematrix-benchmark-bundle-20260605/`
- Bundle input SHA256: `f731578bbaaddc45fae5d9beb534789070beb9ec14a403a984aee62c88488ad1`
- Poster PDF SHA256: `ab80f850be67aedaab7e8c3863d1662c1ba90479216f3979590d43172a0c5b35`
- Benchmark git revision: `b8ddab453721eac7f4cc3b761ce6b79e0d37e1ac`
- Records: 266
- Measured samples: 13,300
- Paired checksum mismatches: 0
- Largest size: n=2048
- Elapsed wall-clock time: 30.85 hours
- Main multiplication result: 20.93x median speedup, 19.17x at n=2048

Speedup is `mathlib Matrix median runtime / DenseMatrix median runtime`.
Values above 1 mean DenseMatrix is faster.

## Reproduce

From the repository root:

```bash
./densematrix-benchmark-bundle-20260605/scripts/reproduce_quick_smoke.sh
```

For the full benchmark profile:

```bash
./densematrix-benchmark-bundle-20260605/scripts/reproduce_full_48h.sh
```

Both scripts default to the bundled runnable source snapshot at
`densematrix-benchmark-bundle-20260605/repo/`. You can pass another checkout
path as the first argument.

The full run uses:

- sizes: `4,8,16,24,32,48,64,80,96,128,160,192,256,384,512,768,1024,1536,2048`
- warmups: 10
- repeats: 50
- pinned CPU core: 3
- output: `bench-results/densematrix-48h-reproduced`

Lake may need to download and build dependencies because `.lake` artifacts and
mathlib source are not vendored in the bundle.

## Files

- `index.html`: public poster and benchmark overview page.
- `artifact.html`: public artifact file index.
- `densematrix-poster-2026sp.pdf`: poster PDF.
- `data/poster-data.json`: compact JSON used by the web page.
- `data/poster-data.js`: browser wrapper for the same JSON data.
- `densematrix-benchmark-bundle-20260605/`: full extracted benchmark bundle.
- `SHA256SUMS`: integrity hashes for tracked files in this export.
