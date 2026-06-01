# DenseMatrix Spring 2026 Poster Artifact

This directory is the public export for the UW Math AI Lab Spring 2026
DenseMatrix poster. It contains static HTML, redacted summary data, assets, and
the exported PDF.

## Data Scope

- Data status: strict poster data
- Profiles: poster, stress
- Records: 2247
- Materialized records: 328
- Max rows: 2048
- Benchmark source archive: densematrix-suite-20260601T133240Z-890971a.tar.gz
- Benchmark source archive SHA256: 34bedc1bbf042d350054527f3d490b3d8f7e81585355e702c3867c2c2865cf24

The raw benchmark suite archive is intentionally not included here because it
contains private-repository context such as git patches and machine environment
captures.

## Reproduce From Private Source

```bash
scripts/verify_densematrix_suite.sh bench-results/2026sp/densematrix-suite-20260601T133240Z-890971a.tar.gz
scripts/build_densematrix_poster_data.mjs --input bench-results/2026sp/densematrix-suite-20260601T133240Z-890971a.tar.gz
scripts/export_densematrix_poster_pdf.sh
scripts/export_densematrix_public_artifact.mjs --suite bench-results/2026sp/densematrix-suite-20260601T133240Z-890971a.tar.gz
```

## Files

- `index.html`: static poster page.
- `densematrix-poster-2026sp.pdf`: exported 16:9 PDF.
- `data/poster-data.json`: redacted summary data used by the poster.
- `data/poster-data.js`: browser-ready wrapper for the same data.
- `SHA256SUMS`: integrity hashes for this public export.
