(function renderDenseMatrixArtifact() {
  const data = window.POSTER_DATA || {};
  const run = data.run || {};
  const operations = Array.isArray(data.operation_summary) ? data.operation_summary : [];
  const mulRows = Array.isArray(data.mul_square_by_size) ? data.mul_square_by_size : [];
  const endpointRows = Array.isArray(data.endpoint_n_2048) ? data.endpoint_n_2048 : [];
  const bundle = data.bundle || {};

  const $ = (id) => document.getElementById(id);
  const setText = (id, value) => {
    const node = $(id);
    if (node) {
      node.textContent = value;
    }
  };
  const num = (value) => Number(value);
  const finite = (value) => Number.isFinite(num(value));
  const fmt = (value, digits = 2) => {
    const n = num(value);
    if (!Number.isFinite(n)) {
      return "--";
    }
    if (Math.abs(n) >= 1000) {
      return Math.round(n).toLocaleString("en-US");
    }
    if (Math.abs(n) >= 100) {
      return n.toFixed(0);
    }
    if (Math.abs(n) >= 10) {
      return n.toFixed(1);
    }
    return n.toFixed(digits);
  };
  const fmtInt = (value) => finite(value) ? Math.round(num(value)).toLocaleString("en-US") : "--";
  const fmtHours = (value) => finite(value) ? `${fmt(value, 2)} h` : "--";
  const fmtSpeedup = (value) => finite(value) ? `${num(value).toFixed(2)}x` : "--x";
  const escapeHtml = (value) => String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");

  const mulSummary = operations.find((row) => row.operation === "mul_square") || {};
  const mulEndpoint = endpointRows.find((row) => row.operation === "mul_square") || {};

  setText("metric-speedup", fmtSpeedup(mulSummary.median_speedup));
  setText("metric-records", fmtInt(run.record_count));
  setText("metric-samples", fmtInt(run.sample_count));
  setText("metric-max-n", finite(run.max_n) ? `n=${fmtInt(run.max_n)}` : "--");
  setText("metric-endpoint", `${fmtSpeedup(mulEndpoint.speedup_mathlib_over_dense)} at n=2048`);
  setText("fact-warmups", fmtInt(run.warmups));
  setText("fact-repeats", fmtInt(run.repeats));
  setText("fact-core", finite(run.core) ? `CPU ${fmtInt(run.core)}` : "--");
  setText("fact-hours", fmtHours(run.elapsed_hours));
  setText("fact-mismatches", fmtInt(run.checksum_mismatch_count));
  setText(
    "source-line",
    `${bundle.name || "densematrix-benchmark-bundle-20260605"} at ${String(bundle.git_rev || "").slice(0, 12)}`
  );

  renderRuntimeChart(mulRows);
  renderOperations(operations);
  renderEndpoint(endpointRows);

  function renderRuntimeChart(rows) {
    const host = $("runtime-chart");
    if (!host) {
      return;
    }
    const points = rows
      .filter((row) => finite(row.n) && finite(row.dense_median_s) && finite(row.mathlib_median_s))
      .sort((a, b) => num(a.n) - num(b.n));
    if (points.length === 0) {
      host.innerHTML = '<p class="body-copy">No multiplication rows were loaded.</p>';
      return;
    }

    const width = 980;
    const height = 360;
    const margin = { top: 26, right: 28, bottom: 52, left: 70 };
    const plotWidth = width - margin.left - margin.right;
    const plotHeight = height - margin.top - margin.bottom;
    const xMin = Math.log10(num(points[0].n));
    const xMax = Math.log10(num(points[points.length - 1].n));
    const values = points.flatMap((row) => [num(row.dense_median_s), num(row.mathlib_median_s)]);
    const yMin = Math.floor(Math.log10(Math.min(...values)));
    const yMax = Math.ceil(Math.log10(Math.max(...values)));
    const x = (n) => margin.left + ((Math.log10(num(n)) - xMin) / (xMax - xMin)) * plotWidth;
    const y = (s) => margin.top + plotHeight - ((Math.log10(num(s)) - yMin) / (yMax - yMin)) * plotHeight;
    const makePath = (key) => points
      .map((row, index) => `${index === 0 ? "M" : "L"} ${x(row.n).toFixed(2)} ${y(row[key]).toFixed(2)}`)
      .join(" ");
    const labels = [4, 16, 64, 256, 1024, 2048]
      .filter((label) => points.some((row) => num(row.n) === label))
      .map((label) => `<text x="${x(label)}" y="${height - 18}" text-anchor="middle">${label}</text>`)
      .join("");
    const grid = [];
    for (let exp = yMin; exp <= yMax; exp += 1) {
      const value = 10 ** exp;
      const yy = y(value);
      grid.push(`<line x1="${margin.left}" x2="${width - margin.right}" y1="${yy}" y2="${yy}" />`);
      grid.push(`<text x="${margin.left - 12}" y="${yy + 5}" text-anchor="end">${formatSeconds(value)}</text>`);
    }
    const denseCircles = points
      .map((row) => `<circle cx="${x(row.n)}" cy="${y(row.dense_median_s)}" r="5" />`)
      .join("");
    const mathlibCircles = points
      .map((row) => `<circle cx="${x(row.n)}" cy="${y(row.mathlib_median_s)}" r="5" />`)
      .join("");

    host.innerHTML = `<svg viewBox="0 0 ${width} ${height}" role="img" aria-label="DenseMatrix and mathlib Matrix square multiplication runtime">
      <g class="chart-grid">${grid.join("")}</g>
      <line class="axis" x1="${margin.left}" x2="${width - margin.right}" y1="${margin.top + plotHeight}" y2="${margin.top + plotHeight}" />
      <line class="axis" x1="${margin.left}" x2="${margin.left}" y1="${margin.top}" y2="${margin.top + plotHeight}" />
      <path class="series dense" d="${makePath("dense_median_s")}" />
      <path class="series mathlib" d="${makePath("mathlib_median_s")}" />
      <g class="points dense">${denseCircles}</g>
      <g class="points mathlib">${mathlibCircles}</g>
      <g class="x-labels">${labels}</g>
      <text class="axis-title" x="${margin.left}" y="18">median seconds</text>
      <text class="axis-title" x="${width - margin.right}" y="${height - 18}" text-anchor="end">n</text>
    </svg>
    <div class="legend">
      <span><i class="legend-dense"></i>DenseMatrix</span>
      <span><i class="legend-mathlib"></i>mathlib Matrix</span>
    </div>`;
  }

  function renderOperations(rows) {
    const host = $("operation-summary");
    if (!host) {
      return;
    }
    const visibleRows = rows
      .filter((row) => finite(row.median_speedup))
      .sort((a, b) => num(b.median_speedup) - num(a.median_speedup));
    if (visibleRows.length === 0) {
      host.innerHTML = '<p class="body-copy">No operation summary rows were loaded.</p>';
      return;
    }
    const max = Math.max(...visibleRows.map((row) => num(row.median_speedup)));
    host.innerHTML = visibleRows.map((row) => {
      const width = Math.max(4, (num(row.median_speedup) / max) * 100);
      return `<div class="bar-row">
        <div class="bar-label">${escapeHtml(labelOperation(row.operation))}</div>
        <div class="bar-track"><span style="width: ${width.toFixed(2)}%"></span></div>
        <strong>${fmtSpeedup(row.median_speedup)}</strong>
      </div>`;
    }).join("");
  }

  function renderEndpoint(rows) {
    const host = $("endpoint-table");
    if (!host) {
      return;
    }
    if (rows.length === 0) {
      host.innerHTML = '<p class="body-copy">No endpoint rows were loaded.</p>';
      return;
    }
    host.innerHTML = `<table>
      <thead>
        <tr>
          <th>Operation</th>
          <th>Dense median</th>
          <th>mathlib median</th>
          <th>Speedup</th>
          <th>Dense CV</th>
          <th>mathlib CV</th>
        </tr>
      </thead>
      <tbody>
        ${rows.map((row) => `<tr>
          <td>${escapeHtml(labelOperation(row.operation))}</td>
          <td>${formatMs(row.dense_median_ms)}</td>
          <td>${formatMs(row.mathlib_median_ms)}</td>
          <td>${fmtSpeedup(row.speedup_mathlib_over_dense)}</td>
          <td>${fmt(row.dense_cv, 4)}</td>
          <td>${fmt(row.mathlib_cv, 4)}</td>
        </tr>`).join("")}
      </tbody>
    </table>`;
  }

  function labelOperation(operation) {
    return {
      construct: "construct",
      get: "get",
      add: "add",
      smul: "scalar multiply",
      transpose: "transpose",
      mul_square: "square multiply",
      ofMatrix: "ofMatrix",
      toMatrix: "toMatrix",
    }[operation] || operation;
  }

  function formatMs(value) {
    const n = num(value);
    if (!Number.isFinite(n)) {
      return "--";
    }
    if (n >= 1000) {
      return `${fmt(n / 1000, 2)} s`;
    }
    return `${fmt(n, 2)} ms`;
  }

  function formatSeconds(value) {
    if (value < 0.001) {
      return `${fmt(value * 1000000, 0)} us`;
    }
    if (value < 1) {
      return `${fmt(value * 1000, 0)} ms`;
    }
    return `${fmt(value, 0)} s`;
  }
})();
