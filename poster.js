(function renderPoster() {
  const data = window.POSTER_DATA || {};
  const scaling = Array.isArray(data.multiplication_scaling) ? data.multiplication_scaling : [];
  const tradeoffs = Array.isArray(data.pointwise_tradeoffs) ? data.pointwise_tradeoffs : [];
  const algorithms = Array.isArray(data.algorithms) ? data.algorithms : [];

  const $ = (id) => document.getElementById(id);
  const fmt = (value, digits = 2) => {
    const number = Number(value);
    if (!Number.isFinite(number)) {
      return "--";
    }
    if (number >= 100) {
      return number.toFixed(0);
    }
    if (number > 0 && number < 0.01) {
      return "<0.01";
    }
    if (number >= 10) {
      return number.toFixed(1);
    }
    return number.toFixed(digits);
  };

  const status = $("data-status");
  if (status) {
    status.classList.toggle("strict", data.strict === true);
    status.classList.toggle("sample", data.strict !== true);
    status.textContent = data.strict ? "Strict data" : "Sample data";
  }

  $("metric-records").textContent = data.record_count ?? "--";
  $("metric-materialized").textContent = data.materialized_record_count ?? "--";
  $("metric-max-size").textContent = data.max_rows ? `n=${data.max_rows}` : "--";

  const sourceLine = $("source-line");
  if (sourceLine) {
    const strictNote = data.strict
      ? "strict poster gate passed"
      : "not a strict poster run";
    sourceLine.textContent = `Data source: ${data.source || "none"} · ${data.profile || "unknown"} · ${strictNote}`;
  }

  const speedups = scaling.map((row) => Number(row.speedup)).filter(Number.isFinite);
  const speedupRange = $("speedup-range");
  if (speedupRange) {
    const min = Math.min(...speedups);
    const max = Math.max(...speedups);
    speedupRange.textContent = speedups.length ? `${fmt(min, 1)}-${fmt(max, 1)}x` : "--x";
  }

  renderMultiplicationChart(scaling);
  renderTradeoffs(tradeoffs);
  renderAlgorithms(algorithms);

  function renderMultiplicationChart(rows) {
    const host = $("comparison-chart");
    if (!host) {
      return;
    }
    if (rows.length === 0) {
      host.innerHTML = '<div class="empty-chart">Run the benchmark suite to render multiplication scaling.</div>';
      return;
    }

    const width = 960;
    const height = 405;
    const margin = { top: 26, right: 42, bottom: 74, left: 88 };
    const plotWidth = width - margin.left - margin.right;
    const plotHeight = height - margin.top - margin.bottom;
    const sizes = [...new Set(rows.map((row) => Number(row.rows)))].sort((a, b) => a - b);
    const series = [
      { op: "mul_square", key: "dense_ms", label: "Square DenseMatrix", color: "#04844B", dash: "" },
      { op: "mul_square", key: "materialized_ms", label: "Square Matrix→Dense", color: "#4B2E83", dash: "8 6" },
      { op: "mul_rect", key: "dense_ms", label: "Rect DenseMatrix", color: "#00A1E0", dash: "" },
      { op: "mul_rect", key: "materialized_ms", label: "Rect Matrix→Dense", color: "#FF9A3C", dash: "8 6" },
    ];
    const values = rows.flatMap((row) => [Number(row.dense_ms), Number(row.materialized_ms)])
      .filter((value) => Number.isFinite(value) && value > 0);
    const minLog = Math.floor(Math.log10(Math.min(...values)));
    const maxLog = Math.ceil(Math.log10(Math.max(...values)));
    const x = (size) => {
      if (sizes.length === 1) {
        return margin.left + plotWidth / 2;
      }
      const index = sizes.indexOf(Number(size));
      return margin.left + (index / (sizes.length - 1)) * plotWidth;
    };
    const y = (value) => {
      const log = Math.log10(Math.max(Number(value), 1e-9));
      return margin.top + plotHeight - ((log - minLog) / (maxLog - minLog)) * plotHeight;
    };
    const yTicks = [];
    for (let tick = minLog; tick <= maxLog; tick += 1) {
      yTicks.push(10 ** tick);
    }
    const grid = yTicks.map((tick) => {
      const yy = y(tick);
      return `<line x1="${margin.left}" y1="${yy}" x2="${width - margin.right}" y2="${yy}" stroke="#D8DDE6" stroke-width="1" />
        <text x="${margin.left - 12}" y="${yy + 5}" text-anchor="end" font-size="13" font-weight="800" fill="#706E6B">${formatAxis(tick)}</text>`;
    }).join("");
    const xLabels = sizes.map((size) => `<text x="${x(size)}" y="${height - 22}" text-anchor="middle" font-size="16" font-weight="800" fill="#032D60">${size}</text>`)
      .join("");
    const paths = series.map((spec) => {
      const points = sizes.map((size) => {
        const row = rows.find((item) => item.operation === spec.op && Number(item.rows) === size);
        if (!row) {
          return null;
        }
        return { x: x(size), y: y(row[spec.key]), value: Number(row[spec.key]) };
      }).filter(Boolean);
      const d = points.map((point, index) => `${index === 0 ? "M" : "L"} ${point.x.toFixed(2)} ${point.y.toFixed(2)}`).join(" ");
      const circles = points.map((point) => `<circle cx="${point.x}" cy="${point.y}" r="5" fill="${spec.color}" stroke="#FFFFFF" stroke-width="2" />`).join("");
      return `<path d="${d}" fill="none" stroke="${spec.color}" stroke-width="4" stroke-linecap="round" stroke-linejoin="round" stroke-dasharray="${spec.dash}" />
        ${circles}`;
    }).join("");

    host.innerHTML = `<svg viewBox="0 0 ${width} ${height}" role="img" aria-label="DenseMatrix benchmark comparison chart">
      <rect x="0" y="0" width="${width}" height="${height}" fill="#FBFCFE" />
      ${grid}
      <line x1="${margin.left}" y1="${margin.top + plotHeight}" x2="${width - margin.right}" y2="${margin.top + plotHeight}" stroke="#D8DDE6" stroke-width="2" />
      <line x1="${margin.left}" y1="${margin.top}" x2="${margin.left}" y2="${margin.top + plotHeight}" stroke="#D8DDE6" stroke-width="2" />
      <text x="22" y="34" font-size="15" font-weight="800" fill="#706E6B">median ms</text>
      <text x="${width - 42}" y="34" text-anchor="end" font-size="15" font-weight="800" fill="#706E6B">rows</text>
      ${paths}
      ${xLabels}
    </svg>`;
  }

  function renderTradeoffs(rows) {
    const host = $("tradeoff-table");
    if (!host) {
      return;
    }
    if (rows.length === 0) {
      host.innerHTML = '<p>No pointwise tradeoff rows in this loaded bundle.</p>';
      return;
    }
    host.innerHTML = [
      '<div class="tradeoff-row"><span>operation</span><span>Dense</span><span>Matrix</span><span>Matrix→Dense</span><span>winner</span></div>',
      ...rows.map((row) => {
        const dense = Number(row.dense_ms);
        const matrix = Number(row.matrix_ms);
        const materialized = Number(row.materialized_ms);
        const min = Math.min(dense, matrix, materialized);
        const winner = min === dense ? "Dense" : min === matrix ? "Matrix" : "M→D";
        return `<div class="tradeoff-row">
          <strong>${escapeXml(row.label)}</strong>
          <span>${fmt(dense, 2)}</span>
          <span>${fmt(matrix, 2)}</span>
          <span>${fmt(materialized, 2)}</span>
          <span>${winner}</span>
        </div>`;
      }),
    ].join("");
  }

  function renderAlgorithms(rows) {
    const host = $("algorithm-table");
    if (!host) {
      return;
    }
    if (rows.length === 0) {
      host.innerHTML = '<p>No high-level Rat algorithm rows in this loaded bundle.</p>';
      return;
    }
    host.innerHTML = rows
      .map((row) => `<div class="algorithm-row">
        <strong>${escapeXml(row.operation)}</strong>
        <span>n=${escapeXml(String(row.rows))}</span>
        <span>${fmt(row.median_ms, 2)} ms</span>
      </div>`)
      .join("");
  }

  function escapeXml(value) {
    return String(value)
      .replaceAll("&", "&amp;")
      .replaceAll("<", "&lt;")
      .replaceAll(">", "&gt;")
      .replaceAll('"', "&quot;");
  }

  function formatAxis(value) {
    if (value >= 1000) {
      return `${value / 1000}k`;
    }
    return String(value);
  }
})();
