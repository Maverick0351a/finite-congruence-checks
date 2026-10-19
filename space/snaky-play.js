(function () {
  "use strict";
  const pointKey = cell => cell.join(",");
  const pointText = cell => `(${cell[0]}, ${cell[1]})`;

  function viewOf(data, index) {
    if (!Number.isInteger(index) || index < 0 || index >= data.play.steps.length) throw new Error("Unknown move");
    const step = data.play.steps[index];
    const next = data.play.steps[index + 1];
    const envelope = next ? next.active.envelope : [];
    return {step, envelope, winner: step.witness ? step.witness.cells : [],
      makerTurns: new Map(data.play.steps.slice(0, index + 1).map(s => [pointKey(s.maker.cell), s.move])),
      breakerTurns: new Map(data.play.steps.slice(0, index + 1).filter(s => s.breaker).map(s => [pointKey(s.breaker.cell), s.move]))};
  }

  if (typeof module !== "undefined" && module.exports) module.exports = {pointKey, pointText, viewOf};
  if (typeof document === "undefined") return;
  const el = id => document.getElementById(id);
  const node = (tag, text, className) => {
    const result = document.createElement(tag);
    if (text !== undefined) result.textContent = text;
    if (className) result.className = className;
    return result;
  };
  const svgNode = (tag, attrs, text) => {
    const result = document.createElementNS("http://www.w3.org/2000/svg", tag);
    for (const [key, value] of Object.entries(attrs)) result.setAttribute(key, String(value));
    if (text !== undefined) result.textContent = text;
    return result;
  };

  function drawBoard(data, view) {
    const svg = svgNode("svg", {viewBox: "0 0 468 472", role: "img", "aria-labelledby": "snaky-board-title snaky-board-desc"});
    svg.append(svgNode("title", {id: "snaky-board-title"}, `Board after Maker move ${view.step.move}`));
    svg.append(svgNode("desc", {id: "snaky-board-desc"}, `${view.step.maker_after.length} Maker cells and ${view.step.breaker_after.length} Breaker cells. ${view.step.won ? "Maker owns a complete Snaky." : "The outlined continuation envelope remains free of Breaker cells."} The complete coordinates are available in the move list and download.`));
    const board = new Set(data.play.board.cells.map(pointKey));
    const envelope = new Set(view.envelope.map(pointKey));
    const winner = new Set(view.winner.map(pointKey));
    for (let y = 0; y <= 16; y++) for (let x = 0; x <= 16; x++) {
      const key = pointKey([x, y]), px = 28 + 25 * x, py = 12 + 25 * (16 - y);
      const classes = ["snaky-grid-cell", board.has(key) ? "on-board" : "", envelope.has(key) ? "in-envelope" : "", winner.has(key) ? "winning" : ""].filter(Boolean).join(" ");
      const cell = svgNode("rect", {x: px, y: py, width: 23, height: 23, rx: 2, class: classes});
      cell.append(svgNode("title", {}, `${pointText([x, y])}: ${view.makerTurns.has(key) ? "Maker, move " + view.makerTurns.get(key) : view.breakerTurns.has(key) ? "Breaker, reply " + view.breakerTurns.get(key) : board.has(key) ? "free" : "outside board"}`));
      svg.append(cell);
      if (view.makerTurns.has(key)) {
        svg.append(svgNode("circle", {cx: px + 8, cy: py + 9, r: 5, class: "snaky-maker"}));
        svg.append(svgNode("text", {x: px + 14, y: py + 19, class: "snaky-turn-label"}, view.makerTurns.get(key)));
      } else if (view.breakerTurns.has(key)) {
        svg.append(svgNode("path", {d: `M${px+4},${py+4} l9,9 m-9,0 l9,-9`, class: "snaky-breaker"}));
        svg.append(svgNode("text", {x: px + 14, y: py + 19, class: "snaky-turn-label"}, view.breakerTurns.get(key)));
      }
    }
    for (let value = 0; value <= 16; value++) {
      svg.append(svgNode("text", {x: 39.5 + 25 * value, y: 451, "text-anchor": "middle", class: "snaky-board-axis"}, value));
      svg.append(svgNode("text", {x: 17, y: 28 + 25 * (16 - value), "text-anchor": "end", class: "snaky-board-axis"}, value));
    }
    svg.append(svgNode("text", {x: 452, y: 466, class: "snaky-board-axis"}, "x"));
    svg.append(svgNode("text", {x: 3, y: 10, class: "snaky-board-axis"}, "y"));
    el("snaky-board").replaceChildren(svg);
  }

  function render(data, index) {
    const view = viewOf(data, index), step = view.step;
    el("snaky-step").value = String(index);
    el("snaky-prev").disabled = index === 0;
    el("snaky-next").disabled = index === data.play.steps.length - 1;
    drawBoard(data, view);
    el("snaky-card-label").textContent = `CARD ${step.active.card}${step.active.inline_path.length ? " · INLINE PATH " + step.active.inline_path.join(" → ") : ""}`;
    el("snaky-move-title").textContent = step.won ? "The six-square shape is complete." : `Maker claims ${pointText(step.maker.cell)}.`;
    const explanation = [node("p", `Move ${step.move}: Maker takes the fresh cell ${pointText(step.maker.cell)}. ${step.maker.kind === "replacement" ? "The prescribed pivot is already owned, so this replacement still consumes one claim." : step.maker.kind === "base_completion" ? "This completes the base card's target." : "This is the selected card's pivot."}`)];
    explanation.push(node("p", step.breaker ? `Breaker then claims ${pointText(step.breaker.cell)}. The next card's envelope avoids this reply and all earlier Breaker cells.` : "Maker has won, so no Breaker reply is required."));
    el("snaky-move-text").replaceChildren(...explanation);
    const rows = [["Actual Maker claims used", step.move], ["Remaining from 21-claim allowance", step.global_budget_after], ["Active card bound before this move", step.active.height], ["Next card bound", step.continuation ? step.continuation.height : "Won"]];
    el("snaky-budget").replaceChildren(...rows.flatMap(([label, value]) => [node("dt", label), node("dd", String(value))]));
    const detail = step.won ? `Winning cells: ${step.witness.cells.map(pointText).join(", ")}.` : `Continue with ${step.continuation.kind === "inline" ? "the nested combination" : "card " + step.continuation.card}. Its required cells are owned by Maker and its envelope is free of Breaker cells.`;
    el("snaky-continuation").replaceChildren(node("p", detail, step.won ? "notice" : ""));
    el("snaky-card-source").href = step.active.certificate_ref.url;
  }

  function start(data) {
    if (!data || data.schema_version !== 1 || !data.play || !Array.isArray(data.play.steps)) throw new Error("The checked presentation data is unavailable.");
    const select = el("snaky-step");
    data.play.steps.forEach((step, index) => {
      const option = node("option", `${step.move} · Maker ${pointText(step.maker.cell)}${step.won ? " · Win" : ""}`);
      option.value = String(index); select.append(option);
    });
    select.addEventListener("change", () => render(data, Number(select.value)));
    el("snaky-prev").addEventListener("click", () => render(data, Number(select.value) - 1));
    el("snaky-next").addEventListener("click", () => render(data, Number(select.value) + 1));
    const table = node("table"), caption = node("caption", "All chosen moves in this illustrative play");
    const head = node("thead"), tr = node("tr");
    ["Move", "Maker cell", "Breaker reply", "Card bound before move", "Continuation bound"].forEach(label => { const th = node("th", label); th.scope = "col"; tr.append(th); });
    head.append(tr); table.append(caption, head);
    const body = node("tbody");
    data.play.steps.forEach(step => {const row = node("tr"); [step.move, pointText(step.maker.cell), step.breaker ? pointText(step.breaker.cell) : "Game won", step.active.height, step.continuation ? step.continuation.height : "Won"].forEach(value => row.append(node("td", String(value)))); body.append(row);});
    table.append(body); el("snaky-move-table").replaceChildren(table);
    el("snaky-evidence").replaceChildren(...data.evidence.map(item => {const card = node("article"); card.append(node("h3", item.title), node("p", item.description)); const link = node("a", "Inspect the exact source ↗"); link.href = item.url; card.append(link); if (item.sha256) card.append(node("code", "SHA-256 " + item.sha256, "snaky-evidence-code")); return card;}));
    el("snaky-query").textContent = data.commands.join("\n");
    el("snaky-content").hidden = false;
    render(data, 0);
  }

  try { start(window.SNAKY_PLAY_DATA); }
  catch (error) { el("snaky-content").hidden = true; el("snaky-error").hidden = false; el("snaky-error").textContent = "The example could not be loaded: " + error.message; }
}());
