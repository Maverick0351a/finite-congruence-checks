"""Build the figures and offline evidence gallery from checked JSON records.

Run from any directory: python scripts/build_charts.py
Validate evidence and committed chart data: python scripts/build_charts.py --check
The check mode uses only the Python standard library. Charts require matplotlib.
"""
from __future__ import annotations

import argparse
import hashlib
import html
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NAVY = "#16324F"
TEAL = "#087F8C"
AMBER = "#C17B16"
INK = "#172B40"
MUTED = "#52677A"
LIGHT = "#E5EDF2"
PAPER = "#FFFFFF"
FIGURES = ["candidate-attrition", "witness-counts", "operation-minima", "witness-examples"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_data():
    sources = {}

    def read(name):
        path = ROOT / "evidence" / name
        sources[f"evidence/{name}"] = sha256(path)
        return json.loads(path.read_text(encoding="utf-8"))

    search = read("search-results.json")
    review = read("independent-review-results.json")
    algebra = read("verified-algebras.json")
    minima = read("minimized-algebras.json")
    require(review["all_expected_outcomes"], "Independent search replay did not pass")
    require(algebra["passed"], "Algebra verification did not pass")
    require(minima["self_check"]["passed"], "Operation-minimization self-check failed")
    if "search_record_file_sha256" in review:
        require(review["search_record_file_sha256"] == sources["evidence/search-results.json"],
                "Independent replay refers to another search file")
    rows = []
    aggregates = []
    review_rows = {(r["lattice"], r["vertices"]): r for r in review["rows"]}
    for name, record in search["lattices"].items():
        m = len(record["lattice"]["elements"])
        require([r["vertices"] for r in record["sizes"]] == list(range(1, search["max_vertices"] + 1)),
                f"{name}: carrier sizes are missing or duplicated")
        lattice_rows = []
        for raw in record["sizes"]:
            n = raw["vertices"]
            counts = raw["counts"]
            row = dict(lattice=name, vertices=n, candidates=counts["candidates"],
                       structural=counts.get("structurally_valid", 0),
                       witnesses=counts.get("witnesses", 0),
                       connectivity_failures=counts.get("seed_connectivity", 0),
                       classes=raw["vertex_isomorphism_classes"])
            require(raw["complete"], f"{name}/{n}: search is incomplete")
            require(row["candidates"] == raw["expected_candidates"] == (m - 1) ** math.comb(n, 2),
                    f"{name}/{n}: candidate-space count mismatch")
            require(row["candidates"] == row["structural"] + counts.get("triangle", 0) +
                    counts.get("order_separation", 0), f"{name}/{n}: attrition does not reconcile")
            require(row["structural"] == row["witnesses"] + row["connectivity_failures"],
                    f"{name}/{n}: connectivity outcomes do not reconcile")
            require(len(raw["representatives"]) == row["classes"], f"{name}/{n}: class-count mismatch")
            require(sum(r["labeled_count"] for r in raw["representatives"]) == row["witnesses"],
                    f"{name}/{n}: class multiplicities do not reconcile")
            replay = review_rows.pop((name, n))
            require(all(replay["matches_primary_record"].values()), f"{name}/{n}: independent replay mismatch")
            for key, replay_key in [("candidates", "labeled_candidates_checked"),
                                    ("structural", "structural_survivors_checked"),
                                    ("witnesses", "witnesses"), ("classes", "vertex_isomorphism_classes")]:
                require(row[key] == replay[replay_key], f"{name}/{n}: {key} replay mismatch")
            lattice_rows.append(row)
            rows.append(row)
        aggregate = dict(lattice=name, lattice_elements=m,
                         minimum_vertices=next((r["vertices"] for r in lattice_rows if r["witnesses"]), None))
        aggregate.update({k: sum(r[k] for r in lattice_rows) for k in
                          ["candidates", "structural", "witnesses", "connectivity_failures", "classes"]})
        require(aggregate["minimum_vertices"] == review["minimum_vertices"][name]["independent_minimum_vertices_found"],
                f"{name}: minimum-carrier replay mismatch")
        aggregates.append(aggregate)
    require(not review_rows, "Independent replay contains unexpected rows")
    registry = {r["path"]: r["sha256"] for r in search["certificates"]}
    require(len(registry) == len(search["certificates"]), "Duplicate certificate path")
    algebra_records = {r["lattice"]: r for r in algebra["certificates"]}
    operation_rows = []
    examples = []
    for row in minima["certificates"]:
        name = row["lattice"]
        cert_name = row["certificate"]
        require(Path(cert_name).name == cert_name, "Certificate must have a plain local filename")
        cert = read(cert_name)
        digest = sources[f"evidence/{cert_name}"]
        require(digest == registry.pop(cert_name) == row["certificate_sha256"], f"{name}: certificate hash mismatch")
        require(cert["source"] == search["source"], f"{name}: upstream provenance mismatch")
        verified = algebra_records.pop(name)
        require(verified["sha256"] == digest, f"{name}: algebra refers to another certificate")
        require(row["passed"] and all(row["checks"].values()), f"{name}: minimization checks failed")
        require(verified["passed"] and all(verified["checks"].values()), f"{name}: algebra checks failed")
        minimum = row["minimum_unary_operation_count"]
        admissible = row["admissible_operation_count"]
        n = row["carrier_size"]
        require(minimum == len(row["selected_unary_operations"]) <= admissible,
                f"{name}: selected-operation count mismatch")
        require(admissible == len(row["admissible_operation_tables"]) == verified["unary_operation_count"],
                f"{name}: admissible-operation count mismatch")
        require(verified["congruence_count"] == len(cert["lattice"]["elements"]),
                f"{name}: congruence count differs from target lattice")
        require(n == len(cert["color"]) == next(r["minimum_vertices"] for r in aggregates if r["lattice"] == name),
                f"{name}: saved carrier is not the minimum found")
        operation_rows.append(dict(lattice=name, carrier_size=n, admissible=admissible, minimum=minimum,
                                   congruences=verified["congruence_count"],
                                   selected_unary_operations=row["selected_unary_operations"]))
        if name in {"N5", "B3"}:
            lattice = cert["lattice"]
            leq = lattice["leq"]
            m = len(lattice["elements"])
            covers = [[a, b] for a in range(m) for b in range(m) if a != b and leq[a][b] and
                      not any(c != a and c != b and leq[a][c] and leq[c][b] for c in range(m))]
            examples.append(dict(lattice=name, elements=lattice["elements"], covers=covers,
                                 color=cert["color"], operations=row["selected_unary_operations"],
                                 congruences=verified["congruence_count"], carrier_size=n))
    require(not registry and not algebra_records, "Certificate records are missing")
    totals = {k: sum(r[k] for r in rows) for k in
              ["candidates", "structural", "witnesses", "connectivity_failures", "classes"]}
    totals["ordered_seed_subsets"] = sum(r["ordered_seed_subsets_enumerated_across_survivors"] for r in review["rows"])
    totals["lattices"] = len(aggregates)
    totals["positive_lattices"] = len(operation_rows)
    return dict(schema_version=1, source=search["source"], max_vertices=search["max_vertices"],
                totals=totals, lattices=aggregates, size_rows=rows, operation_rows=operation_rows,
                examples=examples, sources=dict(sorted(sources.items())),
                scopes=dict(search="All labeled symmetric colorings with bottom exactly on the diagonal, for the selected lattices and carrier sizes.",
                            classes="Vertex permutations only; lattice colors are fixed. Classes from different carrier sizes are distinct.",
                            minima=minima["scope"], negative="A zero witness count is a bounded search result, not global nonrepresentability."),
                checks=dict(candidate_space_reconciled=True, attrition_reconciled=True,
                            independent_replay_agrees=True, certificate_hashes_agree=True,
                            exact_congruence_counts_agree=True, operation_counts_agree=True))


def configure_plotting():
    global plt, colors, ticker
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib import colors, ticker
    matplotlib.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                               "text.color": INK, "axes.labelcolor": MUTED,
                               "xtick.color": MUTED, "ytick.color": INK,
                               "axes.edgecolor": LIGHT, "axes.spines.top": False,
                               "axes.spines.right": False, "axes.spines.left": False,
                               "axes.spines.bottom": False, "figure.facecolor": PAPER,
                               "axes.facecolor": PAPER, "savefig.facecolor": PAPER,
                               "svg.fonttype": "none", "svg.hashsalt": "finite-congruence-checks-v1"})


def header(fig, number, title, subtitle):
    fig.text(.055, .955, f"FINITE CONGRUENCE CHECKS  /  {number:02d}", fontsize=10,
             color=TEAL, weight="bold", va="top")
    fig.text(.055, .908, title, fontsize=23, weight="bold", va="top")
    fig.text(.055, .848, subtitle, fontsize=11.5, color=MUTED, va="top")


def footer(fig, data, caption):
    fig.text(.055, .073, caption, fontsize=10, color=MUTED, va="bottom", linespacing=1.5)
    fig.text(.055, .025,
             f"Source: evidence/*.json  |  openai/math {data['source']['revision'][:12]}  |  Bounded Python checks",
             fontsize=9, color=MUTED, va="bottom")


def save(fig, name):
    out = ROOT / "charts"
    out.mkdir(exist_ok=True)
    fig.savefig(out / f"{name}.svg", metadata={"Date": None, "Creator": "finite-congruence-checks/scripts/build_charts.py"})
    fig.savefig(out / f"{name}.png", dpi=180, metadata={"Software": "finite-congruence-checks"})
    plt.close(fig)


def attrition(data):
    rows = data["lattices"]
    fig, axes = plt.subplots(1, 2, figsize=(13.5, 8.2), gridspec_kw={"width_ratios": [1, 1.25]})
    fig.subplots_adjust(left=.095, right=.94, top=.73, bottom=.22, wspace=.30)
    header(fig, 1, "The last graph condition changes the answer",
           f"{data['totals']['candidates']:,} labeled colorings across {len(rows)} lattices; all carrier sizes 1–{data['max_vertices']} exhausted.")
    y = list(range(len(rows)))
    a, b = axes
    a.barh(y, [r["candidates"] - 1 for r in rows], left=1, color=NAVY, height=.56)
    a.set_xscale("log")
    a.set_xlim(1, max(r["candidates"] for r in rows) * 4)
    a.set_yticks(y, [r["lattice"] for r in rows], weight="bold")
    a.set_xticks([1, 10, 100, 1000, 10000, 100000], ["1", "10", "100", "1k", "10k", "100k"])
    a.xaxis.set_minor_locator(ticker.NullLocator())
    a.grid(axis="x", color=LIGHT, linewidth=.7)
    a.set_axisbelow(True)
    a.set_title("All candidates", loc="left", fontsize=13, weight="bold", pad=19)
    a.set_xlabel("Candidate count · logarithmic axis", labelpad=12)
    for i, row in enumerate(rows):
        a.text(row["candidates"] * 1.15, i, f"{row['candidates']:,}", va="center", fontsize=10, color=NAVY)
    b.barh(y, [r["witnesses"] for r in rows], color=TEAL, height=.56, label="Pass all five conditions")
    b.barh(y, [r["connectivity_failures"] for r in rows], left=[r["witnesses"] for r in rows],
           color="#EBC68C", height=.56, label="Fail seed connectivity")
    b.set_xlim(0, max(r["structural"] for r in rows) * 1.21)
    b.set_yticks(y, [])
    b.set_xlabel("Structural survivor count · linear axis", labelpad=12)
    b.set_title("After the first four conditions", loc="left", fontsize=13, weight="bold", pad=19)
    b.grid(axis="x", color=LIGHT, linewidth=.7)
    b.set_axisbelow(True)
    for i, row in enumerate(rows):
        b.text(row["structural"] + 12, i, f"{row['witnesses']:,} / {row['structural']:,}",
               va="center", fontsize=10, color=INK)
    b.text(.02, 1.015, "Labels: full witnesses / structural survivors", fontsize=9, color=MUTED, transform=b.transAxes)
    handles, labels = b.get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper left", bbox_to_anchor=(.53, .145),
               frameon=False, fontsize=9, ncol=2, borderaxespad=0)
    for ax in axes:
        ax.invert_yaxis()
        ax.tick_params(axis="both", length=0)
    footer(fig, data,
           f"{data['totals']['connectivity_failures']:,} structural survivors fail seed connectivity. M4 has zero witnesses through {data['max_vertices']} vertices.\n"
           "Structural validity includes symmetry, diagonal color, join triangle and order separation. The two panels use different scales.")
    save(fig, "candidate-attrition")


def witness_counts(data):
    names = [r["lattice"] for r in data["lattices"]]
    ns = range(1, data["max_vertices"] + 1)
    lookup = {(r["lattice"], r["vertices"]): r for r in data["size_rows"]}
    fig, axes = plt.subplots(1, 2, figsize=(13.5, 8.4))
    fig.subplots_adjust(left=.10, right=.94, top=.73, bottom=.23, wspace=.34)
    header(fig, 2, "Every tested carrier size, including the zeros",
           f"{data['totals']['witnesses']:,} labeled witnesses collapse to {data['totals']['classes']:,} classes under vertex relabeling.")
    for ax, key, title, base in zip(axes, ["witnesses", "classes"],
                                   ["Labeled witnesses", "Vertex-isomorphism classes"], [TEAL, NAVY]):
        matrix = [[lookup[(name, n)][key] for n in ns] for name in names]
        maxval = max(max(r) for r in matrix)
        cmap = colors.LinearSegmentedColormap.from_list("count", ["#F2F6F8", base])
        ax.imshow(matrix, cmap=cmap, vmin=0, vmax=maxval, aspect="auto")
        for i, row in enumerate(matrix):
            for j, value in enumerate(row):
                ax.text(j, i, str(value), ha="center", va="center", fontsize=14,
                        weight="bold" if value else "normal", color="white" if value > maxval * .72 else INK)
        ax.set_xticks(range(len(list(ns))), [f"n = {n}" for n in ns])
        ax.set_yticks(range(len(names)), names, weight="bold")
        ax.set_xticks([x - .5 for x in range(len(list(ns)) + 1)], minor=True)
        ax.set_yticks([x - .5 for x in range(len(names) + 1)], minor=True)
        ax.grid(which="minor", color="white", linewidth=4)
        ax.tick_params(which="both", length=0, pad=11)
        ax.set_title(title, loc="left", fontsize=13, weight="bold", pad=17)
        ax.set_xlabel("Carrier size (vertices)", labelpad=12)
        cbar = fig.colorbar(ax.images[0], ax=ax, orientation="horizontal", fraction=.045, pad=.20, aspect=30)
        cbar.set_label("Linear color scale · exact counts printed in cells", fontsize=9, labelpad=5)
        cbar.outline.set_visible(False)
        cbar.ax.tick_params(length=0, labelsize=9)
    footer(fig, data,
           "Zero means the entire indicated search space was checked and no witness was found. Lattice colors are held fixed.\n"
           f"M4: no witness on 1–{data['max_vertices']} vertices; larger carriers remain outside this experiment.")
    save(fig, "witness-counts")


def operation_minima(data):
    rows = data["operation_rows"]
    fig, ax = plt.subplots(figsize=(13.5, 8.1))
    fig.subplots_adjust(left=.12, right=.75, top=.73, bottom=.24)
    header(fig, 3, "Small signatures recover the same congruences",
           "All admissible unary maps versus the minimum basic operations for each saved representation.")
    y = list(range(len(rows)))
    ax.barh(y, [r["admissible"] for r in rows], height=.55, color="#DDE7F0", label="All admissible unary maps")
    ax.scatter([r["minimum"] for r in rows], y, s=70, zorder=3, color=AMBER, edgecolors="white", linewidths=1,
               label="Minimum basic unary operations")
    ax.set_yticks(y, [r["lattice"] for r in rows], weight="bold")
    ax.set_xlim(-1.5, max(r["admissible"] for r in rows) * 1.12)
    ax.set_xlabel("Number of unary operations · linear axis", labelpad=13)
    ax.invert_yaxis()
    ax.grid(axis="x", color=LIGHT, linewidth=.7)
    ax.set_axisbelow(True)
    ax.tick_params(length=0)
    for i, row in enumerate(rows):
        ax.text(row["admissible"] + .8, i, str(row["admissible"]), va="center", color=NAVY, fontsize=12, weight="bold")
        op_label = "op" if row["minimum"] == 1 else "ops"
        ax.text(1.045, 1 - (i + .5) / len(rows), f"{row['minimum']} {op_label} · {row['carrier_size']} vertices",
                transform=ax.transAxes, va="center", fontsize=11, color=INK)
    ax.set_ylim(len(rows) - .5, -.5)
    ax.text(1.045, 1.04, "MINIMUM SIGNATURE", transform=ax.transAxes, fontsize=9, color=AMBER, weight="bold")
    ax.legend(loc="upper left", bbox_to_anchor=(-.01, -.16), frameon=False, ncol=2, fontsize=10)
    footer(fig, data,
           "Each minimum fixes both the carrier and the exact saved congruence relations. Other embeddings and higher arities are excluded.\n"
           "Zero is a valid result: the empty operation signature already realizes the full equivalence lattices C2 and M3.")
    save(fig, "operation-minima")


def lattice_positions(example):
    """Deterministic longest-chain ranks; geometry only, never a numerical source."""
    count = len(example["elements"])
    incoming = {i: [a for a, b in example["covers"] if b == i] for i in range(count)}
    rank = {}

    def depth(i):
        if i not in rank:
            rank[i] = max((depth(j) + 1 for j in incoming[i]), default=0)
        return rank[i]

    for i in range(count):
        depth(i)
    if example["lattice"] == "N5":
        # Keep the short branch centered vertically in the pentagon diagram.
        return {0: (0, 0), 1: (-.75, 1), 2: (-.75, 2), 3: (.75, 1.5), 4: (0, 3)}
    result = {}
    for level in sorted(set(rank.values())):
        at_level = [i for i in range(count) if rank[i] == level]
        for index, i in enumerate(at_level):
            result[i] = ((index - (len(at_level) - 1) / 2) * .9, level)
    return result


def witness_examples(data):
    examples = data["examples"]
    fig, axes = plt.subplots(len(examples), 3, figsize=(13.5, 10.3), gridspec_kw={"width_ratios": [1, 1.05, 1.15]})
    fig.subplots_adjust(left=.055, right=.95, top=.77, bottom=.19, wspace=.28, hspace=.45)
    header(fig, 4, "Two certificates, made visible",
           "The saved color matrices and operation tables determine concrete finite algebras.")
    palette = ["#F0F4F6", "#087F8C", "#86C4C5", "#C49344", "#638BAE", "#B0CCD9", "#DAC08A", NAVY]
    for row, ex in enumerate(examples):
        names = ex["elements"]
        m = len(names)
        color_palette = palette[:m - 1] + [NAVY]
        # Explicit contrast for the two dark colors.
        label_colors = ["white" if c in {NAVY, TEAL} else INK for c in color_palette]
        ax, matrix_ax, table_ax = axes[row]
        pos = lattice_positions(ex)
        for a, b in ex["covers"]:
            ax.plot([pos[a][0], pos[b][0]], [pos[a][1], pos[b][1]], color="#9BAEBB", linewidth=2, zorder=1)
        for i, name in enumerate(names):
            ax.scatter(*pos[i], s=530, color=color_palette[i], edgecolor="white", linewidth=2, zorder=2)
            ax.text(*pos[i], name, ha="center", va="center", color=label_colors[i], weight="bold", zorder=3, fontsize=11)
        ax.set_xlim(-1.5, 1.5)
        ax.set_ylim(-.35, max(y for x, y in pos.values()) + .45)
        ax.set_title(f"{ex['lattice']} · {m} lattice elements", loc="left", fontsize=13, weight="bold", pad=12)
        ax.axis("off")
        n = ex["carrier_size"]
        matrix_ax.imshow(ex["color"], cmap=colors.ListedColormap(color_palette), vmin=-.5, vmax=m - .5)
        for i in range(n):
            for j in range(n):
                value = ex["color"][i][j]
                matrix_ax.text(j, i, names[value], ha="center", va="center", fontsize=13,
                               weight="bold", color=label_colors[value])
        matrix_ax.set_xticks(range(n), [f"v{i}" for i in range(n)])
        matrix_ax.set_yticks(range(n), [f"v{i}" for i in range(n)])
        matrix_ax.set_xticks([i - .5 for i in range(n + 1)], minor=True)
        matrix_ax.set_yticks([i - .5 for i in range(n + 1)], minor=True)
        matrix_ax.grid(which="minor", color="white", linewidth=3)
        matrix_ax.tick_params(which="both", length=0, pad=8)
        matrix_ax.set_title(f"Witness · {n} vertices", loc="left", fontsize=13, weight="bold", pad=12)
        table_ax.axis("off")
        table_ax.set_title(f"{len(ex['operations'])} basic unary operations", loc="left", fontsize=13, weight="bold", pad=12)
        table = table_ax.table(cellText=[[f"v{x}" for x in op] for op in ex["operations"]],
                              rowLabels=[f"f{i + 1}(v)" for i in range(len(ex["operations"]))],
                              colLabels=[f"v{i}" for i in range(n)], cellLoc="center", loc="center",
                              bbox=[.12, .43, .88, .41])
        table.auto_set_font_size(False)
        table.set_fontsize(11)
        for (i, j), cell in table.get_celld().items():
            cell.set_edgecolor("white")
            cell.set_linewidth(3)
            cell.set_facecolor(NAVY if i == 0 else "#EDF3F6")
            cell.set_text_props(color="white" if i == 0 else INK, weight="bold" if i == 0 else "normal")
        table_ax.text(.12, .25, f"Exactly {ex['congruences']} congruences recovered.\nAll set partitions were enumerated.",
                      transform=table_ax.transAxes, fontsize=10.5, color=MUTED, linespacing=1.6)
    footer(fig, data,
           "The left diagrams show cover relations. Matrix colors denote lattice elements; vertex labels index the finite carrier.\n"
           "B3 element labels 0–7 are the certificate's subset-bitmask encoding. Operation minima apply to these exact saved relations.")
    save(fig, "witness-examples")


def esc(value):
    return html.escape(str(value), quote=True)


def build_gallery(data):
    totals = data["totals"]
    rev = data["source"]["revision"]
    rows = "".join(
        f'<tr><th scope="row">{esc(r["lattice"])}</th><td>{r["lattice_elements"]}</td>'
        f'<td>{r["candidates"]:,}</td><td>{r["structural"]:,}</td><td>{r["witnesses"]:,}</td>'
        f'<td>{r["classes"]:,}</td><td>{r["minimum_vertices"] if r["minimum_vertices"] else "None ≤ " + str(data["max_vertices"])}</td></tr>'
        for r in data["lattices"])
    size_rows = "".join(f'<tr><th scope="row">{esc(r["lattice"])}</th><td>{r["vertices"]}</td>'
                        f'<td>{r["candidates"]:,}</td><td>{r["structural"]:,}</td><td>{r["witnesses"]:,}</td>'
                        f'<td>{r["classes"]:,}</td></tr>' for r in data["size_rows"])
    op_rows = "".join(f'<tr><th scope="row">{esc(r["lattice"])}</th><td>{r["carrier_size"]}</td>'
                      f'<td>{r["admissible"]}</td><td>{r["minimum"]}</td><td>{r["congruences"]}</td></tr>'
                      for r in data["operation_rows"])
    sources = "".join(f'<li><a href="../{esc(path)}">{esc(path)}</a><code>{digest}</code></li>'
                      for path, digest in data["sources"].items())
    figures = [
        ("candidate-attrition", "01 / SEARCH", "Where the graph conditions matter",
         "The first four conditions leave a much larger set than the complete criterion. The final condition checks whether admissible maps generate the required connections.",
         f"{totals['structural']:,} structural survivors split into {totals['witnesses']:,} full witnesses and {totals['connectivity_failures']:,} seed-connectivity failures. Candidate counts use a logarithmic axis; survivor counts use a linear axis.",
         f"Candidate counts and structural-survivor outcomes for {data['totals']['lattices']} lattices, summed over carrier sizes one to {data['max_vertices']}."),
        ("witness-counts", "02 / COVERAGE", "An explicit result for every tested size",
         "The search covers the full bounded space. Exact cell values make both the positive examples and the negative results inspectable.",
         f"Classes identify colorings up to vertex permutations with lattice colors held fixed. M4 has no witness through {data['max_vertices']} vertices; this says nothing about larger carriers.",
         "Two tables visualized as heatmaps: labeled witnesses and vertex-isomorphism classes by lattice and carrier size. All zero counts are printed."),
        ("operation-minima", "03 / CONSTRUCTIONS", "How few operations are enough?",
         "For each saved representation, the minimizer finds the smallest subset of unary operations whose congruences are exactly the saved target relations.",
         "The result fixes the carrier and its exact relation embedding. It does not minimize over other embeddings or higher-arity operations. Zero basic operations is allowed.",
         "All admissible unary-map counts compared with minimum basic unary-operation counts for seven saved representations."),
        ("witness-examples", "04 / CERTIFICATES", "Read two examples directly",
         "N5 and B3 connect the abstract lattice, a small color matrix and explicit operation tables. A separate partition enumeration recovers the target congruence lattice.",
         "N5 and B3 are illustrative controls; these constructions are not claimed to be new. The numeric B3 labels are preserved from the certificate.",
         "Hasse diagrams, witness color matrices and selected unary-operation tables for the N5 and B3 certificates."),
    ]
    sections = "".join(f'''<section id="{name}" class="figure-section">
<div class="section-copy"><p class="eyebrow">{eyebrow}</p><h2>{title}</h2><p>{intro}</p></div>
<figure><a class="figure-link" href="../charts/{name}.svg" aria-label="Open full-size {title.lower()}"><img src="../charts/{name}.svg" alt="{alt}" loading="lazy"></a>
<figcaption>{caption}<span class="downloads"><a href="../charts/{name}.svg" download>SVG</a><a href="../charts/{name}.png" download>PNG</a></span></figcaption></figure></section>'''
                        for name, eyebrow, title, intro, caption, alt in figures)
    text = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="color-scheme" content="light"><meta name="description" content="Reproducible bounded evidence for finite congruence lattices: exhaustive search, independent replay and concrete finite algebras.">
<title>Finite Congruence Checks · Evidence Atlas</title>
<style>
:root{{--navy:{NAVY};--teal:{TEAL};--amber:#A96B10;--ink:{INK};--muted:{MUTED};--line:#DDE6EB;--paper:#F4F7F8}}
*{{box-sizing:border-box}}html{{scroll-behavior:smooth;scroll-padding-top:90px}}body{{margin:0;background:var(--paper);color:var(--ink);font:17px/1.65 system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}}a{{color:var(--teal);text-underline-offset:4px}}a:hover{{color:var(--navy)}}a:focus-visible,summary:focus-visible{{outline:3px solid #D09B48;outline-offset:5px}}.skip{{position:absolute;left:20px;top:-80px;background:white;padding:10px;z-index:5}}.skip:focus{{top:10px}}.wrap{{max-width:1280px;margin:auto;padding:0 46px}}header{{background:var(--navy);color:white;padding:25px 0 0}}.masthead{{display:flex;justify-content:space-between;gap:20px;align-items:center;padding-bottom:23px;border-bottom:1px solid #3A536D}}.wordmark{{font-size:15px;font-weight:750;letter-spacing:.055em}}.tag{{font-size:12px;letter-spacing:.08em;border:1px solid #6E8DA6;border-radius:20px;padding:4px 12px;color:#E4F3F5}}.hero{{padding:58px 0 55px;max-width:900px}}.eyebrow{{color:var(--teal);font-size:12px;letter-spacing:.12em;text-transform:uppercase;font-weight:750;margin:0 0 12px}}header .eyebrow{{color:#9BDDDD}}h1{{font-size:clamp(38px,5.5vw,68px);letter-spacing:-.045em;line-height:1.06;margin:0 0 25px;max-width:850px}}.hero p:last-child{{font-size:20px;color:#D0DFE9;max-width:760px;margin:0}}nav{{background:white;border-bottom:1px solid var(--line)}}nav .wrap{{display:flex;gap:28px;flex-wrap:wrap;padding-top:14px;padding-bottom:14px}}nav a{{font-size:13px;font-weight:650;text-decoration:none;color:var(--navy)}}.metrics{{display:grid;grid-template-columns:repeat(4,1fr);gap:1px;background:var(--line);border:1px solid var(--line);border-radius:8px;overflow:hidden;margin:36px 0 24px}}.metric{{background:white;padding:23px 26px}}.metric strong{{display:block;color:var(--navy);font-size:34px;line-height:1.2;letter-spacing:-.04em}}.metric span{{font-size:13px;color:var(--muted)}}.scope{{display:grid;grid-template-columns:1fr 1fr;gap:32px;background:#EAF2F3;border-left:4px solid var(--teal);padding:25px 28px;margin-bottom:48px;font-size:14px}}.scope h2{{font-size:15px;letter-spacing:0;margin:0 0 5px}}.scope p{{margin:0}}.figure-section{{margin:60px 0 72px}}.section-copy{{max-width:760px;margin-bottom:25px}}h2{{font-size:31px;line-height:1.2;letter-spacing:-.025em;margin:0 0 13px}}.section-copy>p:last-child{{color:var(--muted);margin:0}}figure{{margin:0;border:1px solid var(--line);border-radius:9px;overflow:hidden;background:white;box-shadow:0 8px 24px #17334F05}}.figure-link{{display:block}}img{{display:block;width:100%;height:auto}}figcaption{{border-top:1px solid var(--line);padding:19px 26px;color:var(--muted);font-size:13px}}.downloads{{display:flex;gap:18px;margin-top:11px;font-size:12px;font-weight:750;letter-spacing:.05em}}.tables{{margin:60px 0}}.table-wrap{{overflow-x:auto;background:white;border:1px solid var(--line);border-radius:8px}}table{{border-collapse:collapse;width:100%;font-size:14px;font-variant-numeric:tabular-nums}}caption{{text-align:left;padding:18px 20px;color:var(--muted);font-size:13px}}thead{{background:var(--navy);color:white}}th,td{{padding:12px 17px;text-align:right;border-bottom:1px solid var(--line);white-space:nowrap}}th:first-child{{text-align:left}}tbody tr:last-child>*{{border-bottom:0}}tbody tr:nth-child(even){{background:#F6F9FA}}.table-note{{font-size:13px;color:var(--muted);margin:12px 0 23px}}details{{margin:18px 0;border:1px solid var(--line);border-radius:8px;padding:17px 20px;background:white}}summary{{cursor:pointer;font-size:14px;font-weight:650;color:var(--navy)}}details .table-wrap{{margin-top:18px}}.sources{{font-size:13px;overflow-wrap:anywhere;padding-left:20px}}.sources li{{padding:10px 0;border-bottom:1px solid var(--line)}}code{{font:12px/1.6 ui-monospace,SFMono-Regular,Consolas,monospace}}.sources code{{display:block;color:var(--muted)}}.provenance{{background:var(--navy);color:#D0DFE9;padding:37px;border-radius:8px;margin:65px 0 35px;font-size:14px}}.provenance h2{{font-size:24px;color:white}}.provenance a{{color:#9BDDDD}}.provenance p{{max-width:900px}}.provenance code{{overflow-wrap:anywhere}}footer{{padding:0 0 40px;color:var(--muted);font-size:12px;display:flex;justify-content:space-between;gap:20px;flex-wrap:wrap}}.small{{font-size:13px;color:var(--muted)}}
@media(max-width:760px){{.wrap{{padding:0 20px}}.hero{{padding:40px 0}}.hero p:last-child{{font-size:17px}}.tag{{display:none}}nav .wrap{{gap:16px}}.metrics{{grid-template-columns:repeat(2,1fr)}}.metric{{padding:18px}}.metric strong{{font-size:28px}}.scope{{grid-template-columns:1fr;gap:20px;padding:22px}}h2{{font-size:26px}}.figure-section{{margin:45px 0}}figcaption{{padding:16px}}.provenance{{padding:25px}}}}
@media(prefers-reduced-motion:reduce){{html{{scroll-behavior:auto}}}}@media print{{nav,.downloads,.skip{{display:none}}body{{background:white}}.wrap{{padding:0}}.hero{{padding:20px 0}}header{{background:white;color:var(--navy)}}header .eyebrow,.hero p:last-child{{color:var(--muted)}}.figure-section{{break-inside:avoid;margin:30px 0}}.provenance{{background:#F2F6F8;color:var(--ink)}}.provenance h2{{color:var(--ink)}}details{{break-inside:avoid}}}}
</style></head><body><a class="skip" href="#content">Skip to evidence</a>
<header><div class="wrap"><div class="masthead"><div class="wordmark">FINITE CONGRUENCE CHECKS</div><span class="tag">REPRODUCIBLE RESEARCH TOOLING</span></div>
<div class="hero"><p class="eyebrow">Evidence atlas / bounded finite models</p><h1>Small algebras.<br>Inspectable evidence.</h1><p>Exhaustive graph searches, a separately implemented replay and concrete congruence calculations for a selected part of the OpenAI math corpus.</p></div></div></header>
<nav aria-label="Evidence sections"><div class="wrap"><a href="#candidate-attrition">Search</a><a href="#witness-counts">Coverage</a><a href="#operation-minima">Constructions</a><a href="#witness-examples">Certificates</a><a href="#tables">Exact data</a><a href="#provenance">Provenance</a></div></nav>
<main id="content" class="wrap"><div class="metrics" aria-label="Experiment totals">
<div class="metric"><strong>{totals['candidates']:,}</strong><span>labeled candidate colorings</span></div>
<div class="metric"><strong>{totals['witnesses']:,}</strong><span>witnesses passing all conditions</span></div>
<div class="metric"><strong>{totals['classes']:,}</strong><span>vertex-isomorphism classes</span></div>
<div class="metric"><strong>{totals['positive_lattices']} / {totals['lattices']}</strong><span>lattices with saved constructions</span></div></div>
<aside class="scope" aria-label="Scope and interpretation"><div><h2>What this evidence establishes</h2><p>The selected lattice searches exhaust carrier sizes 1–{data['max_vertices']}. A separate Python implementation replays every candidate and enumerates {totals['ordered_seed_subsets']:,} nonempty ordered seed subsets across structural survivors.</p></div><div><h2>Where the claim ends</h2><p>These are finite computational checks. They do not prove the universal graph criterion, certify the corpus as a whole or establish mathematical novelty. Formal-proof status is documented separately in the repository.</p></div></aside>
{sections}
<section id="tables" class="tables"><p class="eyebrow">05 / EXACT DATA</p><h2>The numbers behind the figures</h2>
<div class="table-wrap"><table><caption>All tested sizes combined. Minimum carrier means the smallest positive size found in this exhaustive range.</caption><thead><tr><th scope="col">Lattice</th><th scope="col">Elements</th><th scope="col">Candidates</th><th scope="col">Structural</th><th scope="col">Witnesses</th><th scope="col">Classes</th><th scope="col">Min. carrier</th></tr></thead><tbody>{rows}</tbody></table></div>
<p class="table-note">Every zero in the detailed table is a measured outcome. M4's “None ≤ {data['max_vertices']}” is a bounded absence result.</p>
<details><summary>Expand every lattice × carrier-size result</summary><div class="table-wrap"><table><caption>Exact data for every completed search row.</caption><thead><tr><th scope="col">Lattice</th><th scope="col">Vertices</th><th scope="col">Candidates</th><th scope="col">Structural</th><th scope="col">Witnesses</th><th scope="col">Classes</th></tr></thead><tbody>{size_rows}</tbody></table></div></details>
<details><summary>Expand exact operation and congruence counts</summary><div class="table-wrap"><table><caption>Minima fix each saved carrier and its exact threshold relations.</caption><thead><tr><th scope="col">Lattice</th><th scope="col">Vertices</th><th scope="col">All admissible</th><th scope="col">Min. basic ops</th><th scope="col">Congruences</th></tr></thead><tbody>{op_rows}</tbody></table></div></details>
<p class="small"><a href="../charts/chart-data.json" download>Download all plotted data and source hashes (JSON)</a></p></section>
<section id="provenance" class="provenance"><p class="eyebrow" style="color:#9BDDDD">06 / PROVENANCE</p><h2>Trace every figure to a record</h2><p>Upstream comparator: <a href="{esc(data['source']['repository'])}/blob/{rev}/{esc(data['source']['path'])}">FiniteCongruenceGraph.lean</a><br>Commit: <code>{rev}</code></p>
<p>Each build reconciles candidate counts, rejection totals, independent replay results, certificate hashes and operation counts before rendering. All chart quantities come from the recorded JSON inputs. The gallery loads locally without scripts, CDNs or network requests.</p>
<p><a href="../README.md">Repository guide</a> · <a href="../METHOD.md">Method</a> · <a href="../INDEPENDENT_REVIEW.md">Internal independent review</a> · <a href="../RESEARCH_CONTEXT.md">Research context</a></p></section>
<details><summary>Input files and SHA-256 digests used for this build</summary><ul class="sources">{sources}</ul></details>
<footer><span>Finite Congruence Checks · Evidence atlas</span><span>Generated by scripts/build_charts.py · No external assets</span></footer></main></body></html>
'''
    (ROOT / "docs" / "index.html").write_text(text, encoding="utf-8", newline="\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Validate evidence, chart-data freshness and gallery assets without plotting")
    args = parser.parse_args()
    data = load_data()
    data_path = ROOT / "charts" / "chart-data.json"
    if args.check:
        require(json.loads(data_path.read_text(encoding="utf-8")) == data,
                "Chart data is stale: rebuild with python scripts/build_charts.py")
        for name in FIGURES:
            for extension in ["svg", "png"]:
                require((ROOT / "charts" / f"{name}.{extension}").is_file(), f"Missing {name}.{extension}")
        page = (ROOT / "docs" / "index.html").read_text(encoding="utf-8")
        for path, digest in data["sources"].items():
            require(digest in page, f"Gallery has stale provenance for {path}")
        print(f"PASS: {len(data['size_rows'])} rows reconcile; chart data, provenance and 8 figure assets are present.")
        return
    configure_plotting()
    attrition(data)
    witness_counts(data)
    operation_minima(data)
    witness_examples(data)
    data_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8", newline="\n")
    build_gallery(data)
    print(f"Built {len(FIGURES)} SVG + PNG figures, chart-data.json and docs/index.html from {len(data['sources'])} checked sources.")


if __name__ == "__main__":
    main()
