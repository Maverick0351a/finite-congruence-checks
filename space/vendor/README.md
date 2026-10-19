# Cytoscape.js

This directory contains the unmodified UMD browser build of **Cytoscape.js
3.34.4**, distributed under the included MIT license. The application's source
remains under the repository's Apache-2.0 license.

- Upstream: https://github.com/cytoscape/cytoscape.js
- API reference: https://js.cytoscape.org/
- Release archive and npm SHA-512 integrity: `manifest.json`
- Per-file SHA-256 hashes: `manifest.json`

The archive was obtained with `npm pack cytoscape@3.34.4`. Its SHA-512 integrity
was verified before copying only `dist/cytoscape.min.js` and `LICENSE`. The
library makes the map available without a CDN or install step. There are no
extensions or runtime downloads. Run `node scripts/check_atlas_map.cjs` to check
the vendored files and the construction-to-shape projection.

For an upgrade, select an exact version, verify its npm archive integrity,
replace these two files and this manifest, update the HTML script reference,
and rerun the graph checks and browser interaction review. Keep upstream
license text intact. Do not replace this with an unpinned CDN URL.
