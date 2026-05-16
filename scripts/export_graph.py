#!/usr/bin/env python3
"""
Export the full term-level theorem graph as Cytoscape.js-shaped JSON for
the static HTML viewer at `blueprint/graph.html`.

Output: blueprint/graph.json with the shape:
  {
    "nodes": [{"data": {"id", "label", "kind", "file", "module",
                        "has_sorry", "doc"}}],
    "edges": [{"data": {"source", "target"}}]
  }
"""

from __future__ import annotations
import json
from pathlib import Path

import kuzu


PROJECT_ROOT = Path(__file__).resolve().parent.parent
BLUEPRINT_DIR = PROJECT_ROOT / "blueprint"
DB_PATH = BLUEPRINT_DIR / "graph.kuzu"
OUT = BLUEPRINT_DIR / "graph.json"


def main() -> None:
    conn = kuzu.Connection(kuzu.Database(str(DB_PATH)))

    nodes = []
    rs = conn.execute(
        """
        MATCH (d:Decl)
        OPTIONAL MATCH (d)-[:DECLARED_IN]->(m:Module)
        RETURN d.name, d.kind, d.file, m.name, d.namespace,
               d.has_sorry, d.is_proposition, d.doc, d.type_pp
        """
    )
    while rs.has_next():
        name, kind, file, module, ns, has_sorry, is_prop, doc, type_pp = rs.get_next()
        # Short label: last component of the dotted name (with module
        # context) so the graph stays readable.
        label = name.split(".")[-1]
        nodes.append({
            "data": {
                "id": name,
                "label": label,
                "kind": kind,
                "file": file,
                "module": module,
                "namespace": ns,
                "has_sorry": bool(has_sorry),
                "is_proposition": bool(is_prop),
                "doc": doc,
                "type_pp": type_pp,
            }
        })

    edges = []
    rs = conn.execute("MATCH (a:Decl)-[:USES]->(b:Decl) RETURN a.name, b.name")
    while rs.has_next():
        src, dst = rs.get_next()
        edges.append({"data": {"source": src, "target": dst}})

    OUT.write_text(json.dumps({"nodes": nodes, "edges": edges}, indent=2))
    print(f"Exported {len(nodes)} nodes / {len(edges)} edges → {OUT}")


if __name__ == "__main__":
    main()
