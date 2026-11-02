"""Build the Gotham proof viewer: viewer/gotham.html, a single page that steps through the proof.

Untrusted tooling, outside the Lean build. It reads the generated certificate file and changes
nothing in the library; a wrong script draws a wrong page, never a false theorem.

Usage (from the library's root): python -I scripts/build_viewer.py

It reads ChessDemo/GothamCert.lean (written by gen_cert.py) and takes from it, with no chess
library and no engine:
  * each checkpoint `pN` and the FEN in its docstring,
  * each node theorem `wN : WinsIn .c k pN`, with its kind (mated, one attacker move, or every
    defender reply), its moves (UCI from the `play` equations, SAN from the docstring) and the
    checkpoint and node each move leads to,
  * the best move's node (`winsIn`) and the refutations `refutes_<uci>` with their budgets.
The result is inlined as JSON into viewer/template.html, which draws the board and the move lists,
together with the piece images of viewer/pieces/cburnett (see viewer/pieces/README.md).
The page needs no server: open viewer/gotham.html in a browser.
"""
import base64, json, re, sys

CERT = "ChessDemo/GothamCert.lean"
TEMPLATE = "viewer/template.html"
OUT = "viewer/gotham.html"
PIECES = "viewer/pieces/cburnett"
ROOT_FEN = "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1"


def extract(src):
    fens = {m.group(2): m.group(1)
            for m in re.finditer(r"/-- `([^`]+)` -/\s*def (p\d+) : Position", src)}
    fens.setdefault("p0", ROOT_FEN)

    nodes = {}
    node_re = (r"/-- (.*?) -/\s*theorem (w\d+) : WinsIn \.(\w+) (\d+) (p\d+) :="
               r"(.*?)(?=\n\n|\n/-)")
    for m in re.finditer(node_re, src, re.S):
        doc, wid, color, k, pos, body = m.groups()
        doc = " ".join(doc.split())
        node = {"claim": f"WinsIn .{color} {k} {pos}", "color": color, "budget": int(k),
                "pos": pos}
        if "of_mated" in body:
            node["kind"] = "mate"
        elif "replies_of_moves_eq" in body:
            node["kind"] = "replies"
            listed = re.search(r"Game\.chess\.moves \w+ = \[(.*?)\]", body, re.S).group(1)
            ucis = [u.strip() for u in listed.split(",")]
            sans = re.search(r"with the replies (.*?)\.$", doc).group(1).split(", ")
            kids = re.findall(r"\w+\.play (\w+) = (p\d+)\) (w\d+)", body)
            if len(sans) != len(ucis) or [u for u, _, _ in kids] != ucis:
                sys.exit(f"{wid}: the replies do not match the move list")
            node["replies"] = [{"uci": u, "san": s, "to": p, "node": w}
                               for (u, p, w), s in zip(kids, sans)]
        else:
            node["kind"] = "move"
            u, p, w = re.search(r"\w+\.play (\w+) = (p\d+)\) (w\d+)", body).groups()
            san = re.search(r"plays (\S+?)\.$", doc).group(1)
            node["move"] = {"uci": u, "san": san, "to": p, "node": w}
        nodes[wid] = node

    refs = []
    ref_re = (r"/-- After `(\w+)` \((\S+)\), White mates within (\d+)\. -/\s*"
              r"theorem (refutes_\w+) :.*?= (p\d+)\) (w\d+)")
    for m in re.finditer(ref_re, src, re.S):
        u, san, k, name, p, w = m.groups()
        refs.append({"uci": u, "san": san, "budget": int(k), "theorem": name, "to": p, "node": w})
    best = re.search(r"theorem winsIn : .*?play_best (w\d+)", src, re.S).group(1)

    declared = set(re.findall(r"^theorem (w\d+) ", src, re.M))
    targets = {mv["node"] for n in nodes.values()
               for mv in ([n["move"]] if n["kind"] == "move" else n.get("replies", []))}
    if declared != set(nodes) or not targets <= set(nodes) or not {n["pos"] for n in nodes.values()} <= set(fens):
        sys.exit("the certificate file did not parse completely")
    return {"rootFen": ROOT_FEN, "best": {"uci": "b7b2", "san": "Rxb2+", "to": "p1", "node": best},
            "refutations": refs, "nodes": nodes, "fens": fens}


def main():
    data = extract(open(CERT).read())
    blob = json.dumps(data, separators=(",", ":"))
    if "</" in blob:
        sys.exit("the data would close the page's script")
    pieces = {f"{c}{k}": "data:image/svg+xml;base64,"
              + base64.b64encode(open(f"{PIECES}/{c}{k}.svg", "rb").read()).decode()
              for c in "wb" for k in "KQRBNP"}
    page = (open(TEMPLATE).read().replace("__PIECES__", json.dumps(pieces))
            .replace("__DATA__", blob))
    open(OUT, "w").write(page)
    print(f"{OUT}: {len(data['nodes'])} nodes, {len(data['fens'])} positions, "
          f"{len(data['refutations'])} refutations")


if __name__ == "__main__":
    main()
