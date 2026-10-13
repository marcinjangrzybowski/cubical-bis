#!/usr/bin/env python3
"""Render Financial Markdown with Pandoc; preserve local documentation links.

Run from any directory: python3 scripts/render-financial-docs.py
Output: html/Financial/index.html. Existing Agda HTML is left intact.
Requires Pandoc; uncached diagrams also require Chrome/Chromium and the Python
websockets package, with network access on the first run to fetch Mermaid.
Mermaid diagrams are rendered to SVG using Chrome and a cached, pinned Mermaid
bundle. All generated documentation pages can then be opened offline.
"""

import asyncio
import hashlib
import html
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
from urllib.parse import quote, unquote, urlsplit, urlunsplit
from urllib.request import urlretrieve, urlopen


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Cubical/HITs/CauchyReals/Example/Financial"
OUTPUT = ROOT / "html/Financial"
ASSETS = OUTPUT / "_assets"
MERMAID_VERSION = "10.9.3"

CSS = """
:root { color-scheme: light; --ink: #243247; --accent: #1559a5; --line: #dce3eb; }
* { box-sizing: border-box; }
html { scroll-behavior: smooth; }
body { margin: 0; background: #fafbfd; color: var(--ink); font: 17px/1.65 system-ui, sans-serif; }
main { max-width: 1050px; margin: auto; padding: 30px 44px 70px; background: white; min-height: 100vh; }
.site-nav { display: flex; flex-wrap: wrap; gap: 24px; padding-bottom: 18px; border-bottom: 1px solid var(--line); font-size: 14px; }
a { color: var(--accent); text-decoration-thickness: 1px; text-underline-offset: 3px; }
a:hover { color: #073465; }
h1, h2, h3 { line-height: 1.25; color: #12243c; scroll-margin-top: 24px; }
h1 { font-size: 2.2rem; margin: 36px 0 22px; letter-spacing: -.035em; }
h2 { font-size: 1.55rem; margin-top: 2.4em; padding-bottom: 8px; border-bottom: 1px solid var(--line); }
h3 { font-size: 1.2rem; margin-top: 1.8em; }
p { margin: 1em 0; }
li { margin: .4em 0; }
code, pre { font-family: "SFMono-Regular", Menlo, "DejaVu Sans Mono", monospace; }
code { font-size: .85em; overflow-wrap: anywhere; background: #f1f4f8; padding: .13em .3em; border-radius: 4px; }
pre { padding: 18px 22px; background: #f5f7fa; border: 1px solid var(--line); border-radius: 8px; overflow-x: auto; line-height: 1.55; }
pre code { background: transparent; padding: 0; overflow-wrap: normal; }
div.sourceCode { overflow-x: auto; }
table { display: block; width: 100%; overflow-x: auto; border-collapse: collapse; font-size: .9rem; margin: 1.5em 0; }
th, td { padding: 11px 14px; border: 1px solid var(--line); vertical-align: top; min-width: 100px; }
th { background: #edf3fa; text-align: left; }
tr:nth-child(even) { background: #fafbfd; }
blockquote { margin-left: 0; border-left: 4px solid #8ab1d8; padding: 0 20px; color: #45576d; }
details.toc { margin: 22px 0; padding: 12px 20px; background: #f5f8fc; border: 1px solid var(--line); border-radius: 8px; font-size: .9rem; }
details.toc summary { cursor: pointer; font-weight: 600; }
details.toc ul { margin: .5em 0; }
img.diagram { display: block; width: 100%; max-height: 700px; object-fit: contain; margin: 28px auto; }
.document-list { columns: 2 300px; padding-left: 22px; }
.document-list li { break-inside: avoid; padding: 5px 0; }
.muted { color: #5c6d80; font-size: .9rem; }
@media (max-width: 650px) { main { padding: 20px 18px 45px; } body { font-size: 16px; } h1 { font-size: 1.9rem; } pre { padding: 14px; } }
@media print { body, main { background: white; padding: 0; max-width: none; } .site-nav, details.toc { display: none; } pre { white-space: pre-wrap; } table { display: table; font-size: 9pt; } a { color: inherit; } }
"""

TEMPLATE = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>$pagetitle$ · Financial</title><link rel="stylesheet" href="$stylesheet$">
$if(highlighting-css)$<style>$highlighting-css$</style>$endif$
</head><body><main>
<nav class="site-nav"><a href="$home$">Financial documentation</a><a href="$overview$">Overview</a><a href="$source$">Markdown source</a></nav>
$if(toc)$<details class="toc"><summary>On this page</summary>$toc$</details>$endif$
$body$
</main></body></html>
"""


def relative(target, page):
    return quote(os.path.relpath(target, page.parent), safe="/._-")


def walk(value, transform):
    if isinstance(value, dict):
        value = {key: walk(item, transform) for key, item in value.items()}
        return transform(value)
    if isinstance(value, list):
        return [walk(item, transform) for item in value]
    return value


def diagram_path(source):
    digest = hashlib.sha256((MERMAID_VERSION + source).encode()).hexdigest()[:20]
    return ASSETS / ("diagram-" + digest + ".svg")


def render_diagrams(diagrams):
    missing = [text for text in dict.fromkeys(diagrams) if not diagram_path(text).exists()]
    if not missing:
        return
    chrome = shutil.which("google-chrome") or shutil.which("chromium")
    if not chrome:
        candidate = Path("/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")
        chrome = str(candidate) if candidate.exists() else None
    if not chrome:
        raise SystemExit("Chrome or Chromium is required to render the Mermaid diagrams.")
    cache = Path(tempfile.gettempdir()) / "financial-html-render"
    cache.mkdir(exist_ok=True)
    bundle = cache / ("mermaid-" + MERMAID_VERSION + ".min.js")
    if not bundle.exists():
        urlretrieve(f"https://cdn.jsdelivr.net/npm/mermaid@{MERMAID_VERSION}/dist/mermaid.min.js", bundle)
    # Use the browser protocol rather than virtual-time rendering: Mermaid's
    # layout needs real animation frames and font measurements.
    import websockets

    with tempfile.TemporaryDirectory(prefix="financial-diagrams-") as tmp:
        profile = Path(tmp) / "profile"
        browser = subprocess.Popen([chrome, "--headless=new", "--disable-gpu", "--no-first-run",
            "--no-default-browser-check", "--allow-file-access-from-files", "--disable-extensions", "--no-proxy-server",
            "--remote-debugging-port=0", "--user-data-dir=" + str(profile), "about:blank"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            port_file = profile / "DevToolsActivePort"
            deadline = time.monotonic() + 15
            while not port_file.exists():
                if time.monotonic() > deadline or browser.poll() is not None:
                    raise RuntimeError("Chrome did not start its local rendering session")
                time.sleep(.1)
            port = port_file.read_text().splitlines()[0]
            with urlopen(f"http://127.0.0.1:{port}/json", timeout=10) as response:
                targets = json.load(response)
            page = next(target for target in targets if target["type"] == "page")

            async def render():
                async with websockets.connect(page["webSocketDebuggerUrl"], max_size=16000000) as socket:
                    async def evaluate(identifier, expression):
                        await socket.send(json.dumps({"id": identifier, "method": "Runtime.evaluate", "params": {
                            "expression": expression, "awaitPromise": True, "returnByValue": True}}))
                        while True:
                            message = json.loads(await asyncio.wait_for(socket.recv(), timeout=20))
                            if message.get("id") == identifier:
                                if "exceptionDetails" in message.get("result", {}) or "error" in message:
                                    raise RuntimeError(str(message))
                                return message["result"]["result"].get("value")

                    await evaluate(1, bundle.read_text() + "\n; true;")
                    expression = ('(async()=>{'
                        'mermaid.initialize({startOnLoad:false,theme: "neutral",securityLevel:"strict",'
                        'flowchart:{htmlLabels:false},fontFamily:"Arial, sans-serif"});'
                        'const rendered=[];'
                        f'for(const [i,source] of {json.dumps(missing)}.entries())'
                        '{const item=await mermaid.render("diagram"+i,source);rendered.push(item.svg);}'
                        'return rendered;})()')
                    return await evaluate(2, expression)

            rendered = asyncio.run(render())
            if len(rendered) != len(missing):
                raise RuntimeError("Incomplete Mermaid rendering")
            for source, svg in zip(missing, rendered):
                diagram_path(source).write_text(svg)
        finally:
            browser.terminate()
            try:
                browser.wait(timeout=5)
            except subprocess.TimeoutExpired:
                browser.kill()
                browser.wait()


def main():
    if not shutil.which("pandoc"):
        raise SystemExit("Install Pandoc before running this renderer.")
    ASSETS.mkdir(parents=True, exist_ok=True)
    (ASSETS / "style.css").write_text(CSS)
    documents = {}
    diagrams = []
    for source in sorted(SOURCE.rglob("*.md")):
        document = json.loads(subprocess.check_output(
            ["pandoc", "--from=gfm", "--to=json", str(source)], text=True))
        documents[source] = document

        def collect(node):
            if node.get("t") == "CodeBlock" and "mermaid" in node["c"][0][1]:
                diagrams.append(node["c"][1])
            return node

        walk(document, collect)
    render_diagrams(diagrams)

    with tempfile.TemporaryDirectory(prefix="financial-pandoc-") as tmp:
        template = Path(tmp) / "template.html"
        template.write_text(TEMPLATE)
        for source, document in documents.items():
            page = OUTPUT / source.relative_to(SOURCE).with_suffix(".html")
            page.parent.mkdir(parents=True, exist_ok=True)

            def convert(node):
                if node.get("t") == "Link":
                    address = urlsplit(node["c"][2][0])
                    if not address.scheme and not address.netloc and address.path:
                        target = (source.parent / unquote(address.path)).resolve()
                        if target in documents:
                            target = OUTPUT / target.relative_to(SOURCE).with_suffix(".html")
                        elif target.suffix == ".agda" and target.is_relative_to(ROOT):
                            generated = ROOT / "html" / (".".join(target.relative_to(ROOT).with_suffix("").parts) + ".html")
                            if generated.exists():
                                target = generated
                        node["c"][2][0] = urlunsplit(("", "", relative(target, page), address.query, address.fragment))
                if node.get("t") == "CodeBlock" and "mermaid" in node["c"][0][1]:
                    image = relative(diagram_path(node["c"][1]), page)
                    return {"t": "RawBlock", "c": ["html", f'<img class="diagram" src="{image}" alt="Financial workflow diagram">']}
                return node

            document = walk(document, convert)
            title = next((line[2:].strip() for line in source.read_text().splitlines()
                          if line.startswith("# ")), source.stem)
            subprocess.run(["pandoc", "--from=json", "--to=html5", "--standalone", "--toc",
                "--toc-depth=3", "--syntax-highlighting=pygments", "--template=" + str(template),
                "--metadata=pagetitle:" + title,
                "--variable=stylesheet:" + relative(ASSETS / "style.css", page),
                "--variable=home:" + relative(OUTPUT / "index.html", page),
                "--variable=overview:" + relative(OUTPUT / "README.html", page),
                "--variable=source:" + relative(source, page), "--output=" + str(page)],
                input=json.dumps(document), text=True, check=True)

    listing = "".join('<li><a href="' + quote(str(path.relative_to(SOURCE).with_suffix(".html"))) + '">'
        + html.escape(str(path.relative_to(SOURCE))) + '</a></li>' for path in documents)
    (OUTPUT / "index.html").write_text('''<!doctype html><html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Financial documentation</title><link rel="stylesheet" href="_assets/style.css"></head>
<body><main><h1>Financial documentation</h1>
<p>Constructive financial mathematics and certified risk calculations in Cubical Agda.</p>
<p><a href="README.html">Overview</a> · <a href="Broker2/PRESENTATION.html">Broker2 presentation</a> ·
<a href="Broker2/Pipeline/README.html">Relational margin calculation</a></p>
<h2>All documents</h2><ul class="document-list">''' + listing + '''</ul>
<p class="muted">Generated from the Financial Markdown sources. Diagrams are embedded SVG images;
links to Agda use the existing generated module pages where available.</p></main></body></html>''')
    print(f"Rendered {len(documents)} Markdown documents and {len(diagrams)} diagrams.")
    print(OUTPUT / "index.html")


if __name__ == "__main__":
    main()
