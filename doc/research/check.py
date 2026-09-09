"""Check the unified research document and its executable audit references."""

import ast
import re
from collections import Counter
from pathlib import Path


def check(root):
    errors, sources = [], {}

    def visit(path):
        path = path.resolve()
        if path in sources:
            errors.append(f"Repeated TeX input: {path}")
            return
        if not path.is_file():
            errors.append(f"Missing TeX input: {path}")
            return
        source = re.sub(r"(?<!\\)%[^\n]*", "", path.read_text())
        sources[path] = source
        for target in re.findall(r"\\input\{([^}]+)\}", source):
            visit(root / target)

    visit(root / "main.tex")
    expected = set(root.glob("*.tex")) | set((root / "body").rglob("*.tex")) | set((root / "preamble").glob("*.tex"))
    for path in sorted(expected - sources.keys()):
        errors.append(f"Unincluded TeX source: {path}")

    text = "\n".join(sources.values())
    labels = Counter(re.findall(r"\\label\{([^}]+)\}", text))
    for label, count in labels.items():
        if count != 1:
            errors.append(f"Duplicate label: {label}")
    references = set(re.findall(r"\\(?:ref|eqref|pageref)\{([^}#]+)\}", text))
    references.update("note:" + name for name in re.findall(r"\\noteref\{([^}#]+)\}", text))
    for label in sorted(references - labels.keys()):
        errors.append(f"Unresolved reference: {label}")

    bibliography = Counter(re.findall(r"\\bibitem\{([^}]+)\}", text))
    for key, count in bibliography.items():
        if count != 1:
            errors.append(f"Duplicate bibliography key: {key}")
    citations = {key.strip() for group in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", text) for key in group.split(",")}
    for key in sorted(citations - bibliography.keys()):
        errors.append(f"Unresolved citation: {key}")

    for path, source in sources.items():
        if path.parent == root or root not in path.parents:
            continue
        if re.search(r"\\(?:documentclass|maketitle)|\\begin\{(?:document|thebibliography)\}", source):
            errors.append(f"Standalone document wrapper in {path}")
        if re.search(r"doc/research/zk_[\w]+\.py", source):
            errors.append(f"Obsolete audit path in {path}")
        if re.search(r"\\path\{zk-[^}]+\.tex\}", source):
            errors.append(f"External note reference in {path}")

    audits = {path.name: path for path in (root / "audits").glob("*.py")}
    imports = {}
    for name, path in audits.items():
        dependencies = set()
        for node in ast.walk(ast.parse(path.read_text(), filename=str(path))):
            if isinstance(node, ast.ImportFrom):
                modules = [node.module or ""]
            elif isinstance(node, ast.Import):
                modules = [alias.name for alias in node.names]
            else:
                continue
            dependencies.update(module.split(".")[0] + ".py" for module in modules if module.startswith("zk_"))
        imports[name] = dependencies
        for dependency in sorted(dependencies - audits.keys()):
            errors.append(f"Missing local import: {name} -> {dependency}")

    linked = set(re.findall(r"zk_[A-Za-z0-9_]+\.py", text))
    for name in sorted(linked - audits.keys()):
        errors.append(f"Missing audit source: {name}")
    reachable, pending = set(), list(linked)
    while pending:
        name = pending.pop()
        if name not in reachable:
            reachable.add(name)
            pending.extend(imports.get(name, ()))
    for name in sorted(audits.keys() - reachable):
        errors.append(f"Audit has no document or import reference: {name}")
    return errors, len(expected), len(audits)


if __name__ == "__main__":
    failures, tex_count, audit_count = check(Path(__file__).resolve().parent)
    if failures:
        raise SystemExit("\n".join(failures))
    print(f"OK: {tex_count} connected TeX sources, unique labels and citations, {audit_count} reachable audit modules.")
