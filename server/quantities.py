"""Key beam quantities, stationary points, and exact polynomial range certificates.

The course derivation compares end values, both sides of discontinuities, and
stationary points. Irrational stationary coordinates are isolated in rational
intervals. Separate Bernstein coefficient checks bound the entire piecewise
curve, including points that are not sampled or selected by the root finder.
"""
from functools import lru_cache
from math import comb

import sympy as sp

X = sp.Symbol("x")
FIELDS = {
    "M": ("Bending moment", "M", "kN m", 1, "V=0"),
    "V": ("Shear force", "V", "kN", 1, "w=0"),
    "N": ("Normal force", "N", "kN", 1, "N'=0"),
    "theta": ("Physical slope", r"\theta", "mrad", 1000, "M=0"),
    "v": ("Vertical displacement", "v", "mm", 1000, r"\theta=0"),
}


def bernstein_coefficients(expression, start, end):
    """Express p(start + (end-start)*t) in the degree-five Bernstein basis."""
    polynomial = sp.Poly(expression, X)
    powers = [
        (end - start)**j * sum(
            polynomial.nth(k) * comb(k, j) * start**(k-j)
            for k in range(j, 6)
        ) for j in range(6)
    ]
    return tuple(sum(powers[j] * sp.Rational(comb(i, j), comb(5, j))
                     for j in range(i + 1)) for i in range(6))


def stationary_points(expression, start, end):
    """Isolate all real derivative roots inside this open polynomial interval."""
    derivative = sp.Poly(sp.diff(expression, X), X)
    if derivative.is_zero or derivative.degree() == 0:
        return []
    roots = derivative.intervals(eps=(end-start)/10**10, inf=start, sup=end)
    simple_roots = sp.solve(derivative.as_expr(), X) if derivative.degree() <= 2 else []
    result = []
    for (lower, upper), multiplicity in roots:
        if upper <= start or lower >= end:
            continue
        midpoint = (lower + upper) / 2
        exact = lower if lower == upper else None
        if exact is None:
            # Simple radicals make the course derivation easier to recognise.
            # The certificate still uses rational enclosures, not rounded roots.
            for root in simple_roots:
                if root.is_real and bool(root > lower) and bool(root < upper):
                    exact = root
                    break
        result.append({"lower": lower, "upper": upper, "x": midpoint,
                       "exact": exact, "multiplicity": multiplicity})
    return result


@lru_cache(maxsize=160)
def curve_range(intervals):
    """Bound global signed extrema using exact coefficients and actual witnesses.

Each accepted cell covers a closed subinterval. Its Bernstein coefficients
enclose every polynomial value by the convex-hull property. Subdivision stops
when both global bounds are within the stated tolerance of evaluated points.
The returned cells and witness equalities are subsequently checked by Lean.
"""
    candidates, roots, partitions = [], [], []
    for index, (start, end, expression) in enumerate(intervals):
        local_roots = stationary_points(expression, start, end)
        cuts = {start, end}
        for root in local_roots:
            cuts.update((root["lower"], root["x"], root["upper"]))
            roots.append({**root, "piece": index, "derivative": sp.diff(expression, X)})
        cuts = sorted(point for point in cuts if start <= point <= end)
        for point in cuts:
            candidates.append({"piece": index, "x": point,
                               "value": expression.subs(X, point),
                               "side": "+" if point == start else "-" if point == end else ""})
        partitions.extend((index, a, b) for a, b in zip(cuts, cuts[1:]))
    minimum = min(candidates, key=lambda candidate: candidate["value"])
    maximum = max(candidates, key=lambda candidate: candidate["value"])
    tolerance = sp.Rational(1, 10**12) + max(abs(minimum["value"]), abs(maximum["value"])) / 10**8
    cells = []
    pending = list(partitions)
    while pending:
        index, start, end = pending.pop()
        expression = intervals[index][2]
        coefficients = bernstein_coefficients(expression, start, end)
        if (min(coefficients) >= minimum["value"] - tolerance
                and max(coefficients) <= maximum["value"] + tolerance):
            cells.append({"piece": index, "start": start, "end": end, "coefficients": coefficients})
        else:
            midpoint = (start + end) / 2
            pending.extend(((index, start, midpoint), (index, midpoint, end)))
        if len(cells) + len(pending) > 512:
            raise ValueError("The exact range certificate exceeded its subdivision limit. Simplify the loading or rescale the model.")
    cells.sort(key=lambda cell: (cell["piece"], cell["start"]))
    lower = min(min(cell["coefficients"]) for cell in cells)
    upper = max(max(cell["coefficients"]) for cell in cells)
    return {"minimum": minimum, "maximum": maximum, "lower": lower, "upper": upper,
            "tolerance": tolerance, "roots": roots, "cells": cells}


def point_locations(model, beam, section):
    """Collect named points, supports, actions, load boundaries, and the cut."""
    points = {}

    def add(position, label):
        points.setdefault(position, []).append(label)

    origin = next(node for node in model["nodes"] if node["id"] == model["members"][0]["a"])
    for node_index, node in enumerate(model["nodes"]):
        position = sp.Rational(str(node["x"])) - sp.Rational(str(origin["x"]))
        if 0 <= position <= beam.length and sp.Rational(str(node["y"])) == sp.Rational(str(origin["y"])):
            name, index = "", node_index + 1
            while index:
                index, remainder = divmod(index-1, 26)
                name = chr(65+remainder) + name
            add(position, f"Node {name}")
    add(beam.left, "Left support")
    add(beam.right, "Right support")
    add(beam.length / 2, "Midspan")
    add(section, "Selected section")
    for index, load in enumerate(model.get("loads", [])):
        add(sp.Rational(str(load["t"])) * beam.length, f"Load {index+1}" + (" start" if load["kind"] == "distributed" else ""))
        if load["kind"] == "distributed":
            add(sp.Rational(str(load["end"])) * beam.length, f"Load {index+1} end")
    return points


def key_quantities(model, beam, pieces, section, cert, equation, encode_number):
    """Build the presentation and append exact arithmetic claims to the certificate.

`equation` and `encode_number` are the worked-solution presentation and Lean
encoders. Keeping them explicit avoids a circular dependency on that module.
"""
    rat = encode_number
    summaries = []
    for field, (title, symbol, unit, scale, stationary_rule) in FIELDS.items():
        intervals = tuple((piece["start"], piece["end"], piece[field]) for piece in pieces)
        result = curve_range(intervals)
        group = f"range_{field}"
        lower, upper = result["lower"], result["upper"]
        for index, piece in enumerate(pieces):
            cells = [cell for cell in result["cells"] if cell["piece"] == index]
            breaks = [cells[0]["start"]] + [cell["end"] for cell in cells]
            name = f"{field}_breaks_{index}"
            cert.lines.append(f"def {name} : List Rat := [" + ", ".join(rat(x) for x in breaks) + "]")
            cert.prove(group, f"{name}.head? = some {rat(piece['start'])} ∧ {name}.getLast? = some {rat(piece['end'])} ∧ (({name}.zip ({name}.drop 1)).all (fun ab => ab.1 < ab.2)) = true")
            for cell_index, cell in enumerate(cells):
                coefficients = "[" + ", ".join(rat(value) for value in cell["coefficients"]) + "]"
                # Both the basis conversion and inequalities are recomputed by
                # Lean. The coverage statement prevents an omitted interval.
                cert.prove(group, f"affineCompose {field}{index} (coefficient {name} {cell_index}) (coefficient {name} {cell_index+1}) = bernstein5 {coefficients} ∧ ({coefficients}.all (fun c => {rat(lower)} ≤ c && c ≤ {rat(upper)})) = true")
        for which in ("minimum", "maximum"):
            witness = result[which]
            cert.prove(group, f"value {field}{witness['piece']} {rat(witness['x'])} = {rat(witness['value'])}")
        cert.prove(group, f"{rat(result['minimum']['value']-lower)} ≤ {rat(result['tolerance'])} ∧ {rat(upper-result['maximum']['value'])} ≤ {rat(result['tolerance'])}")

        roots = []
        for root in result["roots"]:
            if root["lower"] == root["upper"]:
                cert.prove(group, f"value (D {field}{root['piece']}) {rat(root['x'])} = 0")
            roots.append({
                "interval": root["piece"] + 1,
                "equation": equation("Stationary equation", root["derivative"], "", "0"),
                "coordinateLatex": sp.latex(root["exact"]) if root["exact"] is not None else None,
                "lower": str(root["lower"]), "upper": str(root["upper"]),
                "approx": float(root["x"]),
                "candidateValue": float(scale * pieces[root["piece"]][field].subs(X, root["x"])),
                "valueLatex": sp.latex(scale * pieces[root["piece"]][field].subs(X, root["exact"])) if root["exact"] is not None else None,
            })
        extrema = []
        for which in ("minimum", "maximum", "absolute"):
            if which == "absolute":
                witness = max((result["minimum"], result["maximum"]), key=lambda point: abs(point["value"]))
                low, high = abs(witness["value"]), max(abs(lower), abs(upper))
            else:
                witness = result[which]
                low = lower if which == "minimum" else witness["value"]
                high = witness["value"] if which == "minimum" else upper
            # A coordinate is a representative point for a constant segment.
            # A nonzero enclosure width is never presented as an exact maximum.
            expression = pieces[witness["piece"]][field]
            plateau = sp.diff(expression, X) == 0
            exact_position = bool(witness["side"]) or any(
                root["lower"] == root["upper"] == witness["x"] for root in result["roots"]
            )
            coordinate = sp.latex(witness["x"]) + (rf"^{{{witness['side']}}}" if witness["side"] else "")
            extrema.append({
                "kind": which, "value": float(scale * (low+high)/2),
                "lower": str(scale*low), "upper": str(scale*high), "exact": low == high,
                "x": str(witness["x"]), "xApprox": float(witness["x"]), "side": witness["side"],
                "xExact": exact_position,
                "piece": witness["piece"] + 1, "plateau": plateau,
                "substitution": equation("Value at comparison point", expression.subs(X, witness["x"]) * scale, unit,
                                         rf"{symbol}({coordinate})"),
            })
        summaries.append({"field": field, "title": title, "symbol": symbol, "unit": unit,
                          "stationaryRule": stationary_rule, "extrema": extrema,
                          "roots": roots, "cells": len(result["cells"]), "group": group})

    points = []
    for position, labels in sorted(point_locations(model, beam, section).items()):
        # At a jump, retain both physical faces instead of averaging samples.
        adjacent = [(index, piece) for index, piece in enumerate(pieces)
                    if piece["start"] <= position <= piece["end"]]
        for index, piece in adjacent:
            side = "+" if position == piece["start"] else "-" if position == piece["end"] else ""
            values, substitutions = {}, []
            for field, (_, symbol, unit, scale, _) in FIELDS.items():
                value = piece[field].subs(X, position)
                cert.prove("key_points", f"value {field}{index} {rat(position)} = {rat(value)}")
                values[field] = float(scale * value)
                coordinate = sp.latex(position) + (rf"^{{{side}}}" if side else "")
                substituted = sp.latex(piece[field]).replace("x", rf"\left({sp.latex(position)}\right)")
                substitutions.append(equation("Point substitution", scale*value, unit,
                    rf"{symbol}({coordinate})=" + ("1000" if scale == 1000 else "") + rf"\left({substituted}\right)"))
            points.append({"labels": labels, "x": str(position), "xApprox": float(position),
                           "side": side, "piece": index+1, "values": values, "substitutions": substitutions})
    return {"summaries": summaries, "points": points}
