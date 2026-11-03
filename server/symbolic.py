"""Load-labelled beam algebra before numerical substitution.

The drawn ratios x/L and action directions define a family of similar beams.
Load amplitudes, L, and EI remain symbolic. Exact substitution checks connect
every displayed expression to the existing per-instance Lean certificate.
This module does not claim a universally quantified Lean proof of that family.
"""
from dataclasses import replace

import sympy as sp

from server.verifier import rational


def attach_symbolic_derivation(model, beam, numeric_pieces, section, result):
    """Add symbolic expressions to the existing numeric rows without changing them."""
    # Import at call time: worked owns the polynomial operations and calls this
    # presentation layer only after constructing its numerical certificate.
    from server.worked import (
        X, at, build_polynomials, equation, integrate_pieces,
        integration_constants, require_zero,
    )

    length, rigidity = sp.symbols("L EI", positive=True)
    substitutions = {length: beam.length, rigidity: beam.rigidity}
    display_names = {rigidity: "EI"}
    parameters = [equation("Beam length", beam.length, "m", "L"),
                  equation("Flexural rigidity", beam.rigidity, "kN m²", "EI")]
    load_parameters = []

    def latex(expression):
        return sp.latex(sp.factor(expression), symbol_names=display_names)

    def attach(row, expression, label=None):
        # Refuse a symbolic line that does not reproduce the certified numeric
        # polynomial. This check includes signs, units, and all coefficients.
        require_zero(sp.cancel(expression.subs(substitutions) - sp.sympify(row["exact"])))
        # Keep familiar SI formulas (for example -P*L^3/(48*EI)). Convert the
        # numerical readout separately instead of reducing 1000/48 to 125/6.
        conversion = 1000 if row["unit"] in ("mm", "mrad") else 1
        row["symbolicLatex"] = latex(expression/conversion)
        row["symbolicExact"] = str(expression)
        if conversion != 1:
            row["symbolicUnit"] = "m" if row["unit"] == "mm" else "rad"
        if label is not None:
            row["symbolicLabelLatex"] = label

    def parameter(index, value, unit, component=""):
        symbol = sp.Symbol(f"load{index}{component}")
        token = rf"\loadsymbol{{{index}}}{{{component}}}"
        substitutions[symbol] = value
        display_names[symbol] = token
        load_parameters[index].append(symbol)
        parameters.append(equation("Load parameter", value, unit, token))
        return symbol

    # 1. Establish a unit-length beam. Its moments have force units because
    # physical moments are recovered by multiplying by L. Distributed actions
    # therefore enter as w*L, and applied couples enter as M/L.
    forces, couples, distributions = [], [], []
    for index, load in enumerate(model.get("loads", [])):
        load_parameters.append([])
        start = rational(load["t"])
        if load["kind"] == "force":
            fx, fy = rational(load["fx"]), rational(load["fy"])
            if fx != 0 and fy != 0:
                horizontal = parameter(index, fx, "kN", "x")
                vertical = parameter(index, fy, "kN", "y")
            elif fx != 0:
                horizontal = sp.sign(fx) * parameter(index, abs(fx), "kN")
                vertical = sp.S.Zero
            else:
                horizontal = sp.S.Zero
                vertical = (1 if fy > 0 else -1) * parameter(index, abs(fy), "kN")
            forces.append((start, horizontal, vertical))
        elif load["kind"] == "moment":
            moment = rational(load["mz"])
            amplitude = parameter(index, abs(moment), "kN m")
            couples.append((start, (1 if moment >= 0 else -1) * amplitude / length))
        else:
            end = rational(load["end"])
            first, last = -rational(load["fy"]), -rational(load["qEnd"])
            if first == last:
                initial = final = parameter(index, first, "kN/m")
            else:
                initial = parameter(index, first, "kN/m", "a")
                final = parameter(index, last, "kN/m", "b")
            distributions.append((start, end, -initial * length, -final * length))

        # Coordinates use the same label as the associated action. The a/b
        # subscripts on a varying intensity refer to its start/end values.
        token = rf"\loadsymbol{{{index}}}{{}}"
        coordinates = [(start, rf"x_{{{token}}}")]
        if load["kind"] == "distributed":
            coordinates = [(start, rf"x_{{{token},a}}"), (end, rf"x_{{{token},b}}")]
        for fraction, label in coordinates:
            row = equation("Load coordinate", fraction * beam.length, "m", label)
            attach(row, fraction * length)
            parameters.append(row)

    left, right = beam.left / beam.length, beam.right / beam.length
    horizontal = sum((force[1] for force in forces), sp.S.Zero)
    vertical = sum((force[2] for force in forces), sp.S.Zero)
    moment = sum((force[0] * force[2] for force in forces), sp.S.Zero)
    moment += sum((couple[1] for couple in couples), sp.S.Zero)
    for start, end, q0, q1 in distributions:
        resultant = (q0 + q1) * (end - start) / 2
        vertical += resultant
        moment += start * resultant + (end - start) ** 2 * (q0 + 2 * q1) / 6
    reaction_right = (left * vertical - moment) / (right - left)
    normalized = replace(
        beam, length=sp.S.One, left=left, right=right, rigidity=sp.S.One,
        forces=forces, couples=couples, distributions=distributions,
        reaction_right=reaction_right, reaction_left=-vertical-reaction_right,
        reaction_horizontal=-horizontal, pin_location=beam.pin_location/beam.length,
        total_vertical=vertical, total_moment=moment,
    )
    normalized_pieces, _, _, _ = build_polynomials(normalized)
    require_zero(sp.cancel(normalized.reaction_left + normalized.reaction_right + vertical))
    require_zero(sp.cancel(left*normalized.reaction_left + right*normalized.reaction_right + moment))
    require_zero(sp.cancel(at(normalized_pieces, "v", left)))
    require_zero(sp.cancel(at(normalized_pieces, "v", right)))
    for name, fraction in [("a", left), ("b", right), ("x_s", section/beam.length)]:
        row = equation("Coordinate", fraction * beam.length, "m", name)
        attach(row, fraction * length)
        parameters.append(row)

    # 2. Restore physical x and units before presenting the expressions.
    scales = {"q": 1/length, "N": 1, "V": 1, "M": length,
              "theta": length**2/rigidity, "v": length**3/rigidity}
    physical_pieces = []
    for piece in normalized_pieces:
        physical = {field: sp.expand(piece[field].subs(X, X/length) * scale)
                    for field, scale in scales.items()}
        physical["start"], physical["end"] = piece["start"] * length, piece["end"] * length
        physical_pieces.append(physical)
    for row, expression in zip(result["equilibrium"], [
        horizontal, vertical, length * moment, reaction_right,
        normalized.reaction_left, normalized.reaction_horizontal,
    ]):
        attach(row, expression)

    for index, (physical, numeric, displayed) in enumerate(zip(physical_pieces, numeric_pieces, result["pieces"])):
        require_zero(sp.cancel(sp.diff(physical["V"], X)-physical["q"]))
        require_zero(sp.cancel(sp.diff(physical["M"], X)-physical["V"]))
        require_zero(sp.cancel(sp.diff(physical["v"], X)-physical["theta"]))
        require_zero(sp.cancel(rigidity*sp.diff(physical["theta"], X)-physical["M"]))
        if index:
            for field in ("theta", "v"):
                jump = physical[field]-physical_pieces[index-1][field]
                require_zero(sp.cancel(jump.subs(X, physical["start"])))
        # Also verify the full physical field independently of its display row.
        for field in scales:
            require_zero(sp.cancel(physical[field].subs(substitutions) - numeric[field]))
        displayed["intervalLatex"] = f"{latex(physical['start'])}<x<{latex(physical['end'])}"
        for row, field in zip(displayed["forces"], ["q", "N", "V", "M"]):
            attach(row, -physical[field] if field == "q" else physical[field])
        first, second, rotation_constant, displacement_constant = integration_constants(physical, rigidity)
        c_rotation, c_displacement = sp.symbols(f"C_{2*index+1} C_{2*index+2}")
        attach(displayed["integrations"][0], first+c_rotation)
        attach(displayed["integrations"][1], second+c_rotation*X+c_displacement)
        attach(result["constants"][2*index], rotation_constant)
        attach(result["constants"][2*index+1], displacement_constant)
        for row, field in zip(displayed["displacements"], ["theta", "v"]):
            attach(row, physical[field])

    section_fraction = section / beam.length
    def selected(field, location=section_fraction):
        return at(normalized_pieces, field, location) * scales[field]

    for row, field in zip(result["selected"], ["N", "V", "M", "theta", "v"]):
        attach(row, selected(field) * (1000 if field == "v" else 1),
               (r"\theta" if field == "theta" else field) + "(x_s)")
    attach(result["thetaLeft"], selected("theta", left))

    # 3. Preserve the course-method routes, including their intermediate terms.
    area_index = 0
    for target in (right, section_fraction):
        for weighted in (False, True):
            terms = integrate_pieces(normalized_pieces, left, target, weighted)
            scale = length**(3 if weighted else 2) / rigidity
            row = result["momentArea"][area_index]
            for displayed, (_, _, _, direction, value) in zip(row["terms"], terms):
                attach(displayed, direction * value * scale)
            attach(row["equation"], sum((d*v for _, _, _, d, v in terms), sp.S.Zero) * scale)
            area_index += 1

    virtual_right = (section_fraction-left)/(right-left)
    virtual_left = 1-virtual_right
    virtual_actions = [(left, virtual_left), (right, virtual_right), (section_fraction, -1)]
    for row, expression in zip(result["virtual"]["reactions"], [virtual_left, virtual_right]):
        attach(row, expression)
    virtual_index = 0
    for piece in normalized_pieces:
        breaks = sorted({piece["start"], piece["end"], max(piece["start"], min(section_fraction, piece["end"]))})
        for start, end in zip(breaks, breaks[1:]):
            midpoint = (start+end)/2
            virtual_moment = sum((fy*(X-location) for location, fy in virtual_actions if location < midpoint), sp.S.Zero)
            value = sp.integrate(sp.expand(virtual_moment*piece["M"]), (X, start, end)) * length**3/rigidity
            row = result["virtual"]["rows"][virtual_index]
            row["intervalLatex"] = f"{latex(start*length)}<x<{latex(end*length)}"
            attach(row["equations"][0], length*virtual_moment.subs(X, X/length))
            integral_label = rf"\int_{{{latex(start*length)}}}^{{{latex(end*length)}}}\frac{{m(x)M(x)}}{{EI}}\,\mathrm{{d}}x"
            attach(row["equations"][1], value, integral_label)
            virtual_index += 1
    attach(result["virtual"]["result"], -1000 * selected("v"))
    for index, row in enumerate(result["superposition"]):
        other_loads = {symbol: 0 for i, symbols in enumerate(load_parameters) if i != index for symbol in symbols}
        token = rf"\loadsymbol{{{index}}}{{}}"
        row["labelLatex"] = rf"v^{{({token})}}(x_s)"
        attach(row, 1000 * selected("v").subs(other_loads))

    # Point substitutions stay parametric. Extrema and their locations describe
    # the current loads only: changing amplitudes may change the governing point.
    from server.quantities import FIELDS
    for point in result["quantities"]["points"]:
        coordinate = sp.Rational(point["x"]) / beam.length * length
        piece = physical_pieces[point["piece"]-1]
        for row, (field, (_, symbol, _, scale, _)) in zip(point["substitutions"], FIELDS.items()):
            side = rf"^{{{point['side']}}}" if point["side"] else ""
            label = rf"{symbol}\left({latex(coordinate)}{side}\right)"
            attach(row, scale * piece[field].subs(X, coordinate), label)
    for summary in result["quantities"]["summaries"]:
        field = summary["field"]
        _, symbol, _, scale, _ = FIELDS[field]
        for root in summary["roots"]:
            attach(root["equation"], sp.diff(physical_pieces[root["interval"]-1][field], X))
        for extremum in summary["extrema"]:
            coordinate = sp.Rational(extremum["x"]) / beam.length * length
            expression = physical_pieces[extremum["piece"]-1][field].subs(X, coordinate) * scale
            attach(extremum["substitution"], expression, rf"{symbol}\left({latex(coordinate)}\right)")

    result["parameters"] = parameters
    result["symbolicScope"] = (
        "The symbolic formulas retain the labelled load amplitudes, beam length L, and flexural rigidity EI. "
        "Take L>0 and EI>0. Relative positions x/L follow the drawing. Symbolic displacement and rotation use metres and radians. "
        "For a single-axis force or couple, its symbol is the magnitude in the drawn direction. "
        "A zero force or couple uses a downward or counterclockwise reference direction, respectively. "
        "An inclined force uses signed rightward/upward components. Distributed intensity is positive downward, "
        "with subscripts a and b denoting its start and end values. "
        "SymPy checks parametric equilibrium, polynomial differential relations, support conditions, and continuity. "
        "It also checks each displayed symbolic expression against the current numerical polynomial after substitution. "
        "The Lean certificate checks that substituted model and section, not a theorem for all parameter values."
    )
