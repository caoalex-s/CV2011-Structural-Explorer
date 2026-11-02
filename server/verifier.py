"""Exact reaction, section-force, and displacement checks for guided beams.

Accepted models have one horizontal prismatic beam, one pin, and one vertical
roller. The browser frame solver is an independent numerical implementation.
All model numbers enter SymPy as decimal rationals. User expressions are parsed
through a bounded arithmetic AST, never eval, sympify, or parse_expr.
"""
import ast
import math
from dataclasses import dataclass

import sympy as sp

VERSION = "beam-exact-1"


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError("Model values must be numbers.")
    if not math.isfinite(value) or abs(value) > 1e10:
        raise ValueError("Model value outside the supported finite range.")
    return sp.Rational(str(value))


def parse_arithmetic(text):
    """Evaluate a short arithmetic expression using exact rational operations."""
    if not isinstance(text, str) or len(text) > 200:
        raise ValueError("Use an arithmetic expression of at most 200 characters.")
    text = text.replace("−", "-").replace("^", "**")
    tree = ast.parse(text, mode="eval")
    if sum(1 for _ in ast.walk(tree)) > 80:
        raise ValueError("Expression is too complex.")

    def visit(node, depth=0):
        if depth > 15:
            raise ValueError("Expression nesting is too deep.")
        if isinstance(node, ast.Constant) and type(node.value) in (int, float):
            return rational(node.value)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            value = visit(node.operand, depth + 1)
            return -value if isinstance(node.op, ast.USub) else value
        if isinstance(node, ast.BinOp):
            left = visit(node.left, depth + 1)
            right = visit(node.right, depth + 1)
            if isinstance(node.op, ast.Add):
                result = left + right
            elif isinstance(node.op, ast.Sub):
                result = left - right
            elif isinstance(node.op, ast.Mult):
                result = left * right
            elif isinstance(node.op, ast.Div) and right != 0:
                result = left / right
            elif isinstance(node.op, ast.Pow) and right.is_Integer and abs(right) <= 8:
                if left == 0 and right < 0:
                    raise ValueError("Division by zero.")
                result = left ** right
            else:
                raise ValueError("Use +, -, *, /, parentheses, and integer powers from -8 to 8.")
            if len(str(result)) > 600:
                raise ValueError("Expression produces excessively large numbers.")
            return result
        raise ValueError("Only numbers and arithmetic operations are supported.")

    return visit(tree.body)


@dataclass
class BeamReference:
    length: object
    left: object
    right: object
    rigidity: object
    forces: list
    couples: list
    distributions: list
    reaction_left: object
    reaction_right: object
    reaction_horizontal: object
    pin_location: object
    total_vertical: object
    total_moment: object

    def displacement_base(self, x):
        """Double integral of M/EI before the two integration constants."""
        positive = lambda location, power: max(x - location, sp.S.Zero) ** power
        value = self.reaction_left * positive(self.left, 3) / 6
        value += self.reaction_right * positive(self.right, 3) / 6
        for location, _, fy in self.forces:
            value += fy * positive(location, 3) / 6
        for location, moment in self.couples:
            value -= moment * positive(location, 2) / 2
        for start, end, q0, q1 in self.distributions:
            slope = (q1 - q0) / (end - start)
            value += q0 * positive(start, 4) / 24 + slope * positive(start, 5) / 120
            value -= q1 * positive(end, 4) / 24 + slope * positive(end, 5) / 120
        return value / self.rigidity

    def values(self, x):
        # At the beam end report the left-hand limit; elsewhere use the right.
        active = lambda location: x > location or (x == location and x != self.length)
        normal = -self.reaction_horizontal if active(self.pin_location) else sp.S.Zero
        shear = sum(reaction for location, reaction in
                    [(self.left, self.reaction_left), (self.right, self.reaction_right)] if active(location))
        moment = sum(reaction * (x - location) for location, reaction in
                     [(self.left, self.reaction_left), (self.right, self.reaction_right)] if active(location))
        for location, fx, fy in self.forces:
            if active(location):
                normal -= fx
                shear += fy
                moment += fy * (x - location)
        for location, applied in self.couples:
            if active(location):
                moment -= applied
        for start, end, q0, q1 in self.distributions:
            length = max(sp.S.Zero, min(x, end) - start)
            slope = (q1 - q0) / (end - start)
            resultant = q0 * length + slope * length ** 2 / 2
            first_moment = q0 * length ** 2 / 2 + slope * length ** 3 / 3
            shear += resultant
            moment += (x - start) * resultant - first_moment
        slope_constant = -(self.displacement_base(self.right) - self.displacement_base(self.left)) / (self.right - self.left)
        displacement_constant = -self.displacement_base(self.left) - slope_constant * self.left
        displacement = self.displacement_base(x) + slope_constant * x + displacement_constant
        return {"reaction_left": self.reaction_left, "reaction_right": self.reaction_right,
                "normal": normal, "shear": shear, "moment": moment, "deflection": displacement * 1000}


def reference(model):
    if not isinstance(model, dict) or len(model.get("members", [])) != 1 or len(model.get("supports", [])) != 2:
        raise ValueError("Guided verification requires one beam and two supports.")
    member = model["members"][0]
    nodes = {node["id"]: node for node in model.get("nodes", [])}
    a, b = nodes[member["a"]], nodes[member["b"]]
    if rational(a["y"]) != rational(b["y"]) or rational(b["x"]) <= rational(a["x"]):
        raise ValueError("Draw a horizontal beam from left to right for guided verification.")
    length = rational(b["x"]) - rational(a["x"])
    rigidity = rational(member["EI"])
    if rigidity <= 0 or rational(member["EA"]) <= 0:
        raise ValueError("Rigidity must be positive.")
    supports = sorted(model["supports"], key=lambda support: support["t"])
    if sorted(s["kind"] for s in supports) != ["pin", "roller"]:
        raise ValueError("Use one pin and one vertical roller.")
    for support in supports:
        if support["member"] != member["id"] or not 0 <= rational(support["t"]) <= 1:
            raise ValueError("Support must lie on the beam.")
        if support["kind"] == "roller" and rational(support["angle"]) != 90:
            raise ValueError("Guided verification currently requires a vertical roller reaction.")
    left, right = [rational(s["t"]) * length for s in supports]
    if right <= left:
        raise ValueError("The supports must be distinct.")
    pin_location = next(rational(s["t"]) * length for s in supports if s["kind"] == "pin")
    forces, couples, distributions = [], [], []
    total_horizontal = total_vertical = total_moment = sp.S.Zero
    if len(model.get("loads", [])) > 50:
        raise ValueError("Use at most 50 loads for guided verification.")
    for load in model.get("loads", []):
        if load["member"] != member["id"] or not 0 <= rational(load["t"]) <= 1:
            raise ValueError("Load must lie on the beam.")
        location = rational(load["t"]) * length
        if load["kind"] == "force":
            fx, fy = rational(load["fx"]), rational(load["fy"])
            forces.append((location, fx, fy))
            total_horizontal += fx
            total_vertical += fy
            total_moment += location * fy
        elif load["kind"] == "moment":
            moment = rational(load["mz"])
            couples.append((location, moment))
            total_moment += moment
        elif load["kind"] == "distributed":
            end = rational(load["end"]) * length
            if not location < end <= length:
                raise ValueError("Distributed-load interval must have positive length.")
            q0, q1 = rational(load["fy"]), rational(load["qEnd"])
            interval = end - location
            resultant = (q0 + q1) * interval / 2
            local_first_moment = interval ** 2 * (q0 + 2 * q1) / 6
            total_vertical += resultant
            total_moment += location * resultant + local_first_moment
            distributions.append((location, end, q0, q1))
        else:
            raise ValueError("Unknown load type.")
    reaction_right = (-total_moment + total_vertical * left) / (right - left)
    reaction_left = -total_vertical - reaction_right
    beam = BeamReference(length, left, right, rigidity, forces, couples, distributions,
                         reaction_left, reaction_right, -total_horizontal, pin_location,
                         total_vertical, total_moment)
    # Exact identities provide per-instance checks independent of the numerical solver.
    assert sp.simplify(reaction_left + reaction_right + total_vertical) == 0
    assert sp.simplify(reaction_left * left + reaction_right * right + total_moment) == 0
    assert sp.simplify(beam.values(left)["deflection"]) == 0
    assert sp.simplify(beam.values(right)["deflection"]) == 0
    return beam


UNITS = {"reaction_left": "kN", "reaction_right": "kN", "normal": "kN", "shear": "kN", "moment": "kN m", "deflection": "mm"}
CONVERSIONS = {("N", "kN"): sp.Rational(1, 1000), ("N m", "kN m"): sp.Rational(1, 1000), ("m", "mm"): sp.Integer(1000)}


def check(payload):
    step = payload.get("step")
    if step not in UNITS:
        raise ValueError("Unknown solution step.")
    beam = reference(payload["model"])
    section = rational(payload.get("section", 0.5))
    if not 0 <= section <= 1:
        raise ValueError("Section must lie on the beam.")
    expected = beam.values(section * beam.length)[step]
    try:
        supplied = parse_arithmetic(payload.get("answer", ""))
    except (ValueError, SyntaxError, OverflowError, ZeroDivisionError) as error:
        return {"status": "unresolved", "category": "expression_not_understood", "message": str(error), "verifier": VERSION}
    unit = payload.get("units", "")
    if unit == UNITS[step]:
        factor = sp.S.One
    elif (unit, UNITS[step]) in CONVERSIONS:
        factor = CONVERSIONS[(unit, UNITS[step])]
    else:
        return {"status": "incorrect", "category": "unit_dimension", "message": f"This quantity requires {UNITS[step]} or a compatible unit.", "verifier": VERSION}
    value = supplied * factor
    difference = sp.simplify(value - expected)
    tolerance = max(0.00001, abs(float(expected)) * 0.001)
    if difference == 0:
        return {"status": "correct", "category": "exact_equivalence", "message": "Your expression equals the reference value exactly. Equilibrium and support displacement conditions were checked with exact arithmetic.", "verifier": VERSION}
    if abs(float(difference)) <= tolerance:
        return {"status": "correct", "category": "rounded_value", "message": "Your value agrees within the rounding tolerance (0.1% with a small absolute tolerance). The reference solution was checked with exact arithmetic.", "verifier": VERSION}
    if expected != 0 and abs(float(value + expected)) <= tolerance:
        category, message = "opposite_sign", "The magnitude is consistent with the reference, but the sign is reversed. Check the stated force or displacement convention."
    elif expected != 0 and any(abs(float(value - expected * scale)) <= tolerance * max(1, float(scale)) for scale in (sp.Integer(1000), sp.Rational(1, 1000))):
        category, message = "factor_of_1000", "The answer differs by a factor of 1000. Check the numerical value together with the selected unit."
    else:
        category, message = "equilibrium_or_calculation" if step != "deflection" else "displacement_calculation", "The submitted value does not satisfy this step. Check the free body, load locations, and arithmetic. A value alone does not identify a unique cause."
    return {"status": "incorrect", "category": category, "message": message, "verifier": VERSION}


def solution(payload):
    beam = reference(payload["model"])
    section = rational(payload.get("section", 0.5))
    if not 0 <= section <= 1:
        raise ValueError("Section must lie on the beam.")
    step = payload["step"]
    if step not in UNITS:
        raise ValueError("Unknown solution step.")
    x = section * beam.length
    values = beam.values(x)
    show = lambda value: f"{value} = {float(value):.6g}" if not sp.Rational(value).is_Integer else str(value)
    lines = [f"Beam coordinates: 0 ≤ x ≤ {beam.length} m.",
             f"Supports: a = {beam.left} m, b = {beam.right} m.",
             "Upward forces and counterclockwise applied moments are positive.",
             f"Σ applied Fy = F = {beam.total_vertical} kN.",
             f"Σ applied moment about x = 0: T = {beam.total_moment} kN m.",
             "Σ Fy = 0: RA + RB + F = 0.",
             "Σ Ma = 0: RB (b − a) + T − F a = 0.",
             f"RB = (F a − T)/(b − a) = {show(beam.reaction_right)} kN.",
             f"RA = −F − RB = {show(beam.reaction_left)} kN."]
    if step in ("normal", "shear", "moment", "deflection"):
        lines += [f"Selected section: x = {x} m.",
                  "For the left free body: N = −Σ Fx; V = Σ Fy.",
                  "M = Σ(Fy (x − x_load)) − Σ applied couples.",
                  "Include loads to the left of the cut and integrate only the loaded portion."]
        for location, fx, fy in beam.forces:
            if location <= x:
                lines.append(f"Point force at {location} m: Fx = {fx}, Fy = {fy} kN; lever arm = {x-location} m.")
        for start, end, q0, q1 in beam.distributions:
            active_length = max(sp.S.Zero, min(x, end) - start)
            lines.append(f"Distributed load [{start}, {end}] m: integrate q(s) = {q0} + ({q1-q0}) (s−{start})/({end-start}) over {active_length} m left of the cut.")
        lines.append(f"{step} = {show(values[step])} {UNITS[step]}.")
    if step == "deflection":
        lines += ["EI v″(x) = M(x). Integrate twice with continuous v and v′.",
                  "Let B(x) be the twice-integrated M(x)/EI with zero integration constants.",
                  "C1 = −(B(b) − B(a))/(b − a); C0 = −B(a) − C1 a.",
                  "v(x) = B(x) + C1 x + C0. These constants impose v(a) = v(b) = 0.",
                  f"v({x}) = {show(values[step])} mm."]
    return {"lines": lines, "verification": "SymPy exact checks: vertical and moment equilibrium, and zero displacement at both supports. Lean scope: the reaction-numerator identities in the proof library; see verification status.", "verifier": VERSION}
