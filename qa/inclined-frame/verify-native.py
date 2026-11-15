"""Cross-check native returned intervals against independent beam/statics formulas.

Usage: python qa/inclined-frame/verify-native.py NATIVE_LOG
Uses 90-digit Decimal references, not the matrix assembler or packet producer.
The tiny reference-rounding allowance is numerical test precision, not a proof
or a replacement for the compiled containment/accuracy theorems.
"""
from decimal import Decimal, getcontext
from pathlib import Path
import re
import sys

getcontext().prec = 90
D = Decimal
ZERO = D(0)
EA, EI = D(2000000), D(20000)
LENGTH = D(5).sqrt()
COSINE, SINE = 1 / LENGTH, 2 / LENGTH


def arctangent(value):
    """Alternating power series, used only to obtain an independent pi value."""
    total = ZERO
    power = value
    for index in range(1000):
        term = power / (2 * index + 1)
        total += term if index % 2 == 0 else -term
        if abs(term) < D('1e-85'):
            return total
        power *= value * value
    raise AssertionError('Reference series did not converge')


def roller_normal():
    pi = 16 * arctangent(D(1) / 5) - 4 * arctangent(D(1) / 239)
    angle = 37 * pi / 180
    sine, cosine = angle, D(1)
    sine_term, cosine_term = angle, D(1)
    for index in range(1, 100):
        sine_term *= -angle * angle / ((2 * index) * (2 * index + 1))
        cosine_term *= -angle * angle / ((2 * index - 1) * (2 * index))
        sine += sine_term
        cosine += cosine_term
    return cosine, sine


def cantilever(scale=1):
    """Tip force resolved in member axes; integrated axial and bending strains."""
    length = scale * LENGTH
    axial_force = -11 / LENGTH
    transverse_force = -13 / LENGTH
    axial = axial_force * length / EA
    transverse = transverse_force * length ** 3 / (3 * EI)
    rotation = transverse_force * length ** 2 / (2 * EI)
    fields = [axial_force, -transverse_force, ZERO, rotation,
              COSINE * axial - SINE * transverse, SINE * axial + COSINE * transverse]
    reactions = [D(-3), D(7), D(13 * scale)] + [ZERO] * (3 * scale)
    return fields, reactions


def affine():
    """Zero-resultant affine load: statics fixes the sole base moment."""
    x = LENGTH / 2
    p, q = -5 * SINE, -5 * COSINE
    dp, dq = 10 * SINE / LENGTH, 10 * COSINE / LENGTH
    base_moment = -5 * LENGTH / 6
    axial = (-p * x ** 2 / 2 - dp * x ** 3 / 6) / EA
    transverse = (-base_moment * x ** 2 / 2 + q * x ** 4 / 24 + dq * x ** 5 / 120) / EI
    fields = [-p * x - dp * x ** 2 / 2, q * x + dq * x ** 2 / 2,
              -base_moment + q * x ** 2 / 2 + dq * x ** 3 / 6,
              (-base_moment * x + q * x ** 3 / 6 + dq * x ** 4 / 24) / EI,
              COSINE * axial - SINE * transverse, SINE * axial + COSINE * transverse]
    return fields, [ZERO, ZERO, base_moment, ZERO, ZERO, ZERO]


def roller(right):
    """Global moment equilibrium and exact roller compatibility determine motion."""
    normal_x, normal_y = roller_normal()
    magnitude = D('6.5') / (normal_y - 2 * normal_x)
    bx, by = magnitude * normal_x, magnitude * normal_y
    ax, ay = -3 - bx, 7 - by
    axial_reaction = COSINE * ax + SINE * ay
    shear_reaction = -SINE * ax + COSINE * ay
    axial_force, transverse_force = -11 / LENGTH, -13 / LENGTH
    cut = LENGTH / 2
    axial_tip = -(axial_reaction * LENGTH + axial_force * (LENGTH - cut)) / EA
    normal_axial = COSINE * normal_x + SINE * normal_y
    normal_transverse = -SINE * normal_x + COSINE * normal_y
    transverse_tip = -normal_axial * axial_tip / normal_transverse
    rotation_start = (transverse_tip - shear_reaction * LENGTH ** 3 / (6 * EI)
                      - transverse_force * (LENGTH - cut) ** 3 / (6 * EI)) / LENGTH
    axial = -axial_reaction * cut / EA
    transverse = rotation_start * cut + shear_reaction * cut ** 3 / (6 * EI)
    fields = [-axial_reaction - (axial_force if right else 0),
              shear_reaction + (transverse_force if right else 0), shear_reaction * cut,
              rotation_start + shear_reaction * cut ** 2 / (2 * EI),
              COSINE * axial - SINE * transverse, SINE * axial + COSINE * transverse]
    return fields, [ax, ay, ZERO, bx, by, ZERO, ZERO, ZERO, ZERO]


def read_interval(text):
    values = []
    for endpoint in text.split(','):
        numerator, denominator = endpoint.split('/')
        values.append(D(numerator) / D(denominator))
    assert len(values) == 2 and values[0] <= values[1]
    return values


references = {
    'irrational-cantilever': cantilever(), 'reversed-cantilever': cantilever(),
    'shared-rigid-joint': cantilever(2), 'affine-zero-resultant': affine(),
    'roller-interior-left': roller(False), 'roller-interior-right': roller(True),
}
observed = {}
current = None
for line in Path(sys.argv[1]).read_text().splitlines():
    match = re.fullmatch(r'case=(\S+) accepted=(true|false) expected=(true|false) elapsed_ms=(\d+)', line)
    if match:
        current = match[1]
        assert match[2] == match[3], line
        if current in references:
            assert match[2] == 'true' and current not in observed
            observed[current] = ([], [])
    elif line.startswith('field='):
        assert current in references
        entry = re.fullmatch(r'field=(\d+) interval=(\S+)', line)
        assert entry and int(entry[1]) == len(observed[current][0]), line
        observed[current][0].append(read_interval(entry[2]))
    elif line.startswith('point='):
        assert current in references
        entry = re.fullmatch(r'point=(\d+) direction=(\d+) interval=(\S+)', line)
        position = len(observed[current][1])
        assert entry and (int(entry[1]), int(entry[2])) == (position // 3, position % 3), line
        observed[current][1].append(read_interval(entry[3]))
assert set(observed) == set(references), 'Missing native positive case'
for name, groups in references.items():
    for expected, intervals in zip(groups, observed[name], strict=True):
        assert len(expected) == len(intervals), name
        for value, (lower, upper) in zip(expected, intervals, strict=True):
            assert lower - D('1e-60') <= value <= upper + D('1e-60'), (name, value, lower, upper)
print(f'{len(observed)} native cases agree with independent 90-digit physical references')
