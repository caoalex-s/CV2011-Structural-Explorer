"""Derive the fixed portal's rational tables for review and Lean proof inputs.

Run with Python 3 from the repository root. No Lean or browser is launched.
This generator is untrusted: PortalSoundness must connect every table to the
existing actual model. The inverse is a witness, not an assumed solver result.
"""
from fractions import Fraction as Q
import json
from pathlib import Path


def zeros(rows, columns):
    return [[Q(0) for _ in range(columns)] for _ in range(rows)]


def multiply(left, right):
    return [[sum((a * b for a, b in zip(row, column)), Q(0))
             for column in zip(*right)] for row in left]


def inverse(matrix):
    size = len(matrix)
    augmented = [row[:] + [Q(i == j) for j in range(size)] for i, row in enumerate(matrix)]
    for column in range(size):
        pivot = next(row for row in range(column, size) if augmented[row][column])
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        scale = augmented[column][column]
        augmented[column] = [value / scale for value in augmented[column]]
        for row in range(size):
            if row != column:
                scale = augmented[row][column]
                augmented[row] = [x - scale * y for x, y in zip(augmented[row], augmented[column])]
    return [row[size:] for row in augmented]


# 1. Assemble the three original oriented Euler–Bernoulli elements.
stiffness = zeros(12, 12)
for start, end, length, cosine, sine in [(0, 1, 4, 0, 1), (1, 2, 6, 1, 0), (2, 3, 4, 0, -1)]:
    axial = Q(2000000, length)
    bending = Q(12 * 20000, length**3)
    coupling = Q(6 * 20000, length**2)
    rotation = Q(4 * 20000, length)
    half_rotation = rotation / 2
    local = [
        [axial, 0, 0, -axial, 0, 0],
        [0, bending, coupling, 0, -bending, coupling],
        [0, coupling, rotation, 0, -coupling, half_rotation],
        [-axial, 0, 0, axial, 0, 0],
        [0, -bending, -coupling, 0, bending, -coupling],
        [0, coupling, half_rotation, 0, -coupling, rotation],
    ]
    transform = zeros(6, 6)
    for offset in (0, 3):
        transform[offset][offset] = cosine
        transform[offset][offset + 1] = sine
        transform[offset + 1][offset] = -sine
        transform[offset + 1][offset + 1] = cosine
        transform[offset + 2][offset + 2] = 1
    global_element = multiply(list(zip(*transform)), multiply(local, transform))
    coordinates = [3 * start + d for d in range(3)] + [3 * end + d for d in range(3)]
    for i, row in enumerate(coordinates):
        for j, column in enumerate(coordinates):
            stiffness[row][column] += global_element[i][j]

# 2. Derive and check the fixed inverse and unit-load candidate exactly.
force = [Q(value) for value in [0, 0, 0, 0, 3, 3, 0, 3, -3, 0, 0, 0]]
reduced = [row[3:9] for row in stiffness[3:9]]
witness = inverse(reduced)
assert multiply(witness, reduced) == [[Q(i == j) for j in range(6)] for i in range(6)]
unit = [row[0] for row in multiply(witness, [[value] for value in force[3:9]])]
full_unit = [Q(0)] * 3 + unit + [Q(0)] * 3
reaction = [sum((x * y for x, y in zip(stiffness[i], full_unit)), Q(0)) - force[i]
            for i in [0, 1, 2, 9, 10, 11]]
moment = Q(20000, 6) * (full_unit[8] - full_unit[5]) - Q(3, 2)
displacement = (full_unit[4] + full_unit[7]) / 2 + Q(3, 4) * (full_unit[5] - full_unit[8]) + Q(27, 160000)

# 3. Emit deterministic data and computable Lean constants. Never emit proofs.
target = Path('qa/live-portal')
target.mkdir(parents=True, exist_ok=True)
encode = lambda value: [str(value.numerator), str(value.denominator)]
tables = {'coordinates': [node + component for node in 'ABCD' for component in ['x', 'y', 'rotation']],
          'stiffness': [[encode(value) for value in row] for row in stiffness],
          'unitForce': [encode(value) for value in force],
          'inverse': [[encode(value) for value in row] for row in witness],
          'unitCandidate': [encode(value) for value in full_unit],
          'unitReactions': [encode(value) for value in reaction],
          'unitMidpoint': [encode(moment), encode(displacement)]}
(target / 'tables.json').write_text(json.dumps(tables, indent=2) + '\n', encoding='utf-8')
literal = lambda value: str(value.numerator) if value.denominator == 1 else f'({value.numerator} / {value.denominator})'
vector = lambda row: '[' + ', '.join(literal(value) for value in row) + ']'
matrix = lambda rows: '[\n  ' + ',\n  '.join(vector(row) for row in rows) + '\n]'
lean = ('import Batteries.Data.Rat.Basic\n\nnamespace PortalChecker\n\n'
        '-- Generated exact tables; independently linked to the actual model in PortalSoundness.\n'
        f'def stiffnessRows : List (List Rat) := {matrix(stiffness)}\n\n'
        f'def inverseRows : List (List Rat) := {matrix(witness)}\n\n'
        f'def unitForce : List Rat := {vector(force)}\n\n'
        'def stiffness (i j : Fin 12) : Rat := (stiffnessRows.getD i.val []).getD j.val 0\n'
        'def inverse (i j : Fin 6) : Rat := (inverseRows.getD i.val []).getD j.val 0\n'
        'def force (i : Fin 12) : Rat := unitForce.getD i.val 0\n\nend PortalChecker\n')
Path('proofs/PortalTables.lean').write_text(lean, encoding='utf-8')
print(json.dumps({'unit_candidate': list(map(str, full_unit)), 'unit_reactions': list(map(str, reaction)),
                  'unit_midpoint_M_uy': [str(moment), str(displacement)]}))
