#!/usr/bin/env python3
"""Finite source-fidelity audit only; not a proof of any infinite tiling claim.

Usage: python verify_source_data.py ORIGINAL_TSV LEAN_EXPORT_TSV
Run from the proof repository. No original compiler or Rocq file is executed.
"""
import ast, csv, hashlib, json, re, sys
from pathlib import Path

def parse_tuple(text):
    tokens = re.findall(r'\(|\)|,|[^(),]+', text)
    i = 0
    def parse():
        nonlocal i
        token = tokens[i]; i += 1
        if token != '(':
            return int(token) if re.fullmatch(r'-?\d+', token) else token
        parts = [parse()]
        while tokens[i] == ',':
            i += 1; parts.append(parse())
        assert tokens[i] == ')'; i += 1
        return tuple(parts)
    result = parse()
    assert i == len(tokens)
    return result

def labels(source, name):
    body = source.split('def ' + name, 1)[1].split('#[', 1)[1].split('\n]', 1)[0]
    rows = [tuple(ast.literal_eval(line.strip().rstrip(',')))
            for line in body.splitlines() if line.strip()]
    assert len(set(rows)) == len(rows)
    return {row: i for i, row in enumerate(rows)}

def tm_code(c):
    if c == 'b': return 0
    if c in ('iL', 'iR', 'iH', 'iX'): return 2000 + ('iL','iR','iH','iX').index(c)
    assert isinstance(c, tuple)
    if c[0] == 's':
        assert c[1] in (0,1)
        return 1+c[1]
    if c[0] == 'h':
        assert 0 <= c[1] <= 230 and c[2] in (0,1)
        return 3+2*c[1]+c[2]
    assert c[0] in ('L','R') and 0 <= c[1] <= 230
    return 1000+2*c[1]+(c[0]=='R')

root = Path(__file__).resolve().parent
original, exported = map(Path, sys.argv[1:])
source = (root/'ExactTable.lean').read_text()
H, V = labels(source, 'horizontalLabels'), labels(source, 'verticalLabels')
channels = {'-':0, 0:1, 'a':2, 'b':3}
rows = list(csv.DictReader(original.open(), delimiter='\t'))
expected = []
for row in rows:
    encoded = []
    for side in ('north','east','south','west'):
        base, channel, tm = parse_tuple(row[side])
        assert base[0] == ('v' if side in ('north','south') else 'h')
        dictionary = V if base[0] == 'v' else H
        encoded.extend((dictionary[(base[1],base[2],*base[3])], channels[channel], tm_code(tm)))
    expected.append(tuple(encoded))
actual = [tuple(map(int,line.split('\t'))) for line in exported.read_text().splitlines()]
assert all(len(row)==12 for row in actual)
assert len(expected)==len(actual)==11487
assert len(set(expected))==len(set(actual))==11487
assert set(actual)==set(expected)
print(json.dumps({'scope':'Finite TSV-to-Lean data fidelity only; no infinite tiling conclusion',
                  'status':'pass','distinct_tiles':11487,
                  'original_tsv_sha256':hashlib.sha256(original.read_bytes()).hexdigest(),
                  'lean_export_sha256':hashlib.sha256(exported.read_bytes()).hexdigest()},indent=2))
