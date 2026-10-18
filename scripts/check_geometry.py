"""Exact small geometry checks; does NOT check the non-Rupert certificate."""
from itertools import combinations
import hashlib
import json
from pathlib import Path
from exact import Q5, dot

SHAPE='ccc058dd1600ccf1c334f3365ac9eaba204525f4d86c2dc8fda85ead093d56e5'


def require(ok,message):
    if not ok:
        raise ValueError(message)


def cross(a,b):
    return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])


def check(shape,geometry):
    payload={k:v for k,v in shape.items() if k!='sha256'}
    require(hashlib.sha256(json.dumps(payload,sort_keys=True).encode()).hexdigest()==shape['sha256']==SHAPE,
            'Exact shape-record digest mismatch')
    vertices=[tuple(Q5.read(x) for x in p) for p in shape['vertices']]
    require(len(vertices)==len(set(vertices))==180,'Expected 180 distinct exact points')
    require({tuple(-x for x in p) for p in vertices}==set(vertices),'Central symmetry failed')
    require(any(dot(a,cross(b,c)).sign()!=0 for a,b,c in combinations(vertices,3)), 'Not full-dimensional')
    exposures=geometry['vertex_exposures']
    require(len(exposures)==180 and {e['vertex'] for e in exposures}==set(range(180)), 'Incomplete exposures')
    for e in exposures:
        i=e['vertex'];n=tuple(Q5.read(x) for x in e['normal']);height=dot(n,vertices[i])
        require(all((height-dot(n,p)).sign()>0 for j,p in enumerate(vertices) if j!=i),'Failed strict vertex exposure')
    facets=geometry['verified_supporting_facets']
    require(len(facets)==182,'Unexpected listed facet count')
    seen=set()
    for f in facets:
        n=tuple(Q5.read(x) for x in f['normal'])
        gaps=[Q5(1)-dot(n,p) for p in vertices]
        active=[i for i,g in enumerate(gaps) if g.sign()==0]
        require(all(g.sign()>=0 for g in gaps) and active==f['vertices'],'Failed support/incidence check')
        require(len(active)>=3 and tuple(active) not in seen,'Degenerate/duplicate facet record')
        a=vertices[active[0]]
        differences=[tuple(x-y for x,y in zip(vertices[i],a)) for i in active[1:]]
        require(any(any(x.sign()!=0 for x in cross(u,v)) for u,v in combinations(differences,2)), 'Collinear facet')
        seen.add(tuple(active))
    return dict(exact_vertices=180,centrally_symmetric=True,full_dimensional=True,
                strict_vertex_exposures=180,listed_supporting_facets=182,
                facet_enumeration_completeness_proved=False,non_rupertness_checked=False)


if __name__=='__main__':
    folder=Path(__file__).resolve().parents[1]/'geometry'
    print(json.dumps(check(json.loads((folder/'shape-record.json').read_text()),
                           json.loads((folder/'exact-geometry.json').read_text())),indent=2))
