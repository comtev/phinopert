"""Small exact ordered field Q(sqrt(5)); no floating point in predicates."""
from dataclasses import dataclass
from fractions import Fraction as F


@dataclass(frozen=True)
class Q5:
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Q5) else Q5(x)

    def __add__(self, other):
        o = self.coerce(other)
        return Q5(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        o = self.coerce(other)
        return Q5(self.a*o.a + 5*self.b*o.b, self.a*o.b + self.b*o.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        o = self.coerce(other)
        d = o.a*o.a - 5*o.b*o.b
        if not d:
            raise ZeroDivisionError
        return self * Q5(o.a/d, -o.b/d)

    def sign(self):
        a, b = self.a, self.b
        if not b:
            return (a > 0) - (a < 0)
        if not a:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        d = a*a - 5*b*b
        return ((d > 0) - (d < 0)) * (1 if a > 0 else -1)

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __float__(self):
        return float(self.a) + float(self.b)*5**0.5

    def dump(self):
        return [str(self.a), str(self.b)]

    @classmethod
    def read(cls, pair):
        return cls(F(pair[0]), F(pair[1]))


PHI = Q5(F(1, 2), F(1, 2))


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), Q5())


def cross2(o, a, b):
    return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])


def hull2(points):
    """Exact monotone-chain hull, independent of SciPy/Qhull."""
    points = sorted(set(points))
    if len(points) < 3:
        raise ValueError('Degenerate projection')
    halves = []
    for seq in (points, list(reversed(points))):
        chain = []
        for p in seq:
            while len(chain) >= 2 and cross2(chain[-2], chain[-1], p).sign() <= 0:
                chain.pop()
            chain.append(p)
        halves.append(chain[:-1])
    hull = halves[0] + halves[1]
    if len(hull) < 3:
        raise ValueError('Degenerate projection')
    return hull


def rational_rotation(q):
    """Exact SO(3) matrix from any nonzero integer quaternion (x,y,z,w)."""
    x, y, z, w = map(int, q)
    d = x*x+y*y+z*z+w*w
    if not d:
        raise ValueError('Zero quaternion')
    return [[F(v, d) for v in row] for row in (
        (d-2*(y*y+z*z), 2*(x*y-z*w), 2*(x*z+y*w)),
        (2*(x*y+z*w), d-2*(x*x+z*z), 2*(y*z-x*w)),
        (2*(x*z-y*w), 2*(y*z+x*w), d-2*(x*x+y*y)),
    )]


def verify_passage(vertices, inner_q, outer_q):
    """Prove strict containment for congruent unscaled copies using exact signs."""
    ri, ro = rational_rotation(inner_q), rational_rotation(outer_q)
    inner = [tuple(dot(row, v) for row in ri[:2]) for v in vertices]
    outer = hull2([tuple(dot(row, v) for row in ro[:2]) for v in vertices])
    smallest = None
    count = 0
    for i, a in enumerate(outer):
        b = outer[(i+1) % len(outer)]
        for p in inner:
            d = cross2(a, b, p)
            count += 1
            if d.sign() <= 0:
                return {'verified': False, 'reason': 'Nonpositive exact edge determinant',
                        'edge': i, 'determinant': d.dump()}
            if smallest is None or d < smallest:
                smallest = d
    return {'verified': True, 'arithmetic': 'Q(sqrt(5)), rational rotations',
            'strict_inequalities': count, 'outer_edges': len(outer),
            'minimum_determinant': smallest.dump()}
