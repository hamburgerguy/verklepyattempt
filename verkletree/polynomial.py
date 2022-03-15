#import libraries
import secrets
from hashlib import blake2s


### code for creating ECC for field for polynomial ###

# Curve parameters
q = 2 ** 255 - 19
keylength = 2 ** 252 + 27742317777372353535851937790883648493
cofactor = 8
width = 256  # bit length


# Internal helper methods
def exponent(b, e, m):
    return pow(b, e, m)


def invert(x, p):
    # Assumes `p` is prime
    return exponent(x, p - 2, p)


def xfromy(y):
    temp = (y * y - 1) * invert(d * y * y + 1, q)
    x = exponent(temp, (q + 3) // 8, q)
    if (x * x - temp) % q != 0:
        x = (x * I) % q
    if x % 2 != 0:
        x = q - x
    return x


def bit(h, i):
    return (int(h[i // 8]) >> (i % 8)) & 1


d = -121665 * invert(121666, q)
I = exponent(2, (q - 1) // 4, q)


# An element of the main subgroup scalar field
### class for defining Scalar type ###
class Scalar:
    def __init__(self, x):
        # Generated from an integer value
        if isinstance(x, int):
            self.x = x % keylength
        # Generated from a hex representation
        elif isinstance(x, str):
            try:
                x = bytes.fromhex(x)
                self.x = sum(2 ** i * bit(x, i) for i in range(0, width)) % keylength
            except:
                raise TypeError
        else:
            raise TypeError

    # Multiplicative inversion, with an option to let 1/0 = 0 if you're into that
    def invert(self, allow_zero=False):
        if self.x == 0:
            if allow_zero:
                return Scalar(0)
            else:
                raise ZeroDivisionError
        return Scalar(invert(self.x, keylength))

    # Addition
    def __add__(self, y):
        if isinstance(y, Scalar):
            return Scalar(self.x + y.x)
        return NotImplemented

    # Subtraction
    def __sub__(self, y):
        if isinstance(y, Scalar):
            return Scalar(self.x - y.x)
        return NotImplemented

    # Multiplication (possibly by an integer)
    def __mul__(self, y):
        if isinstance(y, int):
            return Scalar(self.x * y)
        if isinstance(y, Scalar):
            return Scalar(self.x * y.x)
        return NotImplemented

    def __rmul__(self, y):
        if isinstance(y, int):
            return self * y
        return NotImplemented

    # Truncated division (possibly by a positive integer)
    def __truediv__(self, y):
        if isinstance(y, int) and y >= 0:
            return Scalar(self.x // y)
        if isinstance(y, Scalar):
            return Scalar(self.x // y.x)
        raise NotImplemented

    # Integer exponentiation
    def __pow__(self, y):
        if isinstance(y, int) and y >= 0:
            return Scalar(self.x ** y)
        return NotImplemented

    # Equality
    def __eq__(self, y):
        if isinstance(y, Scalar):
            return self.x == y.x
        raise TypeError

    # Inequality
    def __ne__(self, y):
        if isinstance(y, Scalar):
            return self.x != y.x
        raise TypeError

    # Less-than comparison (does not account for overflow)
    def __lt__(self, y):
        if isinstance(y, Scalar):
            return self.x < y.x
        raise TypeError

    # Greater-than comparison (does not account for overflow)
    def __gt__(self, y):
        if isinstance(y, Scalar):
            return self.x > y.x
        raise TypeError

    # Less-than-or-equal comparison (does not account for overflow)
    def __le__(self, y):
        if isinstance(y, Scalar):
            return self.x <= y.x
        raise TypeError

    # Greater-than-or-equal comparison (does not account for overflow)
    def __ge__(self, y):
        if isinstance(y, Scalar):
            return self.x >= y.x
        raise TypeError

    # Hex representation
    def __repr__(self):
        bits = [(self.x >> i) & 1 for i in range(width)]
        return bytes.hex(bytes([sum([bits[i * 8 + j] << j for j in range(8)]) for i in range(width // 8)]))

    # Return underlying integer
    def __int__(self):
        return self.x

    # Modulus (possibly by an integer)
    def __mod__(self, mod):
        if isinstance(mod, int) and mod > 0:
            return Scalar(self.x % mod)
        if isinstance(mod, Scalar) and mod != Scalar(0):
            return Scalar(self.x % mod.x)
        return NotImplemented

    # Negation
    def __neg__(self):
        return Scalar(-self.x)


# An element of the curve group, defines the field
class Point:
    def __init__(self, x, y=None):
        # Generated from integer values
        if isinstance(x, int) and isinstance(y, int) and y is not None:
            self.x = x
            self.y = y

            if not self.on_curve():
                raise ValueError
        # Generated from a hex representation
        elif isinstance(x, str) and y is None:
            try:
                x = bytes.fromhex(x)
                self.y = sum(2 ** i * bit(x, i) for i in range(0, width - 1))
                self.x = xfromy(self.y)
                if self.x & 1 != bit(x, width - 1):
                    self.x = q - self.x
            except:
                raise TypeError

            if not self.on_curve():
                raise ValueError
        else:
            raise TypeError

    # Equality
    def __eq__(self, Q):
        if isinstance(Q, Point):
            return self.x == Q.x and self.y == Q.y
        raise TypeError

    # Inequality
    def __ne__(self, Q):
        if isinstance(Q, Point):
            return self.x != Q.x or self.y != Q.y
        raise TypeError

    # Addition
    def __add__(self, Q):
        if isinstance(Q, Point):
            x1 = self.x
            y1 = self.y
            x2 = Q.x
            y2 = Q.y
            x3 = (x1 * y2 + x2 * y1) * invert(1 + d * x1 * x2 * y1 * y2, q)
            y3 = (y1 * y2 + x1 * x2) * invert(1 - d * x1 * x2 * y1 * y2, q)
            return Point(x3 % q, y3 % q)
        return NotImplemented

    # Subtraction
    def __sub__(self, Q):
        if isinstance(Q, Point):
            x1 = self.x
            y1 = self.y
            x2 = -Q.x
            y2 = Q.y
            x3 = (x1 * y2 + x2 * y1) * invert(1 + d * x1 * x2 * y1 * y2, q)
            y3 = (y1 * y2 + x1 * x2) * invert(1 - d * x1 * x2 * y1 * y2, q)
            return Point(x3 % q, y3 % q)
        return NotImplemented

    # Multiplication
    def __mul__(self, y):
        # Point-Scalar: scalar multiplication
        if isinstance(y, Scalar):
            if y == Scalar(0):
                return Point(0, 1)
            Q = self.__mul__(y / Scalar(2))
            Q = Q.__add__(Q)
            if y.x & 1:
                Q = self.__add__(Q)
            return Q
        return NotImplemented

    def __rmul__(self, y):
        # Scalar-Point
        if isinstance(y, Scalar):
            return self * y
        return NotImplemented

    # Hex representation
    def __repr__(self):
        bits = [(self.y >> i) & 1 for i in range(width - 1)] + [self.x & 1]
        return bytes.hex(bytes([sum([bits[i * 8 + j] << j for j in range(8)]) for i in range(width // 8)]))

    # Curve membership (not main subgroup!)
    def on_curve(self):
        x = self.x
        y = self.y
        return (-x * x + y * y - 1 - d * x * x * y * y) % q == 0

    # Negation
    def __neg__(self):
        return Z - self

### class for defining PointVector datatype ###
class PointVector:
    def __init__(self, points=None):
        if points is None:
            points = []
        for point in points:
            if not isinstance(point, Point):
                raise TypeError
        self.points = points

    # Equality
    def __eq__(self, W):
        if isinstance(W, PointVector):
            return self.points == W.points
        raise TypeError

    # Inequality
    def __ne__(self, W):
        if isinstance(W, PointVector):
            return self.points != W.points
        raise TypeError

    # Addition
    def __add__(self, W):
        if isinstance(W, PointVector) and len(self.points) == len(W.points):
            return PointVector([self.points[i] + W.points[i] for i in range(len(self.points))])
        return NotImplemented

    # Subtraction
    def __sub__(self, W):
        if isinstance(W, PointVector) and len(self.points) == len(W.points):
            return PointVector([self.points[i] - W.points[i] for i in range(len(self.points))])
        return NotImplemented

    # Multiplication
    def __mul__(self, s):
        # PointVector-Scalar: componentwise Point-Scalar multiplication
        if isinstance(s, Scalar):
            return PointVector([self.points[i] * s for i in range(len(self.points))])
        # PointVector-ScalarVector: Hadamard product
        if isinstance(s, ScalarVector) and len(self.points) == len(s.scalars):
            return PointVector([s[i] * self[i] for i in range(len(self))])
        return NotImplemented

    def __rmul__(self, s):
        # Scalar-PointVector
        if isinstance(s, Scalar):
            return self * s
        # ScalarVector-PointVector
        if isinstance(s, ScalarVector):
            return self * s
        return NotImplemented

    # Multiscalar multiplication
    def __pow__(self, s):
        if isinstance(s, ScalarVector) and len(self.points) == len(s.scalars):
            return multiexp(s, self)
        return NotImplemented

    # Length
    def __len__(self):
        return len(self.points)

    # Get slice
    def __getitem__(self, i):
        if not isinstance(i, slice):
            return self.points[i]
        return PointVector(self.points[i])

    # Set at index
    def __setitem__(self, i, P):
        if isinstance(P, Point):
            self.points[i] = P
        else:
            raise TypeError

    # Append
    def append(self, item):
        if isinstance(item, Point):
            self.points.append(item)
        else:
            raise TypeError

    # Extend
    def extend(self, items):
        if isinstance(items, PointVector):
            for item in items.points:
                self.points.append(item)
        else:
            raise TypeError

    # Hex representation of underlying Points
    def __repr__(self):
        return repr(self.points)

    # Negation
    def __neg__(self):
        return PointVector([-P for P in self.points])


### scalarvector datatype ###
class ScalarVector:
    def __init__(self, scalars=None):
        if scalars is None:
            scalars = []
        for scalar in scalars:
            if not isinstance(scalar, Scalar):
                raise TypeError
        self.scalars = scalars

    # Equality
    def __eq__(self, s):
        if isinstance(s, ScalarVector):
            return self.scalars == s.scalars
        raise TypeError

    # Inequality
    def __ne__(self, s):
        if isinstance(s, ScalarVector):
            return self.scalars != s.scalars
        raise TypeError

    # Addition
    def __add__(self, s):
        if isinstance(s, ScalarVector) and len(self.scalars) == len(s.scalars):
            return ScalarVector([self.scalars[i] + s.scalars[i] for i in range(len(self.scalars))])
        return NotImplemented

    # Subtraction
    def __sub__(self, s):
        if isinstance(s, ScalarVector) and len(self.scalars) == len(s.scalars):
            return ScalarVector([self.scalars[i] - s.scalars[i] for i in range(len(self.scalars))])
        return NotImplemented

    # Multiplication
    def __mul__(self, s):
        # ScalarVector-Scalar: componentwise Scalar-Scalar multiplication
        if isinstance(s, Scalar):
            return ScalarVector([self.scalars[i] * s for i in range(len(self.scalars))])
        # ScalarVector-ScalarVector: Hadamard product
        if isinstance(s, ScalarVector) and len(self.scalars) == len(s.scalars):
            return ScalarVector([self.scalars[i] * s.scalars[i] for i in range(len(self.scalars))])
        return NotImplemented

    def __rmul__(self, s):
        # Scalar-ScalarVector
        if isinstance(s, Scalar):
            return self * s
        return NotImplemented

    # Sum of all Scalars
    def sum(self):
        r = Scalar(0)
        for i in range(len(self.scalars)):
            r += self.scalars[i]
        return r

    # Inner product and multiscalar multiplication
    def __pow__(self, s):
        # ScalarVector**ScalarVector: inner product
        if isinstance(s, ScalarVector) and len(self.scalars) == len(s.scalars):
            r = Scalar(0)
            for i in range(len(self.scalars)):
                r += self.scalars[i] * s.scalars[i]
            return r
        # ScalarVector**PointVector: multiscalar multiplication
        if isinstance(s, PointVector):
            return s ** self
        return NotImplemented

    # Length
    def __len__(self):
        return len(self.scalars)

    # Get slice
    def __getitem__(self, i):
        if not isinstance(i, slice):
            return self.scalars[i]
        return ScalarVector(self.scalars[i])

    # Set at index
    def __setitem__(self, i, s):
        if isinstance(s, Scalar):
            self.scalars[i] = s
        else:
            raise TypeError

    # Append
    def append(self, item):
        if isinstance(item, Scalar):
            self.scalars.append(item)
        else:
            raise TypeError

    # Extend
    def extend(self, items):
        if isinstance(items, ScalarVector):
            for item in items.scalars:
                self.scalars.append(item)
        else:
            raise TypeError

    # Hex representation of underlying Scalars
    def __repr__(self):
        return repr(self.scalars)

    # Componentwise inversion (possibly with zero)
    def invert(self, allow_zero=False):
        # If we allow zero, the efficient method doesn't work
        if allow_zero:
            return ScalarVector([s.invert(allow_zero=True) for s in self.scalars])

        # Don't allow zero
        inputs = self.scalars[:]
        n = len(inputs)
        scratch = [Scalar(1)] * n
        acc = Scalar(1)

        for i in range(n):
            if inputs[i] == Scalar(0):
                raise ZeroDivisionError
            scratch[i] = acc
            acc *= inputs[i]
        acc = Scalar(invert(acc.x, keylength))
        for i in range(n - 1, -1, -1):
            temp = acc * inputs[i]
            inputs[i] = acc * scratch[i]
            acc = temp

        return ScalarVector(inputs)

    # Negation
    def __neg__(self):
        return ScalarVector([-s for s in self.scalars])


# Try to make a point from a given y-coordinate
### lol whats the point even? ###
def make_point(y):
    if not y < q:  # stay in the field
        return None
    x = xfromy(y)
    try:
        P = Point(x, y)
    except ValueError:
        return None
    return P


# Hash data to get a Point in the main subgroup
def hash_to_point(*data):
    result = ''
    for datum in data:
        if datum is None:
            raise TypeError
        result += blake2s(str(datum).encode('utf-8')).hexdigest()

    # Continue hashing until we get a valid Point
    while True:
        result = blake2s(result.encode('utf-8')).hexdigest()
        if make_point(int(result, 16)) is not None:
            return make_point(int(result, 16)) * Scalar(cofactor)


# Hash data to get a Scalar
def hash_to_scalar(*data):
    result = ''
    for datum in data:
        if datum is None:
            raise TypeError
        result += blake2s(str(datum).encode('utf-8')).hexdigest()

    # Continue hashing until we get a valid Scalar
    while True:
        result = blake2s(result.encode('utf-8')).hexdigest()
        if int(result, 16) < keylength:
            return Scalar(int(result, 16))


# Generate a random Scalar
def random_scalar(zero=True):
    value = Scalar(secrets.randbelow(keylength))
    if not zero and value == Scalar(0):
        raise ValueError('you messed up, unexpectedly returned zero!')
    return value


# Generate a random Point in the main subgroup
def random_point():
    return hash_to_point(secrets.randbits(width))


# The main subgroup default generator
Gy = 4 * invert(5, q)
Gx = xfromy(Gy)
G = Point(Gx % q, Gy % q)

# Neutral group element
Z = Point(0, 1)


# Perform a multiscalar multiplication
def multiexp(scalars, points):
    if not isinstance(scalars, ScalarVector) or not isinstance(points, PointVector):
        raise TypeError

    if len(scalars) != len(points):
        raise IndexError
    if len(scalars) == 0:
        return Z

    buckets = None
    result = Z  # zero point

    c = 4  # window parameter; NOTE: the optimal value actually depends on len(points) empirically

    # really we want to use the max bitlength to compute groups
    maxscalar = int(max(scalars))
    groups = 0
    while maxscalar >= 2 ** groups:
        groups += 1
    groups = int((groups + c - 1) / c)

    # loop is really (groups-1)..0
    for k in range(groups - 1, -1, -1):
        if result != Z:
            for i in range(c):
                result += result

        buckets = [Z] * (2 ** c)  # clear all buckets

        # partition scalars into buckets
        for i in range(len(scalars)):
            bucket = 0
            for j in range(c):
                if int(scalars[i]) & (1 << (k * c + j)):  # test for bit
                    bucket |= 1 << j

            if bucket == 0:  # zero bucket is never used
                continue

            if buckets[bucket] != Z:
                buckets[bucket] += points[i]
            else:
                buckets[bucket] = points[i]

        # sum the buckets
        pail = Z
        for i in range(len(buckets) - 1, 0, -1):
            if buckets[i] != Z:
                pail += buckets[i]
            if pail != Z:
                result += pail
    return result

'''Polynomial functions'''

def powers(x: Scalar, degree: int) -> ScalarVector:
    powers_x = ScalarVector()
    for i in range(degree + 1):
        powers_x.append(x ** i)
    return powers_x


# polynomial evaluation poly_eval(x)

def poly_eval(x: Scalar, coeff: ScalarVector) -> Scalar:
    degree = len(coeff) - 1
    return powers(x, degree) ** coeff


# polynomial multiplication (can be accelerated with NTT mul) #

def poly_mul(poly_a: ScalarVector, poly_b: ScalarVector) -> ScalarVector:
    prod = [Scalar(0) for i in range(len(poly_a) + len(poly_b) - 1)]
    for i in range(len(poly_a)):
        for j in range(len(poly_b)):
            prod[i + j] += poly_a[i] * poly_b[j]
    return ScalarVector(prod)


# Lagrange interpolation of polynomials
def lagrange(coords: list) -> ScalarVector:
    poly = ScalarVector([Scalar(0) for i in range(len(coords))])
    for i in range(len(coords)):
        basis = ScalarVector([Scalar(1)])
        for j in range(len(coords)):
            if j == i:
                continue
            basis = poly_mul(basis, ScalarVector([-coords[j][0], Scalar(1)]))
            basis *= (coords[i][0] - coords[j][0]).invert()
        poly += basis * coords[i][1]
    return poly

'''Poly commits '''

H = hash_to_point('H')

### function for proving polynomial commitments ###
def prove(G_vec: PointVector, P: Point, x: Scalar, v: Scalar, a_vec: ScalarVector, r: Scalar) -> dict:
    dlen = len(a_vec)
    if dlen & (dlen - 1) != 0 or dlen <= 1:   # check if not power of two
        raise ValueError('length of poly not a power of 2')

    # build statement and P_prm
    b_vec = powers(x, dlen - 1)
    statement = [P, x, v, G_vec]
    U = hash_to_point('U Fiat-Shamir hash', *statement)
    P._prm = P + v * U

    # build L and R (index j is reversed)
    L_vec = PointVector()
    R_vec = PointVector()
    l_vec = ScalarVector()
    r_vec = ScalarVector()
    u_vec = ScalarVector()

    splt = dlen   # vector splitter (the lo & hi subscripts from paper)
    G_prm = G_vec
    a_prm = a_vec
    b_prm = b_vec

    while splt > 1:
        splt //= 2   # split in half evenly
        l_j = random_scalar()   # blinding factor
        r_j = random_scalar()   # blinding factor
        L_j = a_prm[:splt] ** G_prm[splt:] + l_j * H + (a_prm[:splt] ** b_prm[splt:]) * U
        R_j = a_prm[splt:] ** G_prm[:splt] + r_j * H + (a_prm[splt:] ** b_prm[:splt]) * U
        l_vec.append(l_j)
        r_vec.append(r_j)
        L_vec.append(L_j)
        R_vec.append(R_j)
        u_j = hash_to_scalar('LR Fiat-Shamir hash', *statement, L_j, R_j)
        u_vec.append(u_j)
        a_prm = a_prm[splt:] * u_j.invert() + a_prm[:splt] * u_j
        b_prm = b_prm[:splt] * u_j.invert() + b_prm[splt:] * u_j
        G_prm = G_prm[:splt] * u_j.invert() + G_prm[splt:] * u_j

    # zero knowledge opening
    u_vec_sqrd = u_vec * u_vec
    r_prm = l_vec ** u_vec_sqrd + r + r_vec ** u_vec_sqrd.invert()
    Q = a_prm[0] * (G_prm[0] + b_prm[0] * U) + r_prm * H
    d = random_scalar()   # blinding factor
    s = random_scalar()   # blinding factor
    R = d * (G_prm[0] + b_prm[0] * U) + s * H
    c = hash_to_scalar('ZKopen Fiat-Shamir hash', Q, R)
    z1 = a_prm[0] * c + d
    z2 = c * r_prm + s
    zkopen = [R, z1, z2]

    return {'state': statement, 'L': L_vec, 'R': R_vec, 'zkopen': zkopen}


def verify(proof: dict) -> bool:
    # build u_vec (index j is reversed)
    L_vec = proof['L']
    R_vec = proof['R']
    u_vec = ScalarVector()
    for (L_j, R_j) in zip(L_vec, R_vec):
        u_j = hash_to_scalar('LR Fiat-Shamir hash', *proof['state'], L_j, R_j)
        u_vec.append(u_j)

    # build s_vec (be careful on indices), G, and b
    # this is slow, hence this is the reason behind the 'amortization strategy'
    # (Subsection 3.2 from paper), but we will not implement it here
    G_vec = proof['state'][3]
    dlen = len(G_vec)
    b_vec = powers(proof['state'][1], dlen - 1)
    s_vec = ScalarVector()
    for i in range(dlen):
        bin = i
        prod = Scalar(1)
        for j in range(len(u_vec) - 1, -1, -1):   # reverse
            bit = bin & 1
            if bit == 1:
                prod *= u_vec[j]
            else:
                prod *= u_vec[j].invert()
            bin >>= 1
        s_vec.append(prod)
    G = s_vec ** G_vec
    b = s_vec ** b_vec

    # build P_prm and Q
    U = hash_to_point('U Fiat-Shamir hash', *proof['state'])
    P_prm = proof['state'][0] + proof['state'][2] * U
    u_vec_sqrd = u_vec * u_vec
    Q = L_vec ** u_vec_sqrd + P_prm + R_vec ** u_vec_sqrd.invert()

    # verify zero knowledge opening
    R = proof['zkopen'][0]
    c = hash_to_scalar('ZKopen Fiat-Shamir hash', Q, R)
    z1 = proof['zkopen'][1]
    z2 = proof['zkopen'][2]
    return c * Q + R == z1 * (G + b  * U) + z2 * H
