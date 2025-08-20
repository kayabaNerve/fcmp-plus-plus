#!/usr/bin/env sage
# -*- coding: utf-8 -*-

# This script finds efficient elliptic curve tower-cycles for Curve25519.
# The algorithm is described in this paper: https://arxiv.org/pdf/0712.2022.pdf

import sys
from multiprocessing import Pool, cpu_count
from traceback import print_exc

p = 2^255 - 19

# https://en.wikipedia.org/wiki/Cornacchia%27s_algorithm
# Finds [x,y] that solves x^2+d*y^2=m
def cornacchia(d, m):
    g = 1
    try:
        r = Mod(-d, m).sqrt(False)
    except (ValueError):
        for (p,e) in factor(m):
            e = e//2
            if e != 0:
                m //= p^(2*e)
                g *= p^e
        try:
            r = Mod(-d, m).sqrt(False)
        except (ValueError):
            return (None, "No sqrt mod m")
    r = int(r)
    if r > m//2:
       r = m - r
    sm = isqrt(m)
    t = m
    while r > sm:
        rn = t % r
        t = r
        r = rn
    s2 = m - r^2
    if s2 % d != 0:
        return (None, "s2 not divisible by d")
    s2 //= d
    s = isqrt(s2)
    if s*s == s2:
        return (g*r, g*s)
    return (None, "sqrt(s2) not an integer")

# Find an isomorphism with a specific value of the curve parameter "a".
def get_iso(E, ax):
    a = E.a4()
    b = E.a6()
    f = E.base_field()
    u4 = a / ax
    us = u4.nth_root(4,all=True)
    if not us:
        return None
    u = us[0]
    bx = b / u^6
    Eu = EllipticCurve([f(ax), bx])
    assert Eu.is_isomorphic(E)
    return Eu

def find_iso(E):
    # a = -3 for efficient doubling https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html
    iso = get_iso(E, -3)
    if iso is not None:
        return iso
    return E

def find_curves(d, q):
    H = hilbert_class_polynomial(d);
    Sq = H.roots(GF(q))
    Sp = H.roots(GF(p))
    Eqs = []
    Eps = []
    # check the first 12 roots
    num_roots = 12
    for i in range(num_roots):
        j0 = Sq[i][0]
        aq = 27*j0/(4*(1728-j0))
        Eq = EllipticCurve([aq, -aq])
        rq = Eq.count_points()
        if rq == p:
            Eqs.append(Eq)
        Eq = Eq.quadratic_twist()
        rq = Eq.count_points()
        if rq == p:
            Eqs.append(Eq)
    assert len(Eqs) == num_roots
    for i in range(num_roots):
        j0 = Sp[i][0]
        ap = 27*j0/(4*(1728-j0))
        Ep = EllipticCurve([ap, -ap])
        rp = Ep.count_points()
        if rp == q:
            Eps.append(Ep)
        Ep = Ep.quadratic_twist()
        rp = Ep.count_points()
        if rp == q:
            Eps.append(Ep)
    assert len(Eps) == num_roots
    return [Eps, Eqs]

def to_signed(x):
    o = int(x.order())
    i = int(x)
    if i > o - 1000:
        return i - o
    return i

def curve_to_str(E):
    a = to_signed(E.a4())
    b = E.a6()
    estr = "y^2=x^3"
    if a == 1:
        estr += "+"
    elif a == -1:
        estr += "-"
    else:
        estr += "%+i*" % a
    estr += "x+%i" % b
    if not b.is_square():
        estr += " (b is non-square)"
    return estr

def print_curves(d, q):
    output = "D = %i, q = %s" % (d, hex(q))
    if q % 4 == 3:
        output += " (q = 3 mod 4)"
    if 2^256 - 2*q < 2^128:
        output += " (2^256 - 2*q < 2^128)"
    output += "\n"
    (Eps, Eqs) = find_curves(d, q)
    output += "    Ep:\n"
    for Ep in Eps:
        Ep = find_iso(Ep)
        output += "        %s\n" % curve_to_str(Ep)
    output += "    Eq:\n"
    for Eq in Eqs:
        Eq = find_iso(Eq)
        output += "        %s\n" % curve_to_str(Eq)
    sys.stdout.write(output)
    sys.stdout.flush()

def get_discriminants(wid, processes):
    # -D must be 3 mod 8
    for d in range(3 + 8 * wid, 1000000000, 8 * processes):
        yield d

def find_primes(wid, processes):
    for d in get_discriminants(wid, processes):
        (x, y) = cornacchia(d, 4*p)
        if x == None:
            continue
        q = p + 1 - x
        if is_prime(q):
            yield (-d, q)

def run_search(wid, processes):
    for (d, q) in find_primes(wid, processes):
        print_curves(d, q)

def worker(*args):
    try:
        run_search(*args)
    except (KeyboardInterrupt, SystemExit):
        pass
    except:
        print_exc()

processes = cpu_count()
print("p = %s" % hex(p))
print("Searching for curves using %i processes." % (processes,))

pool = Pool(processes=processes)

try:
    for wid in range(processes):
        pool.apply_async(worker, (wid, processes))

    pool.close()
    pool.join()
except (KeyboardInterrupt, SystemExit):
    pass
finally:
    pool.terminate()
