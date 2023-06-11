#! /usr/bin/env python3

# An implementation of the Helfgott-Thompson algorithm for computing the Mertens function.
# See https://arxiv.org/abs/2101.08773 for details.
# This file is a translation of the ancillary files from that link.

from math import isqrt
from time import time
from sys import argv

class primfact: plist, pmark = 0, 0     # "2,3,5,7 is recorded as 111010 010111"    TODO: What does this mean?

def sgn(x): return (x > 0) - (x < 0)
def ceildiv(a, b): return -(a // -b)
def modl(a, b): return (a % abs(b)) if a >= 0 else (b - 1 - (-a-1)%abs(b))
def FlCong(n, a, q): return n - ((n-a) % abs(q))

def introot(n, r=2):    # copied from labmath (https://pypi.org/project/labmath/ or https://github.com/lucasaugustus/labmath)
    """
    Returns the rth root of n, rounded to the nearest integer in the
    direction of zero.  Returns None if r is even and n is negative.
    
    Input:
        n -- an integer
        r -- a natural number or None
    
    Output: An integer
    
    Examples:
    
    >>> [introot(-729, 3), introot(-728, 3)]
    [-9, -8]
    
    >>> [introot(1023, 2), introot(1024, 2)]
    [31, 32]
    """
    if n < 0: return None if r%2 == 0 else -introot(-n, r)
    if n < 2: return n
    if r == 1: return n
    if r == 2: return isqrt(n)
    #if r % 2 == 0: return introot(isqrt(n), r//2)      # TODO Check validity of this line.
    lower = upper = 1 << (n.bit_length() // r)
    while lower ** r >  n: lower >>= 2
    while upper ** r <= n: upper <<= 2
    while lower != upper - 1:
        mid = (lower + upper) // 2
        m = mid**r
        if   m == n: return  mid
        elif m <  n: lower = mid
        elif m >  n: upper = mid
    return lower

def fillisprime(isprime, n):
    # Given a list isprime and an int n, we fill isprime with 0s and 1s so that isprime[n] == 1 iff n is prime.
    # This list goes up to, but does not include, n.
    isprime[0] = isprime[1] = 0
    for i in range(2, n): isprime[i] = 1
    for i in range(2, isqrt(n)+1):
        if isprime[i]:
            for j in range(2*i, n, i):
                isprime[j] = 0

def fillmublock(mun, isprime, n, m):
    # Fills mun[0], ..., mun[m-1] with mu(n), ..., mu(n + m-1).
    # Assumes isprime is filled and valid to up and including sqrt(n+m).
    # Convention: mu(0) == 0.
    
    Pi = [1] * m
    for j in range(m): mun[j] = 1
    
    for p in range(isqrt(n + m) + 1):
        if isprime[p]:
            for x in range( p  * ceildiv(n,  p ), n + m,  p ): mun[x - n] *= -1; Pi[x - n] *= p
            for x in range(p*p * ceildiv(n, p*p), n + m, p*p): mun[x - n]  =  0
    
    for j in range(m):
        if mun[j] != 0 and Pi[j] != n + j:
            mun[j] *= -1

def BruteM(x):
    # Given x, we compute mu(1) + mu(2) + ... + mu(x) by brute force, but segmented to be kind to the memory.
    M = 0
    Delta = isqrt(x)
    
    isprime = bytearray([0]) * (isqrt(x + Delta) + 1)
    mu      =           [0]  * (Delta + 1)
    fillisprime(isprime, Delta + 1)
    
    for n0 in range(1, x+1, Delta):
        fillmublock(mu, isprime, n0, Delta+1)
        M += sum(mu[n] for n in range(min(Delta, x-n0+1)))
    
    return M

def fillfactblock(funplist, funpmark, sqfprod, isprime, n, m):
    # funplist and funpmark are lists of ints
    # In the original code, these were combined as a single list fun of a compound data type, so that
    # fun[k].plist == funplist[k] and fun[k].pmark == funpmark[k]
    # sqfprod and isprime are lists of ints
    # n and m are ints
    # fills fun[0], fun[1],... with the list of prime factors of n, n+1, ..., n+m-1 (no exponents)
    # fills sqfprod[0], sqfprod[1],... with the products of prime divisors of n, n+1,...
    # assumes isprime is filled and valid up to and including sqrt(n+m-1)
    # convention: 1 factorizes into nothing; the factorization of 0 could be goodness knows what; assumes littleendianness
    P = 2*2*2*3*3*5*7*11
    pmax = 11
    
    tabla        = [0] * m
    minitabla    = [1] * P
    minisqfprod  = [1] * P
    minifunplist = [0] * P
    minifunpmark = [0] * P
    
    # In the original C++ files, this loop is prefillfact.
    for p in range(2, pmax+1):
        if isprime[p]:
            pk = p.bit_length() - 1     # floor(log_2(p))
            nmark = 1 << (pk-1)
            trailp = ((1 << pk) - 1) & p         # Given in the C++ as (p & ~((~0ul)<<pk)).  This should take off the leading 1.
            k, d = 1, p
            while P % d == 0:
                uj0 = d if n == 0 else ((n+d-1)//d)*d-n
                for uj in range(uj0, P, d):
                    if k == 1:
                        minifunpmark[uj] <<= pk; minifunpmark[uj] |= nmark
                        minifunplist[uj] <<= pk; minifunplist[uj] |= trailp
                        minisqfprod[uj] *= p
                    minitabla[uj] *= p
                k += 1
                d *= p
    
    # TODO: Instead of working on minitabla, minisqfprod, and minifun and then copying them into tabla, sqfprod, and fun,
    # work on tabla, sqfprod, and fun directly.
    
    for j in range(0, m, P):
        many = min(P, m-j)
        for k in range(many):    tabla[j + k] =    minitabla[k]                        # TODO: Can we do this with slices?
        for k in range(many):  sqfprod[j + k] =  minisqfprod[k]
        for k in range(many): funplist[j + k] = minifunplist[k]
        for k in range(many): funpmark[j + k] = minifunpmark[k]            # TODO: Do all 4 k-iterations in a single loop.
    
    # We now continue with what was fillfactblock in the original C++.
    
    # first, we complete the factorization for small primes, starting where prefillfact stopped
    for p in range(2, pmax+1):
        if isprime[p]:
            dold, d = 1, p
            while P % d == 0: dold, d = d, d*p
            roof = (n+m-1) // p
            while dold <= roof:
                j0 = d if n == 0 else ((n+d-1)//d) * d - n
                for j in range(j0, m, d): tabla[j] *= p
                dold, d = d, d*p
    
    # now for the larger primes...
    p = pmax+2
    while p*p <= n+m-1:
        if isprime[p]:
            pk = p.bit_length() - 1     # floor(log_2(p))
            nmark = 1 << (pk-1)
            trailp = ((1 << pk) - 1) & p         # Given in the C++ as (p & ~((~0ul)<<pk)).  This should take off the leading 1.
            k = 1
            dold = 1
            d = p
            roof = (n+m-1)//p
            while dold <= roof:
                j0 = d if n == 0 else ((n+d-1)//d) * d - n
                for j in range(j0, m, d):
                    if k == 1:
                        funpmark[j] <<= pk; funpmark[j] |= nmark
                        funplist[j] <<= pk; funplist[j] |= trailp
                        sqfprod[j] *= p
                    tabla[j] *= p
                k, dold, d = k+1, d, d*p
        p += 2
    
    for j in range(m):
        if tabla[j] != n+j:
            p = (n+j)//tabla[j]
            pk = p.bit_length() - 1     # floor(log_2(p))
            # The RHS of this next assignment is given in the original C++ as ((fun[j].pmark<<1)|1ul)<<(pk-1).
            # It should be equivalent to (fun[j].pmark * 2 + 1) * 2**(pk-1).
            # Note that pointer arithmetic is used in the original to have off==0.
            funpmark[j] = ((funpmark[j] << 1) | 1) << (pk-1)
            # The RHS of this next assignment is given in the original C++ as (fun[j].plist<<pk) | (p & ~((~0ul)<<pk)).
            # The second operand of the bitwise OR should take off the leading 1 from p.
            # The effect of the whole assignment should be to append pk ones to the little end of fun[j].plist.
            # Note that pointer arithmetic is used in the original to have off==0.
            funplist[j] = (funplist[j] << pk) | (((1 << pk) - 1) & p)
            sqfprod[j] *= p

def FacToSumMu(fplist, fpmark, m, mc, a, n):
    # All arguments are ints.
    # In the original code, fplist and fpmark were combined into a single compound data type.
    if m > a: return 0
    if fpmark == 0: return 1
    if mc >= n: return 0
    
    k = (fpmark & -fpmark).bit_length() # 1 + the # of trailing zeros in fpmark.  Given in the C++ as __builtin_ctzl(f.pmark)+1.
    fpmark >>= k
    p = (1 << k) | (fplist & ((1 << k) - 1))                            # Given in the C++ as (1ul<<k)|(f.plist & ~((~0ul)<<k)).
    fplist >>= k
    
    return FacToSumMu(fplist, fpmark, m, mc*p, a, n) - FacToSumMu(fplist, fpmark, m*p, mc, a, n)

def diophapp(alpa, alpq, Q):
    # In the original code, this returned an object of type diophapp_t, which had 4 attributes: .a, .q, .ainv, and .s.
    # The .s attribute was never used, so I got rid of it.  This now returns a 3-tuple (a, q, ainv).
    
    b = alpa // alpq
    p = b
    q = 1
    pmin = 1
    qmin = 0
    s = 1
    while q <= Q:
        if alpa == b * alpq:
            flip = -qmin if s == 1 else qmin
            return (p, q, flip % abs(q))
        
        qacc = alpq
        alpq = alpa - b*alpq
        alpa = qacc
        b = alpa // alpq
        
        pplus = b*p + pmin
        qplus = b*q + qmin
        
        pmin = p
        qmin = q
        p = pplus
        q = qplus
        s = -s
        
    flip = q if s == 1 else -q
    return (pmin, qmin, flip % abs(qmin))

def LinearSum(f, g, a, b, x, m0, n0, foff, goff):
    # f and g are lists of ints
    # a, b, x, m0, and n0 are ints
    uden = m0 * m0 * n0
    unum = x * (m0 + a)
    m = -a
    S1 = 0
    S10 = 0
    while m < a:
        S1  += f[m+foff] * (unum // uden)
        S10 += f[m+foff]
        m += 1
        unum -= x
    
    uden = m0 * n0 * n0
    unum = x * b
    n = -b
    S2 = 0
    S20 = 0
    while n < b:
        S2  += g[n+goff] * (unum // uden)
        S20 += g[n+goff]
        n += 1
        unum -= x
    
    return S1 * S20 + S10 * S2

def QuadIneqZ(a, b, c):
    # a, b, and c are ints
    # In the original code, the return values were Iint objects.
    Delta = b*b - 4*a*c
    
    if Delta < 0: return (1, 0) # empty interval
    
    Q = isqrt(Delta)
    
    if a < 0:          return (-((    - b - Q) // (-2*a)),  ((      b - Q) // (-2*a)))
    elif Q*Q != Delta: return (-((      b + Q) // ( 2*a)),  ((    - b + Q) // ( 2*a)))
    else:              return ( ((2*a - b - Q) // ( 2*a)), -((2*a + b - Q) // ( 2*a)))

def SumInter(G, r, J_left, J_right, b, q):
    # G is a list of ints
    # r, b, and Q are ints
    # J_left and J_right are ints that were originally in an Iint object.
    if J_left > J_right: return 0
    
    r0 = FlCong(    J_left - 1     , r, q)
    r1 = FlCong(min(J_right, b - 1), r, q)
    
    if r0 >  r1: return 0
    if r1 <  -b: return 0
    if r0 >= -b: return G[r1+b] - G[r0+b]
    return G[r1+b]

def SpecialL2L1(G, xq, appr_q, appr_ainv, R0num, R0den, r0, A2, ncirc, ancirc, m, b, Qfloor, Qceil, betsign, delsign):
    # G is a list of ints, appr_q and appr_ainv) are ints that were originally in a diophapp_t, and the rest are ints
    
    # first compute the contribution of n such that a_0(n-n_0)+r_0 = 1 mod q
    
    # In the original code, JI_left and JI_right were originally in an Iint object, and likewise for J_left and J_right.
    gamma1 = (ancirc - (R0num // R0den) * appr_q - r0) * m
    JI_left, JI_right = QuadIneqZ(A2, gamma1, xq)
    JI_left  -= ncirc
    JI_right -= ncirc
    
    if   delsign >  0: J_left, J_right  = -b       , -Qfloor - 1
    elif delsign <  0: J_left, J_right  = 1 - Qceil, b - 1
    elif betsign >= 0: J_left, J_right  = 1        , 0
    else:              J_left, J_right  = -b       , b - 1
    
    JI_left  = max(JI_left , J_left )
    JI_right = min(JI_right, J_right)
    
    r = -r0 * appr_ainv
    S = SumInter(G, r, J_left, J_right, b, appr_q) - SumInter(G, r, JI_left, JI_right, b, appr_q)
    
    # and now for the contributon of n such that a_0(n-n_0)+r_0 = 0 mod q
    
    gamma1 -= m
    r -= appr_ainv
    JI_left, JI_right = QuadIneqZ(A2, gamma1, xq)
    JI_left  -= ncirc
    JI_right -= ncirc
    J_left, J_right = -b, b-1
    return S + SumInter(G, r, J_left, J_right, b, appr_q) - SumInter(G, r, JI_left, JI_right, b, appr_q)

def Special00(G, x, appr_q, appr_a, R0num, R0den, r0, ncirc, m, b, Qfloor, Qceil, delsign):
    # G is a list of ints.
    # appr_a and appr_q are ints that were originally in a diophapp_t.
    # The rest are ints.
    
    # In the original code, J_left and J_right were combined into an Iint object.
    # In the original code, we had I, a two-element list containing Iints, such that
    # I[0].left == I0l and I[0].right == I0r and I[1].left == I1l and I[1].right == I1r
    
    R0floor = R0num // R0den
    minbetdel = (-1 - Qfloor) if (delsign > 0) else (1 - Qceil)
    
    if appr_a == 0:
        flank0 = ((x//m) // (R0floor + r0    )) - ncirc
        flank1 = ((x//m) // (R0floor + r0 + 1)) - ncirc
        if delsign > 0:
            J_left , J_right = -b        , min(flank0    , minbetdel    ); S0 = SumInter(G, 0, J_left, J_right, b, appr_q)
            J_right, J_left  = flank1    ,                 minbetdel + 1 ; S1 = SumInter(G, 0, J_left, J_right, b, appr_q)
        elif delsign < 0:
            J_right, J_left  = flank0    ,                 minbetdel     ; S0 = SumInter(G, 0, J_left, J_right, b, appr_q)
            J_left , J_right = -b        , min(flank1    , minbetdel - 1); S1 = SumInter(G, 0, J_left, J_right, b, appr_q)
        else:
            S0 = 0
            J_left , J_right = -b        ,     flank1                    ; S1 = SumInter(G, 0, J_left, J_right, b, appr_q)
        return S0 + S1
    else:
        I0l, I0r = QuadIneqZ(-m * appr_a, (appr_a*ncirc - R0floor*appr_q - r0    ) * m, x * appr_q); I0l -= ncirc; I0r -= ncirc
        I1l, I1r = QuadIneqZ(-m * appr_a, (appr_a*ncirc - R0floor*appr_q - r0 - 1) * m, x * appr_q); I1l -= ncirc; I1r -= ncirc
        if delsign > 0:
            J_left , J_right = I0l, min(I0r, minbetdel    ); S0 = SumInter(G, 0, J_left, J_right, b, appr_q)
            J_right, J_left  = I1r, max(I1l, minbetdel + 1); S1 = SumInter(G, 0, J_left, J_right, b, appr_q)
        elif delsign < 0:
            J_right, J_left  = I0r, max(I0l, minbetdel    ); S0 = SumInter(G, 0, J_left, J_right, b, appr_q)
            J_left , J_right = I1l, min(I1r, minbetdel - 1); S1 = SumInter(G, 0, J_left, J_right, b, appr_q)
        else: S0, S1 = 0, SumInter(G, 0, I1l, I1r, b, appr_q)
        return SumInter(G, 0, -b, b-1, b, appr_q) - S0 - S1

def Special0A(G, appr_q, appr_ainv, r0, b, Qfloor, Qceil, betasign, delsign):
    # G is a list of ints.
    # appr_q and appr_ainv are ints that were originally in a diophapp_t.
    # The rest are ints.
    
    # In the original code, J_left and J_right were combined into an Iint object.
    
    if 0 < r0 < appr_q:
        if delsign:
            if delsign  >  0: J_left, J_right = -Qfloor, b - 1
            else:             J_left, J_right = -b, -Qceil
        else:
            if betasign >= 0: J_left, J_right = -b, b - 1
            else:             J_left, J_right = 1, 0
    else:
        if (delsign == 0) or (betasign == 0): J_left, J_right = 1, 0
        elif betasign < 0:
            if delsign < 0:
                J_left, J_right = -b     , -Qceil; S  = SumInter(G, -r0 * appr_ainv, J_left, J_right, b, appr_q)
                J_left, J_right = 1      , b - 1 ; S += SumInter(G, -r0 * appr_ainv, J_left, J_right, b, appr_q)
                return S
            elif delsign > 0:
                J_left, J_right = -b     , -1    ; S  = SumInter(G, -r0 * appr_ainv, J_left, J_right, b, appr_q)
                J_left, J_right = -Qfloor, b - 1 ; S += SumInter(G, -r0 * appr_ainv, J_left, J_right, b, appr_q)
                return S
        else:
            if delsign > 0: J_left, J_right = -Qfloor, -1
            else:           J_left, J_right = 1, -Qceil
    return SumInter(G, -r0 * appr_ainv, J_left, J_right, b, appr_q)

def RaySum(f, q, b, deltasign, foff):
    # f is a list of ints
    # The rest are ints
    if deltasign < 0: return sum(f[n] for n in range(foff+q, foff+b  ,  q))
    if deltasign > 0: return sum(f[n] for n in range(foff-q, foff-b-1, -q))
    return 0

def SumTable(f, b, a0, q, F, rho, sigma, foff):
    # f, F, rho, and sigma are lists of ints
    # b, a0, and q are ints
    # assume: q<=2b
    # assume: f is an array with >= 2b entries at f[-b] ... f[b-1]
    # assume: F is an array with >= 2b entries at F[0] ... F[2b-1]
    # assume: rho and sigma are arrays with >=q and >=q+1 entries (respectively) at rho[0..q-1] and sigma[0..q]
    # assume q does not divide a0
    for n in range(-b, q-b): F[n+b] = f[n+foff]
    for n in range(q-b,  b): F[n+b] = f[n+foff] + F[n-q+b]
    
    a0mod = modl(a0,q)
    r = modl(a0mod * (b-q), q)
    for n in range(b-q, b):
        rho[r] = F[n+b]
        r += a0mod
        if r >= q: r -= q
    
    sigma[0] = 0
    if q > 1: sigma[1] = 0
    for r in range(1, q): sigma[r+1] = sigma[r] + rho[q-r]

def SumByLin(f, g, x, mcirc, ncirc, a, b, foff, goff):
    # f and g are lists of ints
    # The rest are ints
    # Precondition: f and g store the values -1, 0, 1 at entries f[-a],...,f[a-1] and g[-b],...,g[b-1]
    S = LinearSum(f, g, a, b, x, mcirc, ncirc, foff, goff)
    Qfloor, Qceil = 0, 0
    
    if a == 0 or b == 0: return 0
    
    den1 = mcirc * ncirc
    denm = mcirc * den1
    denn = ncirc * den1
    
    appr_a, appr_q, appr_ainv = diophapp(-x, denn, 2*b)  # compute approximation to alpha2 = -x/denn
    
    denmq = appr_q * denm
    delnum = -x * appr_q - denn * appr_a
    delsign = sgn(delnum)
    
    G     = [0] * 2*b
    rho   = [0] * appr_q
    sigma = [0] * (appr_q + 1)
    
    SumTable(g, b, appr_a, appr_q, G, rho, sigma, goff)
    
    Z = RaySum(g, appr_q, b, sgn(delnum), goff)
    delnum_t_mcirc = delnum * mcirc
    R0num = x * (mcirc + a)
    R0num_mod_denm_t_q = (R0num % abs(denm)) * appr_q
    x_mod_denm_t_q = (x % abs(denm)) * appr_q
    a_t_ncirc = ncirc * appr_a
    A2 = -(mcirc-a) * appr_a
    x_t_q = x * appr_q
    m = -a
    m_p_mcirc = mcirc - a
    while m < a:
        if f[m+foff]:
            r0 = (2*R0num_mod_denm_t_q + denm) // (2*denm)
            betanum = R0num_mod_denm_t_q - r0 * denm
            betsign = sgn(betanum)
            if delnum:
                betanum_t_ncirc = betanum * ncirc
                c = betanum_t_ncirc
                d = delnum_t_mcirc
                if d < 0: c, d = -c, -d
                if c >= 0: Qfloor = c//d               ; Qceil  = Qfloor + (1 if c % d else 0)
                else:      Qceil  = (c + (-c % d)) // d; Qfloor = Qceil  - (1 if c % d else 0)  # Qceil is c/d rounded towards 0
            T = sigma[r0]
            if appr_q > 1: T += SpecialL2L1(G, x_t_q, appr_q, appr_ainv, R0num, denm, r0, A2, ncirc, a_t_ncirc, m_p_mcirc, b, Qfloor, Qceil, betsign, delsign)
            else:          T += Special00(  G, x    , appr_q, appr_a   , R0num, denm, r0,     ncirc,            m_p_mcirc, b, Qfloor, Qceil,          delsign)
            T +=                Special0A(  G,        appr_q, appr_ainv,              r0,                                  b, Qfloor, Qceil, betsign, delsign)
            if 0 < r0 < appr_q: T += Z
            S += f[m+foff] * T
        R0num_mod_denm_t_q -= x_mod_denm_t_q
        if R0num_mod_denm_t_q < 0: R0num_mod_denm_t_q += denmq
        m += 1
        m_p_mcirc += 1
        R0num -= x
        A2 -= appr_a
    
    return S

def DDSum(A, Ap, B, Bp, x, D, flag, a, b):
    # All arguments are ints.
    
    prl = isqrt(max(Ap,Bp))
    isprime = bytearray([0]) * (prl + 1)
    fillisprime(isprime, prl + 1)
    
    print((Ap-A+D-1)//D, "by", (Bp-B+D-1)//D)
    
    S = 0
    for m0 in range(A, Ap, D):
        m1 = min(m0 + D, Ap)
        mux = [0] * D
        fillmublock(mux, isprime, m0, m1 - m0)
        for n0 in range(B, Bp, D):
            n1 = min(n0 + D, Bp)
            muy = [0] * D
            fillmublock(muy, isprime, n0, n1 - n0)
            if flag:
                mlow = m0
                while mlow < m1:
                    mhigh = min(mlow + 2*a, m1)
                    mcirc = (mhigh + mlow) // 2
                    mdelt = (mhigh - mlow) // 2
                    nlow = n0
                    while nlow < n1:
                        nhigh = min(nlow + 2*b, n1)
                        ncirc = (nhigh + nlow) // 2
                        ndelt = (nhigh - nlow) // 2
                        S += SumByLin(mux, muy, x, mcirc, ncirc, mdelt, ndelt, mcirc-m0, ncirc-n0)
                        nlow = nhigh
                    mlow = mhigh
            else:
                # This else block is equivalent to
                # S += sum(sum(mux[m-m0] * muy[n-n0] * (x // (m*n)) for n in range(n0, n1)) for m in range(m0, m1))
                # but runs faster because we do less multiplication inside the sum and we skip terms with mux == 0.
                for m in range(m0, m1):
                    if mux[m - m0] != 0:
                        S += mux[m - m0] * sum(muy[n - n0] * (x // (m*n)) for n in range(n0, n1))
    return S

def LargeFree(x, v):
    # x and v are both ints
    S = 0
    Ap = v + 1
    C = 10
    D = 8
    
    sqtv = isqrt(v)
    
    acc = x * 6 * 16 * C * C * C
    end1 = isqrt(isqrt(acc))
    
    while Ap >= 2*D and Ap >= end1:
        Bp = Ap
        A = Ap - 2 * (Ap // (2*D))
        Az = A
        acc = x * 6 * 8 * C * C * C
        acc //= Az
        end2 = introot(acc, 3)
        
        while Bp >= 2*D and Bp >= end2:
            B = Bp - 2 * (Bp // (2*D))
            Bz = B
            a = introot((Az*Az*Az*Az//6)//x, 3)
            b = introot((Az*Bz*Bz*Bz//6)//x, 3)
            
            Delta = (1 + sqtv//max(2*a,2*b)) * max(2*a, 2*b)
            t0 = time()
            T1 = DDSum(A, Ap, B, Bp, x, Delta, 1, a, b)
            S += T1 * (1 if A == B else 2)
            t1 = time()
            print("Wall time", t1 - t0)
            print("Result:", T1)
            
            Bp = B
        S += 2 * DDSum(A, Ap, 1, Bp, x, sqtv + 1, 0, 0, 0)
        Ap = A
    return S + DDSum(1, Ap, 1, Ap, x, sqtv + 1, 0, 0, 0)

def SArr(S, isprime, x, r0, Delta, bigDelta, S0):
    # S and isprime are lists of ints
    # The rest are ints.
    
    funplist = [0] * bigDelta
    funpmark = [0] * bigDelta
    sqfprod  = [0] * bigDelta
    
    fillfactblock(funplist, funpmark, sqfprod, isprime, r0, Delta+1)
    
    Si = 0
    for r in range(r0, r0 + Delta + 1):
        Si += FacToSumMu(funplist[r-r0], funpmark[r-r0], 1, x//r, x//r, sqfprod[r-r0])
        S[r-r0] = Si + S0

def LargeNonFree(x, v, u):
    # All arguments are ints.
    n0 = u + 1
    r0 = x // (u+1) + 1
    Sum = 0
    sig = 0
    sqt1 = isqrt(max(u, x//v))
    
    Delta = sqt1 + 1
    bigDelta = Delta + 1
    sqt2 = isqrt(max(u, x//v + bigDelta))
    safeDelta = sqt2 + 1
    
    isprime = bytearray([0]) * (safeDelta + 1)
    mup     =           [0]  * (    Delta + 1)
    S       =           [0]  * ( bigDelta    )
    
    fillisprime(isprime, safeDelta + 1)
    
    SArr(S, isprime, x, r0, Delta, bigDelta, 1)
    for n in range(u, v, -1):
        #print("\b"*80, n, u, v, end='    ', flush=False)
        if n < n0:
            n0 = max(n0 - (Delta + 1), 1)
            fillmublock(mup, isprime, n0, Delta + 1)
        rororo = mup[n - n0] * ((x//n)//n)
        sig += rororo
        while x // n >= r0 + bigDelta:
            r0 += bigDelta
            SArr(S, isprime, x, r0, Delta, bigDelta, S[bigDelta-1])
        Sum += mup[n-n0] * rororo + 2 * mup[n-n0] * (S[x//n-r0] - sig)
    print()
    
    return Sum

def Mertens(x):
    # x is an int
    
    u = isqrt(x)
    v = introot(x*x, 5) // 3
    
    t0 = time()
    print("v = %d, u = %d" % (v,u))
    
    Bu = BruteM(u)
    print("BruteM(u) =", Bu)
    t1 = time()
    print("Wall time:", t1 - t0)
    
    LF = LargeFree(x, v)
    print("LargeFree(x,v) =", LF)
    t2 = time()
    print("Wall time:", t2 - t1)
    
    LNF = LargeNonFree(x, v, u)
    print("LargeNonFree(x,v,u) =", LNF)
    t3 = time()
    print("Wall time:", t3 - t2)
    
    return 2 * Bu - LNF - LF

"""
import cProfile
cProfile.run("print(Mertens(int(argv[1])))", sort="tottime")
"""
print(Mertens(int(argv[1])))
#"""
