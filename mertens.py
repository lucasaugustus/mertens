#! /usr/bin/env python3

# An implementation of the Helfgott-Thompson algorithm for computing the Mertens function.
# See https://arxiv.org/abs/2101.08773 for details.
# This file is a translation of the ancillary files from that link.

from labmath import introot, isqrt
from time import time
from sys import argv

# For details on how plist and pmark work, see the reference, section 6, subheading "Factorizing via a sieve in little space."

def sgn(x): return (x > 0) - (x < 0)
def mod(a, b): return a % abs(b)
def modl(a, b): return (a % abs(b)) if a >= 0 else (b - 1 - (-a-1)%abs(b))
def FlCong(n, a, q): return n - mod(n - a, q)

def fillisprime(isprime, N):
    # sets isprime[n]=0 if n is composite, isprime[n]=1 i n is prime for 2<=n<N
    for i in range(2, N): isprime[i] = 1
    i = 2
    while i*i < N:      # TODO: Try "for i in range(isqrt(..."
        if isprime[i]:
            j = i
            while j*i < N:
                isprime[j*i] = 0
                j += 1
        i += 1

def fillmublock(mun, isprime, n, m):
    # fills mun[0], mun[1],... with mu(n), mu(n+1), ..., mu(n+m-1)
    # assumes isprime is filled and valid up to and including sqrt(n+m)
    # convention: mu(n)=0
    
    tabla = [1] * m
    
    for i in range(m):
        if (i + n) % 2: mun[i] = 1
        elif (i + n) % 4:
            mun[i] = -1
            tabla[i] = 2
        else: mun[i] = 0
    
    p = 3
    while p*p < n+m:    # TODO: Try "for p in range(isqrt(..."
        if isprime[p]:
            red = n % p
            for j in range(p-red if red else 0, m, p):
                if ((j+n) // p) % p:
                    mun[j] = -mun[j]
                    tabla[j] *= p
                else: mun[j] = 0
        p += 1
    
    for i in range(m):
        if mun[i] != 0 and tabla[i] != n+i:
            mun[i] = -mun[i]

def prefillfact(funplist, funpmark, sqfprod, tabla, isprime, n, P, pmax):
    # In the original code, funplist and funpmark were combined into a single array whose elements were a compound type.
    # fill out an array with P elements, stating which among n,n+1,...,n+P-1 are divisible by primes p|P, and to which powers
    
    for j in range(P):
        tabla[j] = 1
        sqfprod[j] = 1
    
    for j in range(P):
        funplist[j] = 0
        funpmark[j] = 0
    
    for p in range(2, pmax+1):
        if isprime[p]:
            pk = p.bit_length() - 1             # floor(log2(p))
            nmark = 1 << (pk - 1)
            trailp = ((1 << pk) - 1) & p         # Given in the C++ as (p & ~((~0ul)<<pk)).  This takes off the leading 1.
            k, d = 1, p
            while P % d == 0:
                j0 = d if n == 0 else ((n+d-1) // d) * d - n
                for j in range(j0, P, d):
                    if k == 1:
                        funpmark[j] <<= pk; funpmark[j] |= nmark
                        funplist[j] <<= pk; funplist[j] |= trailp
                        sqfprod[j] *= p
                    tabla[j] *= p
                k += 1
                d *= p

def fillfactblock(funplist, funpmark, sqfprod, isprime, n, m, off):
    # In the original code, funplist and funpmark were combined into a single array whose elements were a compound type.
    # In the original code, arithmetic was done on the pointers fun and sqfprod by a function higher up in the call stack.
    # Python does not do that, so I have added the argument off to handle the offsetting explicitly.
    # fills fun[0], fun[1],...  with the list of prime factors of n, n+1, ..., n+m-1
    # (no exponents)
    # fills sqfprod[0], sqfprod[1],... with the products of prime divisors of n, n+1,...
    # assumes isprime is filled and valid up to and including sqrt(n+m-1)
    # convention: 1 factorizes into nothing; the factorization of 0 could be goodness knows what
    # assumes littleendianness
    P, pmax = 2*2*2*3*3*5*7*11, 11
    
    tabla        = [0] * m
    minitabla    = [0] * P
    minisqfprod  = [0] * P
    minifunplist = [0] * P
    minifunpmark = [0] * P
    
    # In the original code, minifunplist and minifunpmark were combined into a single array whose elements were a compound type.
    
    prefillfact(minifunplist, minifunpmark, minisqfprod, minitabla, isprime, n, P, pmax)
    
    # TODO: Instead of working on minitabla, minisqfprod, and minifun and then copying them into tabla, sqfprod, and fun,
    # work on tabla, sqfprod, and fun directly.
    
    for j in range(0, m, P):
        many = min(P, m - j)
        for k in range(many):    tabla[j + k      ] =    minitabla[k]      # TODO: try slices and one single for-loop
        for k in range(many):  sqfprod[j + k + off] =  minisqfprod[k]
        for k in range(many): funplist[j + k + off] = minifunplist[k]
        for k in range(many): funpmark[j + k + off] = minifunpmark[k]
    
    # first, we complete the factorization for small primes, starting where prefillfact stopped
    for p in range(2, pmax+1):
        if isprime[p]:
            dold, d = 1, p
            while P % d == 0: dold, d = d, d*p
            roof = (n + m - 1) // p
            while dold <= roof:
                j0 = d if n == 0 else ((n + d - 1) // d) * d - n
                for j in range(j0, m, d): tabla[j] *= p
                dold, d = d, d*p
    
    # now for the larger primes...
    p = pmax + 2
    while p*p <= n + m - 1:
        if isprime[p]:
            pk = p.bit_length() - 1             # floor(log2(p))
            nmark = 1 << (pk - 1)
            trailp = ((1 << pk) - 1) & p         # Given in the C++ as (p & ~((~0ul)<<pk)).  This should take off the leading 1.
            k, dold, d, roof = 1, 1, p, (n + m - 1) // p
            while dold <= roof:
                j0 = d if n == 0 else ((n + d - 1) // d) * d - n
                for j in range(j0, m, d):
                    if k == 1:
                        funpmark[j + off] <<= pk; funpmark[j + off] |= nmark
                        funplist[j + off] <<= pk; funplist[j + off] |= trailp
                        sqfprod[j + off] *= p
                    tabla[j] *= p
                k, dold, d = k+1, d, d*p
        p += 2
    
    for j in range(m):
        if tabla[j] != n + j:
            p = (n + j) // tabla[j]
            pk = p.bit_length() - 1         # floor(log2(p))
            # The RHS of this next assignment is given in the original C++ as ((fun[j].pmark<<1)|1ul)<<(pk-1).
            # It appends to fun[j].pmark the second-greatest power of 2 that is <= p.
            # Arithmetically, this is equivalent to (fun[j].pmark * 2 + 1) * 2**(pk-1).
            funpmark[j + off] = ((funpmark[j + off] << 1) | 1) << (pk-1)
            # The RHS of this next assignment is given in the original C++ as (fun[j].plist<<pk) | (p & ~((~0ul)<<pk)).
            # The second operand of the bitwise OR takes off the leading 1 from p.
            # The effect of the whole assignment is to append p, except for its leading bit, to fun[j].plist.
            funplist[j + off] = (funplist[j + off] << pk) | (((1 << pk) - 1) & p)
            sqfprod[j + off] *= p

def FacToSumMu(fplist, fpmark, m, mc, a, n):
    # In the original code, fplist and fpmark were combined into a single compound data type.
    if m > a      : return 0
    if fpmark == 0: return 1
    if mc >= n    : return 0
    
    k = (fpmark & -fpmark).bit_length()    # 1 + # of trailing zeros in f.pmark.  Given in the C++ as __builtin_ctzl(f.pmark)+1.
    fpmark >>= k
    p = (1 << k) | (fplist & ((1 << k) - 1))                            # Given in the C++ as (1ul<<k)|(f.plist & ~((~0ul)<<k)).
    fplist >>= k
    
    return FacToSumMu(fplist, fpmark, m, mc*p, a, n) - FacToSumMu(fplist, fpmark, m*p, mc, a, n)

def diophapp(alpa, alpq, Q):
    # constructs approximation a/q, q<=Q, to alpha, and finds a^{-1} mod q
    # assume Q>1
    
    b = alpa // alpq
    p, q, pmin, qmin, s = b, 1, 1, 0, 1
    while q <= Q:
        if alpa == b * alpq: return (p, q, mod(-qmin * s, q))
        
        alpa, alpq = alpq, alpa - b*alpq
        b = alpa // alpq
        
        p, pmin = b * p + pmin, p
        q, qmin = b * q + qmin, q
        
        s = -s
    
    return (pmin, qmin, mod(q * s, qmin))

def LinearSum(f, g, a, b, x, m0, n0, foff, goff):
    # In the original code, arithmetic was done on the pointers f and g by a function higher up in the call stack.
    # Python does not do that, so I have added the arguments foff and goff to handle the offsetting explicitly.
    # return \sum_{(m,n)\in U} f[m] g[n] (floor(alpha[0]+alpha[1] m) + floor(alpha[2] n)), where U = [-a,a) \times [-b,b)
    # alpha[0] = x/m_0 n_0, alpha[1] = -x/m_0^2 n_0, alpha[2] = -x/m_0 n_0^2
    
    uden = m0 * m0 * n0
    unum = x * (m0 + a)
    S1, S10 = 0, 0
    m, aoff = foff - a, a + foff
    while m < aoff:
        S1 += f[m] * (unum // uden)
        S10 += f[m]
        m += 1
        unum -= x
    
    uden = m0 * n0 * n0
    unum = x * b
    S2, S20 = 0, 0
    n, boff = goff - b, b + goff
    while n < boff:
        S2 += g[n] * (unum // uden)
        S20 += g[n]
        n += 1
        unum -= x
    
    return S1 * S20 + S10 * S2

def BruteDoubleSum(m0, m1, n0, n1, f, g, x):
    # This is equivalent to the epic one-liner
    #return sum(f[m - m0] * g[n - n0] * (x // (m*n)) for n in range(n0, n1) for m in range(m0, m1))
    # but faster because we skip all terms with f[m - m0] == 0 and because we do less multiplication.
    S = 0
    for m in range(m0, m1):
        # We could replace the contents of this for-loop with the epic one-liner
        #if f[m - m0] != 0: S += f[m - m0] * sum(g[n - n0] * (x // (m*n)) for n in range(n0, n1)),
        # but that turns out to be slower on my system.
        if f[m - m0] == 1:
            for n in range(n0, n1):
                S += g[n - n0] * (x // (m*n))
        elif f[m - m0] == -1:
            for n in range(n0, n1):
                S -= g[n - n0] * (x // (m*n))
    return S

def SumTable(f, b, a0, q, F, rho, sigma, foff):
    # In the original code, arithmetic was done on the pointer f by a function higher up in the call stack.
    # Python does not do that, so I have added the argument foff to handle the offsetting explicitly.
    # Additionally, that higher-up function added the argument b to the pointer F before passing the result as F.
    # We also handle that explicitly here, but the necessary arguments already existed.
    # assume: q<=2b
    # assume: F and f are arrays with >= 2b entries at F[-b] ... F[b-1]
    # assume: rho and sigma are arrays with >=q and >=q+1 entries (respectively) at rho[0..q-1] and sigma[0..q]
    # assume q does not divide a0
    
    #for n in range( -b, q-b): F[n + b] = f[n + foff]
    #for n in range(q-b,  b ): F[n + b] = f[n + foff] + F[n - q + b]
    foffmb = foff - b
    for n in range(0,  q ): F[n] = f[n + foffmb]
    for n in range(q, 2*b): F[n] = f[n + foffmb] + F[n - q]
    
    a0mod = modl(a0, q)
    r = modl(a0mod * (b-q), q)
    for n in range(2*b-q, 2*b):
        rho[r] = F[n]
        r += a0mod
        if r >= q: r -= q
    
    sigma[0] = 0
    if q > 1: sigma[1] = 0
    for r in range(1, q): sigma[r + 1] = sigma[r] + rho[q - r]

def SumInter(G, r, J_left, J_right, b, q):
    # In the original code, J_left and J_right were combined into a single compound data type.
    # In the original code, a function higher up in the call stack added the argument b to the pointer G and passed the result
    # as G.  Since Python does not do pointer arithmetic, we handle the offset explicitly.
    if J_left > J_right: return 0
    
    r0 = FlCong(    J_left - 1   , r, q)
    r1 = FlCong(min(J_right, b-1), r, q)
    
    if r0 >  r1: return 0
    if r1 <  -b: return 0
    if r0 >= -b: return G[r1 + b] - G[r0 + b]
    return G[r1 + b]

def QuadIneqZ(a, b, c):
    Delta = b*b - 4*a*c
    
    if Delta < 0: return (1, 0) # empty interval
    
    Q = isqrt(Delta)
    
    if a < 0         : return (-((-b - Q      ) // (-2*a)),  (( b - Q      ) // (-2*a)))
    elif Q*Q != Delta: return (-(( b + Q      ) // ( 2*a)),  ((-b + Q      ) // ( 2*a)))
    else             : return ( ((-b - Q + 2*a) // ( 2*a)), -(( b - Q + 2*a) // ( 2*a)))

def SpecialL2L1(G, xq, appr_a, appr_q, appr_ainv, R0num, R0den, r0, A2, ncirc, ancirc, m, b, Qfloor, Qceil, betsign, delsign):
    # In the original code, appr_a, appr_q, and appr_ainv were combined into a single compound data type.
    # In the original code, the function calling this one added the argument b to the pointer G before passing the result here.
    # Since Python does not do pointer arithmetic, we handle the offset explicitly... but since G is never accessed by element
    # in this function (merely passed to a subroutine), that has no effect here.
    
    # In the original code, J_left and J_right were combined into a single compound data type, as were JI_left and JI_right.
    
    # first compute the contribution of n such that a_0(n-n_0)+r_0 = 1 mod q
    
    gamma1 = (ancirc - (R0num // R0den) * appr_q - r0) * m
    JI_left, JI_right = QuadIneqZ(A2, gamma1, xq)
    JI_left  -= ncirc
    JI_right -= ncirc
    if   delsign >  0: J_left, J_right = -b       , -Qfloor - 1
    elif delsign <  0: J_left, J_right = 1 - Qceil, b - 1
    elif betsign >= 0: J_left, J_right = 1        , 0
    else             : J_left, J_right = -b       , b - 1
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
    J_left, J_right  = -b, b - 1
    S += SumInter(G, r, J_left, J_right, b, appr_q) - SumInter(G, r, JI_left, JI_right, b, appr_q)
    
    return S

def Special00(G, x, appr_a, appr_q, appr_ainv, R0num, R0den, r0, ncirc, m, b, Qfloor, Qceil, delsign):
    # In the original code, appr_a, appr_q, and appr_ainv were combined into a single compound data type.
    # In the original code, the function calling this one added the argument b to the pointer G before passing the result here.
    # Since Python does not do pointer arithmetic, we handle the offset explicitly... but since G is never accessed by element
    # in this function (merely passed to a subroutine), that has no effect here.
    
    # In the original code, the _left and _right variables were combined into compound data types.
    I0_left, I0_right, I1_left, I1_right, J_left, J_right = 0, 0, 0, 0, 0, 0
    
    R0floor = (R0num // R0den)
    minbetdel = (-Qfloor - 1) if delsign > 0 else (-Qceil + 1)
    # minbetdel = floor(-beta/delta)+1
    
    if not appr_a:
        flank0 = ((x//m) // (R0floor+r0  )) - ncirc
        flank1 = ((x//m) // (R0floor+r0+1)) - ncirc
        if delsign > 0:
            J_left , J_right = -b    , min(flank0, minbetdel)    ; S0 = SumInter(G, 0, J_left, J_right, b, appr_q)
            J_right, J_left  = flank1,             minbetdel + 1 ; S1 = SumInter(G, 0, J_left, J_right, b, appr_q)
        elif delsign < 0:
            J_right, J_left  = flank0,             minbetdel     ; S0 = SumInter(G, 0, J_left, J_right, b, appr_q)
            J_left , J_right = -b    , min(flank1, minbetdel - 1); S1 = SumInter(G, 0, J_left, J_right, b, appr_q)
        else:
            S0 = 0
            J_left , J_right = -b    ,     flank1                ; S1 = SumInter(G, 0, J_left, J_right, b, appr_q)
        return S0 + S1
    else:
        gamma1 = (appr_a*ncirc - R0floor*appr_q - r0 - 0) * m
        I0_left, I0_right = QuadIneqZ(-appr_a*m, gamma1, x*appr_q)
        I0_left  -= ncirc
        I0_right -= ncirc
        gamma1 = (appr_a*ncirc - R0floor*appr_q - r0 - 1) * m
        I1_left, I1_right = QuadIneqZ(-appr_a*m, gamma1, x*appr_q)
        I1_left  -= ncirc
        I1_right -= ncirc
        if delsign > 0:
            J_left , J_right = I0_left , min(I0_right, minbetdel    ); S0 = SumInter(G, 0, J_left, J_right, b, appr_q)
            J_right, J_left  = I1_right, max(I1_left , minbetdel + 1); S1 = SumInter(G, 0, J_left, J_right, b, appr_q)
        elif delsign < 0:
            J_right, J_left  = I0_right, max(I0_left , minbetdel    ); S0 = SumInter(G, 0, J_left, J_right, b, appr_q)
            J_left , J_right = I1_left , min(I1_right, minbetdel - 1); S1 = SumInter(G, 0, J_left, J_right, b, appr_q)
        else:
            S0 = 0
            S1 = SumInter(G, 0, I1_left, I1_right, b, appr_q)
        J_left, J_right = -b, b - 1
        return SumInter(G, 0, J_left, J_right, b, appr_q) - S0 - S1

def Special0A(G, appr_a, appr_q, appr_ainv, r0, b, Qfloor, Qceil, betasign, delsign):
    # In the original code, appr_a, appr_q, and appr_ainv were combined into a single compound data type.
    # In the original code, the function calling this one added the argument b to the pointer G before passing the result here.
    # Since Python does not do pointer arithmetic, we handle the offset explicitly... but since G is never accessed by element
    # in this function (merely passed to a subroutine), that has no effect here.
    
    # In the original code, J_left and J_right were combined into a single compound data type.
    
    if 0 < r0 < appr_q:
        if delsign:
            if delsign > 0: J_left , J_right = -Qfloor, b-1
            else          : J_right, J_left  = -Qceil , -b
        else:
            if betasign >= 0: J_left, J_right = -b, b-1
            else            : J_left, J_right =  1, 0
    else:
        if (not delsign) or (not betasign): J_left, J_right = 1, 0
        elif betasign < 0:
            if delsign < 0:
                J_left, J_right = -b     , -Qceil; S  = SumInter(G, -r0 * appr_ainv, J_left, J_right, b, appr_q)
                J_left, J_right =  1     , b - 1 ; S += SumInter(G, -r0 * appr_ainv, J_left, J_right, b, appr_q)
                return S
            elif delsign > 0:
                J_left, J_right = -b     ,    -1 ; S  = SumInter(G, -r0 * appr_ainv, J_left, J_right, b, appr_q)
                J_left, J_right = -Qfloor, b - 1 ; S += SumInter(G, -r0 * appr_ainv, J_left, J_right, b, appr_q)
                return S
        else:
            if delsign > 0: J_left , J_right = -Qfloor, -1
            else          : J_right, J_left  = -Qceil ,  1
    return SumInter(G, -r0 * appr_ainv, J_left, J_right, b, appr_q)

def RaySum(f, q, b, deltasign, off):
    # In the original code, arithmetic was done on the pointer f by a function higher up in the call stack.
    # Python does not do that, so I have added the argument off to handle the offsetting explicitly.
    # We could replace this function with the epic one-liner
    #return 0 if deltasign == 0 else sum(f[n] for n in (range(off+q, off+b, q) if deltasign < 0 else range(off-q, off-b-1, -q)))
    # but that turns out to be slower, at least when executed on my machine under PyPy3.
    S = 0
    
    if deltasign < 0:
        for n in range(off + q, off + b, q):
            S += f[n]
    if deltasign > 0:
        for n in range(off - q, off - b - 1, -q):
            S += f[n]
    
    return S

def SumByLin(f, g, x, mcirc, ncirc, a, b, foff, goff):
    # In the original code, arithmetic was done on the pointers f and g by a function higher up in the call stack.
    # Python does not do that, so I have added the arguments foff and goff to handle the offsetting explicitly.
    # Precondition: f and g store the values -1, 0, 1 at entries f[-a],...,f[a-1] and g[-b],...,g[b-1]
    S = LinearSum(f, g, a, b, x, mcirc, ncirc, foff, goff)
    Qfloor, Qceil = 0, 0
    
    if a == 0 or b == 0: return 0
    
    den1 = mcirc * ncirc
    denm = mcirc * den1
    denn = ncirc * den1
    
    appr_a, appr_q, appr_ainv = diophapp(-x, denn, 2*b)     # compute approximation to alpha2 = -x/denn
    
    denmq = appr_q * denm
    delnum = -x * appr_q - appr_a * denn
    # delta = delnum/dennq = -x/mcirc ncirc^2 - a/q
    delsign = sgn(delnum)
    
    G     = [0] * (2*b)
    rho   = [0] *  appr_q
    sigma = [0] * (appr_q + 1)
    
    SumTable(g, b, appr_a, appr_q, G, rho, sigma, goff)
    
    Z = RaySum(g, appr_q, b, sgn(delnum), goff)
    delnum_t_mcirc = delnum * mcirc
    R0num = x * (mcirc + a)
    R0num_mod_denm_t_q = mod(R0num, denm) * appr_q
    x_mod_denm_t_q = mod(x, denm) * appr_q
    a_t_ncirc = appr_a * ncirc
    A2 = -appr_a * (mcirc - a)
    x_t_q = x * appr_q
    m, m_p_mcirc = -a, mcirc - a
    while m < a:
        if f[m + foff]:
            #    R0num/denm = R0 = alpha_0 + alpha_1 m*
            r0 = (2 * R0num_mod_denm_t_q + denm) // (2 * denm)
            # r0 = floor({R_0} q + 1/2)
            # beta = betanum/(denm*q) = {R_0} - r_0/q
            betanum = R0num_mod_denm_t_q - r0 * denm
            betsign = sgn(betanum)
            if delnum:
                betanum_t_ncirc = betanum * ncirc
                Qfloor = betanum_t_ncirc // delnum_t_mcirc
                Qceil = Qfloor + (1 if betanum_t_ncirc % delnum_t_mcirc else 0)
            T = sigma[r0]
            if appr_q > 1: T += SpecialL2L1(G, x_t_q, appr_a, appr_q, appr_ainv, R0num, denm, r0, A2, ncirc, a_t_ncirc, m_p_mcirc, b, Qfloor, Qceil, betsign, delsign)
            else:          T += Special00  (G, x    , appr_a, appr_q, appr_ainv, R0num, denm, r0,     ncirc,            m_p_mcirc, b, Qfloor, Qceil,          delsign)
            T +=                Special0A  (G,        appr_a, appr_q, appr_ainv,              r0,                                  b, Qfloor, Qceil, betsign, delsign)
            if 0 < r0 < appr_q: T += Z
            S += f[m + foff] * T
        R0num_mod_denm_t_q -= x_mod_denm_t_q
        if R0num_mod_denm_t_q < 0: R0num_mod_denm_t_q += denmq
        m += 1
        m_p_mcirc += 1
        R0num -= x
        A2 -= appr_a
    
    return S

def DoubleSum(m0, m1, n0, n1, a, b, mux, muy, x):
    # checked
    # assumes n1-n0 and m1-m0 are even
    S = 0
    
    mlow = m0
    while mlow < m1:
        mhigh = min(mlow + 2 * a, m1)
        mcirc = (mhigh + mlow) // 2
        mdelt = (mhigh - mlow) // 2
        nlow = n0
        while nlow < n1:
            nhigh = min(nlow + 2 * b, n1)
            ncirc = (nhigh + nlow) // 2
            ndelt = (nhigh - nlow) // 2
            S += SumByLin(mux, muy, x, mcirc, ncirc, mdelt, ndelt, mcirc - m0, ncirc - n0)
            nlow = nhigh
        mlow = mhigh
    
    return S

def DDSum(A, Ap, B, Bp, x, D, flag, a, b):
    S = 0
    prl = isqrt(max(Ap, Bp))
    isprime = bytearray([0]) * (prl + 1)
    fillisprime(isprime, prl + 1)
    
    print("%ld by %ld" % ((Ap-A+D-1)//D, ((Bp-B+D-1)//D)))
    
    # TODO: Look into using arrays of signed chars/shorts for mux and muy.
    
    for m0 in range(A, Ap, D):
        m1 = min(m0 + D, Ap)
        mux = [0] * D
        fillmublock(mux, isprime, m0, m1 - m0)
        for n0 in range(B, Bp, D):
            n1 = min(n0 + D, Bp)
            muy = [0] * D
            fillmublock(muy, isprime, n0, n1 - n0)
            if flag: S +=      DoubleSum(m0, m1, n0, n1, a, b, mux, muy, x)
            else:    S += BruteDoubleSum(m0, m1, n0, n1,       mux, muy, x)
    
    return S

def LargeFree(x, v):
    S, C, D = 0, 10, 8
    sqtv = isqrt(v)
    Ap = v + 1
    end1 = isqrt(isqrt(x * 6 * 16 * C * C * C))
    
    while 2 * D <= Ap >= end1:
        Bp = Ap
        A = Ap - 2 * (Ap // (2*D))
        end2 = introot((x * 6 * 8 * C * C * C) // A, 3)
        
        while 2*D <= Bp and Bp >= end2:
            B = Bp - 2 * (Bp // (2*D))
            az = introot((A*A*A*A//6)//x, 3); a = az
            bz = introot((A*B*B*B//6)//x, 3); b = bz
            
            Delta = (1 + sqtv // max(2*a, 2*b)) * max(2*a, 2*b)
            t0 = time()
            T1 = DDSum(A, Ap, B, Bp, x, Delta, 1, a, b)
            S += T1 * (1 if A == B else 2)
            t1 = time()
            print("Wall time %d" % (t1 - t0))
            print("Result: %d" % T1)
            
            Bp = B
        S += 2 * DDSum(A, Ap, 1, Bp, x, sqtv + 1, 0, 0, 0)
        Ap = A
    
    S += DDSum(1, Ap, 1, Ap, x, sqtv + 1, 0, 0, 0)
    return S

def BruteM(x):
    M, Delta = 0, isqrt(x)
    
    isprime = bytearray([0]) * (isqrt(x + Delta + 1) + 1)   # This differs from the original C++, which just had "Delta + 1".
    mu      =           [0]  * (Delta + 1)  # TODO: array of signed chars?
    fillisprime(isprime, Delta + 1)
    
    for n0 in range(1, x+1, Delta):
        fillmublock(mu, isprime, n0, Delta + 1)
        n = n0
        while n < n0 + Delta and n <= x:
            M += mu[n-n0]
            n += 1
    
    return M

def SArr(S, isprime, x, r0, Delta, bigDelta, S0):
    funplist = [0] * bigDelta
    funpmark = [0] * bigDelta
    sqfprod  = [0] * bigDelta
    offset   = [0] * ntasks
    # In the original code, fplist and fpmark were combined into a single array whose elements were of a compound data type.
    
    for j in range(ntasks): fillfactblock(funplist, funpmark, sqfprod, isprime, r0 + j*(Delta+1), Delta+1, j * (Delta+1))
    
    for j in range(ntasks):
        r1 = r0 + j * (Delta+1)
        Si = 0
        for r in range(r1, r1 + Delta + 1):
            Si += FacToSumMu(funplist[r - r0], funpmark[r - r0], 1, x//r, x//r, sqfprod[r - r0])
            S[r - r0] = Si
    
    offset[0] = S0
    for j in range(1, ntasks): offset[j] = offset[j-1] + S[j * (Delta+1) - 1]
    
    for j in range(ntasks):
        r1 = r0 + j * (Delta+1)
        for r in range(r1, r1 + Delta + 1): S[r-r0] += offset[j]

def LargeNonFree(x, v, u):
    n0 = u + 1
    r0 = (x // (u+1)) + 1
    Delta = isqrt(max(u, x//v)) + 1
    bigDelta = ntasks * (Delta+1)
    safeDelta = isqrt(max(u, (x//v) + bigDelta)) + 1
    
    isprime = [0] * (safeDelta + 1)
    mup     = [0] * (    Delta + 1)
    S       = [0] * ( bigDelta    )
    
    fillisprime(isprime, safeDelta + 1)
    
    SArr(S, isprime, x, r0, Delta, bigDelta, 1)
    Sum, sig = 0, 0
    for n in range(u, v, -1):
        if n < n0:
            n0 = max(n0 - (Delta+1), 1)
            fillmublock(mup, isprime, n0, Delta+1)
            #print(n, mup)
        rororo = mup[n-n0] * ((x//n)//n)
        sig += rororo
        while x//n >= r0 + bigDelta:
            r0 += bigDelta
            SArr(S, isprime, x, r0, Delta, bigDelta, S[bigDelta-1])
        Sum += mup[n-n0] * rororo + 2 * mup[n-n0] * (S[x//n-r0] - sig)
        #print("%d %d" % (n, Sum))
    
    return Sum

def Mertens(x):
    u = isqrt(x)
    sqr = x * x
    v = introot(sqr, 5) // 3
    
    # the constant 3 is fairly arbitrary; it's been fine-tuned (well, coarsely tuned)
    # v*=2; v/=5; is an alternative
    
    t0 = time()
    print("v = %d, u = %d" % (v, u))
    
    Bu = BruteM(u)
    print("BruteM(u) = %d" % Bu)
    
    t1 = time()
    print("Wall time: %d" % (t1 - t0))
    
    LF = LargeFree(x, v)
    print("LargeFree(x,v) = %d" % LF)
    
    t2 = time()
    print("Wall time: %d" % (t2 - t1))
    LNF = LargeNonFree(x, v, u)
    print("LargeNonFree(x,v,u) = %d" % LNF)
    print()
    
    t3 = time()
    print("Wall time: %d" % (t3 - t2))
    
    return 2 * Bu - LNF - LF

ntasks = 3

"""
import cProfile
cProfile.run("print(Mertens(int(argv[1])))", sort="tottime")
"""
print(Mertens(int(argv[1])))
#"""
