# Euler for calculating aᵉ (mod n): @power_mod(a,e,n) se [Stein,pp.34-36 §2.3.2]

# find primitive root of natural: @primitive_root(n)


# Find last n digits of aᵉ in base b by hand ... calculate aᵉ (mod bⁿ).
# 1. a^e' ← a^e (mod b^n)
# 2. ...

def crack_when_pq_close(n):
    """When p and q are Close (uses Fermat Factorization Method) p.62"""
    t = Integer(ceil(sqrt(n)))
    while True:
        k = t^2 - n
        if k > 0:
            s = Integer(int(round(sqrt(t^2 - n))))
            if s^2 + n == t^2:
                return t+s, t-s
        t += 1

def pollard_rho(n,g=lambda x: mod(x**2+1,n)):
    """Cormen, Thomas H.; Leiserson, Charles E.; Rivest, Ronald L. & Stein, Clifford (2009). "Section 31.9: Integer factorization". Introduction to Algorithms (third ed.). Cambridge, MA: MIT Press. pp. 975–980. ISBN 978-0-262-03384-8. (this section discusses only Pollard's rho algorithm). Bu taken from wikipedia.

    The algorithm takes as its inputs n, the integer to be factored; and g(x), a polynomial in x computed modulo n. In the original algorithm,

        g(x)=x^2-1  (mod n),

    but nowadays it is more common to use

        g(x)=x^2+1  (mod n)

    """

    x = 2
    y = 2
    d = 1

    while d == 1:
        x = g(x)
        y = g(g(y))
        d = gcd(x - y, n)

    if d == n:
        return None
    else:
        return d

def pollard(N, B=10^5, stop=10):
    """Pollard’s (p − 1)-Method

    Given a positive integer N and a bound B, this algorithm attempts to find a
    nontrivial factor g of N . (Each prime p | g is likely to have the property
    that p − 1 is B-power smooth.)
    """
    m = prod([p^int(math.log(B)/math.log(p))
              for p in prime_range(B+1)])
    for a in [2..stop]:
        x = (Mod(a,N)^m - 1).lift()
        if x == 0: continue
        g = gcd(x, N)
        if g != 1 or g != N: return g
    return 1


def crack_rsa(n, phi_n):
    """Factoring n Given φ(n)"""
    R.<x> = PolynomialRing(QQ)
    f = x^2 - (n+1 - phi_n)*x + n
    return [b for b, _ in f.roots()]


def rsa(bits):
    # from W. A. Stein, Elementary number theory: primes, congruences, and secrets a computational approach. New York, NY: Springer, 2009. p. 58.
    # only prove correctness up to 1024 bits
    proof = (bits <= 1024)
    p = next_prime(ZZ.random_element(2**(bits//2+1)),
            proof=proof)
    q = next_prime(ZZ.random_element(2**(bits//2+1)),
            proof=proof)
    n = p*q
    phi_n = (p-1)*(q-1)
    while True:
        e = ZZ.random_element(1,phi_n)
        if gcd(e,phi_n) == 1: break
    d = lift(Mod(e,phi_n)^(-1))
    return d, n, e

def rsa_e(bits,e):
    # only prove correctness up to 1024 bits
    proof = (bits <= 1024)
    while True:
        p = next_prime(ZZ.random_element(2**(bits//2+1)),
                proof=proof)
        q = next_prime(ZZ.random_element(2**(bits//2+1)),
                proof=proof)
        n = p*q
        phi_n = (p-1)*(q-1)
        if gcd(e,phi_n) == 1: break
    d = lift(Mod(e,phi_n)^(-1))
    return d, n, e

def encrypt(m, n, e):
    assert m < n # message must be in ℤ/nℤ
    return lift(Mod(m,n)^e)

def decrypt(c, d, n):
    return lift(Mod(c,n)^d)