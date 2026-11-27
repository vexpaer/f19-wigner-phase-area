"""Independent numerical and algebraic diagnostics, not a formal proof."""
import sympy as s
import numpy as np
from scipy.special import roots_laguerre, eval_laguerre, gammaln
from scipy.integrate import quad

n, x = s.symbols('n x', real=True)
P = 70*n**4 + 140*n**3 + 170*n**2 + 100*n + 24
coeff = [n*(n-1), -4*n**2, 6*n**2+6*n+2, -4*(n+1)**2, (n+1)*(n+2)]
assert s.expand(sum(c*c for c in coeff)-P)==0
assert s.expand((108*(n+s.Rational(1,2))**4-P).subs(n,x+1)) == 38*x**4+228*x**3+448*x**2+318*x+s.Rational(171,4)
assert s.expand((n+1)**2*(n+s.Rational(5,2))-(n+2)**2*(n+s.Rational(1,2))) == s.Rational(1,2)
a={0:s.Integer(1)}
for _ in range(4):
    b={}
    for k,v in a.items():
        for j,c in [(k+1,-(n+k+1)),(k,2*(n+k)+1),(k-1,-(n+k))]:
            b[j]=b.get(j,0)+v*c
    a=b
assert s.expand(a[0]-P)==0
print('All four exact symbolic identities passed.')
for k in range(1,41):
    endpoints=[0., *(roots_laguerre(k)[0]/2), np.inf]
    w=sum(abs(quad(lambda t: np.exp(-t)*eval_laguerre(k,2*t), l,r,epsabs=1e-11)[0]) for l,r in zip(endpoints,endpoints[1:]))
    p=float(P.subs(n,k))
    upper=(np.pi/(3*np.sqrt(2))*(6*p/32)**.25)**.5
    target=np.exp(k*np.log(2)+2*gammaln(k/2+1)-gammaln(k+1))
    assert w<=upper+1e-8 and upper<target
    print(k,w,upper,target)
