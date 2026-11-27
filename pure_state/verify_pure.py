"""Numerical diagnostics for general pure Fock superpositions (not certificates)."""
import numpy as np
from scipy.special import roots_laguerre, eval_genlaguerre, gammaln

class Quadrature:
    def __init__(self, n, nr=120, nt=256):
        self.n = n
        t, self.w = roots_laguerre(nr)
        theta = np.arange(nt)*2*np.pi/nt
        self.q_basis = []
        self.w_basis = []
        for j in range(n+1):
            self.q_basis.append(np.exp(j/2*np.log(2*t[:,None])-gammaln(j+1)/2+1j*j*theta[None,:]))
        self.q_basis = np.array(self.q_basis).reshape(n+1,-1)
        for m in range(n+1):
            for k in range(m+1):
                d = m-k
                self.w_basis.append(((-1)**k*np.exp((gammaln(k+1)-gammaln(m+1))/2)*eval_genlaguerre(k,d,2*t)[:,None]*(np.sqrt(2*t)[:,None]**d)*np.exp(1j*d*theta[None,:])).reshape(-1))
        self.w_basis = np.array(self.w_basis)
        self.nt = nt

    def eval(self,c):
        c = np.array(c,dtype=complex)
        c /= np.linalg.norm(c)
        q = np.abs(c.conj()@self.q_basis).reshape(-1,self.nt).mean(axis=1)@self.w
        co = np.array([(1 if m==k else 2)*c[m].conjugate()*c[k] for m in range(self.n+1) for k in range(m+1)])
        w = np.abs((co@self.w_basis).real).reshape(-1,self.nt).mean(axis=1)@self.w
        return w,q*q

if __name__ == '__main__':
    rng = np.random.default_rng(20261127)
    for n in [1,2,4,8]:
        q = Quadrature(n)
        q2 = Quadrature(n,180,512)
        best = (0,None)
        for _ in range(100):
            c = rng.normal(size=n+1)+1j*rng.normal(size=n+1)
            a,b = q.eval(c)
            if a/b > best[0]:
                best = (a/b,c)
        a,b = q2.eval(best[1])
        print(n,'random maximum ratio',best[0],'refined',a/b,flush=True)
        for j in [1,n]:
            c = np.zeros(n+1,complex)
            c[0] = 1
            c[j] = 0.05
            a,b = q2.eval(c)
            print('vacuum ray',j,'A',a,'B',b,'gap',b-a,flush=True)
