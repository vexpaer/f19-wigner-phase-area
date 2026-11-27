# Interference formula and the universal square-root-of-two bound

Research note, 2026-11-27. Analytic derivation for independent review, not Lean formalized. No claim of priority or resolution of F19.

References:
- C. N. Gagatsos, arXiv:2611.30969v1, Conjecture 1, Proposition 1, physical phase-space conventions and passive invariance.
- Z. Van Herstraeten and N. J. Cerf, *Wigner entropy conjecture and the interference formula in quantum phase space*, arXiv:2411.05562v2, Section IV (interference identity).

## Theorem (universal improvement)

For every single-mode state with finite \(M(\rho)=\int\sqrt{Q_\rho}\,d^2r\),
\[
\|W_\rho\|_1<\frac{\sqrt2}{8\pi}M(\rho)^2.
\]
For infinite \(M\), the non-strict extended-real bound holds trivially. The normalized constant \(\sqrt2\) is optimal for the corresponding *complex cross-Wigner* inequality, not asserted optimal for the self-Wigner inequality. This improves the previous factor \(2\) of Gagatsos and the uniform factor \((2+4\log2)/\pi\) in UNIVERSAL_BOUND.md. The sharp self-Wigner target remains 1.

In physical coordinates \(r=(x,p)\), set \(G(r)=\pi^{-1}e^{-|r|^2}\) (vacuum Wigner density), \(Q_\rho=W_\rho*G\), and for a normalized vector \(f\) put \(H(f)=M(|f\rangle\langle f|)/\sqrt{8\pi}\). Write \(W_{f,g}\) for the complex cross Wigner with convention
\[
W_{f,g}(x,p)=\pi^{-1}\int f(x+y)\overline{g(x-y)}e^{-2ipy}\,dy.
\]
We prove the stronger complex cross bound
\[
\|W_{f,g}\|_1\le\sqrt2\, H(f)H(g).
\]
The homogeneous version uses \(H(f)=(4\pi)^{-1}\int|\langle r|f\rangle|\,d^2r\) for arbitrary vectors. It agrees with the normalized formula.

### Step 1: squared interference is a nonnegative convolution

For normalized f,g let \(P=W_f*W_g\). Moyal's overlap identity and parity covariance give
\[
P(2r)=\int W_f(u)W_g(2r-u)\,d^2u
=\frac{1}{2\pi}|\langle f|D(r)\Pi D(r)^\dagger|g\rangle|^2
=\frac{\pi}{2}|W_{f,g}(r)|^2 .
\]
In the middle expression the displaced parity operator is self-adjoint and its Wigner covariance maps \(u\) to \(2r-u\). Thus \(P\ge0\). Under finite H hypotheses the original cross estimate or the usual Gaussian-window reconstruction ensures W_f,W_g are integrable; alternatively one can prove the result first for Schwartz vectors and extend by Gaussian-window L1 approximation. For normalized f,g, P has mass 1. Changing variables \(u=2r\) yields
\[
\int \sqrt P\,d^2u=4\sqrt{\frac{\pi}{2}}\,\|W_{f,g}\|_1.
\]
Let \(K=G*G\), a positive probability density. Since \(Q_f*Q_g=P*K\), Jensen for the square root and Tonelli give
\[
\int\sqrt P\le\int\sqrt{Q_f*Q_g}.
\]
This is strict when the right-hand side is finite: equality in pointwise Jensen would require P constant almost everywhere under a translate of the everywhere-positive K. P is integrable of mass 1, hence not a.e. constant. Finiteness of the right side follows from the next step.

### Step 2: conditional Wehrl controls the square-root convolution

Take the two-mode pure state obtained by a balanced passive beam splitter from \(f\otimes g\). Its joint Husimi density is
\[
q(x,y)=Q_f((x+y)/\sqrt2)Q_g((x-y)/\sqrt2),\qquad x,y\in\mathbb R^2.
\]
The orthogonal transformation has determinant of modulus 1, so
\[
\iint\sqrt{q(x,y)}\,d^2x\,d^2y=M(f)M(g).
\]
Its first marginal is \(q_1(x)=2(Q_f*Q_g)(\sqrt2 x)\). For a fixed x with q_1(x)>0, heterodyne measurement of the first output leaves a normalized conditional pure state on the second output. In particular \(q(y\mid x)=q(x,y)/q_1(x)\) is a genuine normalized single-mode Husimi density. This can be checked directly by contracting the two-mode vector with \(\langle x|\) in the first factor, and then applying the coherent resolution of identity. By Lieb–Solovej,
\[
\int\sqrt{q(y\mid x)}\,d^2y\ge\sqrt{8\pi}.
\]
Consequently, using Tonelli,
\[
M(f)M(g)\ge\sqrt{8\pi}\int\sqrt{q_1(x)}\,d^2x
=\sqrt{4\pi}\int\sqrt{Q_f*Q_g}.
\]
The zero-marginal set contributes zero. No assumptions on parity, angular symmetry, or Fock support were used.

Combining both steps gives
\[
\|W_{f,g}\|_1<\frac{\sqrt2}{8\pi}M(f)M(g)
=\sqrt2\,H(f)H(g).
\]
Take f=g and transfer to mixed states using convexity of Wigner L1 and concavity of M squared (Gagatsos Proposition 1, valid for countable spectral mixtures by Tonelli). If M is finite then every positive-weight spectral component has finite M and the component inequalities are strict, so the mixed inequality is strict as well. The finiteness of Wigner L1 for finite M follows also from the weaker bound of Gagatsos.

### Step 3: optimality for complex cross-Wigner

The opposite-squeezed-vacuum example in COHERENT_CONSTELLATIONS.md has
\[
\frac{\|W_{f_s,f_{-s}}\|_1}{H(f_s)H(f_{-s})}
=\sqrt{2-\operatorname{sech}^2s}\to\sqrt2 .
\]
Thus \(\sqrt2\) cannot be improved for arbitrary complex cross Wigner. The remaining loss in the self-Wigner problem is genuinely about identical inputs, not merely rank-one structure.

## Exact deficit tradeoff for the self-Wigner problem

For f=g, define \(p(x)=2P(\sqrt2 x)\), the Wigner-positive first output of the balanced beam splitter. By Step 1, \(p(x)=\pi W_f(x/\sqrt2)^2\), hence \(M_p=\int\sqrt p=2\sqrt\pi A(f)\). Write \(q_1=p*G\), \(M_{q_1}=\int\sqrt{q_1}\), and \(M_{\rm joint}=\iint\sqrt q=M(f)^2\).
Define two dimensionless gains
\[
S=\frac{M_{q_1}}{M_p},\qquad
E=\frac{M_{\rm joint}}{\sqrt{8\pi}M_{q_1}} .
\]
S>=1 by Gaussian smoothing, E>=1 by conditional Wehrl. The F19 ratio is exactly
\[
\frac{A(f)}{H(f)^2}=\frac{\sqrt2}{SE}.
\]
Therefore the sharp inequality is equivalent to \(SE\ge\sqrt2\) for identical inputs, with equality only for coherent f. For coherent f, S=sqrt2 and E=1. For f a pure squeezed vacuum, the output is a product, E=1, and S=sqrt(2 cosh(s))>=sqrt2. The missing theorem is a quantitative tradeoff between the smoothing gain and the conditional Wehrl gain for the particular identical-input beam-splitter family. Independent estimates S>=1 and E>=1 cannot suffice, as the opposite-squeezed cross example shows. Note that identical inputs imply even parity in the difference output, since exchange of the two input modes corresponds to a sign reversal of that output. Thus every conditional second-mode state at a first-mode heterodyne outcome is even. Whether this extra restriction, together with the product structure, gives the desired quantitative tradeoff is open here.

## Consequence: separated arbitrary profiles cannot create a violation by interference

Let \(f_1,\ldots,f_N\) be fixed nonzero vectors of finite H satisfying sharp F19 (homogeneously), and let \(D(b_j(t))\) denote Weyl displacements in physical coordinates with \(|b_i(t)-b_j(t)|\to\infty\) for all i!=j. For fixed coefficients \(c_j\), put \(F_t=\sum_j c_jD(b_j(t))f_j\) and \(h_j=|c_j|H(f_j)\). The Husimi amplitudes have translated moduli, so
\[
H(F_t)\to\sum_j h_j.
\]
Proof: triangle inequality gives the upper bound; the lower bound subtracts twice the sum of pairwise integrated minima of the amplitudes. These minima tend to zero for any pair of integrable functions translated apart, by truncation to compact sets and control of the L1 tails.

Cross Wigner displacement covariance says that after centering at the midpoint \((b_i+b_j)/2\), the paired term is
\[
2\operatorname{Re}\big[c_i\bar c_j e^{i(\ell_{ij}(t)\cdot r+\theta_{ij}(t))} W_{f_i,f_j}(r)\big]
\]
with \(|\ell_{ij}(t)|=|b_i(t)-b_j(t)|\to\infty\) (up to an irrelevant sign or orthogonal symplectic rotation of the frequency). For any integrable complex g, the absolute-cosine Fourier series and Riemann–Lebesgue imply
\[
\int|\operatorname{Re}(e^{i(\ell\cdot r+\theta)}g(r))|\,d^2r\to\frac2\pi\int|g|
\]
uniformly in theta as \(|\ell|\to\infty\): each nonconstant harmonic is the Fourier transform of the L1 function \(|g|e^{2im\arg g}\), and the absolutely summable Fourier coefficients control the tail. Thus triangle inequality and the sharp complex cross bound give
\[
\limsup_{t\to\infty}A(F_t)
\le \sum_j |c_j|^2 A(f_j)+\frac{4\sqrt2}{\pi}\sum_{i<j}h_i h_j.
\]
If the individual profiles satisfy F19, then \(|c_j|^2A(f_j)\le h_j^2\), and therefore
\[
\limsup_{t\to\infty}\frac{A(F_t)}{H(F_t)^2}
\le \frac{\sum_j h_j^2+(4\sqrt2/\pi)\sum_{i<j}h_i h_j}{(\sum_jh_j)^2}<1
\]
when at least two h_j are positive, since \(2\sqrt2/\pi<1\). No noncollision assumption on the pair midpoints is necessary, because the triangle inequality only overestimates their combined contribution. This extends the earlier coherent-constellation argument to arbitrary fixed profiles, including any profiles for which the sharp inequality is already proven. It does not establish a general concentration-compactness theorem or cover overlapping profiles.

## Remaining tasks

Full F19 is still unresolved. The exact SE tradeoff is a new target, and the \(\sqrt2\) complex cross bound is a useful rigorous analytic input for profile-decomposition strategies. All new results in this note await independent review and Lean formalization.
