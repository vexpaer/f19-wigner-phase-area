# Quantitative even-parity conditional Wehrl bound

Research note, 2026-11-27. Analytic proof candidate for independent review. This improves the all-state constant using the identical-input structure. No Lean formalization, independent novelty verification, or solution of the sharp conjecture is claimed.

Use the normalization of Gagatsos, arXiv:2611.30969v1, and the notation of INTERFERENCE_BOUND.md and HEAT_FLOW_BOUND.md:
\[
 A=\|W_\rho\|_1,\qquad B=(\int\sqrt{Q_\rho})^2/(8\pi).
\]
We obtain the uniform bound \(A<1.348 B\) for finite B (and the non-strict extended-real version for all states). The original target is A<=B.

## 1. A maximum-sensitive Wehrl estimate

For a normalized finite Fock vector h, let \(u(z)=|\langle z|h\rangle|^2=e^{-|z|^2}|F_h(z)|^2\) in complex coherent coordinates, \(d\mu=d^2z/\pi\), \(T=\sup u\in(0,1]\), and \(H(h)=\tfrac12\int\sqrt{u}\,d\mu\). Then
\[
H(h)\ge \frac{1+T}{2\sqrt T}.
\]
Here is a direct level-set proof. Write \(m(t)=\mu\{u>t\}\), \(0<t<T\). The sets are bounded and contain no zeros of F. At a regular value t, \(\Delta\log u=-4\) on the superlevel set, so the divergence theorem gives \(\int_{\partial\{u>t\}}|\nabla u|=4t\,|\{u>t\}|\), where the last measure is Euclidean area. Coarea, the planar isoperimetric inequality, and Cauchy–Schwarz imply
\[
-m'(t)=\pi^{-1}\int_{\partial\{u>t\}}|\nabla u|^{-1}\ge 1/t .
\]
The inequality holds a.e. by Sard's theorem, and the distributional inequality follows because the singular part of the derivative of the decreasing function m is nonpositive. Consequently \(v(t)=m(t)-\log(T/t)\) is nonnegative and decreasing, with \(\int_0^T v(t)\,dt=1-T\) by mass normalization. The nonnegativity follows also by integrating the differential inequality from t towards T. Layer cake gives
\[
\int\sqrt u\,d\mu
=\int_0^T \frac{\log(T/t)+v(t)}{2\sqrt t}\,dt
\ge 2\sqrt T+\frac{1-T}{\sqrt T}.
\]
In the last step we used the integral Chebyshev inequality for the two decreasing functions v(t) and \(1/(2\sqrt t)\) on (0,T). It remains valid for unbounded functions by monotone truncation, or by integrating their pairwise differences over the square. This proves the asserted estimate. The argument here only needs finite Fock vectors; no general rearrangement regularity assumption is necessary.

## 2. Even states: a bound in terms of the vacuum amplitude

Suppose h is normalized and has even parity; put \(v=|\langle0|h\rangle|\in[0,1]\). Split off the vacuum and project the coherent vector onto the even nonvacuum subspace. For \(t=|z|^2\), the squared norm of that projection is \(e^{-t}(\cosh t-1)=(1-e^{-t})^2/2\). Hence with \(x=e^{-t/2}\in[0,1]\),
\[
|\langle z|h\rangle|
 \le vx+\sqrt{(1-v^2)/2}(1-x^2)
 \le\sqrt{(1+v^2)/2}.
\]
The final Cauchy–Schwarz step uses \(x^2+(1-x^2)^2\le1\). Therefore \(T\le T_0=(1+v^2)/2\). Since \((1+T)/(2\sqrt T)\) is decreasing on (0,1], Section 1 implies
\[
H(h)-1\ge \frac{(1-\sqrt{T_0})^2}{2\sqrt{T_0}}
\ge c(1-v)^2,\qquad c=3/50.
\]
For clarity the last elementary inequality follows by putting \(s=\sqrt{(1+v^2)/2}\): for v<1 the ratio of the middle term to (1-v)^2 equals
\[
r(v)=\frac{(1+v)^2}{8s(1+s)^2}.
\]
Its logarithmic derivative is \(2/(1+v)-v/(1+v^2)-v/[s(1+s)]\ge0\), since the first term is >=1 and the other two are <=1/2 each. The latter bound follows from \(s\ge v\) and \(s^2\ge v\). At v=0 the ratio is \(3/(2\sqrt2)-1>3/50\). The endpoint v=1 is immediate. This produces an explicit, although non-sharp, conditional Wehrl deficit without invoking an unspecified stability constant.

## 3. Apply the even-state estimate to identical inputs

Let f be normalized with finite Fock support, and \(F\) its Bargmann polynomial. The normalized balanced beam-splitter output has two-variable Bargmann function
\[
K(z,w)=F((z+w)/\sqrt2)F((z-w)/\sqrt2).
\]
Define \(a(z)=(\int |K(z,w)|^2 e^{-|w|^2}\,d^2w/\pi)^{1/2}\), \(v(z)=|K(z,0)|/a(z)\) where \(a(z)>0\), and
\[
d\gamma(z)=(2\pi)^{-1}e^{-|z|^2/2}d^2z,\qquad J=\int a(z)\,d\gamma(z).
\]
The conditional state in w is even. By the previous section, using its norm a(z),
\[
B=\iint |K(z,w)|\,d\gamma(z)d\gamma(w)
\ge J+c\int a(z)(1-v(z))^2\,d\gamma(z).
\]
The equality defining B follows from the orthogonal change to the original two Bargmann variables; B=H(f)^2. Crucially the average conditional vacuum amplitude is exactly fixed:
\[
\int a(z)v(z)\,d\gamma(z)=\int |F(z/\sqrt2)|^2\,d\gamma(z)=1.
\]
Therefore J>=1, and weighted Cauchy–Schwarz yields the new relation
\[
\boxed{ B\ge J+c\frac{(J-1)^2}{J}. }
\]
This is an identical-input estimate, unavailable for arbitrary cross Wigner. In physical coordinates \(J=(\int\sqrt{q_1})/\sqrt{8\pi}\), where q_1 is the first-output Husimi density. By HEAT_FLOW_BOUND.md, with \(p(x)=\pi W_f(x/\sqrt2)^2\) and \(q_1=p*G_{1/4}\), we have
\[
 A^2\le 2J^2-\frac{27}{32}.
\]
Combining the inequalities gives
\[
 A\le \sqrt{2j(B)^2-27/32},\qquad
 j(B)=\frac{B+2c+\sqrt{(B+2c)^2-4c(1+c)}}{2(1+c)} .
\]
The map \(g(J)=J+c(J-1)^2/J\) is increasing and convex on [1,infinity), and j is its increasing concave inverse there. The right-hand side is also increasing and concave on B>=1, by composition with \(J\mapsto\sqrt{2J^2-27/32}\). Thus the bound extends from finite Fock vectors to general pure states by the Fejer approximation and Fatou argument in HEAT_FLOW_BOUND.md, and then to general mixed states by the same spectral-mixture argument. All finite-B components have finite B; infinite B is trivial for the non-strict extended-real inequality.

## 4. Explicit uniform coefficient

For B<=10/3 it is enough to bound the ratio at B=10/3. Indeed the ratio of the last upper bound to B, as a function of J=j(B), is \(\sqrt{2J^2-k}/g(J)\), \(k=27/32\). Its derivative has the sign of
\[
2Jg(J)-(2J^2-k)g'(J)=k(1+c)-4c(J-1)-kc/J^2,
\]
which is positive on \(1\le J\le 10/3\), because it is at least \(k-4c(10/3-1)>0\). Since j(B)<=B, the required range is included. At B>=10/3 use the decreasing earlier Fourier bound \(4/\pi+(4\log2-2)/(\pi B)\). We obtain
\[
\frac AB\le
\max\left\{\frac3{10}\sqrt{2j(10/3)^2-27/32},\
\frac4\pi+\frac{3(4\log2-2)}{10\pi}\right\}<1.348 .
\]
The two terms are about 1.3468814 and 1.3470163 respectively. These numerical inequalities can be verified by squaring rational bounds for the radicals, using \(3.14159<\pi<3.14160\) and \(0.69314<\log2<0.69315\). (For example j(10/3)<3.241 by direct substitution into g, giving first term <1.348.) This improves the previous uniform coefficient <1.370.

## 5. A sharper conditional target and its limit

The identity \(\int a v\,d\gamma=1\) suggests trying the much stronger even-state estimate
\[
H(h)\stackrel{?}{\ge}\sqrt2-(\sqrt2-1)|\langle0|h\rangle|.
\]
This is an unproved auxiliary conjecture, not used above. Even cats at large separation and the two-photon Fock state are candidate limiting/equality tests. It would imply \(B\ge \sqrt2 J-(\sqrt2-1)\), hence \(A\le B+\sqrt2-1\) using the elementary smoothing bound. This would give asymptotic constant 1 but not the full F19 inequality at finite B. A stronger joint estimate involving the smoothing deficit is still necessary. The cap-only level-set proof of Sections 1–2 cannot supply this stronger inequality: its deficit is quadratic near vacuum and the bound at v=0 is only 3/(2 sqrt(2)). Further research should use more of the conditional analytic product, not simply its maximum Husimi overlap.

All results above remain analytic proof candidates. The improvement is to the self-Wigner bound for general states; it does not contradict optimality of the sqrt(2) complex cross-Wigner bound.
