# Topological superlevel-set improvement for even conditional states

Research note, 2026-11-27. Analytic proof candidate, not independently reviewed, priority-checked or Lean formalized. This does not establish the sharp F19 conjecture.

The argument strengthens EVEN_CONDITIONAL_BOUND.md by exploiting the zero count in holes of centrally symmetric Husimi superlevel sets. In the same normalization,
\[
 A=\|W_\rho\|_1,\qquad B=(\int\sqrt{Q_\rho})^2/(8\pi),
\]
the resulting bound is \(A\le 1.318 B\) for every single-mode state with finite B. Infinite B is immediate in the extended-real sense.

## 1. A strengthened distributional derivative estimate

Let h be a normalized even finite Fock vector, \(F\) its Bargmann polynomial, \(u(z)=e^{-|z|^2}|F(z)|^2\), \(v=|F(0)|\), \(T=\max u\), and \(m(t)=|\{u>t\}|/\pi\). The standard coarea, divergence and planar isoperimetric argument in EVEN_CONDITIONAL_BOUND.md gives \(-tm'(t)\ge1\) for almost every \(0<t<T\). We claim additionally that
\[
-tm'(t)\ge \min(2,8/m(t))\ge\min(2,8t)\qquad(v^2<t<T).
\]
The last inequality uses \(tm(t)\le\int u\,d^2z/\pi=1\).

Proof at a regular level t. Its superlevel set is bounded, with smooth compact boundary and finitely many boundary components. The open set is invariant under \(z\mapsto-z\) but excludes the origin. Each connected component contributes at least 1 to \(-tm'(t)\), by applying the usual coarea-isoperimetric argument separately (there are no zeros of F in the component). If the components include a pair exchanged by the symmetry, the claimed bound follows.

Otherwise choose a connected component \(\Omega\) invariant under the symmetry. Its outer Jordan curve and filled-in closed disk are invariant. The origin lies in this closed disk, by the Brouwer fixed-point theorem applied to the central inversion on the topological closed disk. It cannot lie on the level-set boundary or in \(\Omega\), since \(t>v^2\). Thus it is in a bounded complementary component (a hole). Write \(M=|\Omega|/\pi\), \(L= \sum_i |\mathcal H_i|/\pi\) for the sum of areas of its bounded holes, and \(N\) for the number of zeros of F in those holes, with multiplicity. The holes as a collection are invariant under central inversion. On each hole, the outward normal derivative of \(\log u\) is \(|\nabla u|/t>0\) on the boundary, since this normal points toward \(\Omega\). The distributional identity \(\Delta\log u=-4+4\pi\sum_a n_a\delta_a\) implies that the sum of these positive fluxes equals \(4\pi(N-L)\). Thus \(N-L>0\). Because F is even, nonzero zeros occur in opposite pairs and the zero at the origin, if any, has even multiplicity. Consequently \(N\ge2\). The outer boundary's flux in absolute value is \(4\pi(M+L-N)\), again positive; this follows by applying the same identity to the filled-in disk, since there are no zeros in \(\Omega\).

Set \(d=N-L\); the preceding positivity gives \(0<d<M\). Cauchy-Schwarz applied separately to the outer boundary and the union of inner boundaries, followed by the planar isoperimetric inequality, gives the lower bound on their total contribution to \(-tm'(t)\):
\[
\frac{M+L}{M-d}+\frac{L}{d}
=\frac{N}{M-d}+\frac{N}{d}
\ge\frac{4N}{M}\ge\frac8{m(t)}.
\]
For the inner boundary union, the square of its total perimeter is at least \(4\pi\) times the sum of the hole areas, by applying isoperimetry to the individual holes. The identity of fluxes is valid even if other superlevel components lie inside a hole: integrate over the whole hole, counting all its zeros. At regular values all these contours avoid zeros. The same conclusion therefore holds regardless of nested components. Sard's theorem and the fact that the distributional derivative of a decreasing function has nonpositive singular part extend these slope estimates to distributional inequalities.

## 2. Layer cake with a prescribed slope

If \(q(s)\ge1\) on (0,T) is any measurable slope lower bound \(-sm'(s)\ge q(s)\) in the distributional sense, put \(m_q(t)=\int_t^T q(s)\,ds/s\). Then \(m-m_q\) is nonnegative and decreasing. Its integral is \(1-\int_0^T q(s)ds\). Applying the decreasing-functions Chebyshev inequality to \(m-m_q\) and \(1/(2\sqrt t)\) as before gives
\[
H(h)=\tfrac12\int_0^T m(t)\frac{dt}{2\sqrt t}
\ge\frac{1+T}{2\sqrt T}
+\frac12\int_0^T (q(s)-1)(s^{-1/2}-T^{-1/2})\,ds.
\]
All integrands are nonnegative in the additional term; the derivation is via Tonelli and the mass normalization. In particular if T<=1/4, the standard bound alone implies \(H(h)\ge5/4\).

## 3. Uniform improved conditional estimate

We prove
\[
H(h)-1\ge \frac{11}{100}(1-v)^2
\]
for all normalized even finite Fock vectors, by three cases.

**Case 1: \(v\le 1/\sqrt8\).** If T<=1/4, the preceding observation suffices. Otherwise use the slope \(q=1\) on (0,1/8), \(q(s)=8s\) on (1/8,1/4), and \(q=2\) on (1/4,T), justified by Section 1. Direct evaluation of the integrals in Section 2 gives
\[
H(h)\ge \sqrt T+\frac{19}{32\sqrt T}-\frac12+\frac{\sqrt2-1}{6}
\ge \sqrt{19/8}-\frac12+\frac{\sqrt2-1}{6}>\frac{111}{100}.
\]
For clarity, the integrals of \(q-1\) over (1/8,1/4) are \(1/16\) against ds and \((\sqrt2-1)/3\) against \(ds/\sqrt s\); over (1/4,T) they are \(T-1/4\) and \(2\sqrt T-1\), respectively. AM-GM gives the middle inequality. The strict final comparison follows e.g. from \(\sqrt{19/8}>1.54110\) and \(\sqrt2>1.41421\), both by squaring rational numbers.

**Case 2: \(1/\sqrt8<v\le1/2\).** Again T<=1/4 suffices. Otherwise take q=2 on (1/4,T) and q=1 below that interval; \(v^2\le1/4\) justifies this. The result is
\[
H(h)\ge\sqrt T+\frac{5}{8\sqrt T}-\frac12
\ge\sqrt{5/2}-\frac12>1.08.
\]
Since \(v>1/3\), the desired deficit is at most \(11/225<0.08\).

**Case 3: \(1/2\le v\le1\).** Use the previous maximum-sensitive bound
\[
H(h)-1\ge \frac{(1-\sqrt{(1+v^2)/2})^2}{2\sqrt{(1+v^2)/2}}.
\]
For v<1, the quotient by \((1-v)^2\) equals \(r(v)=(1+v)^2/[8s(1+s)^2]\), \(s=\sqrt{(1+v^2)/2}\). As proved in EVEN_CONDITIONAL_BOUND.md this is increasing: the logarithmic derivative is \(2/(1+v)-v/(1+v^2)-v/[s(1+s)]\ge0\) using \(s\ge v\) and \(s^2\ge v\). At v=1/2, \(r(v)>0.1109>11/100\), by substitution and rational square-root bounds. At v=1 the desired inequality is immediate. This proves the improved estimate.

## 4. Global constant

The conditional beam-splitter argument of EVEN_CONDITIONAL_BOUND.md, using \(\int a(z)v(z)d\gamma(z)=1\) and weighted Cauchy-Schwarz, now gives for normalized finite Fock f
\[
B\ge J+c(J-1)^2/J,\qquad c=11/100.
\]
The heat-flow estimate of HEAT_FLOW_BOUND.md gives \(A^2\le2J^2-k\), \(k=27/32\). As J>=1, set \(x=1/J\); then
\[
\frac{A^2}{B^2}\le \frac{2-kx^2}{(1+c(1-x)^2)^2}
\le \frac{2-kx^2}{1+2c(1-x)^2}.
\]
In particular this is less than \(C^2\) for \(C=659/500=1.318\). To verify the last claim, let \(a=2c C^2\). For every real x,
\[
C^2[1+2c(1-x)^2]-(2-kx^2)
=C^2-2+a(1-x)^2+kx^2
\ge C^2-2+\frac{ak}{a+k}>0.
\]
The final number is positive by exact rational arithmetic (about 0.000154506). Thus the estimate holds uniformly with no need for the previous Fourier cutoff. Fejer approximation in Bargmann L1 and Fock L2 followed by Fatou passes it to arbitrary pure states with finite B; Wigner L1 convexity and B concavity pass it to countable spectral mixtures, as in the earlier notes.

## 5. Scope and next target

This proof uses the topology of the conditional state rather than merely its Husimi maximum. It improves the conditional deficit coefficient from 0.06 to 0.11 and gives a global coefficient below 1.318, compared with 1.348 in the previous note. It still does not prove the proposed stronger linear conditional estimate \(H(h)\ge\sqrt2-(\sqrt2-1)v\). Nor would that auxiliary estimate alone settle the full sharp F19 inequality. In particular, the low-superlevel regime of a large connected component with holes only gives the universal derivative bound 1; a sharper integrated argument needs additional information about the conditional product or the same-input interference density. The new result awaits independent proof review and Lean formalization.
