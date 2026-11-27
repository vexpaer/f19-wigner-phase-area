# Quantitative heat-flow improvement of the F19 universal bound

Research note, 2026-11-27. Analytic proof candidate for independent review; not Lean formalized. No priority claim and no claim that the sharp conjecture has been resolved.

Use the physical convention of Gagatsos, arXiv:2611.30969v1. For a normalized single-mode state define
\[
A=\|W_\rho\|_1,\qquad B=\frac1{8\pi}\left(\int\sqrt{Q_\rho(r)}\,d^2r\right)^2.
\]
The result below improves the universal \(\sqrt2\) coefficient of INTERFERENCE_BOUND.md by quantifying its Gaussian smoothing step and combining it with the independent Fourier bound in UNIVERSAL_BOUND.md.

## Theorem

For every state with finite B,
\[
A^2\le 2B^2-\frac{27}{32},\qquad
A\le \frac4\pi B+\frac{4\log2-2}{\pi}.
\]
In particular
\[
A\le C B,\quad
C=\max\left\{\sqrt{2-\frac{675}{5408}},
\frac4\pi+\frac{5(4\log2-2)}{13\pi}\right\}<1.370.
\]
(The cutoff used here is \(B=13/5\); optimizing it is optional.) For infinite B the extended-real linear bound is trivial. F19 asks for A<=B, and the new result does not settle it.

## 1. Explicit two-dimensional Gagliardo–Nirenberg estimate

For \(v\in H^1(\mathbb R^2)\), we have
\[
\|v\|_4^4\le \frac{16}{27\pi}\|v\|_2^2\|\nabla v\|_2^2 .
\]
This is a convenient explicit constant, not the optimal Gagliardo–Nirenberg constant. For completeness use the unitary angular-frequency Fourier transform \(\widehat v(\xi)=(2\pi)^{-1}\int e^{-ix\cdot\xi}v(x)\,d^2x\). The sharp Hausdorff–Young inequality (Babenko–Beckner; W. Beckner, *Inequalities in Fourier Analysis on R^n*, PNAS 72 (1975), 638–641, DOI 10.1073/pnas.72.2.638), applied to the inverse transform at exponent 4/3, gives
\[
\|v\|_4^4\le (2\pi)^{-2}\frac{16}{27}\|\widehat v\|_{4/3}^4.
\]
By Holder, for any a,b>0,
\[
\|\widehat v\|_{4/3}^4
\le \left(\int(a+b|\xi|^2)|\widehat v|^2\right)^2
\int(a+b|\xi|^2)^{-2}\,d^2\xi
=\frac{\pi}{ab}(a\|v\|_2^2+b\|\nabla v\|_2^2)^2.
\]
Choose \(a\|v\|_2^2=b\|\nabla v\|_2^2\) to get the asserted inequality. Nonzero H^1 functions have both squared norms positive, so this choice is legitimate. The Fourier argument may first be performed for smooth rapidly decreasing functions and extended by H^1 approximation.

## 2. Heat-flow growth of the square-root integral

Let p be a probability density and let \(p_t=p*G_t\), \(G_t(r)=(4\pi t)^{-1}e^{-|r|^2/(4t)}\) for t>0. For the moment assume p is a nonnegative squared-polynomial times a Gaussian, as in the pure finite-Fock case below. Put
\[
M(t)=\int\sqrt{p_t},\qquad v_t=p_t^{1/4}.
\]
Then \(\partial_t p_t=\Delta p_t\). Differentiation and integration by parts give
\[
M'(t)=\frac14\int p_t^{-3/2}|\nabla p_t|^2
=4\|\nabla v_t\|_2^2.
\]
Since \(\|v_t\|_4^4=1\) and \(\|v_t\|_2^2=M(t)\), the preceding estimate implies
\[
M(t)M'(t)\ge\frac{27\pi}{4},
\qquad
M(t)^2\ge M(0)^2+\frac{27\pi}{2}t.
\]
Here M(0)=int sqrt(p). The regularity details for this use of the heat equation are as follows. Write \(p(x)=c e^{-|x|^2}R(x)^2\) for a nonzero real polynomial R, as holds below. Completing the square shows \(p_t(x)=c(1+4t)^{-1}e^{-|x|^2/(1+4t)}\mathbb E[R(x/(1+4t)+Y_t)^2]\), with \(Y_t\) centered Gaussian of covariance \(2t/(1+4t)\,I\). Its polynomial factor has a strictly positive uniform lower bound in x for t in compact subintervals of (0,infinity): expand \(R(x/(1+4t)+Y_t)\) in Gaussian Hermite polynomials in Y_t. At least one highest-total-degree coefficient is nonzero and independent of x, and the expected square is the sum of squared coefficients times positive norms. Thus differentiation of square roots and integration by parts have Gaussian-dominated integrands on such time intervals, with no boundary terms. As t decreases to zero the polynomial factors have bounded coefficients, and the square roots have a common integrable polynomial-Gaussian majorant on a compact interval starting at zero. Dominated convergence gives M(t)->M(0).

## 3. Apply to the beam-splitter interference density

For a normalized finite Fock pure state f, the interference identity from INTERFERENCE_BOUND.md gives the Wigner-positive probability density
\[
p(x)=\pi W_f(x/\sqrt2)^2.
\]
It is precisely a squared-polynomial times \(e^{-|x|^2}\); Moyal normalization ensures its mass is one. Its square-root integral is \(M(0)=2\sqrt\pi A\). The vacuum Wigner density is \(G_{1/4}(r)=\pi^{-1}e^{-|r|^2}\), so \(p_{1/4}=q_1\), the first-output Husimi density of the balanced beam splitter with identical input f. Section 2 of INTERFERENCE_BOUND.md (conditional Lieb–Solovej) proved
\[
B\ge \frac{M(1/4)}{\sqrt{8\pi}}.
\]
The heat inequality yields
\[
8\pi B^2\ge M(1/4)^2\ge 4\pi A^2+\frac{27\pi}{8}.
\]
Dividing by \(4\pi\) proves \(A^2\le 2B^2-27/32\).

This inequality extends to normalized arbitrary pure states with finite B: write the Bargmann entire function as \(F(z)=\sum c_n z^n/\sqrt{n!}\). Its weighted L1 norm with measure \((2\pi)^{-1}e^{-|z|^2/2}d^2z\) is H=sqrt(B). Fejer angular averages \(F_N=\sum_{n=0}^N(1-n/(N+1))c_n z^n/\sqrt{n!}\) converge to F in this norm by the positive Fejer approximate identity, since rotations are strongly continuous on the weighted L1 space. They also converge in Fock L2 by coefficient dominated convergence. Normalize these polynomials; their H norms converge. The coarse Gaussian-window cross-Wigner bound \(\|W(f,g)\|_1\le2H(f)H(g)\) implies Wigner L1 convergence, by expanding the difference of rank-one Wigner functions. Alternatively, pointwise convergence by displaced parity and Fatou suffice for this upper bound. Thus the inequality survives the limit.

For mixed states use the countable spectral decomposition and convexity of A, concavity of B. On B>=1 (Lieb–Solovej), the function \(F_*(B)=\sqrt{2B^2-27/32}\) is increasing and concave, since its second derivative is negative. Hence
\[
A(\rho)\le\sum_j p_j F_*(B_j)\le F_*(\sum_j p_jB_j)\le F_*(B_\rho).
\]
All component B_j with positive spectral weights are finite if B_rho is finite, and the weighted sum is bounded by B_rho. Countable Jensen is applicable, e.g. by the tangent-line bound at the finite weighted mean. This proves the nonlinear mixed-state bound.

## 4. Combine the two independent bounds

The earlier cosine-Fourier estimate gives \(A/B\le 4/\pi+(4\log2-2)/(\pi B)\). The new heat estimate gives \(A/B\le\sqrt{2-27/(32B^2)}\). The latter function is increasing in B, and the former is decreasing. At B<=13/5 use the new bound evaluated at 13/5, which equals \(\sqrt{2-675/5408}\). At B>=13/5 use the Fourier bound at 13/5. Both are strictly below 1.370, giving the claimed coefficient. The elementary numerical comparison can be checked with rational enclosures for pi and log(2).

## 5. Remaining gap and future proof target

The bound improves the full-state constant from 2 (Gagatsos) to 1.370, beyond the universal sqrt(2) bound. It also makes the smoothing gain in INTERFERENCE_BOUND.md quantitative:
\[
S^2=\frac{M(1/4)^2}{M(0)^2}\ge 1+\frac{27}{32 A^2}.
\]
This estimate is independent of the conditional Wehrl gain E and gets weaker when A is large. The sharp conjecture still requires a coupling of these gains for identical input states. Even replacing the explicit Gagliardo–Nirenberg constant by the best constant for all H^1 functions does not supply such a coupling. A proof cannot rely only on a stronger numerical constant in the heat inequality. Possible next steps are exploiting that the conditional difference-output state is even, and estimating its conditional vacuum overlap in terms of the gradients or nodal structure of W.

No independent novelty search or Lean formalization of this note has yet been completed.
