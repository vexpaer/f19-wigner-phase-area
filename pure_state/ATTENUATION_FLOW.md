# Attenuation-flow obstruction and a variational identity

Research note, 2026-11-27. Analytic calculations for independent review. These results concern the full pure-state proof strategy; they do not prove or disprove F19 itself. No Lean verification is claimed.

Source normalization: Gagatsos, arXiv:2611.30969v1, Conjecture 1. Write
\[
A(f)=\int_{\mathbb R^2}|W_f(r)|\,d^2r,\qquad
H(f)=\frac1{4\pi}\int_{\mathbb R^2}|\langle u|f\rangle|\,d^2u,\qquad
\mathcal R(f)=A(f)/H(f)^2
\]
for nonzero, possibly unnormalized pure vectors \(f\) with finite \(H\). Here \(W_f\) is the Wigner density of \(|f\rangle\langle f|\). The ratio is invariant under multiplication by a nonzero scalar and under phase-space displacement. The desired conclusion is \(\mathcal R(f)\le1\), with the normalized equality states coherent.

## 1. Exact two-lump and three-lump limits

If \(f_R=a|0\rangle+b|R\rangle\), with fixed nonzero complex \(a,b\) and real coherent amplitude \(R\to+\infty\), then
\[
H(f_R)\longrightarrow |a|+|b|,\qquad
A(f_R)\longrightarrow |a|^2+|b|^2+\frac4\pi|ab|.
\]
These limits are valid for arbitrary fixed relative phase. To see the first, in complex coherent amplitude coordinates use the overlap bound
\[
0\le |a|+|b|-H(f_R)\le 2\sqrt{|ab|}e^{-R^2/8}.
\]
This follows by integrating the reverse triangle inequality and bounding the minimum of the two coherent amplitudes by their geometric mean. In these coordinates \(H(f)=(2\pi)^{-1}\int|\langle z|f\rangle|d^2z\), so each coherent state has H=1.

For the second, write the Wigner function as the sum of the two Gaussian diagonal terms and the real paired cross term. Their envelopes have fixed Gaussian width and centers at \(0,R,R/2\). They become mutually separated. The difference between the norm of the sum and the sum of their norms is bounded by twice the sum of integrals of pairwise minima, which tend to zero by the same geometric-mean Gaussian overlap estimate (the cross envelope has fixed coefficient \(2|ab|\)). The cross term's norm tends to \(4|ab|/\pi\): its normalized Gaussian envelope averages the absolute cosine of a phase whose variance grows as \(R^2\). The Fourier series of the absolute cosine converges absolutely and all its nonconstant harmonics have expectations tending to zero. In particular, for equal-modulus coefficients
\[
\mathcal R(|0\rangle+|R\rangle)\longrightarrow \tfrac12+\tfrac1\pi<1.
\]

Small additional terms do not affect these limits if they tend to zero in H. In fact the parity representation and the triangle inequality give the cross estimate \(\|W(f,g)\|_1\le2H(f)H(g)\), including for unnormalized vectors. Therefore
\[
|A(f+h)-A(f)|\le 4H(f)H(h)+2H(h)^2,\quad
|H(f+h)-H(f)|\le H(h).
\]
In particular \(\mathcal R\) is continuous in the H norm at every nonzero vector. This also follows without appealing to the sharp conjecture.

## 2. Monotonicity under attenuation is false, even for polynomials

Let \(T_s=s^{\hat n}\) for \(0<s\le1\). Coherent states transform as
\[
T_s|\alpha\rangle=e^{-(1-s^2)|\alpha|^2/2}|s\alpha\rangle.
\]
For \(f_R=|0\rangle+e^{R^2/4}|R\rangle\), the output at \(s=1/\sqrt2\) is an equal-amplitude two-lump cat, so its ratio tends to \(1/2+1/\pi\). At \(s=1\) the displaced coherent term dominates; after division by its coefficient and displacement, the remaining perturbation has H tending to zero. Hence the ratio tends to 1. For any fixed R the limit as \(s\to0\) is also 1. Thus neither monotonicity direction holds for all f.

A stronger counterexample excludes quasiconvexity and a general no-interior-maxima strategy. Set
\[
g_R=|0\rangle+e^{R^2/4}|R\rangle+e^{5R^2/8}|2R\rangle.
\]
At \(s^2=1/2\), the output's three coefficients are \(1,1,e^{-3R^2/8}\). The third is negligible in H; the ratio tends to \(1/2+1/\pi\). At \(s^2=3/4\), divide the output by \(e^{R^2/8}\); the coefficients are \(e^{-R^2/8},1,1\). Again the ratio tends to \(1/2+1/\pi\). At the intermediate point \(s^2=5/8\), the coefficients are \(1,e^{R^2/16},e^{-R^2/8}\). Dividing by the middle coefficient leaves one coherent state plus a perturbation tending to zero in H, so the ratio tends to 1. Consequently for all sufficiently large R there is a maximum on the closed attenuation interval which occurs strictly inside the interval, with a value strictly exceeding both endpoint values. This does not assert that the maximum exceeds 1.

The same obstruction holds for finite Bargmann polynomials: fix any sufficiently large finite R giving strict inequalities at the three displayed parameter values, then approximate each coherent exponential by its Taylor polynomials. For fixed R and \(s\in[0,1]\), the polynomial truncations converge in H by Gaussian dominated convergence (domination by a finite sum of constants times \(e^{2R|z|}\) in complex amplitude coordinates). The cross estimate above yields Wigner L1 convergence. Hence the strict three-point comparisons persist at sufficiently large finite truncation degree. No argument proving F19 for all polynomials can assume the ratio is quasiconvex or has no internal maximum along the attenuation path.

## 3. Exact attenuation derivative and the remaining barrier

Let \(f_\tau=e^{-\tau\hat n}f\) with f a nonzero finite Fock superposition. Use physical coordinates r=(x,p), \(\hat n=(\hat x^2+\hat p^2-1)/2\). The Wigner transform obeys the exact differential equation
\[
\partial_\tau W_\tau=\tfrac14\Delta W_\tau+(1-|r|^2)W_\tau.
\]
Indeed, in the Wigner integral the two position second derivatives combine to \((\partial_x^2+\partial_y^2)/4\); Fourier transformation of the y derivative gives \(-p^2 W\), while the position potential contributes \((1-x^2)W+\partial_p^2W/4\).

Define the nodal dissipation
\[
D_\tau=-\int\operatorname{sgn}(W_\tau)\Delta W_\tau\ge0.
\]
This is well defined because W and its derivatives are polynomials times Gaussians. Nonnegativity follows by integrating by parts against \(W/\sqrt{W^2+\epsilon^2}\) and taking \(\epsilon\downarrow0\). The zero set has measure zero because W is a nonzero real polynomial times a positive Gaussian. Dominated convergence therefore differentiates A; the resulting identity is
\[
\frac{d}{d\tau}\log A(f_\tau)=1-
\mathbb E_{|W_\tau|/A}|r|^2-\frac{D_\tau}{4A(f_\tau)}.
\]
In the Bargmann representation, \(P_\tau(z)=P(e^{-\tau}z)\) and
\[
H(f_\tau)=\frac1{2\pi}\int e^{-|z|^2/2}|P(e^{-\tau}z)|\,d^2z.
\]
Making the change \(w=e^{-\tau}z\) before differentiating gives
\[
\frac{d}{d\tau}\log H(f_\tau)=2-\tfrac12
\mathbb E_{|\langle u|f_\tau\rangle|/(4\pi H)}|u|^2,
\qquad u=\sqrt2(\operatorname{Re}z,\pm\operatorname{Im}z).
\]
The sign in the second coordinate depends only on the conjugate Bargmann convention and does not affect the radial moment. Thus
\[
\boxed{\frac{d}{d\tau}\log\mathcal R(f_\tau)=
\mathbb E_{\mathrm{Husimi\ amplitude}}|u|^2
-\mathbb E_{\mathrm{absolute\ Wigner}}|r|^2
-3-\frac{D_\tau}{4A(f_\tau)}.}
\]
This is an exact identity for finite polynomials and also holds with displaced finite-polynomial vectors, by the same Gaussian domination arguments. The sign of the right-hand side is not universal, as Section 2 proves.

For attenuation centered at an arbitrary physical point \(b\), displacement covariance replaces the two squared radii by \(|u-b|^2\) and \(|r-b|^2\), without changing D. The quadratic terms in b cancel. A differentiable local maximizer over all displacement-centered attenuation variations must therefore have matching first moments of its normalized absolute Wigner and Husimi-amplitude densities. This necessary condition alone does not prove the conjecture. The full derivative identity could still be useful for a barrier argument at \(\mathcal R=1\), but that argument would require a new strict moment/dissipation comparison at the boundary. Neither monotonicity nor quasiconvexity of the attenuation ratio supplies it.

## 4. Status

The original sharp conjecture remains open in this research branch. The global improvement in UNIVERSAL_BOUND.md, the verified phase-invariant sector, and the finite-polynomial equivalence are not changed by the counterexamples in this note. All limits and differential identities above are analytic derivations, not a numerical search or an end-to-end Lean proof.
