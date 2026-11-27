# Uniform local F19 under an exponential photon-number moment

Research note, 2026-11-27. Analytic proof candidate, not independently reviewed or Lean formalized. This is a local result in an infinite-dimensional class; it does not establish global F19.

Use physical phase-space coordinates r=(x,p), and write
\[
H(\psi)=\frac1{4\pi}\int_{\mathbb R^2}|\langle u|\psi\rangle|\,d^2u,
\quad B_\psi=H(\psi)^2,\quad A_\psi=\int|W_\psi|.
\]
For normalized pure states \(B_\psi=(\int\sqrt{Q_\psi})^2/(8\pi)\), and \(H(|0\rangle)=1\).
For an unnormalized vector h, let \(W_h\) denote the Wigner function of \(|h\rangle\langle h|\) and \(W_{h0}\) that of \(|h\rangle\langle0|\).

## Theorem (uniform centered exponential-moment neighborhood)

For each finite \(M\ge1\), there exists \(\delta_0(M)>0\) such that every normalized pure state of the form
\[
\psi=c_0|0\rangle+h,\qquad c_0=\sqrt{1-\delta^2},\qquad
h=\sum_{n\ge2}c_n|n\rangle,\quad \|h\|_2=\delta,
\quad \sum_{n\ge2}256^n|c_n|^2\le M^2,
\]
satisfies \(A_\psi<B_\psi\) whenever \(0<\delta<\delta_0(M)\).
At \(\delta=0\) there is equality. By displacement covariance the same result applies after displacement to a best coherent state if the displayed moment bound holds in those centered coordinates. In particular the conclusion is uniform over an infinite-dimensional family, not only along fixed finite Fock rays.

### 1. Centering and the Husimi deficit

Put \(t=|\alpha|^2\). By the coherent expansion and Cauchy-Schwarz,
\[
|\langle\alpha|\psi\rangle|\le c_0 e^{-t/2}
 +\delta\sqrt{1-(1+t)e^{-t}}
\le c_0e^{-t/2}+\delta(1-e^{-t}).
\]
The second inequality uses \(t\ge1-e^{-t}\). Since \(1-e^{-t}\le2(1-e^{-t/2})\), the right side is at most \(c_0\) for \(2\delta\le c_0\). Equality at \(\alpha=0\) shows that vacuum is a closest coherent state. The minimal trace-norm distance to a coherent projector is exactly \(2\delta\), by the elementary rank-two projector formula.

Apply Frank–Nicola–Tilli, The generalized Wehrl entropy bound in quantitative form, JEMS (2025), DOI 10.4171/jems/1674, arXiv:2307.14089v3, Theorem 3, with the continuous convex function \(\Phi(t)=-\sqrt t\). In the normalized coherent measure \(d^2u/(2\pi)\), it gives a constant \(c_\Phi>0\), independent of the state, such that \(2H(\psi)-2\ge c_\Phi(2\delta)^2\). Consequently
\[
B_\psi-1\ge 4c_\Phi\delta^2.
\]
Here \(B_\psi-1=(H-1)(H+1)\) and \(H\ge1\). All quantities are finite by the estimates below.

### 2. Weighted Bargmann evaluation

Write \(P_h(z)=\sum_{n\ge2}c_n z^n/\sqrt{n!}\). By Holder with exponents 4 and 4/3,
\[
\sum_{n\ge2}4^n|c_n|^2
\le\left(\sum256^n|c_n|^2\right)^{1/4}
\left(\sum|c_n|^2\right)^{3/4}
\le M^{1/2}\delta^{3/2}.
\]
Set \(E=M^{1/4}\delta^{3/4}\). Cauchy-Schwarz against the exponential series gives
\[
|P_h(z)|\le E e^{|z|^2/8}.
\]
The standard vacuum cross-Wigner identity (also valid for unnormalized h) then yields, with \(|r|^2=x^2+p^2\),
\[
|W_{h0}(r)|\le \pi^{-1}E e^{-3|r|^2/4}.
\]
Indeed \(W_{h0}(r)=\pi^{-1}e^{-|r|^2}P_h(\sqrt2(x-ip))\), up to the conjugate coordinate convention. Similarly, \(|\langle u|h\rangle|\le E e^{-3|u|^2/16}\), because coherent amplitude coordinates are \(\alpha=(u_x+iu_p)/\sqrt2\).

The parity integral of Gagatsos, arXiv:2611.30969v1, Eq. (13), gives the Gaussian envelope
\[
|W_h(r)|\le \frac1{2\pi^2}\int|\langle r+s|h\rangle|\,|\langle r-s|h\rangle|\,d^2s
\le \frac{4 E^2}{3\pi}e^{-3|r|^2/8}.
\]
We will also use the stronger uniform pointwise bound \(|W_h|\le\delta^2/\pi\) from the operator norm one of displaced parity.

### 3. All negative mass lies outside a growing disk

Choose \(R^2=(7/4)\log(1/\delta)\) for \(0<\delta<1\).
Expand
\[
W_\psi=c_0^2 W_0+2c_0\operatorname{Re} W_{h0}+W_h,
\qquad W_0=\pi^{-1}e^{-|r|^2}.
\]
On \(|r|\le R\), division by \(W_0>0\) and the bounds above show
\[
W_\psi/W_0\ge 1-\delta^2
 -2M^{1/4}\delta^{5/16}-\delta^{1/4}.
\]
This is positive for all sufficiently small \(\delta\), uniformly in the state for fixed M. For the complement of the disk, the nonnegative vacuum term can be dropped when upper bounding the negative part:
\[
(-W_\psi)_+\le2c_0 |W_{h0}|+|W_h|.
\]
Since \(\int_{|r|>R}e^{-a|r|^2}d^2r=(\pi/a)e^{-aR^2}\), we obtain
\[
\begin{aligned}
 A_\psi-1
 &=2\int(-W_\psi)_+\\
 &\le \frac{16}{3}M^{1/4}\delta^{33/16}
 +\frac{64}{9}M^{1/2}\delta^{69/32}.
\end{aligned}
\]
Both exponents strictly exceed 2. Hence \(A_\psi-1=o(\delta^2)\) uniformly under the moment bound, whereas \(B_\psi-1\ge4c_\Phi\delta^2\). This proves the theorem.

### 4. A separate uniform finite-cutoff theorem, including the tangent direction

For each fixed d>=1 there is an epsilon_d>0 such that F19 is strict on every normalized \(\psi\in\mathrm{span}\{|0\rangle,\ldots,|d\rangle\}\) with \(0<\epsilon=\sqrt{1-|c_0|^2}<\epsilon_d\). This version allows a nonzero one-photon coefficient, so it includes the tangent direction to the coherent-state manifold.

The finite cross-Fock Wigner polynomial formula gives, uniformly on this unit sphere,
\[
|W_\psi-W_0|\le C_d\epsilon(1+|r|)^{2d}e^{-|r|^2}.
\]
For small epsilon this implies positivity on the disk of radius \(R_\epsilon=c_d\epsilon^{-1/(2d)}\) with sufficiently small fixed \(c_d>0\). Gaussian tail integration gives \(A_\psi-1=o(\epsilon^k)\) for every fixed positive k, uniformly in the coefficients. For any coherent state alpha, put \(q=1-e^{-|\alpha|^2}\). The norm of its nonvacuum component is \(\sqrt q\). For every unit phase \(\zeta\), \(\|\psi-\zeta|\alpha\rangle\|_2\ge|\epsilon-\sqrt q|\). If \(\sqrt q<\epsilon/2\), this is at least epsilon/2. Otherwise \(t=|\alpha|^2\ge\epsilon^2/4\), and the component outside the cutoff has squared norm \(e^{-t}\sum_{n>d}t^n/n!\). This tail is increasing in t (its derivative is \(e^{-t}t^d/d!\)); its value at \(t=\epsilon^2/4\) is at least \(e^{-1}(\epsilon^2/4)^{d+1}/(d+1)!\) for epsilon<=1. Since psi has no component outside the cutoff, the distance to every coherent vector is thus bounded below by \(c'_d\epsilon^{d+1}\). The rank-one trace-distance formula bounds the projector trace distance below by the phase-optimized vector distance. Quantitative Wehrl stability gives \(B_\psi-1\ge c''_d\epsilon^{2d+2}\), which strictly dominates the superpolynomial negative mass. This proves the uniform local assertion without assuming c1=0.

## Scope and remaining obstacle

These are local theorems, not a full resolution. The bound 256 is a convenient sufficient exponential weight, not an optimized threshold. The radius depends on the perturbation norm. Without uniform control of the high photon-number tail, negativity may be concentrated far away and of first order in the perturbation (e.g., small distant coherent components). Thus an unrestricted local theorem requires a different estimate coupling Husimi deficit and tail negativity rather than only the trace-distance lower bound. Also local maximality cannot by itself imply global maximality.

For the full conjecture, another exact reformulation for finite Bargmann polynomials P uses independent Gaussian variables: with Z a complex variable with independent real/imaginary N(0,1) components and U circular complex Gaussian with E|U|²=1,
\[
\sum_{k=0}^{\deg P} \frac{(-1)^k}{k!}|P^{(k)}(z)|^2
=\mathbb E_U[P(z+U)\overline{P(z-U)}].
\]
This follows by Taylor expansion and E[U^j \bar U^k]=delta_{jk} k!. Thus the sharp problem is a conditional expectation norm inequality under the specified unequal variances. If instead the midpoint is scaled to Z/sqrt2, then the two arguments Z/sqrt2+U and Z/sqrt2-U are independent, each distributed as Z; the sharp-looking inequality for that scaled midpoint follows trivially from conditional Jensen. But that midpoint scaling is essential: it cannot be removed by the standard Gaussian Wick product Holder inequality, nor by ordinary Jensen. The unscaled midpoint is the remaining target. This reformulation does not assume the inequality to be proved.
