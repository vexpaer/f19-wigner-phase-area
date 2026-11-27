# General pure-state work: finite-polynomial reduction and vacuum rays

**Research notes, not a solution of F19.** The phase-invariant theorem is frozen separately. These new arguments are mathematical notes, not yet Lean formalized or independently reviewed.

## 1. A reduction that avoids a questionable sharp Fock truncation

Let \(F(z)=\sum_{n\ge0} c_n z^n/\sqrt{n!}\) be the Bargmann function of a normalized pure state. In coherent amplitude coordinates put
\[
d\gamma(z)=(2\pi)^{-1}e^{-|z|^2/2}d^2z,\quad H(F)=\int |F(z)|\,d\gamma(z).
\]
In the quadrature normalization of F19 the right side is exactly \(H(F)^2\).

If \(H(F)=\infty\), the extended inequality is automatic. Otherwise take the Fejér polynomials
\[
F_N(z)=\sum_{n=0}^N (1-n/(N+1))\,c_n z^n/\sqrt{n!}.
\]
They are the averages of \(F(e^{i\theta}z)\) against the nonnegative normalized Fejér kernel \(K_N(\theta)\). The rotation action is continuous in \(L^1(d\gamma)\): approximate \(F\) by compactly supported continuous functions, use uniform continuity there and the isometric action of rotations. The Fejér approximate identity therefore yields \(\|F_N-F\|_{L^1(d\gamma)}\to0\). In particular \(H(F_N)\to H(F)\). Dominated convergence in the square-summable coefficients gives Hilbert norm convergence of their corresponding vectors.

Normalize each nonzero approximant. Their pure-state density operators converge in trace norm. Since displaced parity is bounded, the Wigner functions converge pointwise; Fatou gives \(\|W_\psi\|_1\le\liminf_N\|W_{\psi_N}\|_1\). Homogeneity and the convergence of \(H\) now give the inequality for \(\psi\) if it holds for every finite Fock polynomial. This reduction does not establish equality rigidity in the infinite-dimensional limit.

## 2. Strict inequality along every fixed finite Fock ray from vacuum

Fix a nonzero finite superposition \(\phi=\sum_{n=1}^d b_n|n\rangle\) orthogonal to vacuum, and set
\[
|\psi_\epsilon\rangle=(|0\rangle+\epsilon|\phi\rangle)/\sqrt{1+\epsilon^2 S},
\quad S=\sum_{n=1}^d |b_n|^2,\quad \epsilon\in\mathbb R.
\]
Claim: for each fixed \(\phi\), there is \(\epsilon_0(\phi)>0\) such that the sharp F19 inequality is strict for \(0<|\epsilon|<\epsilon_0(\phi)\).

### Husimi expansion

Put \(P(z)=\sum_{n=1}^d b_n z^n/\sqrt{n!}\) and take \(Z\sim\gamma\). Orthogonality of the angular harmonics gives \(E P=E P^2=0\), \(E|P|^2=\sum_n2^n|b_n|^2\). The local expansion
\[
|1+u|=1+\operatorname{Re} u+\tfrac12(\operatorname{Im}u)^2+O(|u|^3)
\]
therefore yields
\[
H(F_\epsilon)^2
=1+\epsilon^2\sum_{n=1}^d(2^{n-1}-1)|b_n|^2+O(|\epsilon|^3).
\]
To justify this under the integral, restrict to \(|Z|\le |\epsilon|^{-1/(2d)}\), where \(|\epsilon P(Z)|\le C|\epsilon|^{1/2}\); the Taylor remainder is bounded by \(C|\epsilon|^3 E|P|^3\), while the omitted polynomially weighted Gaussian tail is smaller than every power of \(|\epsilon|\). The displayed coefficient is positive whenever any \(b_n\ne0\) for \(n\ge2\).

The exceptional direction is \(\phi=b_1|1\rangle\). Write \(\delta=\epsilon |b_1|\). Rotational invariance and the binomial series give
\[
E|1+\delta Z|=1+\delta^2/2+\delta^4/8+O(\delta^6).
\]
Indeed the circle-average coefficients are \(\binom{1/2}{k}^2\), and \(E|Z|^2=2,\ E|Z|^4=8\). Use the same cutoff and a sixth-order remainder (or expand through fifth order, whose angular average is zero). Thus
\[
H(F_\epsilon)^2=(E|1+\delta Z|)^2/(1+\delta^2)
=1+\delta^4/2+O(\delta^6).
\]

### Wigner negativity is beyond all algebraic orders along these rays

For finite Fock support, \(W_{\psi_\epsilon}(r)=e^{-|r|^2}R_\epsilon(r)/(\pi(1+\epsilon^2S))\) for a real polynomial
\(R_\epsilon=1+\epsilon R_1+\epsilon^2 R_2\), with \(R_1\) of degree at most \(d\) and \(R_2\) of degree at most \(2d\). This follows by expanding displaced-parity matrix elements in the Fock basis. On \(|r|\le |\epsilon|^{-1/(2d)}\), the two perturbation terms are \(O(|\epsilon|^{1/2})\) and \(O(|\epsilon|)\) uniformly, so the Wigner function is nonnegative there for small enough \(|\epsilon|\). Outside that disk its absolute integral is bounded by a polynomially weighted Gaussian tail, \(o(|\epsilon|^k)\) for every fixed \(k>0\). Normalization implies
\[
\|W_{\psi_\epsilon}\|_1=1+2\int(-W_{\psi_\epsilon})_+ =1+o(|\epsilon|^k).
\]
Comparing with the strictly positive quadratic or quartic Husimi gap proves the raywise claim. Displacements preserve the inequality, so the same statement holds for the displaced rays.

**Limitations:** the threshold depends on the direction and cutoff. This is not a uniform neighborhood in the full Hilbert or modulation-space topology; it does not prove the general local-maximizer question posed in the preprint. Nor does it prove the inequality at arbitrary finite superposition amplitudes.

## 3. Numerical diagnostics

Run python pure_state/verify_pure.py (NumPy and SciPy). Uses Gauss–Laguerre radial quadrature and periodic angular quadrature with all cross-Fock terms. The fixed seed sample of 100 complex random normalized states per cutoff d=1,2,4,8 gave refined maximum ratios A/H² of 0.9999564, 0.9862145, 0.9305723, 0.8032609. These are sample maxima, not upper bounds or certificates. The qubit vacuum-ray test at epsilon=.05 gives gap 3.12505e-6, consistent with the quartic expansion. Random sampling near the vacuum and high-degree perturbations should be supplemented by analytic bounds or certified numerical methods.

## 4. Remaining research problem

The finite-polynomial inequality still needs to be proved with a constant independent of degree. The sharp estimate is quadratic in one and the same state; the existing triangle-inequality argument in Gagatsos, arXiv:2611.30969v1, loses a factor two. A generic bound for arbitrary two-mode wavefunctions cannot recover it. Do not present a bound with the weak constant as the solution. Investigate uniform estimates retaining the phases of the cross-Fock terms and seek adversarial counterexamples.
