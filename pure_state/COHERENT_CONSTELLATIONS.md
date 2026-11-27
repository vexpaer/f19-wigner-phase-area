# Coherent constellations and a bilinear obstruction

Research note, 2026-11-27. Mathematical derivations for review, not Lean formalized. This note gives a new sufficient condition at the sharp F19 constant and rules out a natural stronger conjecture. It does not settle the full F19 conjecture or claim priority.

## 1. An explicit sharp result for arbitrarily many separated coherent components

Use complex coherent amplitude \(\alpha=(x+ip)/\sqrt2\). For an unnormalized vector \(f=\sum_{j=1}^M c_j|\alpha_j\rangle\), put
\[
H(f)=\frac1{2\pi}\int_{\mathbb C}|\langle z|f\rangle|\,d^2z,
\qquad S=\sum_j|c_j|,\qquad D=\sum_j |c_j|^2.
\]
Then F19 is the homogeneous inequality \(\|W_f\|_1\le H(f)^2\), where \(W_f\) denotes the Wigner density of the unnormalized rank-one operator \(|f\rangle\langle f|\), integrated in either coordinate convention with its corresponding Jacobian. In complex amplitude coordinates the normalized vacuum density is \((2/\pi)e^{-2|z|^2}\). In particular \(H(|\alpha\rangle)=1\).

**Proposition.** Suppose \(M\ge2\), \(f\ne0\), the pairwise separations satisfy \(|\alpha_i-\alpha_j|\ge7\), and \(D/S^2\le1/2\). Then \(\|W_f\|_1<H(f)^2\). Thus this covers equal-modulus superpositions of arbitrarily many well-separated coherent states, with completely arbitrary relative phases, as well as unequal coefficients satisfying the displayed participation-ratio condition.

### Husimi lower bound
Write \(v_j(z)=c_j\langle z|\alpha_j\rangle\). The elementary pointwise estimate
\[
\left|\sum_jv_j\right|\ge\sum_j|v_j|-2\sum_{i<j}\min(|v_i|,|v_j|)
\]
follows by choosing a largest summand and applying the reverse triangle inequality; the pairwise minima include every other summand at least once. Since \(\min(a,b)\le\sqrt{ab}\), integrating Gaussian overlaps gives
\[
H(f)\ge S-2\sum_{i<j}\sqrt{|c_i c_j|}\,e^{-|\alpha_i-\alpha_j|^2/8}.
\]
Indeed \(|\langle z|\alpha_j\rangle|=e^{-|z-\alpha_j|^2/2}\), and completing the square in the geometric mean gives the exponential factor. The arithmetic-geometric mean inequality implies
\[
H(f)\ge(1-\delta)S,\qquad
\delta=\max_i\sum_{j\ne i}e^{-|\alpha_i-\alpha_j|^2/8}.
\]

### Wigner upper bound retaining real interference
The complex cross Wigner density for \(|\alpha_i\rangle\langle\alpha_j|\) is
\[
W_{ij}(z)=\frac2\pi\exp\left(-2|z|^2+2z\bar\alpha_j+2\bar z\alpha_i
-\alpha_i\bar\alpha_j-\frac{|\alpha_i|^2+|\alpha_j|^2}{2}\right).
\]
This follows immediately by evaluating \(\langle\alpha_j|D(2z)\Pi|\alpha_i\rangle\) and including the Jacobian to complex amplitude coordinates. Its modulus is \((2/\pi)e^{-2|z-(\alpha_i+\alpha_j)/2|^2}\). If \(d=|\alpha_i-\alpha_j|\), then its phase (including the coefficients) is a constant plus a centered real normal variable of variance \(d^2\) under that Gaussian envelope. Pairing conjugate cross terms and applying the Fourier series for \(|\cos|\) gives
\[
\int|\operatorname{Re}(e^{i\theta}W_{ij})|\,d^2z
\le q(d):=\frac2\pi+\frac4\pi\sum_{m\ge1}\frac{e^{-2m^2d^2}}{4m^2-1}
\le\frac2\pi(1+e^{-2d^2}),
\]
uniformly in \(\theta\); the final sum bound uses \(\sum_{m\ge1}(4m^2-1)^{-1}=1/2\). Consequently if all distances are at least \(d_0\),
\[
\|W_f\|_1\le D+q_0(S^2-D),\qquad q_0=\frac2\pi(1+e^{-2d_0^2}).
\]
Combining the two estimates yields the more general sufficient criterion
\[
\delta<1,\qquad (1-\delta)^2\ge q_0+(1-q_0)D/S^2
\]
when \(q_0<1\). A strict comparison implies strict F19.

### Uniform separation, independent of number of components
For a fixed center \(i\), the number of other centers with \(kd_0\le|\alpha_j-\alpha_i|<(k+1)d_0\) is at most \((2k+3)^2\): the radius-\(d_0/2\) disks about those centers have disjoint interiors and are all inside the disk of radius \((k+3/2)d_0\) about \(\alpha_i\). Hence for \(d_0=7\),
\[
\delta\le\sum_{k=1}^\infty(2k+3)^2e^{-49k^2/8}
\le25\sum_{k=1}^\infty k^2 e^{-6k}
=25\frac{x(1+x)}{(1-x)^3},\quad x=e^{-6}.
\]
Using \(e^6>350\), the last expression is less than \(1/12\) (verify by substituting \(x=1/350\) and comparing rationals). Also \(q_0<2/3\) since \(\pi>3.1\) and \(e^{-98}<0.01\). The coefficient hypothesis then gives
\[
H(f)^2>(11/12)^2 S^2=\frac{121}{144}S^2>
\frac56 S^2>\|W_f\|_1.
\]
The inequalities are homogeneous, so normalizing the vector does not change the conclusion.

This proof is uniform in the number of coherent components and works for arbitrary complex phases. It does not imply density of the separated subclass in the Bargmann L1 norm. The separation and participation assumptions cannot simply be removed by taking a limit; arbitrarily small coherent components are not covered by this criterion.

## 2. The sharp complex-bilinear extension fails

One might try proving \(\|W(f,g)\|_1\le H(f)H(g)\) for arbitrary normalized pure vectors \(f,g\), which would imply F19 when \(f=g\). This stronger assertion is false.

Take normalized real wavefunctions \(f_\lambda(x)=(\lambda/\pi)^{1/4}e^{-\lambda x^2/2}\) and \(g_\mu(x)=(\mu/\pi)^{1/4}e^{-\mu x^2/2}\). With the physical convention
\[
W(f,g)(x,p)=\pi^{-1}\int f(x+y)\overline{g(x-y)}e^{-2ipy}\,dy,
\]
direct Gaussian integration gives
\[
|W(f_\lambda,g_\mu)(x,p)|=
\frac{\sqrt2(\lambda\mu)^{1/4}}{\pi\sqrt{\lambda+\mu}}
e^{-2\lambda\mu x^2/(\lambda+\mu)-2p^2/(\lambda+\mu)},
\quad
\|W(f_\lambda,g_\mu)\|_1=
\sqrt{\frac{\lambda+\mu}{2\sqrt{\lambda\mu}}}.
\]
For a squeezed vacuum with \(\lambda=e^{2s}\), the covariance of its Husimi density is \(\mathrm{diag}((1+\lambda^{-1})/2,(1+\lambda)/2)\). Evaluating the Gaussian root integral gives \(H(f_\lambda)^2=\cosh s\). Taking \(\mu=e^{-2s}\) yields
\[
\frac{\|W(f_{e^{2s}},g_{e^{-2s}})\|_1}
 {H(f_{e^{2s}})H(g_{e^{-2s}})}
=\frac{\sqrt{\cosh(2s)}}{\cosh s}
=\sqrt{2-\operatorname{sech}^2s}>1\quad(s\ne0).
\]
The ratio approaches \(\sqrt2\) as \(|s|\to\infty\). Thus any uniform bound for the *complex* cross Wigner norm must have normalized constant at least \(\sqrt2\). This is consistent with F19, which concerns a self-Wigner function and hence its real structure. It makes a sharp estimate for the real paired interference terms a more appropriate target than a sharp complex-bilinear estimate.

## 3. Relation to the general conjecture

The sufficient criterion above is a genuine sharp-constant subclass beyond phase-invariant states and finite Fock-degree cases. The obstruction explains why direct polarization or bilinear norm arguments cannot simply recover constant one. A full proof still needs control of overlapping coherent amplitudes, particularly cancellation at each midpoint. The universal harmonic bound in UNIVERSAL_BOUND.md remains applicable without any separation or participation assumption.
