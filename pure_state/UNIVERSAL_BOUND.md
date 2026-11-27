# A dimension-free improvement of the universal single-mode F19 bound

Research note, 2026-11-27. Mathematical derivation for independent review; not yet Lean formalized and not a resolution of the sharp conjecture. No priority claim is made. Uses the normalization and parity integral of Gagatsos, arXiv:2611.30969v1, Eq. (13).

## Claim

Write \(B_\rho=(\int \sqrt{Q_\rho}\,d^2r)^2/(8\pi)\). For every single-mode density operator,
\[
\|W_\rho\|_1\le \frac4\pi B_\rho+\frac{4\log2-2}{\pi}
\le \frac{2+4\log2}{\pi} B_\rho.
\]
The last factor is approximately 1.519, compared with 2 in Gagatsos's Proposition 2; F19 asks for factor 1 and its equality cases. Equivalently the uniform coefficient multiplying \((\int\sqrt Q)^2\) is \((1+2\log2)/(4\pi^2)\).

## Proof

It suffices first to take \(\rho=|\psi\rangle\langle\psi|\) with \(\|\psi\|_2=1\), and write \(a(u)=\langle u|\psi\rangle\) in physical phase-space coordinates \(u=(x,p)\). Then \(Q=|a|^2/(2\pi)\), and coherent resolution of identity gives \(\int |a(u)|^2\,d^2u=2\pi\). Set \(L=\int |a|\) and \(B=L^2/(16\pi^2)\). If \(L=\infty\) the extended-real inequality is automatic. Otherwise choose a measurable argument \(\theta(u)=\arg a(u)\), arbitrary at zeros.

Gagatsos's parity representation is
\[
W(r)=\frac1{2\pi^2}\int e^{i r\wedge s}a(r+s)\overline{a(r-s)}\,d^2s,
\qquad r\wedge s=x s_p-p s_x .
\]
Because \(W\) is real, take the real part before the triangle inequality. Under \(u=r+s,v=r-s\), one has \(r\wedge s=-u\wedge v/2\) and the Jacobian is \(1/4\). Thus with \(\Phi(u,v)=\theta(u)-\theta(v)-u\wedge v/2\),
\[
\|W\|_1 \le \frac1{8\pi^2}\iint |a(u)a(v)|\,|\cos\Phi(u,v)|\,d^2u\,d^2v.
\]
All integrals here converge absolutely since \(a\in L^1\).

For each positive integer \(m\), let \(f_m(u)=|a(u)|e^{2im\theta(u)}\); hence \(f_m\in L^1\cap L^2\) and \(\|f_m\|_2^2=2\pi\). Define
\[
I_m=\iint f_m(u)\overline{f_m(v)} e^{-im u\wedge v}\,d^2u\,d^2v.
\]
For the unnormalized Fourier transform \(\mathcal F f(\xi)=\int f(u)e^{-iu\cdot\xi}d^2u\) on \(\mathbb R^2\), Plancherel gives \(\|\mathcal F f\|_2=2\pi\|f\|_2\). Put \(Jv=(v_p,-v_x)\), so \(u\wedge v=u\cdot Jv\). Scaling the frequency variable by \(m\) gives
\[
\|\mathcal F f_m(mJ\,\cdot)\|_2=(2\pi/m)\|f_m\|_2.
\]
Fubini and Cauchy-Schwarz yield \(|I_m|\le 4\pi^2/m\). Notice that \(\operatorname{Re} I_m=\iint |a(u)a(v)|\cos(2m\Phi(u,v))\,du\,dv\). This use of a single scalar amplitude with an exact \(L^2\) normalization is where rank-one structure enters.

The absolutely and uniformly convergent Fourier series
\[
|\cos t|=\frac2\pi+\frac4\pi\sum_{m=1}^{\infty}
\frac{(-1)^{m+1}}{4m^2-1}\cos(2mt)
\]
can be integrated termwise against \(|a(u)a(v)|\). Bounding each harmonic by the Plancherel estimate gives
\[
\begin{aligned}
\|W\|_1&\le\frac1{8\pi^2}
\left(\frac2\pi L^2+\frac4\pi\sum_{m\ge1}\frac{|I_m|}{4m^2-1}\right)\\
&\le \frac4\pi B+\frac2\pi\sum_{m\ge1}\frac1{m(4m^2-1)}
=\frac4\pi B+\frac{4\log2-2}\pi.
\end{aligned}
\]
The sum is \(2\log2-1\), since its Nth partial sum is \(2(H_{2N}-H_N)+1/(2N+1)-1\), by the partial fraction identity \(1/[m(4m^2-1)]=1/(2m-1)+1/(2m+1)-1/m\).

For a general density operator with finite \(B_\rho\), take a countable spectral decomposition \(\rho=\sum_j p_j|\psi_j\rangle\langle\psi_j|\). Convexity of Wigner L1 and concavity of \(B\) (Gagatsos Proposition 1) transfer the affine bound: \(\|W_\rho\|_1\le \sum_jp_j\|W_j\|_1\le (4/\pi)B_\rho+(4\log2-2)/\pi\). The countable extension follows from the triangle inequality, Tonelli, and pointwise convergence via bounded displaced parity; the concavity estimate follows from pointwise Cauchy-Schwarz in the spectral weights followed by Tonelli. Finally \(B_\rho\ge1\) by Lieb–Solovej, and \(4\log2-2>0\). This proves the displayed uniform bound.

## Remaining sharp gap

The use of \(|\cos\Phi|\) still loses cancellation between positive and negative real contributions at fixed midpoint \(r\). Its constant Fourier coefficient \(2/\pi\) produces the asymptotic factor \(4/\pi>1\), even if the harmonic correction is entirely removed. Thus improving the bounds on \(I_m\) alone cannot complete F19 by this estimate; one needs to retain cancellation inside the midpoint integral, or another argument exploiting the analytic Bargmann structure. No claim about equality rigidity of the original sharp inequality follows from this estimate.
