# Improved hole-flux bound and uniform coefficient 1.300

Research note, 2026-11-27. Analytic proof candidate, not independently reviewed or Lean formalized. No claim of priority or solution of the sharp F19 conjecture.

We refine TOPOLOGICAL_CONDITIONAL_BOUND.md. In the established normalization \(A=\|W_\rho\|_1\), \(B=(\int\sqrt{Q_\rho})^2/(8\pi)\), the new consequence is \(A\le 1.300 B\) for every state with finite B. The sharp target remains \(A\le B\).

## 1. Improved hole-flux inequality

Retain the notation of the previous topological note: for an even normalized finite Fock state \(h\), \(u(z)=e^{-|z|^2}|F(z)|^2\), \(v=|F(0)|\), \(T=\max u\), \(m(t)=|\{u>t\}|/\pi\). At regular levels \(v^2<t<T\), an exchanged pair of superlevel components contributes at least 2 to \(-tm'(t)\). An invariant component instead contributes at least
\[
\frac{M+L}{M-d}+\frac{L}{d}
=\frac{NM}{d(M-d)},\qquad d=N-L,\quad 0<d<M,\quad N\ge2,
\]
where M is its normalized area, L the total normalized hole area, and N the number of zeros in its holes, counted with multiplicity. This is exactly the flux and perimeter argument of the preceding note. The new observation is that \(d\le N\), because L is nonnegative.

If \(N\ge M/2\), the contribution is at least \(4N/M\ge2\). Otherwise \(2\le N<M/2\), hence M>4. Since \(d(M-d)\) is increasing for \(0<d<M/2\), we have
\[
\frac{NM}{d(M-d)}\ge \frac{M}{M-N}\ge\frac{M}{M-2}.
\]
As M<=m(t), and x/(x-2) decreases for x>2, combining the two cases (and the exchanged pair case) gives
\[
-tm'(t)\ge
\begin{cases}
2,&m(t)\le4,\\
m(t)/(m(t)-2),&m(t)>4.
\end{cases}
\]
This is strictly stronger in the large-area regime than the earlier bound \(\max(1,\min(2,8/m(t)))\).

Also, the universal slope \(-sm'(s)\ge1\), integrated for \(0<s<t\), gives \(m(s)\ge m(t)+\log(t/s)\). Normalization \(\int_0^T m(s)ds=1\) implies
\[
m(t)\le 1/t-1,
\]
because \(\int_0^t\log(t/s)ds=t\). All the slope inequalities extend distributionally as before; the singular part of the derivative of a decreasing function is nonpositive. Thus
\[
-tm'(t)\ge q_*(t):=
\begin{cases}
(1-t)/(1-3t),&0<t<1/5,\\
2,&1/5\le t<T
\end{cases}
\qquad(v^2<t<T).
\]
Indeed for \(t<1/5\) with m>4, \(m/(m-2)\ge (1-t)/(1-3t)\); for m<=4 the lower bound 2 suffices. For t>=1/5 the mass estimate forces m<=4.

## 2. Improved even-state overlap cap

The earlier even-state projection estimate gives
\[
\sqrt T\le \max_{0\le x\le1} \{vx+a(1-x^2)\},\qquad a=\sqrt{(1-v^2)/2}.
\]
Optimizing this quadratic exactly gives
\[
\sqrt T\le
\begin{cases}
a+v^2/(4a),&v^2\le2/3,\\
v,&v^2\ge2/3.
\end{cases}
\]
The v=1 endpoint uses the second branch and needs no division by a. This improves the earlier Cauchy--Schwarz cap.

## 3. A uniform conditional deficit with coefficient 3/20

We prove
\[
H(h)=\frac12\int\sqrt u\,d^2z/\pi\ge 1+\frac3{20}(1-v)^2.
\]
Use the layer-cake slope estimate established in TOPOLOGICAL_CONDITIONAL_BOUND.md:
\[
H(h)\ge\frac{1+T}{2\sqrt T}
+\frac12\int_0^T (q(t)-1)(t^{-1/2}-T^{-1/2})dt,
\]
for any valid slope lower bound q>=1.

First consider v<=1/2. For T<=1/5 the standard term alone gives \(H\ge3/\sqrt5>1.15\). In the following subcases with T>1/5, let \(\ell\) be a fixed number at least v^2 and at most 1/5. Use q=1 below ell, then
\[
q(t)=1+P(t),\quad P(t)=2t+6t^2+18t^3+54t^4
\]
on \((\ell,1/5)\), and q=2 above 1/5. The polynomial is a lower bound for \(q_*(t)-1=2t/(1-3t)\) by the geometric series. Put
\[
I_\ell=\sum_{i=1}^4 2\,3^{i-1}\frac{(1/5)^{i+1}-\ell^{i+1}}{i+1},\qquad
K_\ell=\sum_{i=1}^4 2\,3^{i-1}\frac{(1/5)^{i+1/2}-\ell^{i+1/2}}{i+1/2}.
\]
The integrated estimate and AM--GM give
\[
H(h)\ge \sqrt T+\frac{6/5-I_\ell}{2\sqrt T}-\frac1{\sqrt5}+\frac{K_\ell}{2}
\ge\sqrt{2(6/5-I_\ell)}-\frac1{\sqrt5}+\frac{K_\ell}{2}.
\]

* If \(0\le v\le1/20\), choose \(\ell=1/400\). Here \(I_\ell=1706232795473/25600000000000<0.066650\) and \(K_\ell>0.18900\). Since \(\sqrt{2(6/5-I_\ell)}>1.50555\), \(1/\sqrt5<0.44722\), the displayed bound exceeds 1.15283, hence 1.15.
* If \(1/20<v\le1/5\), choose \(\ell=1/25\). Here \(I_\ell=3169696/48828125<0.064916\) and \(K_\ell>0.17766\). Since \(\sqrt{2(6/5-I_\ell)}>1.50670\), the bound exceeds 1.14831, greater than \(1+(3/20)(19/20)^2=1.135375\).
* If \(1/5<v\le1/\sqrt5\), choose \(\ell=1/5\), so I=K=0. Then \(H\ge\sqrt{12/5}-1/\sqrt5>1.1019>1+(3/20)(4/5)^2=1.096\).

All decimal comparisons in these three cases are rational certificates: the I values are exact, the radical inequalities follow by squaring positive rational bounds, and the K inequalities follow directly from their displayed sums, using \(2.2360679<\sqrt5<2.2360680\) and the exact square roots of ell.

* If \(1/\sqrt5<v\le1/2\), use q=2 on (1/4,T), q=1 below 1/4, when T>1/4; this is valid because \(v^2\le1/4\). Then \(H\ge\sqrt{5/2}-1/2>1.08\). For T<=1/4, \(H\ge5/4\). Both exceed \(1+(3/20)(1-1/\sqrt5)^2\), which is less than 1.05.

It remains to prove the deficit for \(v\ge1/2\). If \(1/2\le v\le\sqrt{2/3}\), the optimized overlap cap gives simultaneously
\[
\sqrt T\le (1+v)/2,\qquad \sqrt T\le\sqrt{2/3}.
\]
For the first inequality, \(a+v^2/(4a)\le(1+v)/2\) is equivalent, after multiplying by 4a and squaring positive sides, to
\[
p(v)=-3v^4-4v^3+4v^2+4v-2\ge0.
\]
On [1/2,5/6] this polynomial is concave, since \(p''=-36v^2-24v+8<0\), and its endpoint values are \(5/16\) and \(151/432\), both positive. The required interval lies within [1/2,5/6]. The second inequality follows by squaring the optimized cap: \((2-v^2)^2/[8(1-v^2)]\le2/3\) is equivalent to \(3v^4+4v^2-4\le0\), valid when \(v^2\le2/3\). Thus the standard layer-cake estimate alone yields
\[
H-1\ge \frac{(1-\sqrt T)^2}{2\sqrt T}
\ge\frac{(1-v)^2}{8\sqrt{2/3}}>\frac3{20}(1-v)^2
\]
(the non-strict version is sufficient). Finally if \(\sqrt{2/3}\le v\le1\), the exact overlap cap is \(\sqrt T\le v\), and \(H-1\ge(1-v)^2/(2v)\ge(1-v)^2/2\). This completes the conditional estimate.

## 4. Consequence for F19

Repeat the identical-input conditional beam-splitter argument of EVEN_CONDITIONAL_BOUND.md. It gives
\[
 B\ge J+c(J-1)^2/J,\qquad c=3/20,\qquad J\ge1.
\]
The heat-flow estimate is \(A^2\le2J^2-k\), \(k=27/32\). Put \(x=1/J\). Then
\[
\frac{A^2}{B^2}\le\frac{2-kx^2}{[1+c(1-x)^2]^2}
\le\frac{2-kx^2}{1+2c(1-x)^2}< (13/10)^2.
\]
The last inequality is an exact rational certificate: set \(C=13/10\) and \(a=2cC^2\); completing the square,
\[
C^2(1+2c(1-x)^2)-(2-kx^2)
\ge C^2-2+\frac{ak}{a+k}=\frac{2413}{360200}>0.
\]
No numerical optimization is used in this proof. The existing Fejer approximation, parity/Fatou limit and mixed-state spectral convexity/concavity arguments extend the bound from finite Fock states to arbitrary single-mode states. One may use a strictly smaller uniform coefficient than 1.300 since the displayed certificate has positive margin; we retain the convenient rational constant.

## 5. Remaining gap

This improves the uniform conditional coefficient 0.11 to 0.15, and the uniform F19 coefficient 1.318 to 1.300. It still does not establish the sharp even-state linear deficit or the required coupled heat/conditional inequality for identical inputs. In fact any estimate obtained solely by substituting a quadratic vacuum deficit into the present heat bound cannot yield the sharp factor 1: at J=1 the heat bound gives \(A^2\le2-27/32>1\), whereas the exact vacuum has A=1. The issue is not numerical optimization of the hole flux alone; the smoothing and conditional deficits must be linked. Independent review and Lean verification are pending.
