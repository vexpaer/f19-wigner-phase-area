# F19 — Wigner negativity costs phase-space area

Research candidate for the phase-invariant sector of C. N. Gagatsos, *Wigner negativity costs phase-space area: A conjectured refinement of the Lieb–Solovej inequality at Rényi order one half*, [arXiv:2611.30969](https://arxiv.org/abs/2611.30969), Conjecture 1.

**Status:** verified analytic core, not a complete formalization of the phase-invariant conjecture. No claim of priority or full solution is made.

## Verified baseline

[CI run 20](https://github.com/vexpaer/f19-wigner-phase-area/actions/runs/45986945290) successfully compiled commit `7d9192a544238a1a973b82c167c72095a55010ae` with Lean 4.19.0 and Mathlib v4.19.0. All 16 reported theorem dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`. The baseline includes:
- algebraic fourth-moment certificates;
- Gamma log-convexity, a finite-shift bound, duplication and factorial formulas;
- Husimi Gamma integral;
- Bochner integral Cauchy–Schwarz;
- optimized fourth-moment bound.

The [verification PR](https://github.com/vexpaer/f19-wigner-phase-area/pull/1) contains additional experimental code for the reciprocal quartic integral, explicit Laguerre orthogonality, exact fourth moment and radial Wigner/Husimi comparison. Its results are not certified until the respective build and axiom audit succeed.

## Reproduce
Run `lake update`, `lake exe cache get`, `lake build`, and `lake env lean F19/Algebra.lean`. Run `python -m pip install -r requirements.txt && python verify.py` for independent symbolic/numerical diagnostics.

## Mathematical route
With the phase-space conventions of the cited preprint, let t=x²+p², f_n(t)=exp(-t)L_n(2t), A_n=∫₀∞|f_n|, B_n=2^n Γ(n/2+1)^2/n!. Let P(n)=70n⁴+140n³+170n²+100n+24.

The Fock-state inequality reduces to A_n≤B_n. Laguerre orthogonality gives ∫f_n²=1/2 and the fourth moment ∫t⁴f_n²=P(n)/32. With the weight 1+(t/a)^4 and a⁴=6P(n)/32, Cauchy–Schwarz and the reciprocal quartic integral yield A_n⁸≤π⁴P(n)/1728.

Write R(n)=Γ((n+2)/2)/Γ((n+1)/2). Gamma log-convexity and recurrence give R(n)²≥(n+1)²/[2(n+2)] and R(n+2)=(n+2)R(n)/(n+1). Applying the lower bound at n+6 and substituting the recurrence gives 2R(n)²≥U(n)/V(n), where U=((n+1)(n+3)(n+5)(n+7))² and V=(n+8)((n+2)(n+4)(n+6))². For n≥1 the polynomial 108U⁴-PV⁴ has strictly positive coefficients when expanded in n-1. Thus P(n)<1728R(n)⁸. Gamma duplication gives B_n=√π R(n). The vacuum is the equality case.

For the physical extension to number-diagonal mixtures, Proposition 1 of Gagatsos establishes convexity/concavity reduction from componentwise pure-state inequalities. The identification of the radial formulas with quantum states and the countable mixture extension are not yet formalized in Lean.

Manuscript preparation is gated on validation and novelty review.
