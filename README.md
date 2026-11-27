# F19 — Wigner negativity costs phase-space area

Research candidate for the phase-invariant sector of C. N. Gagatsos, *Wigner negativity costs phase-space area: A conjectured refinement of the Lieb–Solovej inequality at Rényi order one half*, [arXiv:2611.30969](https://arxiv.org/abs/2611.30969), Conjecture 1.

**Status:** sharp inequality for all phase-invariant single-mode states, including arbitrary countable Fock mixtures, proved in the manuscript; the explicit planar series inequality is verified in Lean. The general F19 conjecture remains open in this project.

## Verified release baseline

- [Manuscript (LaTeX)](paper/manuscript.tex), Ximing Wang.
- [CI run 82](https://github.com/vexpaer/f19-wigner-phase-area/actions/runs/45998583445), verified commit `ddeab5edf826752e1588932ac238f204d472ae57`, Lean 4.19.0 / Mathlib v4.19.0.
- Main theorems: `F19.planar_diagonal_inequality`, `F19.planar_diagonal_strict`, `F19.diagonal_series_abs_summable_ae`, and `F19.planarDiagonalHusimiRoot_sq`.
- The audited theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. The quantum operator identification and displacement covariance are mathematical arguments in the paper, not formalized here.
- This is a restricted-sector result, not a claim of a solution to all of F19. Independent mathematical and novelty review remains appropriate.

## Reproduce
Run `lake update`, `lake exe cache get`, `lake build`, and `lake env lean F19/Algebra.lean`. Run `python -m pip install -r requirements.txt && python verify.py` for independent symbolic/numerical diagnostics.

## Mathematical route
With the phase-space conventions of the cited preprint, let t=x²+p², f_n(t)=exp(-t)L_n(2t), A_n=∫₀∞|f_n|, B_n=2^n Γ(n/2+1)^2/n!. Let P(n)=70n⁴+140n³+170n²+100n+24.

The Fock-state inequality reduces to A_n≤B_n. Laguerre orthogonality gives ∫f_n²=1/2 and the fourth moment ∫t⁴f_n²=P(n)/32. With the weight 1+(t/a)^4 and a⁴=6P(n)/32, Cauchy–Schwarz and the reciprocal quartic integral yield A_n⁸≤π⁴P(n)/1728.

Write R(n)=Γ((n+2)/2)/Γ((n+1)/2). Gamma log-convexity and recurrence give R(n)²≥(n+1)²/[2(n+2)] and R(n+2)=(n+2)R(n)/(n+1). Applying the lower bound at n+6 and substituting the recurrence gives 2R(n)²≥U(n)/V(n), where U=((n+1)(n+3)(n+5)(n+7))² and V=(n+8)((n+2)(n+4)(n+6))². For n≥1 the polynomial 108U⁴-PV⁴ has strictly positive coefficients when expanded in n-1. Thus P(n)<1728R(n)⁸. Gamma duplication gives B_n=√π R(n). The vacuum is the equality case.

For the physical extension to number-diagonal mixtures, Proposition 1 of Gagatsos establishes convexity/concavity reduction from componentwise pure-state inequalities. The countable mixture extension, including the planar integral and finite-RHS convergence, is now formalized in Lean; the identification of the radial formulas with quantum operators is supplied separately in the manuscript.

The manuscript is a preprint draft; no journal acceptance or independent verification is claimed.
