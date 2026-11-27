# F19 — Wigner negativity costs phase-space area

Research candidate for the phase-invariant sector of C. N. Gagatsos, *Wigner negativity costs phase-space area: A conjectured refinement of the Lieb–Solovej inequality at Rényi order one half*, [arXiv:2611.30969](https://arxiv.org/abs/2611.30969).

Current scope: algebraic certificates and a conditional comparison, not complete verification of the physical theorem. No claim of priority is made. 

## Reproduce
Run `lake update`, `lake exe cache get`, `lake build`, and `lake env lean F19/Algebra.lean`. Inspect the axiom reports. Run `python -m pip install -r requirements.txt && python verify.py` for independent numerical/symbolic diagnostics.

## Proof roadmap
For a number state in the paper's convention, put t=x²+p², f_n(t)=exp(-t)L_n(2t), A_n=∫₀∞|f_n|, B_n=2^n Γ(n/2+1)^2/n!. Let P(n)=70n⁴+140n³+170n²+100n+24.

1. Derive the Wigner and Husimi number-state formulas and the radial integrals.
2. Laguerre orthogonality and recurrence give ∫f_n²=1/2 and ∫t⁴f_n²=P(n)/32.
3. Weighted Cauchy–Schwarz, ∫₀∞1/(1+u⁴)du=π/(2√2), and a=(6P(n)/32)^(1/4) yield A_n⁸≤π⁴P(n)/1728.
4. Gamma duplication and recurrence give B_(n+2)/B_n=(n+2)/(n+1). The normalized squared ratio B_n²/(n+1/2) decreases on each parity to π/2 by Stirling, hence B_n⁸≥π⁴(n+1/2)^4/16.
5. P(n)<108(n+1/2)^4 for n≥1, proving the conditional strict comparison. Vacuum is equality.
6. For a number-diagonal mixture Q=Σp_n Q_n with M=∫√Q finite, weighted Cauchy–Schwarz gives (∫√Q_n)²≤M∫Q_n/√Q. Tonelli gives Σp_n B_n≤M²/(8π). Trace-norm convergence and bounded displaced parity identify the Wigner series; its L¹ norm is bounded by Σp_n A_n. Infinite M is treated in extended reals.

Steps 1–4 (analytic inputs), vacuum and step 6 still need formalization. The present Lean code certifies the polynomial identities and conditional step 5. A successful build alone does not certify the original conjecture. Manuscript preparation is gated on full analytic verification and novelty review.
