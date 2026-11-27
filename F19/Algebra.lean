import Mathlib

/-! Algebraic certificates. The analytic inputs are explicit hypotheses. -/
namespace F19

def momentPoly (n : ℝ) : ℝ :=
  70*n^4 + 140*n^3 + 170*n^2 + 100*n + 24

theorem moment_coefficients (n : ℝ) :
    (n*(n-1))^2 + (4*n^2)^2 + (6*n^2+6*n+2)^2 +
      (4*(n+1)^2)^2 + ((n+1)*(n+2))^2 = momentPoly n := by
  unfold momentPoly
  ring

theorem moment_gap (n : ℝ) (hn : 1 ≤ n) :
    momentPoly n < 108*(n+1/2)^4 := by
  have hx : 0 ≤ n-1 := by linarith
  have h : 0 < 38*(n-1)^4 + 228*(n-1)^3 + 448*(n-1)^2 +
      318*(n-1) + (171/4 : ℝ) := by positivity
  have he : 108*(n+1/2)^4 - momentPoly n =
      38*(n-1)^4 + 228*(n-1)^3 + 448*(n-1)^2 +
      318*(n-1) + (171/4 : ℝ) := by
    unfold momentPoly
    ring
  linarith

theorem gamma_ratio_gap (n : ℝ) :
    (n+1)^2*(n+5/2) - (n+2)^2*(n+1/2) = 1/2 := by ring

theorem fock_comparison (n A B : ℝ) (hn : 1 ≤ n)
    (hB0 : 0 ≤ B)
    (hA : A^8 ≤ Real.pi^4 * momentPoly n / 1728)
    (hB : Real.pi^4 * (n+1/2)^4 / 16 ≤ B^8) : A < B := by
  have hp : 0 < Real.pi^4 := pow_pos Real.pi_pos 4
  have hg := moment_gap n hn
  have hm := mul_lt_mul_of_pos_left hg hp
  have hgap : Real.pi^4 * momentPoly n / 1728 <
      Real.pi^4 * (n+1/2)^4 / 16 := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1728)).2
    calc
      Real.pi^4 * momentPoly n < Real.pi^4 * (108*(n+1/2)^4) := hm
      _ = Real.pi^4 * (n+1/2)^4 / 16 * 1728 := by ring
  have hab : A^8 < B^8 := lt_of_le_of_lt hA (lt_of_lt_of_le hgap hB)
  by_contra! h
  have hpow : B^8 ≤ A^8 := by gcongr
  exact (not_lt_of_ge hpow) hab

#print axioms moment_coefficients
#print axioms moment_gap
#print axioms gamma_ratio_gap
#print axioms fock_comparison

end F19
