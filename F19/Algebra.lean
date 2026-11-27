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


namespace F19

noncomputable def gammaRatio (n : ℝ) : ℝ :=
  Real.Gamma ((n+2)/2) / Real.Gamma ((n+1)/2)

theorem gammaRatio_pos (n : ℝ) (hn : 0 ≤ n) : 0 < gammaRatio n := by
  unfold gammaRatio
  exact div_pos (Real.Gamma_pos_of_pos (by linarith))
    (Real.Gamma_pos_of_pos (by linarith))

/- Gamma log-convexity at two adjacent half-integers. -/
theorem gamma_midpoint_sq (x : ℝ) (hx : 0 < x) :
    Real.Gamma (x+1)^2 ≤ Real.Gamma (x+1/2) * Real.Gamma (x+3/2) := by
  have hs : 0 < x+1/2 := by linarith
  have ht : 0 < x+3/2 := by linarith
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    (s := x+1/2) (t := x+3/2) (a := (1/2 : ℝ)) (b := (1/2 : ℝ))
    hs ht (by norm_num) (by norm_num) (by norm_num)
  rw [show (1/2 : ℝ)*(x+1/2)+1/2*(x+3/2) = x+1 by ring,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have hp : 0 ≤ Real.Gamma (x+1) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hh : Real.Gamma (x+1)^2 ≤
      (Real.sqrt (Real.Gamma (x+1/2)) * Real.sqrt (Real.Gamma (x+3/2)))^2 := by
    gcongr
  rw [mul_pow, Real.sq_sqrt (Real.Gamma_pos_of_pos hs).le,
    Real.sq_sqrt (Real.Gamma_pos_of_pos ht).le] at hh
  exact hh

theorem gammaRatio_lower (n : ℝ) (hn : 0 ≤ n) :
    (n+1)^2 / (2*(n+2)) ≤ gammaRatio n ^ 2 := by
  let x : ℝ := (n+1)/2
  have hx : 0 < x := by dsimp [x]; linarith
  have hx' : 0 < x+1/2 := by linarith
  have hg : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have h := gamma_midpoint_sq x hx
  rw [show x+3/2 = (x+1/2)+1 by ring,
    Real.Gamma_add_one hx'.ne', Real.Gamma_add_one hx.ne'] at h
  have hd : 0 < 2*(n+2) := by linarith
  have hh : (n+1)^2 * Real.Gamma x ^ 2 ≤
      (2*(n+2)) * Real.Gamma (x+1/2)^2 := by
    dsimp [x] at *
    nlinarith only [h]
  unfold gammaRatio
  rw [show (n+2)/2 = x+1/2 by dsimp [x]; ring,
    show (n+1)/2 = x by rfl, div_pow]
  apply (le_div_iff₀ (pow_pos hg 2)).2
  apply (div_mul_le_iff₀ hd).2
  nlinarith only [hh]

theorem gammaRatio_step (n : ℝ) (hn : 0 ≤ n) :
    gammaRatio (n+2) = ((n+2)/(n+1)) * gammaRatio n := by
  have h1 : 0 < (n+1)/2 := by linarith
  have h2 : 0 < (n+2)/2 := by linarith
  have hg := Real.Gamma_pos_of_pos h1
  unfold gammaRatio
  rw [show (n+2+2)/2 = (n+2)/2+1 by ring,
      show (n+2+1)/2 = (n+1)/2+1 by ring,
      Real.Gamma_add_one h2.ne', Real.Gamma_add_one h1.ne']
  field_simp [h1.ne', hg.ne', show n+1 ≠ 0 by linarith]
  <;> ring

/- A finite shift is enough; no asymptotic Gamma estimate is needed. -/
def shiftNum (n : ℝ) : ℝ := ((n+1)*(n+3)*(n+5)*(n+7))^2
def shiftDen (n : ℝ) : ℝ := (n+8)*((n+2)*(n+4)*(n+6))^2

theorem gammaRatio_shift_lower (n : ℝ) (hn : 1 ≤ n) :
    shiftNum n / shiftDen n ≤ 2 * gammaRatio n ^ 2 := by
  have h0 : 0 ≤ n := by linarith
  have h1 : 0 ≤ n+2 := by linarith
  have h2 : 0 ≤ n+4 := by linarith
  have h3 : 0 ≤ n+6 := by linarith
  have he : gammaRatio (n+6) =
      ((n+6)/(n+5))*((n+4)/(n+3))*((n+2)/(n+1))*gammaRatio n := by
    have e4 := gammaRatio_step (n+4) h2
    rw [show n+4+2 = n+6 by ring, show n+4+1 = n+5 by ring] at e4
    have e2 := gammaRatio_step (n+2) h1
    rw [show n+2+2 = n+4 by ring, show n+2+1 = n+3 by ring] at e2
    rw [e4, e2, gammaRatio_step n h0]
    ring
  have hl := gammaRatio_lower (n+6) h3
  rw [he] at hl
  have hp : 0 < ((n+6)/(n+5))*((n+4)/(n+3))*((n+2)/(n+1)) := by positivity
  have heq : shiftNum n / shiftDen n =
      2 * ((n+6+1)^2 / (2*(n+6+2))) /
        (((n+6)/(n+5))*((n+4)/(n+3))*((n+2)/(n+1)))^2 := by
    unfold shiftNum shiftDen
    field_simp [show n+1 ≠ 0 by linarith, show n+2 ≠ 0 by linarith,
      show n+3 ≠ 0 by linarith, show n+4 ≠ 0 by linarith,
      show n+5 ≠ 0 by linarith, show n+6 ≠ 0 by linarith,
      show n+8 ≠ 0 by linarith, hp.ne']
    <;> ring
  rw [heq]
  apply (div_le_iff₀ (pow_pos hp 2)).2
  rw [mul_pow] at hl
  nlinarith only [hl]

set_option maxHeartbeats 4000000 in
theorem shifted_poly_gap (n : ℝ) (hn : 1 ≤ n) :
    momentPoly n * shiftDen n ^ 4 < 108 * shiftNum n ^ 4 := by
  let x : ℝ := n-1
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have he : 108 * shiftNum n ^ 4 - momentPoly n * shiftDen n ^ 4 =
    38*x^32 + 5940*x^31 + 446850*x^30 + 21544740*x^29 +
    748060722*x^28 + 19925053956*x^27 + 423485879394*x^26 +
    7376060745684*x^25 + 107298661697946*x^24 + 1321944040877796*x^23 +
    13939121972500362*x^22 + 126797624772593364*x^21 +
    1001022674234300826*x^20 + 6889086949304768436*x^19 +
    41460008535029771082*x^18 + 218636787374014669956*x^17 +
    1011290504081527437894*x^16 + 4102980566948319381084*x^15 +
    14587739243423820885382*x^14 + 45362953319451427171116*x^13 +
    123006227929380041617494*x^12 + 289612505870838933208524*x^11 +
    588695607836589748480614*x^10 + 1025387160392392988094396*x^9 +
    1515490607621005698010590*x^8 + 1876313814294250299314700*x^7 +
    1913006553974704584137070*x^6 + 1569101399583245302427100*x^5 +
    1001722257930360707382366*x^4 + 473673165383798386109820*x^3 +
    152998700982392717658990*x^2 + 28986479375862271473900*x +
    2203477203979083439368 := by
    dsimp [x, shiftNum, shiftDen, momentPoly]
    ring
  have hp : 0 < 108 * shiftNum n ^ 4 - momentPoly n * shiftDen n ^ 4 := by
    rw [he]
    positivity
  linarith

theorem gamma_moment_gap (n : ℝ) (hn : 1 ≤ n) :
    momentPoly n < 1728 * gammaRatio n ^ 8 := by
  have h0 : 0 ≤ n := by linarith
  have hd : 0 < shiftDen n := by unfold shiftDen; positivity
  have hnum : 0 ≤ shiftNum n := by unfold shiftNum; positivity
  have h := shifted_poly_gap n hn
  have hl : momentPoly n < 108*(shiftNum n/shiftDen n)^4 := by
    rw [div_pow, ← mul_div_assoc]
    exact (lt_div_iff₀ (pow_pos hd 4)).2 h
  have hp : 0 ≤ shiftNum n / shiftDen n := div_nonneg hnum hd.le
  have hshift := gammaRatio_shift_lower n hn
  have hh : (shiftNum n / shiftDen n)^4 ≤ (2*gammaRatio n ^ 2)^4 := by
    gcongr
  calc
    momentPoly n < 108*(shiftNum n/shiftDen n)^4 := hl
    _ ≤ 108*(2*gammaRatio n^2)^4 := by gcongr
    _ = 1728*gammaRatio n^8 := by ring

theorem fock_comparison_gamma (n A : ℝ) (hn : 1 ≤ n)
    (hA : A^8 ≤ Real.pi^4 * momentPoly n / 1728) :
    A < Real.sqrt Real.pi * gammaRatio n := by
  have hB : 0 ≤ Real.sqrt Real.pi * gammaRatio n :=
    mul_nonneg (Real.sqrt_nonneg _) (gammaRatio_pos n (by linarith)).le
  have hp : 0 < Real.pi^4 := pow_pos Real.pi_pos 4
  have h := mul_lt_mul_of_pos_left (gamma_moment_gap n hn) hp
  have he : (Real.sqrt Real.pi * gammaRatio n)^8 = Real.pi^4 * gammaRatio n^8 := by
    rw [mul_pow]
    have hs : (Real.sqrt Real.pi)^8 = Real.pi^4 := by
      calc
        (Real.sqrt Real.pi)^8 = ((Real.sqrt Real.pi)^2)^4 := by ring
        _ = Real.pi^4 := by rw [Real.sq_sqrt Real.pi_pos.le]
    rw [hs]
  have hab : A^8 < (Real.sqrt Real.pi * gammaRatio n)^8 := by
    rw [he]
    linarith only [hA, h]
  by_contra! hcontra
  have hpow : (Real.sqrt Real.pi * gammaRatio n)^8 ≤ A^8 := by gcongr
  exact (not_lt_of_ge hpow) hab

#print axioms gamma_midpoint_sq
#print axioms gammaRatio_lower
#print axioms gammaRatio_step
#print axioms gammaRatio_shift_lower
#print axioms shifted_poly_gap
#print axioms gamma_moment_gap
#print axioms fock_comparison_gamma

end F19
