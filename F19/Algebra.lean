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
  calc
    (n+1)^2 / (2*(n+2)) * Real.Gamma x ^ 2 =
        ((n+1)^2 * Real.Gamma x ^ 2) / (2*(n+2)) := by ring
    _ ≤ Real.Gamma (x+1/2)^2 := (div_le_iff₀ hd).2 (by nlinarith only [hh])

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


namespace F19

open MeasureTheory Set

theorem husimi_gamma_integral (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ ((n : ℝ)/2)) =
      Real.Gamma ((n : ℝ)/2+1) := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  rw [Real.Gamma_eq_integral (show 0 < (n : ℝ)/2+1 by linarith)]
  simp only [add_sub_cancel_right]

theorem gammaRatio_factorial (n : ℕ) :
    (2 : ℝ)^n * Real.Gamma ((n : ℝ)/2+1)^2 / (n.factorial : ℝ) =
      Real.sqrt Real.pi * gammaRatio (n : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hs : 0 < ((n : ℝ)+1)/2 := by linarith
  have h := Real.Gamma_mul_Gamma_add_half_of_pos hs
  rw [show ((n : ℝ)+1)/2+1/2 = (n : ℝ)/2+1 by ring,
    show 2*(((n : ℝ)+1)/2) = (n : ℝ)+1 by ring] at h
  rw [show 1-((n : ℝ)+1) = -(n : ℝ) by ring,
    Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)),
    Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  have hg : Real.Gamma (((n : ℝ)+1)/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos hs).ne'
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have ht : (2 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold gammaRatio
  rw [show ((n : ℝ)+2)/2 = (n : ℝ)/2+1 by ring]
  field_simp [hg, hf]
  field_simp [ht] at h
  simp only [show ((n : ℝ)+2)/2 = (n : ℝ)/2+1 by ring] at h ⊢
  linear_combination Real.Gamma ((n : ℝ)/2+1) * h

theorem fock_comparison_factorial (n : ℕ) (A : ℝ) (hn : 1 ≤ n)
    (hA : A^8 ≤ Real.pi^4 * momentPoly (n : ℝ) / 1728) :
    A < (2 : ℝ)^n * Real.Gamma ((n : ℝ)/2+1)^2 / (n.factorial : ℝ) := by
  rw [gammaRatio_factorial]
  exact fock_comparison_gamma (n : ℝ) A (by exact_mod_cast hn) hA

#print axioms husimi_gamma_integral
#print axioms gammaRatio_factorial
#print axioms fock_comparison_factorial

end F19


namespace F19

open MeasureTheory

theorem integral_cauchy_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ)
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hb : 0 < ∫ x, g x ^ 2 ∂μ) :
    (∫ x, f x * g x ∂μ)^2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  let A := ∫ x, f x ^ 2 ∂μ
  let B := ∫ x, g x ^ 2 ∂μ
  let C := ∫ x, f x * g x ∂μ
  let k := C / B
  have hb' : 0 < B := hb
  have hfg' : Integrable (fun x => (2*k)*(f x*g x)) μ := hfg.const_mul _
  have hgg' : Integrable (fun x => k^2*(g x^2)) μ := hg.const_mul _
  have he : (∫ x, (f x-k*g x)^2 ∂μ) = A-2*k*C+k^2*B := by
    calc
      _ = ∫ x, f x^2 - (2*k)*(f x*g x) + k^2*(g x^2) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ = A-2*k*C+k^2*B := by
        have hsub : Integrable (fun x => f x^2 - (2*k)*(f x*g x)) μ := hf.sub hfg'
        rw [integral_add hsub hgg', integral_sub hf hfg',
          integral_const_mul, integral_const_mul]
  have hnon : 0 ≤ A-2*k*C+k^2*B := by
    rw [← he]
    exact integral_nonneg (fun x => sq_nonneg (f x-k*g x))
  have hk : k*B = C := by
    dsimp [k]
    exact div_mul_cancel₀ _ hb'.ne'
  have hh := mul_nonneg hnon hb'.le
  have heq : (A-2*k*C+k^2*B)*B = A*B-C^2 := by
    rw [← hk]
    ring
  rw [heq] at hh
  change C^2 ≤ A*B
  linarith

theorem optimized_moment_bound (n A a : ℝ) (ha : 0 < a)
    (hscale : a^4 = 6*momentPoly n/32)
    (hCS : A^2 ≤ (1/2+momentPoly n/(32*a^4))*(Real.pi*a/(2*Real.sqrt 2))) :
    A^8 ≤ Real.pi^4 * momentPoly n / 1728 := by
  have ha4 : 0 < a^4 := pow_pos ha 4
  have hfrac : momentPoly n / (32*a^4) = 1/6 := by
    apply (div_eq_iff (by positivity : (32*a^4 : ℝ) ≠ 0)).2
    linarith only [hscale]
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hA : A^2 ≤ Real.pi*a/(3*Real.sqrt 2) := by
    rw [hfrac] at hCS
    calc
      A^2 ≤ (1/2+1/6)*(Real.pi*a/(2*Real.sqrt 2)) := hCS
      _ = Real.pi*a/(3*Real.sqrt 2) := by
        field_simp [hs.ne']
        <;> ring
  have hp : (A^2)^4 ≤ (Real.pi*a/(3*Real.sqrt 2))^4 := by
    have hnon : 0 ≤ A^2 := sq_nonneg _
    gcongr
  have hs4 : (Real.sqrt (2 : ℝ))^4 = 4 := by
    calc
      _ = ((Real.sqrt (2 : ℝ))^2)^2 := by ring
      _ = 4 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have he : (Real.pi*a/(3*Real.sqrt 2))^4 =
      Real.pi^4 * momentPoly n / 1728 := by
    rw [div_pow, mul_pow, mul_pow, hs4, hscale]
    ring
  rw [he] at hp
  calc
    A^8 = (A^2)^4 := by ring
    _ ≤ Real.pi^4 * momentPoly n / 1728 := hp

#print axioms integral_cauchy_sq
#print axioms optimized_moment_bound

end F19


namespace F19

open MeasureTheory Set

theorem weighted_cauchy_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f w : α → ℝ) (hw : ∀ x, 0 < w x)
    (hf : Integrable (fun x => |f x|) μ)
    (hfw : Integrable (fun x => f x ^ 2 * w x) μ)
    (hi : Integrable (fun x => (w x)⁻¹) μ)
    (hb : 0 < ∫ x, (w x)⁻¹ ∂μ) :
    (∫ x, |f x| ∂μ)^2 ≤
      (∫ x, f x ^ 2 * w x ∂μ) * (∫ x, (w x)⁻¹ ∂μ) := by
  let F : α → ℝ := fun x => |f x| * Real.sqrt (w x)
  let G : α → ℝ := fun x => (Real.sqrt (w x))⁻¹
  have eF : (fun x => F x ^ 2) = (fun x => f x ^ 2 * w x) := by
    funext x
    dsimp [F]
    rw [mul_pow, sq_abs, Real.sq_sqrt (hw x).le]
  have eG : (fun x => G x ^ 2) = (fun x => (w x)⁻¹) := by
    funext x
    dsimp [G]
    rw [inv_pow, Real.sq_sqrt (hw x).le]
  have eFG : (fun x => F x * G x) = (fun x => |f x|) := by
    funext x
    dsimp [F,G]
    rw [mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 (hw x)).ne', mul_one]
  have hF : Integrable (fun x => F x ^ 2) μ := by rw [eF]; exact hfw
  have hG : Integrable (fun x => G x ^ 2) μ := by rw [eG]; exact hi
  have hFG : Integrable (fun x => F x * G x) μ := by rw [eFG]; exact hf
  have hB : 0 < ∫ x, G x ^ 2 ∂μ := by rw [eG]; exact hb
  have h := integral_cauchy_sq μ F G hF hG hFG hB
  rw [eFG, eF, eG] at h
  exact h

noncomputable def quarticWeight (a t : ℝ) : ℝ := 1 + (t/a)^4

theorem quarticWeight_pos (a t : ℝ) : 0 < quarticWeight a t := by
  unfold quarticWeight
  positivity

theorem radial_moment_comparison (n : ℕ) (f : ℝ → ℝ) (a : ℝ)
    (hn : 1 ≤ n) (ha : 0 < a)
    (hscale : a^4 = 6*momentPoly (n : ℝ)/32)
    (hf : IntegrableOn (fun t => |f t|) (Ioi (0 : ℝ)))
    (h2 : IntegrableOn (fun t => f t ^ 2) (Ioi (0 : ℝ)))
    (h4 : IntegrableOn (fun t => t^4 * f t ^ 2) (Ioi (0 : ℝ)))
    (hi : IntegrableOn (fun t => (quarticWeight a t)⁻¹) (Ioi (0 : ℝ)))
    (hm2 : (∫ t in Ioi (0 : ℝ), f t ^ 2) = 1/2)
    (hm4 : (∫ t in Ioi (0 : ℝ), t^4 * f t ^ 2) = momentPoly (n : ℝ)/32)
    (hwi : (∫ t in Ioi (0 : ℝ), (quarticWeight a t)⁻¹) =
      Real.pi*a/(2*Real.sqrt 2)) :
    (∫ t in Ioi (0 : ℝ), |f t|) <
      (2 : ℝ)^n * Real.Gamma ((n : ℝ)/2+1)^2 / (n.factorial : ℝ) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have eqw : (fun t => f t ^ 2 * quarticWeight a t) =
      (fun t => f t ^ 2 + (a^4)⁻¹ * (t^4 * f t ^ 2)) := by
    funext t
    unfold quarticWeight
    rw [div_pow, div_eq_mul_inv]
    ring
  have h2' : Integrable (fun t => f t ^ 2) μ := h2
  have h4' : Integrable (fun t => (a^4)⁻¹ * (t^4 * f t ^ 2)) μ :=
    h4.const_mul _
  have hw : Integrable (fun t => f t ^ 2 * quarticWeight a t) μ := by
    rw [eqw]
    exact h2'.add h4'
  have hB : 0 < ∫ t, (quarticWeight a t)⁻¹ ∂μ := by
    change 0 < ∫ t in Ioi (0 : ℝ), (quarticWeight a t)⁻¹
    rw [hwi]
    positivity
  have hW : (∫ t, f t ^ 2 * quarticWeight a t ∂μ) =
      1/2+momentPoly (n : ℝ)/(32*a^4) := by
    rw [eqw, integral_add h2' h4', integral_const_mul]
    change (∫ t in Ioi (0 : ℝ), f t ^ 2) +
      (a^4)⁻¹ * (∫ t in Ioi (0 : ℝ), t^4 * f t ^ 2) = _
    rw [hm2, hm4]
    ring
  have h := weighted_cauchy_sq μ f (quarticWeight a) (quarticWeight_pos a) hf hw hi hB
  rw [hW] at h
  change (∫ t in Ioi (0 : ℝ), |f t|)^2 ≤
    (1/2+momentPoly (n : ℝ)/(32*a^4)) *
      (∫ t in Ioi (0 : ℝ), (quarticWeight a t)⁻¹) at h
  rw [hwi] at h
  exact fock_comparison_factorial n _ hn
    (optimized_moment_bound (n : ℝ) _ a ha hscale h)

#print axioms weighted_cauchy_sq
#print axioms radial_moment_comparison

end F19


namespace F19

open MeasureTheory Set Filter
open scoped Topology

noncomputable def quarticPrimitive (x : ℝ) : ℝ :=
  (Real.log ((x+1)^2+1) - Real.log ((x-1)^2+1))/4 +
    (Real.arctan (x+1)+Real.arctan (x-1))/2

theorem quarticPrimitive_deriv (x : ℝ) :
    HasDerivAt quarticPrimitive (4/(x^4+4)) x := by
  have hp : 0 < (x+1)^2+1 := by positivity
  have hq : 0 < (x-1)^2+1 := by positivity
  have hd : 0 < x^4+4 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => (y+1)^2+1) (2*(x+1)) x := by
    convert (((hasDerivAt_id x).add_const 1).pow 2).add_const 1 using 1 <;> simp only [id_eq] <;> ring
  have h2 : HasDerivAt (fun y : ℝ => (y-1)^2+1) (2*(x-1)) x := by
    convert (((hasDerivAt_id x).sub_const 1).pow 2).add_const 1 using 1 <;> simp only [id_eq] <;> ring
  have h3 : HasDerivAt (fun y : ℝ => Real.arctan (y+1)) (1/(1+(x+1)^2)) x := by
    simpa using (Real.hasDerivAt_arctan (x+1)).comp x ((hasDerivAt_id x).add_const 1)
  have h4 : HasDerivAt (fun y : ℝ => Real.arctan (y-1)) (1/(1+(x-1)^2)) x := by
    simpa using (Real.hasDerivAt_arctan (x-1)).comp x ((hasDerivAt_id x).sub_const 1)
  unfold quarticPrimitive
  convert (((h1.log hp.ne').sub (h2.log hq.ne')).div_const 4).add
    ((h3.add h4).div_const 2) using 1
  have hp' : 0 < 1+(x+1)^2 := by positivity
  have hq' : 0 < 1+(x-1)^2 := by positivity
  field_simp [hp.ne', hq.ne', hp'.ne', hq'.ne', hd.ne']
  <;> ring

theorem quarticPrimitive_zero : quarticPrimitive 0 = 0 := by
  unfold quarticPrimitive
  norm_num [Real.arctan_neg]

theorem quarticPrimitive_limit :
    Tendsto quarticPrimitive atTop (𝓝 (Real.pi/2)) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hp : Tendsto (fun x : ℝ => (1+x⁻¹)^2+x⁻¹^2) atTop (𝓝 1) := by
    simpa using ((hone.add hi).pow 2).add (hi.pow 2)
  have hq : Tendsto (fun x : ℝ => (1-x⁻¹)^2+x⁻¹^2) atTop (𝓝 1) := by
    simpa using ((hone.sub hi).pow 2).add (hi.pow 2)
  have hratio : Tendsto (fun x : ℝ => ((x+1)^2+1)/((x-1)^2+1)) atTop (𝓝 1) := by
    have h := hp.div hq one_ne_zero
    simp only [div_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hq' : 0 < (1-x⁻¹)^2+x⁻¹^2 := by positivity
    have hq'' : 0 < (x-1)^2+1 := by positivity
    field_simp [hx.ne', hq'.ne', hq''.ne']
    <;> ring
  have hlog : Tendsto (fun x : ℝ => Real.log ((x+1)^2+1) -
      Real.log ((x-1)^2+1)) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto.comp hratio
    simp only [Real.log_one] at h
    refine h.congr' (Filter.Eventually.of_forall fun x => ?_)
    exact Real.log_div (by positivity) (by positivity)
  have hatan : Tendsto Real.arctan atTop (𝓝 (Real.pi/2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have h1 := hatan.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
  have h2 : Tendsto (fun x : ℝ => Real.arctan (x-1)) atTop (𝓝 (Real.pi/2)) := by
    simpa [Function.comp_def, sub_eq_add_neg] using
      hatan.comp (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  have h1' : Tendsto (fun x : ℝ => Real.arctan (x+1)) atTop (𝓝 (Real.pi/2)) := h1
  unfold quarticPrimitive
  convert (hlog.div_const 4).add ((h1'.add h2).div_const 2) using 1 <;> ring

noncomputable def scaledQuarticPrimitive (a t : ℝ) : ℝ :=
  (a/Real.sqrt 2) * quarticPrimitive ((Real.sqrt 2/a)*t)

theorem scaledQuarticPrimitive_deriv (a t : ℝ) (ha : 0 < a) :
    HasDerivAt (scaledQuarticPrimitive a) (quarticWeight a t)⁻¹ t := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs4 : (Real.sqrt (2 : ℝ))^4 = 4 := by
    calc
      _ = ((Real.sqrt (2 : ℝ))^2)^2 := by ring
      _ = 4 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  unfold scaledQuarticPrimitive
  convert ((quarticPrimitive_deriv ((Real.sqrt 2/a)*t)).comp t
    ((hasDerivAt_id t).const_mul (Real.sqrt 2/a))).const_mul (a/Real.sqrt 2) using 1
  have he : ((Real.sqrt 2/a)*t)^4+4 = 4*quarticWeight a t := by
    unfold quarticWeight
    rw [mul_pow, div_pow, hs4, div_pow]
    ring
  rw [he]
  have hw := quarticWeight_pos a t
  field_simp [ha.ne', hs.ne', hw.ne']
  <;> ring

theorem scaledQuarticPrimitive_limit (a : ℝ) (ha : 0 < a) :
    Tendsto (scaledQuarticPrimitive a) atTop (𝓝 (Real.pi*a/(2*Real.sqrt 2))) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hlin : Tendsto (fun t : ℝ => (Real.sqrt 2/a)*t) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (div_pos hs ha)).2 tendsto_id
  unfold scaledQuarticPrimitive
  convert (quarticPrimitive_limit.comp hlin).const_mul (a/Real.sqrt 2) using 1
  ring

theorem quarticWeight_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t => (quarticWeight a t)⁻¹) (Ioi (0 : ℝ)) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => scaledQuarticPrimitive_deriv a t ha)
    (fun t _ => (inv_pos.mpr (quarticWeight_pos a t)).le)
    (scaledQuarticPrimitive_limit a ha)

theorem quarticWeight_integral (a : ℝ) (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), (quarticWeight a t)⁻¹) =
      Real.pi*a/(2*Real.sqrt 2) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ))
    (fun t _ => scaledQuarticPrimitive_deriv a t ha)
    (fun t _ => (inv_pos.mpr (quarticWeight_pos a t)).le)
    (scaledQuarticPrimitive_limit a ha)
  simpa [scaledQuarticPrimitive, quarticPrimitive_zero] using h

#print axioms quarticPrimitive_deriv
#print axioms quarticPrimitive_limit
#print axioms quarticWeight_integrable
#print axioms quarticWeight_integral

end F19


namespace F19

open MeasureTheory Set Polynomial
open scoped BigOperators Polynomial

noncomputable def laguerre (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (-1 : ℝ)^j * (n.choose j : ℝ) / (j.factorial : ℝ) * x^j

theorem signed_binomial_moment (n k : ℕ) :
    (∑ j ∈ Finset.range (n+1), (-1 : ℝ)^j * (n.choose j : ℝ) *
      ((k+j).choose k : ℝ)) = (-1 : ℝ)^n * (k.choose n : ℝ) := by
  have ep : (∑ j ∈ Finset.range (n+1),
      Polynomial.C ((-1 : ℝ)^j * (n.choose j : ℝ)) *
        ((Polynomial.X : ℝ[X])+1)^(k+j)) =
      Polynomial.C ((-1 : ℝ)^n) *
        ((Polynomial.X : ℝ[X])^n * (Polynomial.X+1)^k) := by
    calc
      _ = ((Polynomial.X : ℝ[X])+1)^k *
          (∑ j ∈ Finset.range (n+1),
            (-((Polynomial.X : ℝ[X])+1))^j * (1 : ℝ[X])^(n-j) *
              (n.choose j : ℝ[X])) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [show -((Polynomial.X : ℝ[X])+1) =
            Polynomial.C (-1 : ℝ)*(Polynomial.X+1) by simp]
        rw [mul_pow, pow_add, one_pow, mul_one, map_mul, map_pow]
        simp only [map_neg, map_one, map_natCast]
        ring
      _ = ((Polynomial.X : ℝ[X])+1)^k * (-((Polynomial.X : ℝ[X])+1)+1)^n := by
        rw [add_pow (-((Polynomial.X : ℝ[X])+1)) 1 n]
      _ = _ := by
        rw [show -((Polynomial.X : ℝ[X])+1)+1 = -Polynomial.X by ring,
          show -(Polynomial.X : ℝ[X]) = Polynomial.C (-1 : ℝ)*Polynomial.X by simp,
          mul_pow, map_pow]
        ring
  have hc := congrArg (fun p : ℝ[X] => p.coeff k) ep
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_one_pow, Polynomial.coeff_X_pow_mul'] at hc
  rw [hc]
  by_cases h : n ≤ k
  · simp [h, Nat.choose_symm h]
  · simp [h, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]

theorem exp_monomial_integrable (k : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x)*x^k) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (k : ℝ)) (b := (1 : ℝ)) (by
      have hk : 0 ≤ (k : ℝ) := by positivity
      linarith) (by norm_num) one_pos
  simpa [Real.rpow_natCast, Real.rpow_one, mul_comm] using h

theorem exp_monomial_integral (k : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x)*x^k) = (k.factorial : ℝ) := by
  have h := Real.Gamma_eq_integral (show 0 < (k : ℝ)+1 by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  simpa [Real.rpow_natCast] using h.symm

theorem laguerre_monomial_integrable (n k : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x)*x^k*laguerre n x) (Ioi (0 : ℝ)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have he : (fun x : ℝ => Real.exp (-x)*x^k*laguerre n x) =
      (fun x => ∑ j ∈ Finset.range (n+1),
        ((-1 : ℝ)^j*(n.choose j : ℝ)/(j.factorial : ℝ)) *
          (Real.exp (-x)*x^(k+j))) := by
    funext x
    unfold laguerre
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add]
    ring
  rw [he]
  change Integrable _ μ
  exact integrable_finset_sum _ (fun j _ => (exp_monomial_integrable (k+j)).const_mul _)

theorem laguerre_monomial_integral (n k : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x)*x^k*laguerre n x) =
      (-1 : ℝ)^n * (k.factorial : ℝ) * (k.choose n : ℝ) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have he : (fun x : ℝ => Real.exp (-x)*x^k*laguerre n x) =
      (fun x => ∑ j ∈ Finset.range (n+1),
        ((-1 : ℝ)^j*(n.choose j : ℝ)/(j.factorial : ℝ)) *
          (Real.exp (-x)*x^(k+j))) := by
    funext x
    unfold laguerre
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add]
    ring
  change (∫ x, Real.exp (-x)*x^k*laguerre n x ∂μ) = _
  rw [he, integral_finset_sum]
  · simp_rw [integral_const_mul]
    change (∑ j ∈ Finset.range (n+1),
      (-1 : ℝ)^j*(n.choose j : ℝ)/(j.factorial : ℝ) *
        (∫ x in Ioi (0 : ℝ), Real.exp (-x)*x^(k+j))) = _
    simp_rw [exp_monomial_integral]
    calc
      _ = (k.factorial : ℝ) * (∑ j ∈ Finset.range (n+1),
          (-1 : ℝ)^j * (n.choose j : ℝ) * ((k+j).choose k : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Nat.cast_add_choose ℝ]
        have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
        have hg : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
        field_simp [hf,hg]
        <;> ring
      _ = _ := by rw [signed_binomial_moment]; ring
  · intro j hj
    exact (exp_monomial_integrable (k+j)).const_mul _

#print axioms signed_binomial_moment
#print axioms exp_monomial_integrable
#print axioms exp_monomial_integral
#print axioms laguerre_monomial_integrable
#print axioms laguerre_monomial_integral

end F19


namespace F19

open MeasureTheory Set
open scoped BigOperators

theorem laguerre_product_integrable (n m k : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x)*x^k*laguerre n x*laguerre m x)
      (Ioi (0 : ℝ)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have he : (fun x : ℝ => Real.exp (-x)*x^k*laguerre n x*laguerre m x) =
      (fun x => ∑ j ∈ Finset.range (m+1),
        ((-1 : ℝ)^j*(m.choose j : ℝ)/(j.factorial : ℝ)) *
          (Real.exp (-x)*x^(k+j)*laguerre n x)) := by
    funext x
    change _ * (∑ j ∈ Finset.range (m+1), (-1 : ℝ)^j * (m.choose j : ℝ) / (j.factorial : ℝ) * x^j) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add]
    ring
  rw [he]
  change Integrable _ μ
  exact integrable_finset_sum _ (fun j _ => (laguerre_monomial_integrable n (k+j)).const_mul _)

theorem laguerre_product_integral (n m k : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x)*x^k*laguerre n x*laguerre m x) =
      ∑ j ∈ Finset.range (m+1),
        ((-1 : ℝ)^j*(m.choose j : ℝ)/(j.factorial : ℝ)) *
          ((-1 : ℝ)^n*((k+j).factorial : ℝ)*((k+j).choose n : ℝ)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have he : (fun x : ℝ => Real.exp (-x)*x^k*laguerre n x*laguerre m x) =
      (fun x => ∑ j ∈ Finset.range (m+1),
        ((-1 : ℝ)^j*(m.choose j : ℝ)/(j.factorial : ℝ)) *
          (Real.exp (-x)*x^(k+j)*laguerre n x)) := by
    funext x
    change _ * (∑ j ∈ Finset.range (m+1), (-1 : ℝ)^j * (m.choose j : ℝ) / (j.factorial : ℝ) * x^j) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add]
    ring
  change (∫ x, Real.exp (-x)*x^k*laguerre n x*laguerre m x ∂μ) = _
  rw [he, integral_finset_sum]
  · simp_rw [integral_const_mul]
    change (∑ j ∈ Finset.range (m+1),
      ((-1 : ℝ)^j*(m.choose j : ℝ)/(j.factorial : ℝ)) *
        (∫ x in Ioi (0 : ℝ), Real.exp (-x)*x^(k+j)*laguerre n x)) = _
    simp_rw [laguerre_monomial_integral]
  · intro j hj
    exact (laguerre_monomial_integrable n (k+j)).const_mul _

theorem laguerre_norm_integral (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x)*laguerre n x*laguerre n x) = 1 := by
  have h := laguerre_product_integral n n 0
  simp only [pow_zero, mul_one, zero_add] at h
  rw [h, Finset.sum_eq_single n]
  · simp only [Nat.choose_self, Nat.cast_one, mul_one]
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hpow : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      (-1 : ℝ)^n / (n.factorial : ℝ) * ((-1 : ℝ)^n * (n.factorial : ℝ)) =
          (-1 : ℝ)^n * (-1 : ℝ)^n := by
        field_simp [hf]
        <;> ring
      _ = 1 := hpow
  · intro j hj hjn
    have hj' : j < n := by have := Finset.mem_range.mp hj; omega
    simp [Nat.choose_eq_zero_of_lt hj']
  · simp

theorem laguerre_orthogonal_of_lt (n m : ℕ) (hm : m < n) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x)*laguerre n x*laguerre m x) = 0 := by
  have h := laguerre_product_integral n m 0
  simp only [pow_zero, mul_one, zero_add] at h
  rw [h]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j < n := by have := Finset.mem_range.mp hj; omega
  simp [Nat.choose_eq_zero_of_lt hj']

theorem laguerre_orthogonality (n m : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x)*laguerre n x*laguerre m x) =
      if n = m then 1 else 0 := by
  by_cases h : n = m
  · subst m
    simp [laguerre_norm_integral]
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have he : (fun x : ℝ => Real.exp (-x)*laguerre n x*laguerre m x) =
          (fun x => Real.exp (-x)*laguerre m x*laguerre n x) := by
        funext x
        ring
      rw [he]
      exact laguerre_orthogonal_of_lt m n hlt
    · exact laguerre_orthogonal_of_lt n m hgt

#print axioms laguerre_product_integrable
#print axioms laguerre_product_integral
#print axioms laguerre_norm_integral
#print axioms laguerre_orthogonality

end F19


namespace F19

open MeasureTheory Set
open scoped BigOperators

noncomputable def risingFour (x : ℝ) : ℝ := (x+1)*(x+2)*(x+3)*(x+4)

theorem factorial_add_four (j : ℕ) :
    ((j+4).factorial : ℝ) = (j.factorial : ℝ)*risingFour (j : ℝ) := by
  unfold risingFour
  norm_num [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  <;> ring

theorem fourth_moment_term (m i : ℕ) (hi : i < 5) :
    ((-1 : ℝ)^(m+i)*((m+4).choose (m+i) : ℝ)/((m+i).factorial : ℝ)) *
      ((-1 : ℝ)^(m+4)*((4+(m+i)).factorial : ℝ)*((4+(m+i)).choose (m+4) : ℝ)) =
    (-1 : ℝ)^i * (risingFour ((m+i : ℕ) : ℝ))^2 /
      (((4-i).factorial : ℝ)*(i.factorial : ℝ)) := by
  have hi' : i ≤ 4 := by omega
  have h1 : m+i ≤ m+4 := by omega
  have h2 : m+4 ≤ m+i+4 := by omega
  rw [show 4+(m+i) = m+i+4 by omega]
  rw [← Nat.choose_symm h1, show m+4-(m+i) = 4-i by omega,
    ← Nat.choose_symm h2, show m+i+4-(m+4) = i by omega]
  rw [Nat.cast_choose ℝ (show 4-i ≤ m+4 by omega),
    Nat.cast_choose ℝ (show i ≤ m+i+4 by omega),
    show m+4-(4-i)=m+i by omega, show m+i+4-i=m+4 by omega,
    factorial_add_four (m+i)]
  have hsign : (-1 : ℝ)^(m+i)*(-1 : ℝ)^(m+4) = (-1 : ℝ)^i := by
    rw [pow_add, pow_add]
    norm_num
    have hm : (-1 : ℝ)^m * (-1 : ℝ)^m = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = ((-1 : ℝ)^m*(-1 : ℝ)^m)*(-1 : ℝ)^i := by ring
      _ = _ := by rw [hm, one_mul]
  have hf (j : ℕ) : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  calc
    _ = ((-1 : ℝ)^(m+i)*(-1 : ℝ)^(m+4)) *
        (risingFour ((m+i : ℕ) : ℝ))^2 /
        (((4-i).factorial : ℝ)*(i.factorial : ℝ)) := by
      field_simp [hf]
      <;> ring
    _ = _ := by rw [hsign]

set_option maxHeartbeats 4000000 in
theorem laguerre_fourth_moment (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x)*x^4*laguerre n x*laguerre n x) =
      momentPoly (n : ℝ) := by
  rw [laguerre_product_integral]
  by_cases hn : n < 4
  · interval_cases n <;> norm_num [momentPoly, Finset.sum_range_succ, Nat.choose, Nat.factorial]
  · let m := n-4
    have hnm : n = m+4 := by dsimp [m]; omega
    rw [hnm]
    change (∑ j ∈ Finset.range (m+5),
      ((-1 : ℝ)^j*((m+4).choose j : ℝ)/(j.factorial : ℝ)) *
        ((-1 : ℝ)^(m+4)*((4+j).factorial : ℝ)*((4+j).choose (m+4) : ℝ))) =
      momentPoly ((m+4 : ℕ) : ℝ)
    rw [Finset.sum_range_add]
    have hz : (∑ j ∈ Finset.range m,
      ((-1 : ℝ)^j*((m+4).choose j : ℝ)/(j.factorial : ℝ)) *
        ((-1 : ℝ)^(m+4)*((4+j).factorial : ℝ)*((4+j).choose (m+4) : ℝ))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' : 4+j < m+4 := by have := Finset.mem_range.mp hj; omega
      simp [Nat.choose_eq_zero_of_lt hj']
    rw [hz, zero_add]
    calc
      _ = ∑ i ∈ Finset.range 5, (-1 : ℝ)^i * (risingFour ((m+i : ℕ) : ℝ))^2 /
          (((4-i).factorial : ℝ)*(i.factorial : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact fourth_moment_term m i (Finset.mem_range.mp hi)
      _ = _ := by
        norm_num [Finset.sum_range_succ, risingFour, momentPoly, Nat.factorial, Nat.cast_add]
        <;> ring

#print axioms factorial_add_four
#print axioms fourth_moment_term
#print axioms laguerre_fourth_moment

end F19


namespace F19

open MeasureTheory Set
open scoped BigOperators

noncomputable def radialFock (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t)*laguerre n (2*t)

theorem radialFock_integrable (n : ℕ) :
    IntegrableOn (radialFock n) (Ioi (0 : ℝ)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have he : radialFock n = (fun t => ∑ j ∈ Finset.range (n+1),
    ((-1 : ℝ)^j*(n.choose j : ℝ)/(j.factorial : ℝ)*(2 : ℝ)^j) *
      (Real.exp (-t)*t^j)) := by
    funext t
    unfold radialFock laguerre
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_pow]
    ring
  rw [he]
  change Integrable _ μ
  exact integrable_finset_sum _ (fun j _ => (exp_monomial_integrable j).const_mul _)

theorem radialFock_sq (n : ℕ) (t : ℝ) :
    radialFock n t ^ 2 =
      Real.exp (-(2*t))*laguerre n (2*t)*laguerre n (2*t) := by
  unfold radialFock
  rw [mul_pow, pow_two (Real.exp (-t)), ← Real.exp_add]
  rw [show -t + -t = -(2*t) by ring]
  ring

theorem radialFock_norm (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), radialFock n t ^ 2) = 1/2 := by
  simp_rw [radialFock_sq]
  have h := integral_comp_mul_left_Ioi
    (fun x : ℝ => Real.exp (-x)*laguerre n x*laguerre n x)
    (0 : ℝ) (by norm_num : 0 < (2 : ℝ))
  simp only [mul_zero, smul_eq_mul, laguerre_norm_integral] at h
  simpa using h

theorem radialFock_fourth (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^4*radialFock n t ^ 2) =
      momentPoly (n : ℝ)/32 := by
  have he : (fun t => t^4*radialFock n t ^ 2) =
      (fun t => (1/16 : ℝ)*(Real.exp (-(2*t))*(2*t)^4*
        laguerre n (2*t)*laguerre n (2*t))) := by
    funext t
    rw [radialFock_sq]
    ring
  rw [he, integral_const_mul]
  have h := integral_comp_mul_left_Ioi
    (fun x : ℝ => Real.exp (-x)*x^4*laguerre n x*laguerre n x)
    (0 : ℝ) (by norm_num : 0 < (2 : ℝ))
  simp only [mul_zero, smul_eq_mul, laguerre_fourth_moment] at h
  rw [h]
  ring

theorem momentPoly_pos_nat (n : ℕ) : 0 < momentPoly (n : ℝ) := by
  unfold momentPoly
  positivity

theorem radialFock_strict (n : ℕ) (hn : 1 ≤ n) :
    (∫ t in Ioi (0 : ℝ), |radialFock n t|) <
      (2 : ℝ)^n * Real.Gamma ((n : ℝ)/2+1)^2 / (n.factorial : ℝ) := by
  let c := 6*momentPoly (n : ℝ)/32
  have hc : 0 < c := by dsimp [c]; have := momentPoly_pos_nat n; positivity
  let a := Real.sqrt (Real.sqrt c)
  have ha : 0 < a := Real.sqrt_pos.2 (Real.sqrt_pos.2 hc)
  have hscale : a^4 = c := by
    dsimp [a]
    calc
      _ = ((Real.sqrt (Real.sqrt c))^2)^2 := by ring
      _ = c := by rw [Real.sq_sqrt (Real.sqrt_nonneg c), Real.sq_sqrt hc.le]
  have h2 : IntegrableOn (fun t => radialFock n t^2) (Ioi (0 : ℝ)) := by
    apply Integrable.of_integral_ne_zero
    rw [radialFock_norm]
    norm_num
  have h4 : IntegrableOn (fun t => t^4*radialFock n t^2) (Ioi (0 : ℝ)) := by
    apply Integrable.of_integral_ne_zero
    rw [radialFock_fourth]
    exact (div_pos (momentPoly_pos_nat n) (by norm_num)).ne'
  have hf : IntegrableOn (fun t => |radialFock n t|) (Ioi (0 : ℝ)) := by
    simpa [Real.norm_eq_abs] using (radialFock_integrable n).norm
  exact radial_moment_comparison n (radialFock n) a hn ha hscale
    hf h2 h4 (quarticWeight_integrable a ha) (radialFock_norm n)
    (radialFock_fourth n) (quarticWeight_integral a ha)

theorem radialFock_vacuum :
    (∫ t in Ioi (0 : ℝ), |radialFock 0 t|) = 1 := by
  have he : (fun t => |radialFock 0 t|) = (fun t => Real.exp (-t)*t^0) := by
    funext t
    simp [radialFock, laguerre, Finset.sum_range_succ, abs_of_pos (Real.exp_pos _)]
  rw [he, exp_monomial_integral]
  norm_num

theorem radialFock_theorem (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), |radialFock n t|) ≤
      (2 : ℝ)^n * Real.Gamma ((n : ℝ)/2+1)^2 / (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · subst n
    rw [radialFock_vacuum]
    norm_num [Real.Gamma_one]
  · exact (radialFock_strict n (by omega)).le

#print axioms radialFock_norm
#print axioms radialFock_fourth
#print axioms radialFock_strict
#print axioms radialFock_vacuum
#print axioms radialFock_theorem

end F19


namespace F19

open MeasureTheory Set

noncomputable def radialWigner (n : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ)^n * radialFock n t

noncomputable def radialHusimiRoot (n : ℕ) (t : ℝ) : ℝ :=
  ((2 : ℝ)^((n : ℝ)/2)/(Real.sqrt 2*Real.sqrt (n.factorial : ℝ))) *
    (Real.exp (-((1/4 : ℝ)*t))*(((1/4 : ℝ)*t)^((n : ℝ)/2)))

noncomputable def radialHusimi (n : ℕ) (t : ℝ) : ℝ :=
  radialHusimiRoot n t ^ 2

theorem rpow_half_nat_sq (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (x^((n : ℝ)/2))^2 = x^n := by
  rw [← Real.rpow_natCast (x^((n : ℝ)/2)) 2,
    ← Real.rpow_mul hx, show (n : ℝ)/2*(↑(2 : ℕ) : ℝ) = (n : ℝ) by norm_num <;> ring,
    Real.rpow_natCast]

theorem radialHusimi_density_formula (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    radialHusimi n t =
      (1/2 : ℝ)*Real.exp (-t/2)*(t/2)^n/(n.factorial : ℝ) := by
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  unfold radialHusimi radialHusimiRoot
  rw [mul_pow, div_pow, mul_pow, rpow_half_nat_sq 2 (by norm_num),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hfac.le,
    mul_pow, rpow_half_nat_sq _ (by positivity),
    pow_two (Real.exp (-((1/4 : ℝ)*t))), ← Real.exp_add,
    show -((1/4 : ℝ)*t) + -((1/4 : ℝ)*t) = -t/2 by ring]
  have hpow : (2 : ℝ)^n * ((1/4 : ℝ)*t)^n = (t/2)^n := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    _ = Real.exp (-t/2)*((2 : ℝ)^n*((1/4 : ℝ)*t)^n)/(2*(n.factorial : ℝ)) := by
      field_simp [hfac.ne']
      <;> ring
    _ = _ := by rw [hpow]; ring

theorem radialHusimiRoot_nonneg (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ radialHusimiRoot n t := by
  unfold radialHusimiRoot
  positivity

theorem radialHusimiRoot_integral (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), radialHusimiRoot n t) =
      ((2 : ℝ)^((n : ℝ)/2)/(Real.sqrt 2*Real.sqrt (n.factorial : ℝ))) *
        (4*Real.Gamma ((n : ℝ)/2+1)) := by
  unfold radialHusimiRoot
  rw [integral_const_mul]
  have h := integral_comp_mul_left_Ioi
    (fun x : ℝ => Real.exp (-x)*x^((n : ℝ)/2))
    (0 : ℝ) (by norm_num : 0 < (1/4 : ℝ))
  simp only [mul_zero, smul_eq_mul, husimi_gamma_integral] at h
  rw [h]
  norm_num

theorem radialHusimi_rhs (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), Real.sqrt (radialHusimi n t))^2 / 8 =
      (2 : ℝ)^n * Real.Gamma ((n : ℝ)/2+1)^2/(n.factorial : ℝ) := by
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have he : (∫ t in Ioi (0 : ℝ), Real.sqrt (radialHusimi n t)) =
      ∫ t in Ioi (0 : ℝ), radialHusimiRoot n t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change Real.sqrt (radialHusimiRoot n t ^ 2) = radialHusimiRoot n t
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (radialHusimiRoot_nonneg n t ht.le)]
  rw [he, radialHusimiRoot_integral, mul_pow, div_pow, mul_pow,
    rpow_half_nat_sq 2 (by norm_num),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hfac.le]
  ring

theorem radialWigner_abs (n : ℕ) (t : ℝ) :
    |radialWigner n t| = |radialFock n t| := by
  simp [radialWigner, abs_mul, abs_pow]

theorem fock_radial_husimi_inequality (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), |radialWigner n t|) ≤
      (∫ t in Ioi (0 : ℝ), Real.sqrt (radialHusimi n t))^2 / 8 := by
  simp_rw [radialWigner_abs]
  rw [radialHusimi_rhs]
  exact radialFock_theorem n

#print axioms radialHusimi_density_formula
#print axioms radialHusimiRoot_integral
#print axioms radialHusimi_rhs
#print axioms fock_radial_husimi_inequality

end F19


namespace F19

open MeasureTheory
open scoped ENNReal

-- Cauchy–Schwarz for arbitrary countable sums, including infinite values.
theorem enn_countable_cauchy (a b : ℕ → ℝ≥0∞) :
    (∑' i, a i * b i) ≤
      (∑' i, a i ^ 2) ^ (1/2 : ℝ) * (∑' i, b i ^ 2) ^ (1/2 : ℝ) := by
  have hpq : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.mpr (by norm_num)
  have ha : AEMeasurable a Measure.count := (measurable_of_countable a).aemeasurable
  have hb : AEMeasurable b Measure.count := (measurable_of_countable b).aemeasurable
  have h := lintegral_mul_le_Lp_mul_Lq Measure.count hpq ha hb
  simpa only [Pi.mul_apply, ENNReal.rpow_two, lintegral_count] using h

theorem enn_half_sq (x : ℝ≥0∞) : (x ^ (1/2 : ℝ))^2 = x := by
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num [ENNReal.rpow_one]

noncomputable def mixtureRoot {α : Type*} (p : ℕ → ℝ≥0∞)
    (f : ℕ → α → ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  (∑' i, p i * f i x ^ 2) ^ (1/2 : ℝ)

theorem mixtureRoot_pair_bound {α : Type*} (p : ℕ → ℝ≥0∞)
    (f : ℕ → α → ℝ≥0∞) (x y : α) :
    (∑' i, p i * (f i x * f i y)) ≤ mixtureRoot p f x * mixtureRoot p f y := by
  have h := enn_countable_cauchy
    (fun i => (p i)^(1/2 : ℝ) * f i x)
    (fun i => (p i)^(1/2 : ℝ) * f i y)
  simp only [mul_pow, enn_half_sq] at h
  unfold mixtureRoot
  refine le_trans (le_of_eq ?_) h
  apply tsum_congr
  intro i
  calc
    p i * (f i x * f i y) = ((p i)^(1/2 : ℝ))^2 * (f i x * f i y) := by rw [enn_half_sq]
    _ = _ := by rw [pow_two]; ac_rfl

-- A Tonelli proof of concavity of the squared root integral for countable
-- nonnegative mixtures; no finite-entropy hypothesis is necessary.
theorem countable_mixture_root_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℕ → ℝ≥0∞) (f : ℕ → α → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑' i, p i * (∫⁻ x, f i x ∂μ)^2) ≤
      (∫⁻ x, mixtureRoot p f x ∂μ)^2 := by
  have hm : Measurable (mixtureRoot p f) := by
    unfold mixtureRoot
    exact (Measurable.ennreal_tsum (fun i => (hf i).pow_const 2 |>.const_mul (p i))).pow_const (1/2 : ℝ)
  have he : (∫⁻ x, ∫⁻ y, ∑' i, p i * (f i x * f i y) ∂μ ∂μ) =
      ∑' i, p i * (∫⁻ x, f i x ∂μ)^2 := by
    have hx (x : α) : (∫⁻ y, ∑' i, p i * (f i x * f i y) ∂μ) =
        ∑' i, (p i * f i x) * (∫⁻ y, f i y ∂μ) := by
      rw [lintegral_tsum (fun i => ((measurable_const.mul (measurable_const.mul (hf i)))).aemeasurable)]
      apply tsum_congr
      intro i
      simp_rw [← mul_assoc]
      rw [lintegral_const_mul _ (hf i)]
    simp_rw [hx]
    rw [lintegral_tsum (fun i => ((measurable_const.mul (hf i)).mul_const _).aemeasurable)]
    apply tsum_congr
    intro i
    rw [lintegral_mul_const _ (measurable_const.mul (hf i)), lintegral_const_mul _ (hf i), pow_two]
    ac_rfl
  rw [← he, pow_two, ← lintegral_lintegral_mul hm.aemeasurable hm.aemeasurable]
  exact lintegral_mono (fun x => lintegral_mono (fun y => mixtureRoot_pair_bound p f x y))

#print axioms enn_countable_cauchy
#print axioms mixtureRoot_pair_bound
#print axioms countable_mixture_root_bound

end F19


namespace F19

open MeasureTheory Set
open scoped ENNReal

theorem enn_abs_tsum_le (a : ℕ → ℝ) :
    ENNReal.ofReal |∑' i, a i| ≤ ∑' i, ENNReal.ofReal |a i| := by
  by_cases h : (∑' i, ENNReal.ofReal |a i|) = ⊤
  · rw [h]; exact le_top
  · have hc : (∑' i, ((Real.toNNReal |a i| : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := h
    have hs := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hc
    have ha : Summable (fun i => |a i|) := by
      simpa only [Real.coe_toNNReal _ (abs_nonneg _)] using hs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg (a i)) ha]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := a) (by simpa only [Real.norm_eq_abs] using ha))

theorem radialRoot_integrable (n : ℕ) :
    IntegrableOn (radialHusimiRoot n) (Ioi (0 : ℝ)) := by
  apply Integrable.of_integral_ne_zero
  rw [radialHusimiRoot_integral]
  have h := Real.Gamma_pos_of_pos (show 0 < (n : ℝ)/2+1 by positivity)
  positivity

theorem radialFock_enn_component (n : ℕ) :
    8 * (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal |radialWigner n t|) ≤
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (radialHusimiRoot n t))^2 := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hW : Integrable (fun t => |radialWigner n t|) μ := by
    simp_rw [radialWigner_abs]
    simpa only [Real.norm_eq_abs] using (radialFock_integrable n).norm
  have hQ : Integrable (radialHusimiRoot n) μ := radialRoot_integrable n
  have hQpos : 0 ≤ᵐ[μ] radialHusimiRoot n := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact radialHusimiRoot_nonneg n t ht.le
  have hWpos : 0 ≤ᵐ[μ] (fun t => |radialWigner n t|) :=
    Filter.Eventually.of_forall (fun t => abs_nonneg _)
  have h := fock_radial_husimi_inequality n
  have he : (∫ t in Ioi (0 : ℝ), Real.sqrt (radialHusimi n t)) =
      ∫ t in Ioi (0 : ℝ), radialHusimiRoot n t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change Real.sqrt (radialHusimiRoot n t ^ 2) = radialHusimiRoot n t
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (radialHusimiRoot_nonneg n t ht.le)]
  rw [he] at h
  have hr : 8 * (∫ t, |radialWigner n t| ∂μ) ≤
      (∫ t, radialHusimiRoot n t ∂μ)^2 := by
    change (∫ t, |radialWigner n t| ∂μ) ≤ (∫ t, radialHusimiRoot n t ∂μ)^2 / 8 at h
    linarith
  have hnn := integral_nonneg_of_ae hQpos
  have h' := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
    ENNReal.ofReal_pow hnn, ofReal_integral_eq_lintegral_ofReal hW hWpos,
    ofReal_integral_eq_lintegral_ofReal hQ hQpos] at h'
  norm_num at h'
  exact h'

-- Countable mixtures with an explicit signed radial Wigner series.
noncomputable def diagonalWigner (p : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n, p n * radialWigner n t

noncomputable def diagonalHusimiRoot (p : ℕ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  mixtureRoot (fun n => ENNReal.ofReal (p n))
    (fun n t => ENNReal.ofReal (radialHusimiRoot n t)) t

theorem diagonal_radial_inequality (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n) :
    8 * (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal |diagonalWigner p t|) ≤
      (∫⁻ t in Ioi (0 : ℝ), diagonalHusimiRoot p t)^2 := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let q : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (p n)
  let f : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (radialHusimiRoot n t)
  let w : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal |radialWigner n t|
  have hf : ∀ n, Measurable (f n) := by
    intro n
    dsimp [f, radialHusimiRoot]
    fun_prop
  have hw : ∀ n, Measurable (w n) := by
    intro n
    dsimp [w, radialWigner, radialFock, laguerre]
    fun_prop
  have htriangle (t : ℝ) :
      ENNReal.ofReal |diagonalWigner p t| ≤ ∑' n, q n * w n t := by
    unfold diagonalWigner
    have h := enn_abs_tsum_le (fun n => p n * radialWigner n t)
    simp_rw [abs_mul, abs_of_nonneg (hp _), ENNReal.ofReal_mul (hp _)] at h
    exact h
  have hsum : (∫⁻ t, ∑' n, q n * w n t ∂μ) =
      ∑' n, q n * (∫⁻ t, w n t ∂μ) := by
    rw [lintegral_tsum (fun n => (measurable_const.mul (hw n)).aemeasurable)]
    apply tsum_congr
    intro n
    exact lintegral_const_mul _ (hw n)
  change 8 * (∫⁻ t, ENNReal.ofReal |diagonalWigner p t| ∂μ) ≤
    (∫⁻ t, mixtureRoot q f t ∂μ)^2
  calc
    _ ≤ 8 * (∫⁻ t, ∑' n, q n * w n t ∂μ) :=
      mul_le_mul_left' (lintegral_mono htriangle) _
    _ = ∑' n, q n * (8 * (∫⁻ t, w n t ∂μ)) := by
      rw [hsum, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro n
      ac_rfl
    _ ≤ ∑' n, q n * (∫⁻ t, f n t ∂μ)^2 := by
      exact ENNReal.tsum_le_tsum (fun n => mul_le_mul_left' (radialFock_enn_component n) _)
    _ ≤ _ := countable_mixture_root_bound μ q f hf

#print axioms enn_abs_tsum_le
#print axioms radialFock_enn_component
#print axioms diagonal_radial_inequality

end F19
