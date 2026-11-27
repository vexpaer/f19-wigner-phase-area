
import F19.Algebra
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# General-pure-state reduction

The statements below isolate analytic limit and averaging lemmas used in the
finite Bargmann polynomial reduction. They are not a proof of the finite
polynomial inequality, nor of the full F19 conjecture.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace F19.Pure

/-- Fatou transfers a uniform upper bound on approximants to the limit. -/
theorem lintegral_limit_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w : ℕ → α → ℝ≥0∞) (W : α → ℝ≥0∞) (b : ℕ → ℝ≥0∞) (B : ℝ≥0∞)
    (hw : ∀ n, Measurable (w n))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (W x)))
    (hb : Tendsto b atTop (𝓝 B))
    (hle : ∀ n, (∫⁻ x, w n x ∂μ) ≤ b n) :
    (∫⁻ x, W x ∂μ) ≤ B := by
  calc
    _ = ∫⁻ x, liminf (fun n => w n x) atTop ∂μ :=
      lintegral_congr_ae (hlim.mono fun _ h => h.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ x, w n x ∂μ) atTop := lintegral_liminf_le hw
    _ ≤ liminf b atTop := Filter.liminf_le_liminf (Eventually.of_forall hle)
    _ = B := hb.liminf_eq

/-- Abstract sharp inequality is closed under Wigner pointwise convergence and
convergence of the nonnegative Husimi root integrals. -/
theorem sharp_limit {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w : ℕ → α → ℝ≥0∞) (W : α → ℝ≥0∞) (h : ℕ → ℝ≥0∞) (H : ℝ≥0∞)
    (hw : ∀ n, Measurable (w n))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (W x)))
    (hh : Tendsto h atTop (𝓝 H))
    (hle : ∀ n, (∫⁻ x, w n x ∂μ) ≤ h n ^ 2) :
    (∫⁻ x, W x ∂μ) ≤ H ^ 2 := by
  apply lintegral_limit_bound μ w W (fun n => h n ^ 2) (H ^ 2) hw hlim
  · exact (ENNReal.continuous_pow 2).continuousAt.tendsto.comp hh
  · exact hle

/-- A useful form of the preceding result when the Husimi integrands have
a common integrable majorant. -/
theorem sharp_limit_dominated {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (w : ℕ → α → ℝ≥0∞) (W : α → ℝ≥0∞)
    (f : ℕ → β → ℝ≥0∞) (F g : β → ℝ≥0∞)
    (hw : ∀ n, Measurable (w n))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (W x)))
    (hf : ∀ n, Measurable (f n))
    (hdom : ∀ n, f n ≤ᵐ[ν] g) (hfin : (∫⁻ y, g y ∂ν) ≠ ⊤)
    (hflim : ∀ᵐ y ∂ν, Tendsto (fun n => f n y) atTop (𝓝 (F y)))
    (hle : ∀ n, (∫⁻ x, w n x ∂μ) ≤ (∫⁻ y, f n y ∂ν)^2) :
    (∫⁻ x, W x ∂μ) ≤ (∫⁻ y, F y ∂ν)^2 := by
  exact sharp_limit μ w W (fun n => ∫⁻ y, f n y ∂ν) (∫⁻ y, F y ∂ν)
    hw hlim (tendsto_lintegral_of_dominated_convergence g hf hdom hfin hflim) hle

/-- Fejér coefficient, including the exact cutoff beyond degree N. -/
noncomputable def fejerWeight (N n : ℕ) : ℝ := 1 - min 1 ((n : ℝ)/(N+1))

theorem fejerWeight_nonneg (N n : ℕ) : 0 ≤ fejerWeight N n := by
  unfold fejerWeight
  linarith [min_le_left (1 : ℝ) ((n : ℝ)/(N+1))]

theorem fejerWeight_le_one (N n : ℕ) : fejerWeight N n ≤ 1 := by
  unfold fejerWeight
  have h : 0 ≤ min (1 : ℝ) ((n : ℝ)/(N+1)) := le_min (by norm_num) (by positivity)
  linarith

theorem fejerWeight_cutoff (N n : ℕ) (hn : N < n) : fejerWeight N n = 0 := by
  unfold fejerWeight
  have h : (1 : ℝ) ≤ (n : ℝ)/(N+1) := by
    apply (le_div_iff₀ (by positivity : 0 < (N : ℝ)+1)).2
    have h' : (N : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (show N+1 ≤ n by omega)
    simpa using h'
  rw [min_eq_left h, sub_self]

theorem fejerWeight_in_range (N n : ℕ) (hn : n ≤ N) :
    fejerWeight N n = 1 - (n : ℝ)/(N+1) := by
  unfold fejerWeight
  have h : (n : ℝ)/(N+1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (N : ℝ)+1)).2
    have h' : (n : ℝ) ≤ N := by exact_mod_cast hn
    linarith
  rw [min_eq_right h]

theorem fejerWeight_zero (N : ℕ) : fejerWeight N 0 = 1 := by
  simp [fejerWeight]

/-- Each coefficient tends to one as the degree tends to infinity. -/
theorem fejerWeight_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => fejerWeight N n) atTop (𝓝 1) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun N : ℕ => ((N : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hd : Tendsto (fun N : ℕ => (n : ℝ)/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hi.const_mul (n : ℝ)
  have hm : Tendsto (fun N : ℕ => min (1 : ℝ) ((n : ℝ)/(N+1))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.min hd : Tendsto _ atTop (𝓝 (min (1 : ℝ) 0)))
  simpa [fejerWeight] using
    (tendsto_const_nhds.sub hm : Tendsto _ atTop (𝓝 ((1 : ℝ)-0)))

/-- Fejér coefficients act contractively on square-summable sequences. -/
theorem fejer_square_le (N n : ℕ) (c : ℂ) :
    ‖(fejerWeight N n : ℂ) * c‖ ^ 2 ≤ ‖c‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejerWeight_nonneg N n)]
  have h : fejerWeight N n * ‖c‖ ≤ ‖c‖ := by
    simpa using mul_le_mul_of_nonneg_right (fejerWeight_le_one N n) (norm_nonneg c)
  exact pow_le_pow_left₀ (mul_nonneg (fejerWeight_nonneg N n) (norm_nonneg c)) h 2

/-- The elementary nonnegative kernel underlying Fejér averaging. -/
noncomputable def fejerKernel (N : ℕ) (z : ℂ) : ℝ :=
  ‖∑ k ∈ Finset.range (N+1), z^k‖^2/(N+1)

theorem fejerKernel_nonneg (N : ℕ) (z : ℂ) : 0 ≤ fejerKernel N z := by
  unfold fejerKernel
  positivity

#print axioms lintegral_limit_bound
#print axioms sharp_limit
#print axioms sharp_limit_dominated
#print axioms fejerWeight_cutoff
#print axioms fejerWeight_tendsto
#print axioms fejer_square_le
#print axioms fejerKernel_nonneg

end F19.Pure


namespace F19.Pure

theorem fejer_error_square_le (N n : ℕ) (c : ℂ) :
    ‖(fejerWeight N n : ℂ) * c - c‖^2 ≤ ‖c‖^2 := by
  rw [← sub_one_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h0 := fejerWeight_nonneg N n
  have h1 := fejerWeight_le_one N n
  rw [abs_of_nonpos (sub_nonpos.mpr h1)]
  have h : -(fejerWeight N n-1)*‖c‖ ≤ ‖c‖ := by
    have h' : -(fejerWeight N n-1) ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_right h' (norm_nonneg c)
  exact pow_le_pow_left₀ (mul_nonneg (by linarith) (norm_nonneg c)) h 2

theorem fejer_error_tendsto (n : ℕ) (c : ℂ) :
    Tendsto (fun N : ℕ => ENNReal.ofReal (‖(fejerWeight N n : ℂ)*c-c‖^2))
      atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto 1).comp (fejerWeight_tendsto n)
  have hc : Tendsto (fun N : ℕ => (fejerWeight N n : ℂ)*c-c) atTop (𝓝 0) := by
    simpa using (h.mul_const c).sub_const c
  simpa using ENNReal.tendsto_ofReal (hc.norm.pow 2)

-- Convergence in the squared ℓ² coefficient error, for every square-summable
-- coefficient sequence. No finite-support assumption is made on c.
theorem fejer_l2_error_tendsto (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖^2)) :
    Tendsto (fun N : ℕ => ∑' n, ENNReal.ofReal (‖(fejerWeight N n : ℂ)*c n-c n‖^2))
      atTop (𝓝 0) := by
  let f : ℕ → ℕ → ℝ≥0∞ := fun N n => ENNReal.ofReal (‖(fejerWeight N n : ℂ)*c n-c n‖^2)
  let g : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (‖c n‖^2)
  have hfin : (∫⁻ n, g n ∂Measure.count) ≠ ⊤ := by
    rw [lintegral_count]
    dsimp [g]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖c n‖) hc]
    exact ENNReal.ofReal_ne_top
  have hf : ∀ N, Measurable (f N) := fun N => measurable_of_countable _
  have hdom : ∀ N, f N ≤ᵐ[Measure.count] g := fun N =>
    Eventually.of_forall (fun n => ENNReal.ofReal_le_ofReal (fejer_error_square_le N n (c n)))
  have hlim : ∀ᵐ n ∂(Measure.count : Measure ℕ),
      Tendsto (fun N => f N n) atTop (𝓝 ((fun _ : ℕ => (0 : ℝ≥0∞)) n)) :=
    Eventually.of_forall (fun n => fejer_error_tendsto n (c n))
  have h := tendsto_lintegral_of_dominated_convergence g hf hdom hfin hlim
  simpa [lintegral_count, f] using h

#print axioms fejer_error_square_le
#print axioms fejer_error_tendsto
#print axioms fejer_l2_error_tendsto

end F19.Pure


namespace F19.Pure

-- The cross Wigner function with one vacuum input has an exact norm
-- identity, not the factor-two estimate for generic cross Wigner functions.
-- The argument below concerns the explicit phase-space functions.
noncomputable def bargmannPolynomial (N : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N+1), c n * z^n / (Real.sqrt (n.factorial : ℝ) : ℂ)

noncomputable def husimiAmplitude (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  Real.exp (-‖z‖^2/2) * ‖F z‖

noncomputable def vacuumCrossWigner (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((Real.exp (-‖z‖^2)/Real.pi : ℝ) : ℂ) * F (Real.sqrt 2 • z)

theorem vacuumCross_pointwise (F : ℂ → ℂ) (z : ℂ) :
    ‖vacuumCrossWigner F z‖ = husimiAmplitude F (Real.sqrt 2 • z) / Real.pi := by
  unfold vacuumCrossWigner husimiAmplitude
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (Real.exp_pos _) Real.pi_pos), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show -(2 * ‖z‖^2)/2 = -‖z‖^2 by ring]
  ring

theorem vacuumCross_integral (F : ℂ → ℂ) :
    (∫ z : ℂ, ‖vacuumCrossWigner F z‖) =
      (∫ z : ℂ, husimiAmplitude F z)/(2*Real.pi) := by
  simp_rw [vacuumCross_pointwise F, div_eq_mul_inv]
  rw [integral_mul_const,
    Measure.integral_comp_smul_of_nonneg volume (husimiAmplitude F) (Real.sqrt 2)
      (hR := Real.sqrt_nonneg 2),
    Complex.finrank_real_complex, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), smul_eq_mul]
  ring

-- The right hand side is the normalized Bargmann L¹ functional H(F).
-- No normalization of the finite coefficient sequence is needed.
theorem finite_vacuum_cross_identity (N : ℕ) (c : ℕ → ℂ) :
    (∫ z : ℂ, ‖vacuumCrossWigner (bargmannPolynomial N c) z‖) =
      (∫ z : ℂ, husimiAmplitude (bargmannPolynomial N c) z)/(2*Real.pi) :=
  vacuumCross_integral _

#print axioms vacuumCross_pointwise
#print axioms vacuumCross_integral
#print axioms finite_vacuum_cross_identity

end F19.Pure


namespace F19.Pure

/-- Polynomial part of a cross-Fock Wigner function, in the conjugate
quadrature convention z = x - i p. The Gaussian and π are factored out. -/
noncomputable def crossFockCoeff (m n k : ℕ) : ℝ :=
  (-1 : ℝ)^k * (m.choose k : ℝ) * (n.choose k : ℝ) *
      (k.factorial : ℝ) /
      (Real.sqrt (m.factorial : ℝ) * Real.sqrt (n.factorial : ℝ))

theorem crossFockCoeff_symm (m n k : ℕ) : crossFockCoeff m n k = crossFockCoeff n m k := by
  unfold crossFockCoeff
  rw [show ((-1 : ℝ)^k * (m.choose k : ℝ) * (n.choose k : ℝ) *
      (k.factorial : ℝ)) = ((-1 : ℝ)^k * (n.choose k : ℝ) * (m.choose k : ℝ) *
      (k.factorial : ℝ)) by ring, mul_comm (Real.sqrt (m.factorial : ℝ))]

noncomputable def crossFockKernel (m n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (min m n+1),
    (crossFockCoeff m n k : ℂ) * z^(m-k) * (star z)^(n-k)

theorem crossFockKernel_vacuum (m : ℕ) (z : ℂ) :
    crossFockKernel m 0 z = z^m / (Real.sqrt (m.factorial : ℝ) : ℂ) := by
  unfold crossFockKernel crossFockCoeff
  simp [Finset.sum_range_succ, div_eq_mul_inv, mul_comm]

theorem crossFockKernel_conj (m n : ℕ) (z : ℂ) :
    star (crossFockKernel m n z) = crossFockKernel n m z := by
  unfold crossFockKernel
  rw [min_comm m n]
  have hc (k : ℕ) : star (crossFockCoeff m n k : ℂ) = (crossFockCoeff n m k : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, crossFockCoeff_symm]
  simp only [star_sum, star_mul', star_pow, star_star, hc]
  apply Finset.sum_congr rfl
  intro k hk
  ring

noncomputable def finiteWignerPolynomial (N : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (N+1), ∑ n ∈ Finset.range (N+1),
    c m * star (c n) * crossFockKernel m n z

theorem finiteWignerPolynomial_real (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    star (finiteWignerPolynomial N c z) = finiteWignerPolynomial N c z := by
  unfold finiteWignerPolynomial
  simp only [star_sum, star_mul', star_star, crossFockKernel_conj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  ring

noncomputable def finiteCrossVacuum (N : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ((Real.exp (-‖z‖^2)/Real.pi : ℝ) : ℂ) *
    ∑ m ∈ Finset.range (N+1), c m * crossFockKernel m 0 (Real.sqrt 2 • z)

theorem finiteCrossVacuum_eq (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    finiteCrossVacuum N c z = vacuumCrossWigner (bargmannPolynomial N c) z := by
  unfold finiteCrossVacuum vacuumCrossWigner bargmannPolynomial
  simp_rw [crossFockKernel_vacuum, mul_div_assoc]

theorem finiteCrossVacuum_norm (N : ℕ) (c : ℕ → ℂ) :
    (∫ z : ℂ, ‖finiteCrossVacuum N c z‖) =
      (∫ z : ℂ, husimiAmplitude (bargmannPolynomial N c) z)/(2*Real.pi) := by
  simp_rw [finiteCrossVacuum_eq]
  exact finite_vacuum_cross_identity N c

#print axioms crossFockKernel_vacuum
#print axioms crossFockKernel_conj
#print axioms finiteWignerPolynomial_real
#print axioms finiteCrossVacuum_norm

end F19.Pure


namespace F19.Pure

/-- The explicit real polynomial for a vacuum--one-photon superposition
with real coefficients (the relative phase can be removed by rotation). -/
noncomputable def qubitWignerPoly (a b x y : ℝ) : ℝ :=
  a^2-b^2+2*b^2*(x^2+y^2)+2*Real.sqrt 2*a*b*x

theorem qubitWignerPoly_square (a b x y : ℝ) (hb : b ≠ 0) :
    qubitWignerPoly a b x y =
      b^2*(2*((x+a/(Real.sqrt 2*b))^2+y^2)-1) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hden : Real.sqrt 2*b ≠ 0 := mul_ne_zero hs.ne' hb
  have hA : (a/(Real.sqrt 2*b))^2 = a^2/(2*b^2) := by
    rw [div_pow, mul_pow, hs2]
  have hB : 4*b^2*x*(a/(Real.sqrt 2*b)) = 2*Real.sqrt 2*a*b*x := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hden).2
    linear_combination -congrArg (fun u : ℝ => 2*a*b^2*x*u) hs2
  unfold qubitWignerPoly
  rw [add_sq, hA]
  have hb2 : b^2 ≠ 0 := pow_ne_zero _ hb
  have hC : 2*b^2*(a^2/(2*b^2)) = a^2 := by
    field_simp [hb2]
  linear_combination -hB-hC

theorem qubitWignerPoly_negative_iff (a b x y : ℝ) (hb : b ≠ 0) :
    qubitWignerPoly a b x y < 0 ↔ (x+a/(Real.sqrt 2*b))^2+y^2 < 1/2 := by
  rw [qubitWignerPoly_square a b x y hb]
  have hb2 : 0 < b^2 := sq_pos_of_ne_zero hb
  constructor
  · intro h
    by_contra! h'
    have hnon : 0 ≤ 2*((x+a/(Real.sqrt 2*b))^2+y^2)-1 := by linarith
    exact (not_lt_of_ge (mul_nonneg hb2.le hnon)) h
  · intro h
    exact mul_neg_of_pos_of_neg hb2 (by linarith)

#print axioms qubitWignerPoly_square
#print axioms qubitWignerPoly_negative_iff

end F19.Pure


namespace F19.Pure

/-- The kth normalized polynomial jet (the kth derivative divided by k!).
The explicit formula avoids any assumption about differentiability. -/
noncomputable def jetTerm (c : ℕ → ℂ) (m k : ℕ) (z : ℂ) : ℂ :=
  c m * ((m.choose k : ℝ) / Real.sqrt (m.factorial : ℝ) : ℝ) * z^(m-k)

noncomputable def bargmannJet (N k : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (N+1), jetTerm c m k z

noncomputable def jetWeight (k : ℕ) : ℝ := (-1 : ℝ)^k * k.factorial

theorem jetTerm_star (c : ℕ → ℂ) (m k : ℕ) (z : ℂ) :
    star (jetTerm c m k z) =
      star (c m) * ((m.choose k : ℝ) / Real.sqrt (m.factorial : ℝ) : ℝ) *
        (star z)^(m-k) := by
  unfold jetTerm
  have h : star (((m.choose k : ℝ) / Real.sqrt (m.factorial : ℝ) : ℝ) : ℂ) =
      (((m.choose k : ℝ) / Real.sqrt (m.factorial : ℝ) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  simp only [star_mul', star_pow, h]

theorem crossFockKernel_range (N m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) (z : ℂ) :
    crossFockKernel m n z = ∑ k ∈ Finset.range (N+1),
      (crossFockCoeff m n k : ℂ) * z^(m-k) * (star z)^(n-k) := by
  unfold crossFockKernel
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hnot
    have hlt : min m n < k := by
      simp only [Finset.mem_range, not_lt] at hnot
      omega
    have hzero : m.choose k = 0 ∨ n.choose k = 0 := by
      by_cases h : m ≤ n
      · left
        rw [min_eq_left h] at hlt
        exact Nat.choose_eq_zero_of_lt hlt
      · right
        rw [min_eq_right (by omega)] at hlt
        exact Nat.choose_eq_zero_of_lt hlt
    rcases hzero with h | h <;> simp [crossFockCoeff, h]

theorem jet_cross_term (c : ℕ → ℂ) (m n k : ℕ) (z : ℂ) :
    c m * star (c n) *
      ((crossFockCoeff m n k : ℂ) * z^(m-k) * (star z)^(n-k)) =
      (jetWeight k : ℂ) * (jetTerm c m k z * star (jetTerm c n k z)) := by
  rw [jetTerm_star]
  unfold crossFockCoeff jetWeight jetTerm
  push_cast
  ring

/-- All interference terms can be regrouped into a single alternating
sum of squared polynomial jets. This is an exact finite-dimensional
identity, not an estimate using the triangle inequality. -/
theorem finiteWigner_jet_identity (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    finiteWignerPolynomial N c z =
      ∑ k ∈ Finset.range (N+1),
        (jetWeight k : ℂ) * (bargmannJet N k c z * star (bargmannJet N k c z)) := by
  classical
  let S := Finset.range (N+1)
  calc
    finiteWignerPolynomial N c z =
        ∑ m ∈ S, ∑ n ∈ S, ∑ k ∈ S,
          (jetWeight k : ℂ) * (jetTerm c m k z * star (jetTerm c n k z)) := by
      unfold finiteWignerPolynomial
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [crossFockKernel_range N m n (by have h := Finset.mem_range.mp hm; omega) (by have h := Finset.mem_range.mp hn; omega),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact jet_cross_term c m n k z
    _ = ∑ k ∈ S, ∑ m ∈ S, ∑ n ∈ S,
          (jetWeight k : ℂ) * (jetTerm c m k z * star (jetTerm c n k z)) := by
      calc
        _ = ∑ m ∈ S, ∑ k ∈ S, ∑ n ∈ S,
            (jetWeight k : ℂ) * (jetTerm c m k z * star (jetTerm c n k z)) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    _ = _ := by
      unfold bargmannJet
      apply Finset.sum_congr rfl
      intro k hk
      simp only [star_sum]
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum, Finset.mul_sum]

/-- Real-valued alternating jet norm formula. -/
noncomputable def jetAlternating (N : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℝ :=
  ∑ k ∈ Finset.range (N+1), jetWeight k * ‖bargmannJet N k c z‖^2

theorem finiteWigner_jet_real (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    finiteWignerPolynomial N c z = (jetAlternating N c z : ℂ) := by
  rw [finiteWigner_jet_identity]
  unfold jetAlternating
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [Complex.star_def, Complex.mul_conj']

#print axioms crossFockKernel_range
#print axioms jet_cross_term
#print axioms finiteWigner_jet_identity
#print axioms finiteWigner_jet_real

end F19.Pure


namespace F19.Pure

noncomputable def gaussianMean (g : ℂ → ℝ) : ℝ :=
  (∫ z : ℂ, Real.exp (-‖z‖^2/2) * g z)/(2*Real.pi)

noncomputable def finiteWigner (N : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℝ :=
  (Real.exp (-‖z‖^2)/Real.pi) *
    (finiteWignerPolynomial N c (Real.sqrt 2 • z)).re

theorem finiteWigner_abs_jet (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    |finiteWigner N c z| =
      (Real.exp (-‖z‖^2)/Real.pi) * |jetAlternating N c (Real.sqrt 2 • z)| := by
  unfold finiteWigner
  rw [finiteWigner_jet_real, Complex.ofReal_re, abs_mul,
    abs_of_pos (div_pos (Real.exp_pos _) Real.pi_pos)]

theorem finiteWigner_gaussian_identity (N : ℕ) (c : ℕ → ℂ) :
    (∫ z : ℂ, |finiteWigner N c z|) =
      gaussianMean (fun z => |jetAlternating N c z|) := by
  simp_rw [finiteWigner_abs_jet]
  unfold gaussianMean
  let g : ℂ → ℝ := fun z => Real.exp (-‖z‖^2/2) * |jetAlternating N c z|
  have he (z : ℂ) :
      (Real.exp (-‖z‖^2)/Real.pi) * |jetAlternating N c (Real.sqrt 2 • z)| =
        g (Real.sqrt 2 • z) / Real.pi := by
    dsimp [g]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
      mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      show -(2*‖z‖^2)/2 = -‖z‖^2 by ring]
    ring
  simp_rw [he, div_eq_mul_inv]
  rw [integral_mul_const,
    Measure.integral_comp_smul_of_nonneg volume g (Real.sqrt 2)
      (hR := Real.sqrt_nonneg 2),
    Complex.finrank_real_complex, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), smul_eq_mul]
  change _ = (∫ z : ℂ, g z) * _
  ring

-- Exact finite polynomial target. This is an equivalence, not a proof
-- that either inequality holds. All non-diagonal terms remain present.
theorem finite_pure_gaussian_iff (N : ℕ) (c : ℕ → ℂ) :
    ((∫ z : ℂ, |finiteWigner N c z|) ≤
      ((∫ z : ℂ, husimiAmplitude (bargmannPolynomial N c) z)/(2*Real.pi))^2) ↔
    (gaussianMean (fun z => |jetAlternating N c z|) ≤
      (gaussianMean (fun z => ‖bargmannPolynomial N c z‖))^2) := by
  rw [finiteWigner_gaussian_identity]
  rfl

#print axioms finiteWigner_abs_jet
#print axioms finiteWigner_gaussian_identity
#print axioms finite_pure_gaussian_iff

end F19.Pure


namespace F19.Pure

-- The gamma-ratio recurrence yields monotone normalized squares.
-- These polynomial certificates are the two signs needed for
-- 1/3 ≤ Var(chi_{2k+2}) ≤ 1/2.
theorem gamma_quarter_poly (t : ℝ) :
    (t+1/2)^2*(t-1/4)-t^2*(t+1-1/4) = -1/16 := by ring

theorem gamma_sixth_poly (t : ℝ) (ht : 1 ≤ t) :
    0 < (t+1/2)^2*(t-1/6)-t^2*(t+1-1/6) := by
  calc
    _ = t/12-1/24 := by ring
    _ > 0 := by linarith

theorem chi_increment_sq (t h v : ℝ) (ht : 0 < t)
    (hv : v = 2*t-h^2) :
    (h*(1+1/(2*t))-h)^2 = 1/(2*t)-v/(4*t^2) := by
  rw [hv]
  field_simp [ht.ne']
  ring

/-- The explicit gamma negative-part bound is dominated by the
coefficient of the Poisson variance deficit, at every positive index. -/
theorem qubit_negative_coeff_le (k : ℕ) (hk : 1 ≤ k) :
    1/((2:ℝ)^k*((k:ℝ)+1)*((k:ℝ)+2)*(k.factorial:ℝ)) ≤ 1/(12*(k:ℝ)) := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hp : (2:ℝ) ≤ 2^k := by
    calc
      (2:ℝ) = 2^1 := by norm_num
      _ ≤ 2^k := by exact pow_le_pow_right₀ (by norm_num) hk
  have hf : (1:ℝ) ≤ k.factorial := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos k) : 1 ≤ k.factorial)
  have hpoly : 6*(k:ℝ) ≤ ((k:ℝ)+1)*((k:ℝ)+2) := by
    rcases eq_or_lt_of_le hk with h | h
    · subst k; norm_num
    · have h2 : (2:ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      nlinarith [mul_nonneg (show 0 ≤ (k:ℝ)-1 by linarith)
        (show 0 ≤ (k:ℝ)-2 by linarith)]
  have hD : 12*(k:ℝ) ≤ (2:ℝ)^k*((k:ℝ)+1)*((k:ℝ)+2)*(k.factorial:ℝ) := by
    calc
      _ = 2*(6*(k:ℝ))*1 := by ring
      _ ≤ 2*(((k:ℝ)+1)*((k:ℝ)+2))*1 := by gcongr
      _ ≤ (2:ℝ)^k*(((k:ℝ)+1)*((k:ℝ)+2))* (k.factorial:ℝ) := by gcongr
      _ = _ := by ring
  exact one_div_le_one_div_of_le (by positivity) hD

/-- The key positive-index coefficient comparison uses only the
lower variance bound for the preceding gamma component. -/
theorem qubit_negative_coeff_variance (k : ℕ) (hk : 1 ≤ k) (v : ℝ)
    (hv : 1/3 ≤ v) :
    1/((2:ℝ)^k*((k:ℝ)+1)*((k:ℝ)+2)*(k.factorial:ℝ)) ≤ v/(4*(k:ℝ)) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  calc
    _ ≤ 1/(12*(k:ℝ)) := qubit_negative_coeff_le k hk
    _ = (1/3)/(4*(k:ℝ)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hv (by positivity)

-- Isolate the final algebra of the variance-deficit comparison for
-- arbitrary real first/second moments and negative part.
theorem qubit_deficit_algebra (mean second neg absMoment : ℝ)
    (habs : absMoment = second-1+2*neg)
    (hdeficit : second-mean^2+2*neg ≤ 1) :
    absMoment ≤ mean^2 := by linarith

#print axioms gamma_quarter_poly
#print axioms gamma_sixth_poly
#print axioms chi_increment_sq
#print axioms qubit_negative_coeff_le
#print axioms qubit_negative_coeff_variance
#print axioms qubit_deficit_algebra

end F19.Pure


namespace F19.Pure

noncomputable def chiGammaSq (k : ℕ) : ℝ :=
  F19.gammaRatio (2*(k:ℝ)+1)^2

theorem chiGammaSq_lower (k : ℕ) :
    ((k:ℝ)+1)^2/((k:ℝ)+1+1/2) ≤ chiGammaSq k := by
  have h := F19.gammaRatio_lower (2*(k:ℝ)+1) (by positivity)
  unfold chiGammaSq
  convert h using 1
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  field_simp <;> ring

theorem chiGammaSq_upper (k : ℕ) : chiGammaSq k ≤ (k:ℝ)+1 := by
  let t : ℝ := (k:ℝ)+1
  have ht : 0 < t := by dsimp [t]; positivity
  have ht' : 0 < t-1/2 := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have h := F19.gamma_midpoint_sq (t-1/2) ht'
  rw [show t-1/2+1 = t+1/2 by ring,
    show t-1/2+1/2 = t by ring,
    show t-1/2+3/2 = t+1 by ring, Real.Gamma_add_one ht.ne'] at h
  have hg : 0 < Real.Gamma t := Real.Gamma_pos_of_pos ht
  unfold chiGammaSq F19.gammaRatio
  rw [show (2*(k:ℝ)+1+2)/2 = t+1/2 by dsimp [t]; ring,
    show (2*(k:ℝ)+1+1)/2 = t by dsimp [t]; ring, div_pow]
  apply (div_le_iff₀ (pow_pos hg 2)).2
  change _ ≤ t * Real.Gamma t^2
  nlinarith only [h]

theorem chiGammaSq_step (k : ℕ) :
    chiGammaSq (k+1) = (((k:ℝ)+1+1/2)/((k:ℝ)+1))^2 * chiGammaSq k := by
  unfold chiGammaSq
  push_cast
  rw [show 2*((k:ℝ)+1)+1 = (2*(k:ℝ)+1)+2 by ring,
    F19.gammaRatio_step _ (by positivity), mul_pow]
  congr 1
  congr 1
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  field_simp <;> ring

noncomputable def chiGammaNormalized (a : ℝ) (k : ℕ) : ℝ :=
  chiGammaSq k / ((k:ℝ)+1-a)

theorem chiGammaNormalized_tendsto (a : ℝ) (ha : a < 1) :
    Tendsto (chiGammaNormalized a) atTop (𝓝 1) := by
  let t : ℕ → ℝ := fun k => (k:ℝ)+1
  have ht : Tendsto t atTop atTop :=
    tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun k => (t k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  have h1 : Tendsto (fun k => 1+(1/2:ℝ)*(t k)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (hi.const_mul (1/2:ℝ)) :
      Tendsto _ atTop (𝓝 ((1:ℝ)+(1/2:ℝ)*0)))
  have h2 : Tendsto (fun k => 1-a*(t k)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (hi.const_mul a) :
      Tendsto _ atTop (𝓝 ((1:ℝ)-a*0)))
  have hl : Tendsto (fun k => (1:ℝ)/((1+(1/2:ℝ)*(t k)⁻¹)*(1-a*(t k)⁻¹)))
      atTop (𝓝 1) := by
    simpa only [one_mul, div_one, Pi.div_apply] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).div (h1.mul h2) (by norm_num : (1:ℝ)*1 ≠ 0)
  have hu : Tendsto (fun k => (1:ℝ)/(1-a*(t k)⁻¹)) atTop (𝓝 1) := by
    simpa only [div_one, Pi.div_apply] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).div h2 one_ne_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro k
    have ht0 : 0 < t k := by dsimp [t]; positivity
    have hta : 0 < t k-a := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) k]
    change (1:ℝ)/((1+(1/2:ℝ)*(t k)⁻¹)*(1-a*(t k)⁻¹)) ≤ chiGammaNormalized a k
    have he : (1:ℝ)/((1+(1/2:ℝ)*(t k)⁻¹)*(1-a*(t k)⁻¹)) =
        (t k)^2/(t k+1/2)/(t k-a) := by
      field_simp [ht0.ne', hta.ne', ne_of_gt (add_pos ht0 (by norm_num : (0:ℝ)<1/2))]
      <;> ring
    rw [he]
    exact div_le_div_of_nonneg_right (chiGammaSq_lower k) hta.le
  · intro k
    have ht0 : 0 < t k := by dsimp [t]; positivity
    have hta : 0 < t k-a := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) k]
    change chiGammaNormalized a k ≤ (1:ℝ)/(1-a*(t k)⁻¹)
    have he : (1:ℝ)/(1-a*(t k)⁻¹) = t k/(t k-a) := by
      field_simp [ht0.ne', hta.ne']
      <;> ring
    rw [he]
    exact div_le_div_of_nonneg_right (chiGammaSq_upper k) hta.le

theorem chiGammaNormalized_quarter_antitone : Antitone (chiGammaNormalized (1/4)) := by
  apply antitone_nat_of_succ_le
  intro k
  let t : ℝ := (k:ℝ)+1
  have ht : 1 ≤ t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have h0 : 0 < t := by linarith
  have h1 : 0 < t-1/4 := sub_pos.mpr (lt_of_lt_of_le (by norm_num : (1/4:ℝ)<1) ht)
  have h2 : 0 < t+1-1/4 := by linarith
  unfold chiGammaNormalized
  rw [chiGammaSq_step]
  push_cast
  change ((t+1/2)/t)^2*chiGammaSq k/(t+1-1/4) ≤ chiGammaSq k/(t-1/4)
  have he : ((t+1/2)/t)^2*(t-1/4) ≤ t+1-1/4 := by
    rw [div_pow, div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos h0 2)).2
    linarith [gamma_quarter_poly t]
  apply (div_le_div_iff₀ h2 h1).2
  calc
    _ = (((t+1/2)/t)^2*(t-1/4))*chiGammaSq k := by ring
    _ ≤ (t+1-1/4)*chiGammaSq k := mul_le_mul_of_nonneg_right he (sq_nonneg _)
    _ = _ := by ring

theorem chiGammaNormalized_sixth_monotone : Monotone (chiGammaNormalized (1/6)) := by
  apply monotone_nat_of_le_succ
  intro k
  let t : ℝ := (k:ℝ)+1
  have ht : 1 ≤ t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have h0 : 0 < t := by linarith
  have h1 : 0 < t-1/6 := sub_pos.mpr (lt_of_lt_of_le (by norm_num : (1/6:ℝ)<1) ht)
  have h2 : 0 < t+1-1/6 := by linarith
  unfold chiGammaNormalized
  rw [chiGammaSq_step]
  push_cast
  change chiGammaSq k/(t-1/6) ≤ ((t+1/2)/t)^2*chiGammaSq k/(t+1-1/6)
  have he : t+1-1/6 ≤ ((t+1/2)/t)^2*(t-1/6) := by
    rw [div_pow, div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos h0 2)).2
    linarith [gamma_sixth_poly t ht]
  apply (div_le_div_iff₀ h1 h2).2
  calc
    _ = (t+1-1/6)*chiGammaSq k := by ring
    _ ≤ (((t+1/2)/t)^2*(t-1/6))*chiGammaSq k :=
      mul_le_mul_of_nonneg_right he (sq_nonneg _)
    _ = _ := by ring

theorem chiGammaSq_quarter (k : ℕ) : (k:ℝ)+1-1/4 ≤ chiGammaSq k := by
  have h : 1 ≤ chiGammaNormalized (1/4) k :=
    le_of_tendsto (chiGammaNormalized_tendsto (1/4) (by norm_num))
      ((eventually_ge_atTop k).mono fun n hn => chiGammaNormalized_quarter_antitone hn)
  unfold chiGammaNormalized at h
  have hp : 0 < (k:ℝ)+1-1/4 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have h' := (le_div_iff₀ hp).1 h
  linarith

theorem chiGammaSq_sixth (k : ℕ) : chiGammaSq k ≤ (k:ℝ)+1-1/6 := by
  have h : chiGammaNormalized (1/6) k ≤ 1 :=
    ge_of_tendsto (chiGammaNormalized_tendsto (1/6) (by norm_num))
      ((eventually_ge_atTop k).mono fun n hn => chiGammaNormalized_sixth_monotone hn)
  unfold chiGammaNormalized at h
  have hp : 0 < (k:ℝ)+1-1/6 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have h' := (div_le_iff₀ hp).1 h
  linarith

theorem chi_variance_bounds (k : ℕ) :
    1/3 ≤ 2*((k:ℝ)+1)-2*chiGammaSq k ∧
      2*((k:ℝ)+1)-2*chiGammaSq k ≤ 1/2 := by
  constructor <;> linarith [chiGammaSq_quarter k, chiGammaSq_sixth k]

#print axioms chiGammaSq_lower
#print axioms chiGammaSq_upper
#print axioms chiGammaNormalized_tendsto
#print axioms chi_variance_bounds

end F19.Pure


namespace F19.Pure

/-- Binomial expectation, constructed by repeated Bernoulli convolution.
This definition is finite and requires no probability-space axioms. -/
noncomputable def bernMean (p : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, f => f 0
  | n+1, f => (1-p)*bernMean p n f + p*bernMean p n (fun k => f (k+1))

theorem bernMean_add (p : ℝ) (n : ℕ) (f g : ℕ → ℝ) :
    bernMean p n (fun k => f k+g k) = bernMean p n f + bernMean p n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [bernMean, ih]
    ring

theorem bernMean_sub (p : ℝ) (n : ℕ) (f g : ℕ → ℝ) :
    bernMean p n (fun k => f k-g k) = bernMean p n f - bernMean p n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [bernMean, ih]
    ring

theorem bernMean_mono (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : ℕ) (f g : ℕ → ℝ) (h : ∀ k, f k ≤ g k) :
    bernMean p n f ≤ bernMean p n g := by
  induction n generalizing f g with
  | zero => exact h 0
  | succ n ih =>
    simp only [bernMean]
    exact add_le_add (mul_le_mul_of_nonneg_left (ih f g h) (sub_nonneg.mpr hp'))
      (mul_le_mul_of_nonneg_left (ih _ _ (fun k => h (k+1))) hp)

theorem bernMean_jensen_square (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : ℕ) (f : ℕ → ℝ) :
    (bernMean p n f)^2 ≤ bernMean p n (fun k => (f k)^2) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [bernMean]
    have h := add_le_add
      (mul_le_mul_of_nonneg_left (ih f) (sub_nonneg.mpr hp'))
      (mul_le_mul_of_nonneg_left (ih (fun k => f (k+1))) hp)
    have hpos : 0 ≤ p*(1-p)*(bernMean p n f-bernMean p n (fun k => f (k+1)))^2 :=
      mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hp')) (sq_nonneg _)
    nlinarith only [h, hpos]

noncomputable def bernVar (p : ℝ) (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  bernMean p n (fun k => (f k)^2) - (bernMean p n f)^2

noncomputable def deltaSq (f : ℕ → ℝ) (k : ℕ) : ℝ := (f (k+1)-f k)^2

theorem bernVar_succ (p : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    bernVar p (n+1) f =
      (1-p)*bernVar p n f + p*bernVar p n (fun k => f (k+1)) +
      p*(1-p)*(bernMean p n (fun k => f (k+1))-bernMean p n f)^2 := by
  unfold bernVar
  simp only [bernMean]
  ring

/-- Finite binomial Poincare inequality, the tensorization step for a
Poisson Poincare proof by the law of small numbers. -/
theorem bernVar_poincare (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : ℕ) (f : ℕ → ℝ) :
    bernVar p (n+1) f ≤ ((n:ℝ)+1)*p*(1-p)*bernMean p n (deltaSq f) := by
  have hpq : 0 ≤ p*(1-p) := mul_nonneg hp (sub_nonneg.mpr hp')
  induction n generalizing f with
  | zero =>
    rw [bernVar_succ]
    simp [bernVar, bernMean, deltaSq]
    <;> ring_nf
    <;> linarith
  | succ n ih =>
    rw [bernVar_succ]
    have h1 := mul_le_mul_of_nonneg_left (ih f) (sub_nonneg.mpr hp')
    have h2 := mul_le_mul_of_nonneg_left (ih (fun k => f (k+1))) hp
    have hj := bernMean_jensen_square p hp hp' (n+1) (fun k => f (k+1)-f k)
    rw [bernMean_sub] at hj
    have hj' : (bernMean p (n+1) (fun k => f (k+1))-bernMean p (n+1) f)^2 ≤
        bernMean p (n+1) (deltaSq f) := hj
    have h3 := mul_le_mul_of_nonneg_left hj' hpq
    have hshift : deltaSq (fun k => f (k+1)) = (fun k => deltaSq f (k+1)) := rfl
    rw [hshift] at h2
    have he : bernMean p (n+1) (deltaSq f) =
      (1-p)*bernMean p n (deltaSq f) + p*bernMean p n (fun k => deltaSq f (k+1)) := rfl
    push_cast
    rw [he] at h3 ⊢
    nlinarith only [h1, h2, h3]

#print axioms bernMean_jensen_square
#print axioms bernVar_succ
#print axioms bernVar_poincare

end F19.Pure


namespace F19.Pure

theorem qubit_negative_polynomial_integral (k : ℕ) :
    (∫ u in (0:ℝ)..(1/2:ℝ), (1-2*u)*u^k) =
      (1/2:ℝ)^(k+1)/(((k:ℝ)+1)*((k:ℝ)+2)) := by
  have he (u : ℝ) : (1-2*u)*u^k = u^k-2*u^(k+1) := by
    rw [pow_succ]
    ring
  simp_rw [he]
  have h1 : IntervalIntegrable (fun u : ℝ => u^k) volume 0 (1/2) :=
    (continuous_id.pow k).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun u : ℝ => 2*u^(k+1)) volume 0 (1/2) :=
    (continuous_const.mul (continuous_id.pow (k+1))).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
  push_cast
  rw [show k+1+1 = (k+1)+1 by rfl, pow_succ (1/2:ℝ) (k+1)]
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  field_simp <;> ring

theorem qubit_negative_gamma_bound (k : ℕ) :
    (2:ℝ)/(k.factorial:ℝ) *
      (∫ u in (0:ℝ)..(1/2:ℝ), (1-2*u)*Real.exp (-u)*u^k) ≤
      1/((2:ℝ)^k*((k:ℝ)+1)*((k:ℝ)+2)*(k.factorial:ℝ)) := by
  have h1 : IntervalIntegrable (fun u : ℝ => (1-2*u)*Real.exp (-u)*u^k) volume 0 (1/2) :=
    (by fun_prop : Continuous (fun u : ℝ => (1-2*u)*Real.exp (-u)*u^k)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun u : ℝ => (1-2*u)*u^k) volume 0 (1/2) :=
    (by fun_prop : Continuous (fun u : ℝ => (1-2*u)*u^k)).intervalIntegrable _ _
  have hle : (∫ u in (0:ℝ)..(1/2:ℝ), (1-2*u)*Real.exp (-u)*u^k) ≤
      ∫ u in (0:ℝ)..(1/2:ℝ), (1-2*u)*u^k := by
    apply intervalIntegral.integral_mono_on (by norm_num) h1 h2
    intro u hu
    have h0 : 0 ≤ u := hu.1
    have htop : u ≤ 1/2 := hu.2
    have hpos : 0 ≤ 1-2*u := by linarith
    have hexp : Real.exp (-u) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hpos) (pow_nonneg h0 k)
    simpa using h
  calc
    _ ≤ (2:ℝ)/(k.factorial:ℝ) *
        (∫ u in (0:ℝ)..(1/2:ℝ), (1-2*u)*u^k) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by
      rw [qubit_negative_polynomial_integral, pow_succ, div_pow]
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      have hf : (0:ℝ) < k.factorial := by positivity
      field_simp <;> ring

#print axioms qubit_negative_polynomial_integral
#print axioms qubit_negative_gamma_bound

end F19.Pure


namespace F19.Pure
open scoped NNReal

/-- Exact Poisson coefficient recurrence, including the zero-rate case. -/
theorem poisson_weight_succ (r : ℝ≥0) (k : ℕ) :
    ((k:ℝ)+1) * ProbabilityTheory.poissonPMFReal r (k+1) =
      (r:ℝ) * ProbabilityTheory.poissonPMFReal r k := by
  unfold ProbabilityTheory.poissonPMFReal
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hf : (0:ℝ) < (k.factorial:ℝ) := by positivity
  field_simp [hk.ne', hf.ne'] <;> ring

/-- Size-bias shift for arbitrary summable weighted test functions. -/
theorem poisson_shift (r : ℝ≥0) (g : ℕ → ℝ)
    (hs : Summable (fun k => ProbabilityTheory.poissonPMFReal r k *
      (k:ℝ) * g (k-1))) :
    (∑' k, ProbabilityTheory.poissonPMFReal r k * (k:ℝ) * g (k-1)) =
      (r:ℝ) * ∑' k, ProbabilityTheory.poissonPMFReal r k * g k := by
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
  have he (k : ℕ) : ProbabilityTheory.poissonPMFReal r (k+1) *
      ((k+1:ℕ):ℝ) * g (k+1-1) =
      (r:ℝ) * (ProbabilityTheory.poissonPMFReal r k * g k) := by
    rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      mul_comm (ProbabilityTheory.poissonPMFReal r (k+1)), poisson_weight_succ]
    ring
  simp_rw [he]
  rw [tsum_mul_left]

/-- Unit mass of the Poisson weights, supplied by Mathlib. -/
theorem poisson_mass (r : ℝ≥0) :
    (∑' k, ProbabilityTheory.poissonPMFReal r k) = 1 :=
  (ProbabilityTheory.poissonPMFRealSum r).tsum_eq

/-- Passing the finite Poincare inequality to a limit is separate from
proving binomial-to-Poisson convergence of the three expectations. -/
theorem poincare_limit (r : ℝ) (p : ℕ → ℝ) (f : ℕ → ℝ)
    (m s d : ℝ) (hp : ∀ n, 0 ≤ p n) (hp' : ∀ n, p n ≤ 1)
    (hm : Tendsto (fun n => bernMean (p n) (n+1) f) atTop (𝓝 m))
    (hs : Tendsto (fun n => bernMean (p n) (n+1) (fun k => (f k)^2)) atTop (𝓝 s))
    (hd : Tendsto (fun n => bernMean (p n) n (deltaSq f)) atTop (𝓝 d))
    (hr : Tendsto (fun n : ℕ => ((n:ℝ)+1)*p n*(1-p n)) atTop (𝓝 r)) :
    s-m^2 ≤ r*d := by
  have hl : Tendsto (fun n => bernVar (p n) (n+1) f) atTop (𝓝 (s-m^2)) :=
    hs.sub (hm.pow 2)
  have hh : Tendsto (fun n : ℕ => ((n:ℝ)+1)*p n*(1-p n)*bernMean (p n) n (deltaSq f))
      atTop (𝓝 (r*d)) := hr.mul hd
  exact le_of_tendsto_of_tendsto' hl hh (fun n => bernVar_poincare (p n) (hp n) (hp' n) n f)

#print axioms poisson_weight_succ
#print axioms poisson_shift
#print axioms poisson_mass
#print axioms poincare_limit

end F19.Pure


namespace F19.Pure

noncomputable def binWeight (p : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p^k * (1-p)^(n-k)

theorem binWeight_zero (p : ℝ) (n : ℕ) : binWeight p n 0 = (1-p)^n := by
  simp [binWeight]

theorem binWeight_outside (p : ℝ) (n k : ℕ) (h : n < k) :
    binWeight p n k = 0 := by
  simp [binWeight, Nat.choose_eq_zero_of_lt h]

theorem binWeight_step (p : ℝ) (n k : ℕ) (hk : k ≤ n) :
    binWeight p (n+1) (k+1) =
      (1-p)*binWeight p n (k+1)+p*binWeight p n k := by
  rcases eq_or_lt_of_le hk with he | hlt
  · subst k
    rw [binWeight_outside p n (n+1) (by omega)]
    simp [binWeight, pow_succ]
    <;> ring
  · have hd : n-k = n-(k+1)+1 := by omega
    unfold binWeight
    rw [Nat.choose_succ_succ', Nat.cast_add, show n+1-(k+1) = n-k by omega]
    rw [pow_succ p k, hd, pow_succ (1-p) (n-(k+1))]
    ring

theorem bernMean_binomial (p : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    bernMean p n f = ∑ k ∈ Finset.range (n+1), binWeight p n k * f k := by
  induction n generalizing f with
  | zero => simp [bernMean, binWeight]
  | succ n ih =>
    rw [bernMean, ih, ih]
    rw [Finset.sum_range_succ' (fun k => binWeight p (n+1) k * f k)]
    have hz : binWeight p (n+1) 0 = (1-p)*binWeight p n 0 := by
      rw [binWeight_zero, binWeight_zero, pow_succ]
      ring
    rw [hz]
    have he : ∑ k ∈ Finset.range (n+1), binWeight p (n+1) (k+1) * f (k+1) =
        (1-p)*(∑ k ∈ Finset.range (n+1), binWeight p n (k+1)*f (k+1)) +
          p*(∑ k ∈ Finset.range (n+1), binWeight p n k*f (k+1)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [binWeight_step p n k (by have h := Finset.mem_range.mp hk; omega)]
      ring
    rw [he]
    have ht : ∑ k ∈ Finset.range (n+1), binWeight p n (k+1)*f (k+1) =
        ∑ k ∈ Finset.range n, binWeight p n (k+1)*f (k+1) := by
      rw [Finset.sum_range_succ, binWeight_outside p n (n+1) (by omega), zero_mul, add_zero]
    rw [ht]
    rw [Finset.sum_range_succ' (fun k => binWeight p n k * f k)]
    ring

#print axioms binWeight_step
#print axioms bernMean_binomial

end F19.Pure


namespace F19.Pure

/-- Unnormalized binomial odds weights. Using these rather than the
probabilities themselves avoids needing a separate exponential limit. -/
noncomputable def oddsWeight (r : ℝ) (d n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (r / ((n:ℝ)+d))^k

theorem oddsWeight_zero (r : ℝ) (d n : ℕ) : oddsWeight r d n 0 = 1 := by
  simp [oddsWeight]

theorem oddsWeight_nonneg (r : ℝ) (hr : 0 ≤ r) (d n k : ℕ) :
    0 ≤ oddsWeight r d n k := by
  unfold oddsWeight
  positivity

theorem oddsWeight_outside (r : ℝ) (d n k : ℕ) (h : n < k) :
    oddsWeight r d n k = 0 := by
  simp [oddsWeight, Nat.choose_eq_zero_of_lt h]

theorem oddsWeight_step (r : ℝ) (d n k : ℕ) :
    ((k:ℝ)+1)*oddsWeight r d n (k+1) =
      (((n-k:ℕ):ℝ)* (r/((n:ℝ)+d))) * oddsWeight r d n k := by
  have h : (n.choose (k+1):ℝ)*((k:ℝ)+1) =
      (n.choose k:ℝ)*((n-k:ℕ):ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  unfold oddsWeight
  rw [pow_succ]
  calc
    _ = ((n.choose (k+1):ℝ)*((k:ℝ)+1))*(r/((n:ℝ)+d))^k*(r/((n:ℝ)+d)) := by ring
    _ = _ := by rw [h]; ring

theorem oddsWeight_bound (r : ℝ) (hr : 0 ≤ r) (d n k : ℕ) :
    oddsWeight r d n k ≤ r^k/(k.factorial:ℝ) := by
  induction k with
  | zero => simp [oddsWeight]
  | succ k ih =>
    have hk : 0 < (k:ℝ)+1 := by positivity
    have hf : 0 < (k.factorial:ℝ) := by positivity
    have hd : 0 ≤ (n:ℝ)+d := by positivity
    have hn : ((n-k:ℕ):ℝ) ≤ (n:ℝ)+d := by
      have h : ((n-k:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.sub_le n k
      linarith [Nat.cast_nonneg (α := ℝ) d]
    have hcoef : ((n-k:ℕ):ℝ)*(r/((n:ℝ)+d)) ≤ r := by
      rcases eq_or_lt_of_le hd with hzero | hpos
      · rw [← hzero, div_zero, mul_zero]; exact hr
      · rw [mul_div_assoc]
        apply (div_le_iff₀ hpos).2
        exact mul_le_mul_of_nonneg_right hn hr
    have he := oddsWeight_step r d n k
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
    apply (le_div_iff₀ (mul_pos hk hf)).2
    calc
      _ = (((n-k:ℕ):ℝ)*(r/((n:ℝ)+d)))*oddsWeight r d n k*(k.factorial:ℝ) := by
        rw [← he]; ring
      _ ≤ r*oddsWeight r d n k*(k.factorial:ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef
          (oddsWeight_nonneg r hr d n k)) hf.le
      _ ≤ r*(r^k/(k.factorial:ℝ))*(k.factorial:ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ih hr) hf.le
      _ = _ := by field_simp [hf.ne'] <;> ring

theorem oddsCoefficient_tendsto (r : ℝ) (d k : ℕ) :
    Tendsto (fun n : ℕ => ((n-k:ℕ):ℝ)*(r/((n:ℝ)+d))) atTop (𝓝 r) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+d) atTop atTop :=
    tendsto_atTop_add_const_right atTop (d:ℝ) tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp ht
  have hl : Tendsto (fun n : ℕ => r-r*((k:ℝ)+d)*((n:ℝ)+d)⁻¹) atTop (𝓝 r) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).sub
      (hi.const_mul (r*((k:ℝ)+d))))
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (k+1)] with n hn
  have hkn : k ≤ n := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : 0 < (n:ℝ)+d := add_pos_of_pos_of_nonneg hnpos (Nat.cast_nonneg d)
  rw [Nat.cast_sub hkn]
  field_simp [hd.ne'] <;> ring

theorem oddsWeight_tendsto (r : ℝ) (d k : ℕ) :
    Tendsto (fun n : ℕ => oddsWeight r d n k) atTop (𝓝 (r^k/(k.factorial:ℝ))) := by
  induction k with
  | zero => simpa [oddsWeight] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  | succ k ih =>
    have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
    have he (n : ℕ) : oddsWeight r d n (k+1) =
        (((n-k:ℕ):ℝ)*(r/((n:ℝ)+d)))*oddsWeight r d n k/((k:ℝ)+1) := by
      apply (eq_div_iff hk.ne').2
      rw [mul_comm, oddsWeight_step]
    have hl := ((oddsCoefficient_tendsto r d k).mul ih).div_const ((k:ℝ)+1)
    simp_rw [he]
    convert hl using 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
    have hf : (0:ℝ) < (k.factorial:ℝ) := by positivity
    field_simp [hk.ne', hf.ne'] <;> ring

/-- Convergence of weighted odds expectations under a summable
factorial majorant. The test function need not be bounded. -/
theorem odds_tsum_tendsto (r : ℝ) (hr : 0 ≤ r) (d : ℕ) (f : ℕ → ℝ)
    (hs : Summable (fun k => (r^k/(k.factorial:ℝ))*‖f k‖)) :
    Tendsto (fun n : ℕ => ∑' k, oddsWeight r d n k * f k) atTop
      (𝓝 (∑' k, (r^k/(k.factorial:ℝ))*f k)) := by
  apply tendsto_tsum_of_dominated_convergence hs
  · intro k
    exact (oddsWeight_tendsto r d k).mul_const (f k)
  · exact Eventually.of_forall (fun n k => by
      rw [norm_mul, Real.norm_of_nonneg (oddsWeight_nonneg r hr d n k)]
      exact mul_le_mul_of_nonneg_right (oddsWeight_bound r hr d n k) (norm_nonneg _))

#print axioms oddsWeight_step
#print axioms oddsWeight_bound
#print axioms oddsCoefficient_tendsto
#print axioms oddsWeight_tendsto
#print axioms odds_tsum_tendsto

end F19.Pure


namespace F19.Pure
open scoped NNReal

theorem bernMean_one (p : ℝ) (n : ℕ) :
    bernMean p n (fun _ => 1) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bernMean, ih]; ring

noncomputable def oddsProb (r : ℝ) (d n : ℕ) : ℝ :=
  r/((n:ℝ)+d+r)

theorem binWeight_eq_odds (r : ℝ) (hr : 0 ≤ r) (d n k : ℕ)
    (hd : 0 < (n:ℝ)+d) :
    binWeight (oddsProb r d n) n k =
      (1-oddsProb r d n)^n * oddsWeight r d n k := by
  by_cases hk : k ≤ n
  · let t : ℝ := (n:ℝ)+d
    have ht : 0 < t := hd
    have htr : 0 < t+r := add_pos_of_pos_of_nonneg ht hr
    have he : oddsProb r d n = (1-oddsProb r d n)*(r/t) := by
      unfold oddsProb
      change r/(t+r) = (1-r/(t+r))*(r/t)
      field_simp [ht.ne', htr.ne'] <;> ring
    unfold binWeight oddsWeight
    change (n.choose k:ℝ)*(oddsProb r d n)^k*(1-oddsProb r d n)^(n-k) =
      (1-oddsProb r d n)^n*((n.choose k:ℝ)*(r/t)^k)
    have hp : (oddsProb r d n)^k = (1-oddsProb r d n)^k*(r/t)^k := by
      rw [← mul_pow, ← he]
    have hn : (1-oddsProb r d n)^n =
        (1-oddsProb r d n)^k*(1-oddsProb r d n)^(n-k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    rw [hp, hn]
    ring
  · have hlt : n < k := by omega
    rw [binWeight_outside _ n k hlt, oddsWeight_outside _ d n k hlt, mul_zero]

theorem odds_tsum_eq_sum (r : ℝ) (d n : ℕ) (f : ℕ → ℝ) :
    (∑' k, oddsWeight r d n k * f k) =
      ∑ k ∈ Finset.range (n+1), oddsWeight r d n k * f k := by
  apply tsum_eq_sum
  intro k hk
  have h : n < k := by
    simp only [Finset.mem_range, not_lt] at hk
    omega
  rw [oddsWeight_outside _ _ _ _ h, zero_mul]

theorem bernMean_odds (r : ℝ) (hr : 0 ≤ r) (d n : ℕ)
    (hd : 0 < (n:ℝ)+d) (f : ℕ → ℝ) :
    bernMean (oddsProb r d n) n f =
      (∑' k, oddsWeight r d n k*f k)/(∑' k, oddsWeight r d n k) := by
  rw [odds_tsum_eq_sum, odds_tsum_eq_sum]
  have h (g : ℕ → ℝ) : bernMean (oddsProb r d n) n g =
      (1-oddsProb r d n)^n * ∑ k ∈ Finset.range (n+1), oddsWeight r d n k*g k := by
    rw [bernMean_binomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [binWeight_eq_odds r hr d n k hd]
    ring
  have hmass := h (fun _ => 1)
  rw [bernMean_one] at hmass
  simp only [mul_one] at hmass
  have hden : (∑ k ∈ Finset.range (n+1), oddsWeight r d n k) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hmass
    norm_num at hmass
  have hmass' : (1-oddsProb r d n)^n *
      (∑ k ∈ Finset.range (n+1), oddsWeight r d n k) = 1 := hmass.symm
  simp only [mul_one]
  rw [h f]
  apply (eq_div_iff hden).2
  rw [mul_assoc, mul_comm (∑ k ∈ Finset.range (n+1), oddsWeight r d n k*f k),
    ← mul_assoc, hmass', one_mul]

/-- Law of small numbers for test functions dominated by a summable
factorial envelope, in expectation rather than merely in distribution. -/
theorem bernMean_poisson_tendsto (r : ℝ≥0) (d : ℕ) (f : ℕ → ℝ)
    (hs : Summable (fun k => ((r:ℝ)^k/(k.factorial:ℝ))*‖f k‖)) :
    Tendsto (fun n : ℕ => bernMean (oddsProb r d n) n f) atTop
      (𝓝 (∑' k, ProbabilityTheory.poissonPMFReal r k*f k)) := by
  have hmass : HasSum (fun k : ℕ => (r:ℝ)^k/(k.factorial:ℝ)) (Real.exp r) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ (r:ℝ)
  have hnum := odds_tsum_tendsto (r:ℝ) r.property d f hs
  have hden := odds_tsum_tendsto (r:ℝ) r.property d (fun _ => 1)
    (by simpa using hmass.summable)
  simp only [mul_one, hmass.tsum_eq] at hden
  have hl := hnum.div hden (Real.exp_ne_zero _)
  have he : (∑' k, ProbabilityTheory.poissonPMFReal r k*f k) =
      (∑' k, ((r:ℝ)^k/(k.factorial:ℝ))*f k)/Real.exp r := by
    unfold ProbabilityTheory.poissonPMFReal
    have h (k : ℕ) : Real.exp (-(r:ℝ))*(r:ℝ)^k/(k.factorial:ℝ)*f k =
        (Real.exp (r:ℝ))⁻¹ * (((r:ℝ)^k/(k.factorial:ℝ))*f k) := by
      rw [Real.exp_neg]; ring
    simp_rw [h, tsum_mul_left]
    ring
  rw [he]
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : 0 < (n:ℝ)+d := add_pos_of_pos_of_nonneg hn' (Nat.cast_nonneg d)
  rw [bernMean_odds (r:ℝ) r.property d n hd]
  simp only [mul_one]

#print axioms binWeight_eq_odds
#print axioms bernMean_odds
#print axioms bernMean_poisson_tendsto

end F19.Pure


namespace F19.Pure
open scoped NNReal

theorem oddsProb_nonneg (r : ℝ) (hr : 0 ≤ r) (d n : ℕ) :
    0 ≤ oddsProb r d n := by
  unfold oddsProb
  positivity

theorem oddsProb_le_one (r : ℝ) (hr : 0 ≤ r) (d n : ℕ)
    (hd : 0 < (n:ℝ)+d) : oddsProb r d n ≤ 1 := by
  unfold oddsProb
  apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hd hr)).2
  linarith

theorem oddsProb_tendsto_zero (r : ℝ) (d : ℕ) :
    Tendsto (fun n => oddsProb r d n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+d+r) atTop atTop :=
    tendsto_atTop_add_const_right atTop r
      (tendsto_atTop_add_const_right atTop (d:ℝ) tendsto_natCast_atTop_atTop)
  have hi := tendsto_inv_atTop_zero.comp ht
  simpa [oddsProb, div_eq_mul_inv] using hi.const_mul r

theorem oddsProb_poincare_factor (r : ℝ≥0) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)*oddsProb (r:ℝ) 1 n*(1-oddsProb (r:ℝ) 1 n))
      atTop (𝓝 (r:ℝ)) := by
  have hp := oddsProb_tendsto_zero (r:ℝ) 1
  have he (n : ℕ) : ((n:ℝ)+1)*oddsProb (r:ℝ) 1 n = (r:ℝ)*(1-oddsProb (r:ℝ) 1 n) := by
    unfold oddsProb
    have hd : 0 < (n:ℝ)+1+(r:ℝ) := by positivity
    field_simp [hd.ne'] <;> ring
  simp_rw [he]
  have ht : Tendsto (fun n : ℕ => 1-oddsProb (r:ℝ) 1 n) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hp)
  simpa using (ht.const_mul (r:ℝ)).mul ht

/-- Poisson Poincare inequality for functions with summable factorial
envelopes for their first and second moments and squared increments. -/
theorem poisson_poincare (r : ℝ≥0) (f : ℕ → ℝ)
    (hm : Summable (fun k => ((r:ℝ)^k/(k.factorial:ℝ))*‖f k‖))
    (hs : Summable (fun k => ((r:ℝ)^k/(k.factorial:ℝ))*‖(f k)^2‖))
    (hd : Summable (fun k => ((r:ℝ)^k/(k.factorial:ℝ))*‖deltaSq f k‖)) :
    (∑' k, ProbabilityTheory.poissonPMFReal r k*(f k)^2) -
        (∑' k, ProbabilityTheory.poissonPMFReal r k*f k)^2 ≤
      (r:ℝ)*(∑' k, ProbabilityTheory.poissonPMFReal r k*deltaSq f k) := by
  let p : ℕ → ℝ := oddsProb (r:ℝ) 1
  have hfirst (g : ℕ → ℝ)
      (hg : Summable (fun k => ((r:ℝ)^k/(k.factorial:ℝ))*‖g k‖)) :
      Tendsto (fun n => bernMean (p n) (n+1) g) atTop
        (𝓝 (∑' k, ProbabilityTheory.poissonPMFReal r k*g k)) := by
    have h := (bernMean_poisson_tendsto r 0 g hg).comp (tendsto_add_atTop_nat 1)
    simpa [p, oddsProb, Nat.cast_add] using h
  exact poincare_limit (r:ℝ) p f _ _ _
    (fun n => oddsProb_nonneg _ r.property 1 n)
    (fun n => oddsProb_le_one _ r.property 1 n (by positivity))
    (hfirst f hm) (hfirst (fun k => (f k)^2) hs)
    (bernMean_poisson_tendsto r 1 (deltaSq f) hd) (oddsProb_poincare_factor r)

#print axioms oddsProb_poincare_factor
#print axioms poisson_poincare

end F19.Pure
