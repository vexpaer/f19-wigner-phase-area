
import F19.Algebra

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
      apply Finset.sum_congr rfl
      intro n hn
      ring

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
