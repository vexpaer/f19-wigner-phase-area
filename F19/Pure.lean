
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

/-- A useful form of the preceding result when the Husimi integrands admit
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
    have h' : N+1 ≤ n := hn
    exact_mod_cast (show N+1 ≤ n by omega)
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
  gcongr
  positivity

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
