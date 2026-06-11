import Mathlib.Probability.Moments.SubGaussian

/-!
# Conditional Hoeffding lemma (the missing martingale-difference rung)

Mathlib (`Mathlib/Probability/Moments/SubGaussian.lean`) already proves:
* `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` — the *unconditional*
  Hoeffding lemma: a mean-zero r.v. a.s. in `Set.Icc a b` is sub-Gaussian with parameter
  `((b - a) / 2) ^ 2`.
* `ProbabilityTheory.HasCondSubgaussianMGF` — the conditional sub-Gaussian MGF predicate.
* `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF` — Azuma–Hoeffding, which
  *consumes* `HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i+1)) (cY (i+1)) μ` hypotheses.

What is **missing**: a producer that turns a bounded, conditionally-centered martingale
difference into a `HasCondSubgaussianMGF` term. Without it, Azuma cannot be discharged for a
concrete bounded forecaster. This is the conditional analogue of `hasSubgaussianMGF_of_mem_Icc`
and is upstreamable to Mathlib.

PROOF ROUTE: mirrors the unconditional proof but works under the conditional-expectation kernel
`condExpKernel μ m`. For `μ.trim`-a.e. `ω'`, the conditional law is a probability measure supported
in `[a, b]` with conditional mean `0`, so the pointwise Hoeffding MGF bound applies to each
`mgf X (condExpKernel μ m ω') t`. The statement keeps the parameter `((‖b - a‖₊ / 2) ^ 2)` and stays
faithful to Azuma's expected input, so it composes directly with
`measure_sum_ge_le_of_hasCondSubgaussianMGF`. Proved with no strengthened hypotheses; `#print axioms`
reports only `propext`, `Classical.choice`, `Quot.sound`.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}

/-- **Conditional Hoeffding lemma.** A random variable a.s. in `Set.Icc a b` whose conditional
expectation given `m` is `0` is conditionally sub-Gaussian with parameter `((b - a) / 2) ^ 2`. -/
lemma hasCondSubgaussianMGF_of_mem_Icc {a b : ℝ}
    (hX : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hc : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by
  -- For `μ.trim`-a.e. `ω'`, the conditional law `condExpKernel μ m ω'` is a probability measure
  -- supported in `[a, b]`.
  have hb_ker : ∀ᵐ ω' ∂(μ.trim hm), ∀ᵐ ω ∂(condExpKernel μ m ω'), X ω ∈ Set.Icc a b := by
    apply Measure.ae_ae_of_ae_comp
    rw [condExpKernel_comp_trim hm]
    exact hb
  -- a.e. the variable is measurable for the conditional law.
  have hX_ae : ∀ᵐ ω' ∂(μ.trim hm), AEStronglyMeasurable X (condExpKernel μ m ω') := by
    filter_upwards [aestronglyMeasurable_trim_condExpKernel hm hX.aestronglyMeasurable] with ω' hω'
    exact (hX.aestronglyMeasurable.stronglyMeasurable_mk).aestronglyMeasurable.congr hω'.symm
  -- a.e. the conditional mean is `0`.
  have hmean : ∀ᵐ ω' ∂(μ.trim hm), ∫ x, X x ∂(condExpKernel μ m ω') = 0 := by
    have hint : Integrable X μ := Integrable.of_mem_Icc a b hX hb
    have h1 := condExp_ae_eq_trim_integral_condExpKernel hm hint
    have h2 : (μ[X | m]) =ᵐ[μ.trim hm] 0 :=
      stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_const hc
    filter_upwards [h1, h2] with ω' h1' h2'
    rw [← h1', h2']
    rfl
  refine ⟨?_, ?_⟩
  · -- integrability of `exp (t * X)` against `condExpKernel μ m ∘ₘ μ.trim hm = μ`.
    intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hX hb
  · -- apply the pointwise Hoeffding MGF bound to each conditional law.
    filter_upwards [hb_ker, hmean, hX_ae] with ω' hb' hmean' hX' t
    exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hX'.aemeasurable hb' hmean').mgf_le t

end ProbabilityTheory
