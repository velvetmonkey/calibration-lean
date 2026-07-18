# calibration-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](Calibration)

**calibration-lean: Formal concentration tooling for verified forecast calibration in Lean 4.**

The missing martingale-difference rung between Mathlib's Hoeffding lemma and its Azuma-Hoeffding inequality, proved and ready to discharge concentration bounds for bounded online forecasters. **Zero `sorry`. Standard axioms only** (`propext`, `Classical.choice`, `Quot.sound`).

## What this is, and why it matters

This library supplies a missing concentration lemma for martingale differences. Its headline result, `hasCondSubgaussianMGF_of_mem_Icc`, proves that an almost-everywhere measurable random variable bounded in `[a,b]` and conditionally centered at zero has the conditional sub-Gaussian moment bound expected by Mathlib's Azuma-Hoeffding theorem.

The result matters because it connects two existing pieces of Mathlib. The proof transfers boundedness and zero conditional mean to almost every conditional law, applies the ordinary Hoeffding bound there, and packages the result in the exact `HasCondSubgaussianMGF` form consumed by Azuma.

The scope is one concentration producer. This repository does not yet prove a forecast-calibration bound, certify an online forecaster, or complete the proposed Brier scoring loop. Those are downstream applications identified in the roadmap, not claims of the present theorem.

## Background and motivation

Mathlib already ships both ends of the concentration story for sub-Gaussian martingales:

* `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`: the **unconditional** Hoeffding lemma. A mean-zero random variable a.s. in `[a, b]` is sub-Gaussian with parameter `((b - a) / 2)²`.
* `HasCondSubgaussianMGF`: the **conditional** sub-Gaussian MGF predicate.
* `measure_sum_ge_le_of_hasCondSubgaussianMGF`: **Azuma-Hoeffding**, which *consumes* per-step `HasCondSubgaussianMGF` hypotheses.

What is **missing** is the producer: nothing turns a bounded, conditionally-centered martingale difference into a `HasCondSubgaussianMGF` term. Without it, Azuma cannot be discharged for a concrete bounded forecaster, because the inequality has no way to receive its hypotheses. This library proves that producer.

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `hasCondSubgaussianMGF_of_mem_Icc` | **Conditional Hoeffding lemma.** A random variable a.s. in `Set.Icc a b` whose conditional expectation given a sub-σ-algebra `m` is `0` is conditionally sub-Gaussian with parameter `((‖b - a‖₊ / 2)²)`. |

The statement is kept faithful to Azuma's expected input (`HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ`) so it composes directly with `measure_sum_ge_le_of_hasCondSubgaussianMGF`. No strengthened hypotheses.

### Proof route

Unfolding to `Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)`, the two structure fields are discharged through the conditional-expectation kernel:

* **Integrability** of `exp (t * X)` against `condExpKernel μ m ∘ₘ μ.trim hm = μ` (via `condExpKernel_comp_trim`) follows from `integrable_exp_mul_of_mem_Icc`.
* For `μ.trim`-a.e. `ω'`, the conditional law `condExpKernel μ m ω'` is a probability measure supported in `[a, b]` (transferring the a.s. bound through `Measure.ae_ae_of_ae_comp`) with conditional mean `0` (combining `condExp_ae_eq_trim_integral_condExpKernel` with the centering hypothesis pushed to the trimmed measure). The pointwise Hoeffding MGF bound then applies to each conditional law.

## Roadmap

This lemma is the concentration kernel. The arc it serves:

1. **Conditional Hoeffding producer.** Done (this repo).
2. **Calibration-error concentration.** Bound the deviation of empirical calibration error from its conditional mean for a bounded online forecaster, by feeding the per-step difference through this lemma into Azuma.
3. **Brier-loop certification.** Wire the concentration bound to the verifier-closed Brier scoring loop, so a forecaster's measured calibration carries a machine-checked confidence interval rather than an asserted one.

## Upstream

`hasCondSubgaussianMGF_of_mem_Icc` is the conditional analogue of an existing Mathlib lemma, sits in the same file's naming scheme, and fills a documented gap (predicate plus consumer present, producer absent). It is upstreamable to `Mathlib/Probability/Moments/SubGaussian.lean`. Contribution to Mathlib is planned via the standard Zulip-first process.

## Build

```sh
lake exe cache get
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain` (v4.28.0) and Mathlib at the matching rev.

## Related

Part of a family of Lean 4 verification libraries: [crdt-lean](https://github.com/velvetmonkey/crdt-lean) (CRDT convergence), [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) (phase synchrony), [online-learning-lean](https://github.com/velvetmonkey/online-learning-lean) (FTRL regret bounds).
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
