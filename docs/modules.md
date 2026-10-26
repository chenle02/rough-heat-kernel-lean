---
layout: page
title: Module and API map
---
# Module and API map

The umbrella `RoughHeatKernel.lean` imports all fifteen modules below. There are 142 public theorem/lemma declarations; the [index](declarations.md) names each one.

<div class="table-scroll" markdown="1">

| Module | Public theorems | API boundary |
|---|---:|---|
| Kernel | 15 | One-dimensional variance-t Gaussian kernel, mass and semigroup |
| Lq | 4 | Exact kernel Lq norms and constants, including q = infinity |
| Gaussian | 3 | Mathlib Gaussian density and integration bridges |
| Tempered | 19 | Gaussian-tempered positive measures, convergent flows, joint positive-time continuity, weighted and local bounds |
| RoughMeasure | 10 | Signed Jordan pairs, total variation, positive/Dirac/Lebesgue constructors |
| Finite | 12 | Finite data, Mathlib SignedMeasure bridge, genuinely signed example |
| Increments | 12 | First derivatives, moments and spatial/time L1 kernel increments |
| ChenDalang | 11 | Gaussian product/comparison, shifted semigroup identity, quadratic convolution estimate and its pointwise-in-time step, Bochner-to-lower-integral bound, local finiteness |
| SquareKernel | 4 | Squared-kernel identity, arcsine integral, white-noise-shaped deterministic convolution bound |
| FlowSemigroup | 2 | Positive heat-flow semigroup and its time integral |
| Doubled | 6 | Gaussian doubling and time-resolved doubled-profile bounds |
| SpatialEnvelope | 11 | Uniform quarter-Hölder Gaussian envelope with a universal numerical constant |
| Beta | 2 | Real Beta integral on [0, t] and integrability of its integrand |
| Scaled | 2 | Squared-kernel and semigroup identities for the diffusion-scale kernel heatKernel (ν * t) |
| Erf | 29 | Error function (derivative, parity, signs, limits), standard normal density (mass one) and distribution function (bounds, monotonicity), Φ–erf identity, Gamma series for e^{z²}(1 + erf z) |

</div>

## Measures and flows

`IsGaussianTempered` requires a finite Gaussian-weighted mass for every positive Gaussian exponent. It permits infinite total mass. `RoughMeasure` records mutually singular positive and negative tempered measures; their sum is its total variation. Mathlib's finite SignedMeasure is a source for this construction, not the general model for infinite-mass data.

`heatFlow` is real-valued and uses Bochner integration. `lheatFlow` uses nonnegative extended-real lower integration and is defined for every measure. Conversion to real values requires finiteness; the library proves that for tempered data at positive times.

## Special functions

`erf x = (2/√π) ∫_0^x e^{-t²} dt` is an oriented interval integral, written exactly as TauCeti's `erf`, so a later bridge is definitional; `erfc = 1 - erf`. `normalCDF x` integrates the standard normal density over `(-∞, x]`. The series `hasSum_pow_div_Gamma` is DLMF 7.6.2 reindexed and assumes `z ≥ 0`. The Beta integral `integral_rpow_mul_sub_rpow` is DLMF 5.12.1 scaled to `[0, t]` and assumes `a, b, t > 0`.

## Limitations

Joint positive-time continuity is established in the source for positive and signed Gaussian-tempered data. Initial weak trace and continuity at time zero remain outside the API. The squared-kernel convolution estimate is deterministic; its stochastic interpretation does not add a stochastic integral construction to this package.
