# Module and API map

The umbrella `RoughHeatKernel.lean` imports all twelve modules below. There are 104 public theorem/lemma declarations; the [index](declarations.md) names each one.

| Module | Public theorems | API boundary |
|---|---:|---|
| Kernel | 15 | One-dimensional variance-t Gaussian kernel, mass and semigroup |
| Lq | 4 | Exact kernel Lq norms and constants, including q = infinity |
| Gaussian | 3 | Mathlib Gaussian density and integration bridges |
| Tempered | 19 | Gaussian-tempered positive measures, convergent flows, joint positive-time continuity, weighted and local bounds |
| RoughMeasure | 10 | Signed Jordan pairs, total variation, positive/Dirac/Lebesgue constructors |
| Finite | 12 | Finite data, Mathlib SignedMeasure bridge, genuinely signed example |
| Increments | 12 | First derivatives, moments and spatial/time L1 kernel increments |
| ChenDalang | 6 | Gaussian product/comparison, quadratic convolution estimate, local finiteness |
| SquareKernel | 4 | Squared-kernel identity, arcsine integral, white-noise-shaped deterministic convolution bound |
| FlowSemigroup | 2 | Positive heat-flow semigroup and its time integral |
| Doubled | 6 | Gaussian doubling and time-resolved doubled-profile bounds |
| SpatialEnvelope | 11 | Uniform quarter-Hölder Gaussian envelope with a universal numerical constant |

## Measures and flows

`IsGaussianTempered` requires a finite Gaussian-weighted mass for every positive Gaussian exponent. It permits infinite total mass. `RoughMeasure` records mutually singular positive and negative tempered measures; their sum is its total variation. Mathlib's finite SignedMeasure is a source for this construction, not the general model for infinite-mass data.

`heatFlow` is real-valued and uses Bochner integration. `lheatFlow` uses nonnegative extended-real lower integration and is defined for every measure. Conversion to real values requires finiteness; the library proves that for tempered data at positive times.

## Limitations

Joint positive-time continuity is established in the source for positive and signed Gaussian-tempered data. Initial weak trace and continuity at time zero remain outside the API. The squared-kernel convolution estimate is deterministic; its stochastic interpretation does not add a stochastic integral construction to this package.
