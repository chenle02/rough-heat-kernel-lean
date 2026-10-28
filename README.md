<div align="center">

<img src="docs/assets/mark.svg" width="88" height="88" alt="RoughHeatKernel abstract mark">

# RoughHeatKernel

[Documentation](https://chenle02.github.io/rough-heat-kernel-lean/) · [API](https://chenle02.github.io/rough-heat-kernel-lean/api.html) · [Verification](#verification-at-a-glance)

</div>

Verified revision `00b39962d332`: the source adds deterministic causal heat-kernel L² continuity and weighted continuity, with 160 public theorems and 56 curated claims. A fresh native verification receipt binds source `00b39962d332`; all 56 curated statements passed the official three-kernel comparison. The published release records below retain their original source scope.

The one-dimensional heat kernel and the heat flow of rough positive and signed measures, formalized in Lean 4.

This library treats measures with Gaussian-tempered total variation: they may have infinite total mass, but their integral against every decaying Gaussian is finite. Dirac masses, finite signed measures and Lebesgue measure are examples. The results are standard analysis; no new mathematics is claimed.

**Historical source API 0.11.0 release.** Version 0.11.0 adds elementary facts about `erf`, `erfc` and the standard normal distribution function (derivatives, parity, signs, limits, bounds, monotonicity), makes the shifted semigroup identity `∫ p_a(y − m) p_b(x − y) dy = p_{a+b}(x − m)` and `lheatFlow_sq_eq` public, and adds the pointwise-in-time step of the Chen–Dalang estimate and the integrability-free bound `ofReal (∫ f) ≤ ∫⁻ ofReal f` for nonnegative `f`. Version 0.10.0 added `RoughHeatKernel.Beta`, `RoughHeatKernel.Scaled` and `RoughHeatKernel.Erf`. The source now has 142 public theorem/lemma declarations across 15 library modules and 51 curated reusable claims; every 0.10.0 statement, hypothesis and definition is unchanged. Scientific source `6a35f44f2d51` passed both verification tiers; receipts for 0.10.0 and earlier remain historical.

## What is proved

| Area | Results |
|---|---|
| Gaussian heat kernel | Positivity, mass one, convolution semigroup, Gaussian-density bridge, exact Lq norms including the supremum norm |
| Rough positive data | Absolute convergence, joint positive-time continuity, Gaussian growth, Gaussian-weighted integrability and local small-time bounds |
| Signed data | Jordan-pair rough measures, domination by total variation, Dirac and genuinely signed examples, finite Mathlib SignedMeasure interoperability |
| Kernel regularity | First spatial and time derivatives, Gaussian moments, spatial and forward-time L1 increments, uniform quarter-Hölder Gaussian envelope |
| Convolution estimates | Chen–Dalang Gaussian quadratic bound, squared-kernel and arcsine identities, heat-flow semigroup, doubled-profile linear and quadratic bounds |
| Diffusion-scale kernel | Squared-kernel and semigroup identities for the kernel `p_{νt}` of `∂_t u = (ν/2) ∂_x² u` |
| Special functions | Real Beta integral on `[0, t]`, error function, standard normal density and distribution function, `Φ(x) = (1 + erf(x/√2))/2`, Gamma series for `e^{z²}(1 + erf z)` |

The [API guide](docs/modules.md) maps these results to modules. The [declaration index](docs/declarations.md) lists every public theorem, and [claims.yaml](claims.yaml) describes the curated reusable source claims; registry acceptance is separate.

## Scope and assumptions

The kernel has variance `t`, so its heat equation has diffusion coefficient `1/2`. Analytic statements assume positive time; at nonpositive times its definition has the junk value zero. Real-valued heat flows use Bochner integration and require the stated integrability hypotheses. Extended-real lower integrals are defined for arbitrary measures and may be infinite.

Heat-flow continuity is joint in time and space at every strictly positive time, for positive and signed Gaussian-tempered data. The quarter-Hölder kernel envelope has the universal constant `2 * exp(1)`, before all positive times and spatial points. Continuity at time zero, weak convergence to initial data, higher dimensions, higher derivatives, Fourier estimates and stochastic integration remain outside this release. The finite SignedMeasure bridge goes into RoughMeasure; there is no general converse API yet. No stochastic PDE well-posedness theorem is claimed.

## Build and use

Install [elan](https://github.com/leanprover/elan), then use the toolchain pinned in [lean-toolchain](lean-toolchain): currently Lean `v4.35.0`, with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get
lake build
LIBRARY_AUDIT_DIR="$PWD/.lake/native-audit" bash verify.sh "$PWD/.lake/verify.log"
```

Use `import RoughHeatKernel`, or a narrower module such as `import RoughHeatKernel.Increments`. [Examples](RoughHeatKernelTest/Examples.lean) cover finite, signed and infinite-mass data. The [getting-started guide](docs/getting-started.md) and [dependency guide](docs/dependency.md) explain reproducibility and the public dependency interface.

## Verification

Scientific source `6a35f44f2d51` passed the complete fresh local verifier and independent three-kernel comparison for all 51 curated claims. The verifier checked all 142 public propositions, compiled-environment ownership and axiom dependencies for 326 production/positive-test declarations in 33 modules and 297 proved-reference declarations in 16 modules, elaborated types, examples and eleven strict negative fixtures with separately compiled witnesses, with compiled escape controls and exact native module replay. The permitted axioms are `Classical.choice`, `Quot.sound` and `propext`. The [trust guide](docs/trust.md) explains each check. Receipts bind the scientific source, dependency pins and retained outputs; proof checking does not validate this prose or remove hypotheses from a theorem.

## Attribution and AI assistance

The rough-data framework and convolution estimates are based on Le Chen and Robert C. Dalang, *Moments and growth indices for the nonlinear stochastic heat equation with rough initial conditions*, Annals of Probability 43 (2015), 3006–3051. General Gaussian and measure-theoretic foundations come from Mathlib. See [NOTICE](NOTICE).

The original Lean development used Anthropic Claude under the author's direction. Release documentation and review also used OpenAI Codex. Mathematical statements, trust claims and publication decisions remain the author's responsibility.

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
The verification record identifies the executors for this release. See the [historical resource acknowledgment](docs/citation.md#historical-compute) for earlier development.

## Author, license and citation

Le Chen, Auburn University. Licensed under [Apache-2.0](LICENSE). Citation metadata is in [CITATION.cff](CITATION.cff); record the exact source commit used. See [contribution guidance](CONTRIBUTING.md) and [agent guidance](AGENTS.md).

See the [verification recipe](docs/verification.md) for the exact command, required output variables and retained evidence.

## Verification record

The generated summary below preserves the source-freeze description “release verification pending” from `coverage.yaml`; that sentence records the pre-gate state. The current source-bound record covers **56 of 56 curated statements**, with both tiers passed at `d4b93224f565`; earlier receipts remain historical.

<!-- lean-pkg:page:begin -->
<!-- Generated by `lean-pkg page rough-heat-kernel` from coverage.yaml, claims.yaml, the claims ledger and the receipts committed under .lean-receipts/. Do not edit between the markers: change the data and run `lean-pkg page rough-heat-kernel --write`. -->

## Verification at a glance

**How to read this page.** Lean has checked every step of the proofs listed here. Each result is exactly its Lean statement: read the statements below to see what is proved. The titles, the words and the notes are the authors' description, which Lean does not check.

Deterministic one-dimensional Gaussian heat kernels, positive and signed Gaussian-tempered initial measures, kernel increments and rough-data convolution bounds. Causal and weighted continuity retain the explicit hypotheses in their declarations.

- Main results: 56; verified: 56 of 56.

## Main results

### Heat-kernel convolution semigroup

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Semigroup identity p_t * p_s = p_{t+s} for the 1-d heat kernel, as functions via Mathlib's convolution, for s,t > 0.
```

**In Lean.** `RoughHeatKernel.heatKernel_convolution_heatKernel` in [Challenge/Reference/RoughHeatKernel/Kernel.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Kernel.lean#L152): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem heatKernel_convolution_heatKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    convolution (heatKernel t) (heatKernel s) (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure ℝ) = heatKernel (t + s)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Exact heat-kernel Lq norm

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Exact L^q norm of the heat kernel for every q in [1, infinity]: C_q t^{-(1-1/q)/2} with an explicit constant.
```

**In Lean.** `RoughHeatKernel.eLpNorm_heatKernel` in [Challenge/Reference/RoughHeatKernel/Lq.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Lq.lean#L170): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem eLpNorm_heatKernel {q : ℝ≥0∞} (hq : 1 ≤ q) {t : ℝ} (ht : 0 < t) :
    eLpNorm (heatKernel t) q volume =
      ENNReal.ofReal (heatLqConst q * t ^ (-(1 - q⁻¹.toReal) / 2))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Spatial continuity of positive rough-data heat flow

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For a Gaussian-tempered positive measure (possibly of infinite mass) and t > 0, the heat flow x -> int p_t(x-y) nu(dy) is continuous.
```

**In Lean.** `RoughHeatKernel.continuous_heatFlow` in [Challenge/Reference/RoughHeatKernel/Tempered.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Tempered.lean#L144): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem continuous_heatFlow {ν : Measure ℝ} (hν : IsGaussianTempered ν) {t : ℝ}
    (ht : 0 < t) : Continuous (heatFlow ν t)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Gaussian-weighted Lp integrability

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Weighted bound for the heat flow of a Gaussian-tempered measure: e^{-a x^2} (heat flow)^p is integrable for a, t > 0, p >= 1.
```

**In Lean.** `RoughHeatKernel.integrable_exp_mul_heatFlow_rpow` in [Challenge/Reference/RoughHeatKernel/Tempered.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Tempered.lean#L283): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integrable_exp_mul_heatFlow_rpow {ν : Measure ℝ} (hν : IsGaussianTempered ν)
    {a t p : ℝ} (ha : 0 < a) (ht : 0 < t) (hp : 1 ≤ p) :
    Integrable (fun x => Real.exp (-a * x ^ 2) * (heatFlow ν t x) ^ p)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Local small-time heat-flow bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Local small-time bound: sqrt(s) times the heat flow of a Gaussian-tempered measure is bounded uniformly on s in (0,T], |y| <= R.
```

**In Lean.** `RoughHeatKernel.exists_sqrt_mul_heatFlow_le` in [Challenge/Reference/RoughHeatKernel/Tempered.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Tempered.lean#L395): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem exists_sqrt_mul_heatFlow_le {ν : Measure ℝ} (hν : IsGaussianTempered ν) {T : ℝ}
    (hT : 0 < T) (R : ℝ) :
    ∃ C : ℝ, ∀ s ∈ Set.Ioc 0 T, ∀ y : ℝ, |y| ≤ R → Real.sqrt s * heatFlow ν s y ≤ C
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Real and extended-real heat-flow conversion

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For a Gaussian-tempered measure and t > 0, the extended-real heat flow lheatFlow equals ofReal of the real heat flow (and is finite).
```

**In Lean.** `RoughHeatKernel.ofReal_heatFlow` in [Challenge/Reference/RoughHeatKernel/Tempered.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Tempered.lean#L194): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem ofReal_heatFlow {ν : Measure ℝ} (hν : IsGaussianTempered ν) {t : ℝ} (ht : 0 < t)
    (x : ℝ) : ENNReal.ofReal (heatFlow ν t x) = lheatFlow ν t x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Signed-flow domination by total variation

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For a signed measure with Gaussian-tempered total variation (Jordan pair), |heat flow of mu| <= heat flow of |mu|.
```

**In Lean.** `RoughHeatKernel.RoughMeasure.abs_heatFlow_le` in [Challenge/Reference/RoughHeatKernel/RoughMeasure.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/RoughMeasure.lean#L73): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem abs_heatFlow_le (μ : RoughMeasure) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |μ.heatFlow t x| ≤ RoughHeatKernel.heatFlow μ.totalVariation t x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Finite-data heat-flow bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For a finite signed measure, |heat flow| <= (2 pi t)^{-1/2} |mu|(R) at every point.
```

**In Lean.** `RoughHeatKernel.RoughMeasure.abs_heatFlow_le_of_isFiniteMeasure` in [Challenge/Reference/RoughHeatKernel/Finite.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Finite.lean#L47): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem abs_heatFlow_le_of_isFiniteMeasure (μ : RoughMeasure)
    [IsFiniteMeasure μ.totalVariation] {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |μ.heatFlow t x| ≤ 1 / Real.sqrt (2 * Real.pi * t) * (μ.totalVariation Set.univ).toReal
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Mathlib Gaussian-density bridge

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
The heat kernel is Mathlib's centred Gaussian density: heatKernel t = gaussianPDFReal 0 t.toNNReal for every real t.
```

**In Lean.** `RoughHeatKernel.heatKernel_eq_gaussianPDFReal` in [Challenge/Reference/RoughHeatKernel/Gaussian.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Gaussian.lean#L30): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem heatKernel_eq_gaussianPDFReal (t x : ℝ) :
    heatKernel t x = gaussianPDFReal 0 t.toNNReal x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Integration against a Gaussian law

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Integration against the normal law gaussianReal x t equals integration against heatKernel t (x - y), for t != 0.
```

**In Lean.** `RoughHeatKernel.integral_gaussianReal_eq_integral_heatKernel` in [Challenge/Reference/RoughHeatKernel/Gaussian.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Gaussian.lean#L53): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_gaussianReal_eq_integral_heatKernel {t : NNReal} (ht : t ≠ 0) (x : ℝ)
    (f : ℝ → ℝ) :
    ∫ y, f y ∂gaussianReal x t = ∫ y, heatKernel t (x - y) * f y
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Mathlib finite SignedMeasure bridge

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
A Mathlib SignedMeasure on R becomes a RoughMeasure via its Jordan decomposition; positive minus negative part recovers s, and the total variation is s.totalVariation.
```

**In Lean.** `RoughHeatKernel.RoughMeasure.toSignedMeasure_ofSignedMeasure` in [Challenge/Reference/RoughHeatKernel/Finite.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Finite.lean#L121): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem toSignedMeasure_ofSignedMeasure (s : SignedMeasure ℝ) :
    (ofSignedMeasure s).pos.toSignedMeasure - (ofSignedMeasure s).neg.toSignedMeasure = s
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Extended-real Gaussian-weight formula

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For every measure and every real t, the extended-real heat flow equals ofReal((2 pi t)^{-1/2}) times the lower integral of exp(-(x-y)^2/(2t)).
```

**In Lean.** `RoughHeatKernel.lheatFlow_eq_ofReal_mul_lintegral` in [Challenge/Reference/RoughHeatKernel/Tempered.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Tempered.lean#L206): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lheatFlow_eq_ofReal_mul_lintegral (ν : Measure ℝ) (t x : ℝ) :
    lheatFlow ν t x =
      ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi * t)) *
        ∫⁻ y, ENNReal.ofReal (Real.exp (-(x - y) ^ 2 / (2 * t))) ∂ν
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Rough measure from a tempered Jordan pair

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
A Jordan pair whose total variation pos + neg is Gaussian-tempered is a RoughMeasure (single-condition form of the class), with that total variation.
```

**In Lean.** `RoughHeatKernel.RoughMeasure.totalVariation_ofTempered` in [Challenge/Reference/RoughHeatKernel/RoughMeasure.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/RoughMeasure.lean#L92): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem totalVariation_ofTempered (pos neg : Measure ℝ) (h : pos ⟂ₘ neg)
    (hE : IsGaussianTempered (pos + neg)) :
    (ofTempered pos neg h hE).totalVariation = pos + neg
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Spatial L1 kernel increment

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Spatial L^1 increment of the 1-d heat kernel: int |p_t(x-y) - p_t(z-y)| dy <= min(2, |x-z|/sqrt t) for t > 0.
```

**In Lean.** `RoughHeatKernel.integral_abs_heatKernel_sub_sub_le` in [Challenge/Reference/RoughHeatKernel/Increments.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Increments.lean#L330): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_abs_heatKernel_sub_sub_le {t : ℝ} (ht : 0 < t) (x z : ℝ) :
    ∫ y, |heatKernel t (x - y) - heatKernel t (z - y)| ≤ min 2 (|x - z| / Real.sqrt t)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Forward-time L1 kernel increment

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Time L^1 increment of the 1-d heat kernel: int |p_{t+e}(x-y) - p_t(x-y)| dy <= min(2, e/t) for t > 0, e >= 0.
```

**In Lean.** `RoughHeatKernel.integral_abs_heatKernel_add_sub_le` in [Challenge/Reference/RoughHeatKernel/Increments.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Increments.lean#L345): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_abs_heatKernel_add_sub_le {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (x : ℝ) :
    ∫ y, |heatKernel (t + ε) (x - y) - heatKernel t (x - y)| ≤ min 2 (ε / t)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Time derivative of the heat kernel

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Time derivative of the heat kernel: d/dt p_t(x) = (x^2 - t)/(2 t^2) p_t(x) for t > 0 (the spatial one, -(x/t) p_t(x), is hasDerivAt_heatKernel).
```

**In Lean.** `RoughHeatKernel.hasDerivAt_heatKernel_time` in [Challenge/Reference/RoughHeatKernel/Increments.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Increments.lean#L59): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem hasDerivAt_heatKernel_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatKernel s x) ((x ^ 2 - t) / (2 * t ^ 2) * heatKernel t x) t
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### L1 mean-value inequality

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
L^1 mean-value inequality: if F has derivative F' in theta on [a,b], F' is continuous in theta for each y and jointly measurable, then int |F(b,y)-F(a,y)| dy <= int_a^b int |F'(theta,y)| dy dtheta (lower integrals).
```

**In Lean.** `RoughHeatKernel.lintegral_enorm_sub_le_lintegral` in [Challenge/Reference/RoughHeatKernel/Increments.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Increments.lean#L157): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_enorm_sub_le_lintegral {F F' : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ y, ∀ θ ∈ Icc a b, HasDerivAt (fun θ => F θ y) (F' θ y) θ)
    (hF'c : ∀ y, ContinuousOn (fun θ => F' θ y) (Icc a b))
    (hF'm : Measurable (Function.uncurry F')) :
    ∫⁻ y, ‖F b y - F a y‖ₑ ≤ ∫⁻ θ in Ioc a b, ∫⁻ y, ‖F' θ y‖ₑ
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Second Gaussian kernel moment

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Gaussian moments of the heat kernel: int x^2 p_t(x) dx = t, and int |x| p_t(x) dx <= sqrt t (integral_abs_mul_heatKernel_le), for t > 0.
```

**In Lean.** `RoughHeatKernel.integral_sq_mul_heatKernel` in [Challenge/Reference/RoughHeatKernel/Increments.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Increments.lean#L103): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_sq_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    ∫ x, x ^ 2 * heatKernel t x = t
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Chen–Dalang Gaussian convolution estimate

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Chen-Dalang estimate (Gaussian case): for s-finite nu, t > 0, measurable h >= 0, int_0^t int J(s,y)^2 p_{(t-s)/2}(x-y) h(t-s) dy ds <= 2 sqrt t J(2t,x)^2 int_0^t h(t-s)/sqrt s ds, J = lheatFlow nu (lower integrals).
```

**In Lean.** `RoughHeatKernel.lintegral_sq_lheatFlow_conv_le` in [Challenge/Reference/RoughHeatKernel/ChenDalang.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/ChenDalang.lean#L233): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_sq_lheatFlow_conv_le (ν : Measure ℝ) [SFinite ν] {t : ℝ} (ht : 0 < t)
    (x : ℝ) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ s in Ioo 0 t, ∫⁻ y, lheatFlow ν s y ^ 2 *
        ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * h (t - s) ≤
      ENNReal.ofReal (2 * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2 *
        ∫⁻ s in Ioo 0 t, h (t - s) * ENNReal.ofReal (1 / Real.sqrt s)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Gaussian product identity

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Gaussian product identity: p_t(y-z1) p_t(y-z2) = p_{2t}(z1-z2) p_{t/2}(y-(z1+z2)/2) for t > 0.
```

**In Lean.** `RoughHeatKernel.heatKernel_mul_heatKernel_eq` in [Challenge/Reference/RoughHeatKernel/ChenDalang.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/ChenDalang.lean#L72): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem heatKernel_mul_heatKernel_eq {t : ℝ} (ht : 0 < t) (y z₁ z₂ : ℝ) :
    heatKernel t (y - z₁) * heatKernel t (y - z₂) =
      heatKernel (2 * t) (z₁ - z₂) * heatKernel (t / 2) (y - (z₁ + z₂) / 2)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Heat-kernel comparison across times

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Heat-kernel comparison across times: p_a(x) <= sqrt(b/a) p_b(x) for 0 < a <= b.
```

**In Lean.** `RoughHeatKernel.heatKernel_le_sqrt_div_mul` in [Challenge/Reference/RoughHeatKernel/ChenDalang.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/ChenDalang.lean#L49): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem heatKernel_le_sqrt_div_mul {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    heatKernel a x ≤ Real.sqrt (b / a) * heatKernel b x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Local finiteness of Gaussian-tempered measures

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
A Gaussian-tempered measure on R is locally finite (finite on bounded sets), hence sigma-finite.
```

**In Lean.** `RoughHeatKernel.IsGaussianTempered.isLocallyFiniteMeasure` in [Challenge/Reference/RoughHeatKernel/ChenDalang.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/ChenDalang.lean#L288): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem IsGaussianTempered.isLocallyFiniteMeasure {ν : Measure ℝ} (hν : IsGaussianTempered ν) :
    IsLocallyFiniteMeasure ν
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Squared-kernel rough-data convolution bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
White-noise Chen-Dalang bound: for s-finite nu and t > 0, int_0^t int J(s,y)^2 p_{t-s}(x-y)^2 dy ds <= sqrt(pi) sqrt(t) J(2t,x)^2 with J = lheatFlow nu, as lower integrals.
```

**In Lean.** `RoughHeatKernel.lintegral_sq_lheatFlow_mul_heatKernel_sq_le` in [Challenge/Reference/RoughHeatKernel/SquareKernel.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/SquareKernel.lean#L146): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_sq_lheatFlow_mul_heatKernel_sq_le (ν : Measure ℝ) [SFinite ν] {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    ∫⁻ s in Ioo 0 t, ∫⁻ y, lheatFlow ν s y ^ 2 *
        ENNReal.ofReal (heatKernel (t - s) (x - y) ^ 2) ≤
      ENNReal.ofReal (Real.sqrt Real.pi * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Squared heat-kernel identity

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Squared heat kernel: p_r(z)^2 = p_{r/2}(z) (4 pi r)^{-1/2} for r > 0; hence int p_r^2 = (4 pi r)^{-1/2} (integral_heatKernel_sq).
```

**In Lean.** `RoughHeatKernel.heatKernel_sq_eq` in [Challenge/Reference/RoughHeatKernel/SquareKernel.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/SquareKernel.lean#L41): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem heatKernel_sq_eq {r : ℝ} (hr : 0 < r) (z : ℝ) :
    heatKernel r z ^ 2 = heatKernel (r / 2) z * (1 / Real.sqrt (4 * Real.pi * r))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Arcsine integral

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
The arcsine integral: int_0^t ds / sqrt(s (t - s)) = pi for t > 0, as a lower Lebesgue integral.
```

**In Lean.** `RoughHeatKernel.lintegral_arcsine` in [Challenge/Reference/RoughHeatKernel/SquareKernel.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/SquareKernel.lean#L88): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_arcsine {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Ioo 0 t, ENNReal.ofReal (1 / Real.sqrt (s * (t - s))) = ENNReal.ofReal Real.pi
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Positive heat-flow semigroup

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Heat-flow semigroup: for s-finite nu and 0 < s < t, int p_{t-s}(x-y) J(s,y) dy = J(t,x) with J = lheatFlow nu, as a lower integral.
```

**In Lean.** `RoughHeatKernel.lintegral_heatKernel_mul_lheatFlow` in [Challenge/Reference/RoughHeatKernel/FlowSemigroup.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/FlowSemigroup.lean#L62): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_heatKernel_mul_lheatFlow (ν : Measure ℝ) [SFinite ν] {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) * lheatFlow ν s y =
      lheatFlow ν t x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Time-integrated positive heat-flow semigroup

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Time-integrated heat-flow semigroup: for s-finite nu, int_0^t int p_{t-s}(x-y) J(s,y) dy ds = t J(t,x) with J = lheatFlow nu, as lower integrals.
```

**In Lean.** `RoughHeatKernel.lintegral_lintegral_heatKernel_mul_lheatFlow` in [Challenge/Reference/RoughHeatKernel/FlowSemigroup.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/FlowSemigroup.lean#L92): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_lintegral_heatKernel_mul_lheatFlow (ν : Measure ℝ) [SFinite ν] (t x : ℝ) :
    ∫⁻ s in Ioo 0 t, ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) * lheatFlow ν s y =
      ENNReal.ofReal t * lheatFlow ν t x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Gaussian doubling comparison

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For t > 0 and 0 <= s <= t, p_(t+s)(x) <= sqrt(2) p_(2t)(x).
```

**In Lean.** `RoughHeatKernel.heatKernel_add_le_sqrt_two_mul` in [Challenge/Reference/RoughHeatKernel/Doubled.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Doubled.lean#L42): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem heatKernel_add_le_sqrt_two_mul {s t : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (hst : s ≤ t)
    (ξ : ℝ) : heatKernel (t + s) ξ ≤ Real.sqrt 2 * heatKernel (2 * t) ξ
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Positive heat-flow doubling comparison

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For every positive measure nu, t > 0 and 0 <= s <= t, J(t+s,x) <= sqrt(2) J(2t,x), with J = lheatFlow nu.
```

**In Lean.** `RoughHeatKernel.lheatFlow_add_le_sqrt_two_mul` in [Challenge/Reference/RoughHeatKernel/Doubled.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Doubled.lean#L51): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lheatFlow_add_le_sqrt_two_mul (ν : Measure ℝ) {s t : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hst : s ≤ t) (x : ℝ) :
    lheatFlow ν (t + s) x ≤ ENNReal.ofReal (Real.sqrt 2) * lheatFlow ν (2 * t) x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Doubled heat-flow semigroup identity

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For every s-finite nu and 0 < s < t, the lower integral of p_(t-s)(x-y) J(2s,y) equals J(t+s,x).
```

**In Lean.** `RoughHeatKernel.lintegral_heatKernel_mul_lheatFlow_two_mul` in [Challenge/Reference/RoughHeatKernel/Doubled.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Doubled.lean#L63): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_heatKernel_mul_lheatFlow_two_mul (ν : Measure ℝ) [SFinite ν] {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) * lheatFlow ν (2 * s) y =
      lheatFlow ν (t + s) x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Doubled heat-flow linear bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For every s-finite nu and 0 < s < t, the lower integral of p_(t-s)(x-y) J(2s,y) is at most sqrt(2) J(2t,x).
```

**In Lean.** `RoughHeatKernel.lintegral_heatKernel_mul_lheatFlow_two_mul_le` in [Challenge/Reference/RoughHeatKernel/Doubled.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Doubled.lean#L73): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_heatKernel_mul_lheatFlow_two_mul_le (ν : Measure ℝ) [SFinite ν] {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) * lheatFlow ν (2 * s) y ≤
      ENNReal.ofReal (Real.sqrt 2) * lheatFlow ν (2 * t) x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Doubled Gaussian product convolution bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For 0 < s < t, the lower integral of p_(2s)(y-z1) p_(2s)(y-z2) p_((t-s)/2)(x-y) is at most sqrt(2t/s) p_(2t)(x-z1) p_(2t)(x-z2).
```

**In Lean.** `RoughHeatKernel.lintegral_heatKernel_two_mul_mul_le` in [Challenge/Reference/RoughHeatKernel/Doubled.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Doubled.lean#L103): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_heatKernel_two_mul_mul_le {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (x z₁ z₂ : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (2 * s) (y - z₁)) *
        ENNReal.ofReal (heatKernel (2 * s) (y - z₂)) *
        ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) ≤
      ENNReal.ofReal (Real.sqrt (2 * t / s)) *
        (ENNReal.ofReal (heatKernel (2 * t) (x - z₁)) *
          ENNReal.ofReal (heatKernel (2 * t) (x - z₂)))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Doubled heat-flow quadratic bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For every s-finite nu and 0 < s < t, the lower integral of p_(t-s)(x-y)^2 J(2s,y)^2 is at most sqrt(t)/(sqrt(2*pi)*sqrt(s*(t-s))) J(2t,x)^2.
```

**In Lean.** `RoughHeatKernel.lintegral_heatKernel_sq_mul_lheatFlow_two_mul_sq_le` in [Challenge/Reference/RoughHeatKernel/Doubled.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Doubled.lean#L187): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_heatKernel_sq_mul_lheatFlow_two_mul_sq_le (ν : Measure ℝ) [SFinite ν]
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y) ^ 2) * lheatFlow ν (2 * s) y ^ 2 ≤
      ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi) * (Real.sqrt t / Real.sqrt (s * (t - s)))) *
        lheatFlow ν (2 * t) x ^ 2
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Local positive-time Gaussian domination

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Local Gaussian-square domination on a positive-time neighborhood with bounded output displacement; an explicit integrable envelope for continuity arguments.
```

**In Lean.** `RoughHeatKernel.heatKernel_sq_le_local` in [Challenge/Reference/RoughHeatKernel/Kernel.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Kernel.lean#L170): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem heatKernel_sq_le_local {t u s x z y : ℝ}
    (ht : 0<t) (hu0 : 3*t/4≤u) (hu1 : u≤5*t/4)
    (hs0 : 0≤s) (hs1 : s≤t/4) (hx : |x-z|≤1) :
    heatKernel (u-s) (x-y)^2 ≤
      (4*Real.exp (6/t))*heatKernel (2*t-s) (z-y)^2
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Joint positive-time heat-flow continuity

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Joint time-space continuity of the heat flow at every positive time for any Gaussian-tempered positive measure, including infinite mass.
```

**In Lean.** `RoughHeatKernel.continuousAt_heatFlow_joint` in [Challenge/Reference/RoughHeatKernel/Tempered.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Tempered.lean#L172): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem continuousAt_heatFlow_joint {ν : Measure ℝ}
    (hν : IsGaussianTempered ν) (a : ℝ × ℝ) (ha : 0<a.1) :
    ContinuousAt (fun z : ℝ × ℝ => RoughHeatKernel.heatFlow ν z.1 z.2) a
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Joint positive-time signed heat-flow continuity

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Joint time-space continuity at every positive time for signed Jordan data with Gaussian-tempered total variation; no finite-total-variation assumption.
```

**In Lean.** `RoughHeatKernel.RoughMeasure.continuousAt_heatFlow_joint` in [Challenge/Reference/RoughHeatKernel/RoughMeasure.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/RoughMeasure.lean#L61): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem continuousAt_heatFlow_joint (μ : RoughMeasure) (a : ℝ × ℝ) (ha : 0 < a.1) :
    ContinuousAt (fun z : ℝ × ℝ => μ.heatFlow z.1 z.2) a
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Uniform quarter-Hölder Gaussian envelope

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For all r>0 and u,v, |p_r(u)-p_r(v)| <= 2 exp(1) |u-v|^(1/4) r^(-1/8) (p_(2r)(u)+p_(2r)(v)); one numerical constant precedes all variables.
```

**In Lean.** `RoughHeatKernel.SpatialEnvelope.quarter_increment` in [Challenge/Reference/RoughHeatKernel/SpatialEnvelope.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/SpatialEnvelope.lean#L180): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem quarter_increment {r : ℝ} (hr : 0<r) (u v : ℝ) :
    |heatKernel r u-heatKernel r v| ≤
      (2*Real.exp 1)*|u-v|^(1/4:ℝ)*r^(-(1/8:ℝ))*
        (heatKernel (2*r) u+heatKernel (2*r) v)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Real Beta integral on \[0, t\]

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
int_0^t s^(a-1) (t-s)^(b-1) ds = t^(a+b-1) Gamma(a) Gamma(b)/Gamma(a+b) for a, b, t > 0 (DLMF 5.12.1, scaled).
```

**In Lean.** `RoughHeatKernel.integral_rpow_mul_sub_rpow` in [Challenge/Reference/RoughHeatKernel/Beta.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Beta.lean#L34): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_rpow_mul_sub_rpow {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    ∫ s in (0 : ℝ)..t, s ^ (a - 1) * (t - s) ^ (b - 1) =
      t ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Squared heat kernel at diffusion scale

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
p_(nu t)(x)^2 = p_((nu/2) t)(x) (4 pi nu)^(-1/2) t^(-1/2) for nu, t > 0.
```

**In Lean.** `RoughHeatKernel.heatKernel_mul_sq_eq` in [Challenge/Reference/RoughHeatKernel/Scaled.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Scaled.lean#L33): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem heatKernel_mul_sq_eq {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    heatKernel (ν * t) x ^ 2 =
      heatKernel (ν / 2 * t) x * (1 / Real.sqrt (4 * Real.pi * ν)) * t ^ (-(1 / 2 : ℝ))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Heat-kernel semigroup at diffusion scale

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
int p_(nu(t-s))(x-y) p_(nu s)(y) dy = p_(nu t)(x) for nu > 0 and 0 < s < t.
```

**In Lean.** `RoughHeatKernel.integral_heatKernel_mul_sub_mul` in [Challenge/Reference/RoughHeatKernel/Scaled.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Scaled.lean#L45): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_heatKernel_mul_sub_mul {ν s t : ℝ} (hν : 0 < ν) (hs : 0 < s) (hst : s < t)
    (x : ℝ) :
    ∫ y, heatKernel (ν * (t - s)) (x - y) * heatKernel (ν * s) y = heatKernel (ν * t) x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Standard normal distribution function at zero

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
The standard normal distribution function equals 1/2 at 0.
```

**In Lean.** `RoughHeatKernel.normalCDF_zero` in [Challenge/Reference/RoughHeatKernel/Erf.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Erf.lean#L112): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem normalCDF_zero : normalCDF 0 = 1 / 2
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Derivative of the standard normal distribution function

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
The standard normal distribution function has derivative (2 pi)^(-1/2) e^(-x^2/2) at every x.
```

**In Lean.** `RoughHeatKernel.hasDerivAt_normalCDF` in [Challenge/Reference/RoughHeatKernel/Erf.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Erf.lean#L127): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem hasDerivAt_normalCDF (x : ℝ) : HasDerivAt normalCDF (normalDensity x) x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Normal distribution function and the error function

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
normalCDF x = (1 + erf(x/sqrt 2))/2, with erf x = (2/sqrt pi) int_0^x e^(-t^2) dt.
```

**In Lean.** `RoughHeatKernel.normalCDF_eq_erf` in [Challenge/Reference/RoughHeatKernel/Erf.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Erf.lean#L162): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem normalCDF_eq_erf (x : ℝ) : normalCDF x = (1 + erf (x / Real.sqrt 2)) / 2
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Gamma-series for the error function

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For z >= 0, sum_k z^k / Gamma(k/2 + 1) = e^(z^2) (1 + erf z) (DLMF 7.6.2, reindexed).
```

**In Lean.** `RoughHeatKernel.hasSum_pow_div_Gamma` in [Challenge/Reference/RoughHeatKernel/Erf.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Erf.lean#L299): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem hasSum_pow_div_Gamma {z : ℝ} (hz : 0 ≤ z) :
    HasSum (fun k : ℕ => z ^ k / Real.Gamma ((k : ℝ) / 2 + 1))
      (Real.exp (z ^ 2) * (1 + erf z))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Pointwise-in-time Chen-Dalang heat-flow step

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For 0 < r < R and s-finite nu, int J(r,y)^2 p_((R-r)/2)(x-y) dy <= 2 sqrt(R/r) J(2R,x)^2, with J = lheatFlow nu.
```

**In Lean.** `RoughHeatKernel.lintegral_sq_lheatFlow_mul_le` in [Challenge/Reference/RoughHeatKernel/ChenDalang.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/ChenDalang.lean#L187): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_sq_lheatFlow_mul_le (ν : Measure ℝ) [SFinite ν] {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (x : ℝ) :
    ∫⁻ y, lheatFlow ν r y ^ 2 * ENNReal.ofReal (heatKernel ((R - r) / 2) (x - y)) ≤
      ENNReal.ofReal (2 * Real.sqrt (R / r)) * lheatFlow ν (2 * R) x ^ 2
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Shifted heat-kernel semigroup identity

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
int p_a(y-m) p_b(x-y) dy = p_(a+b)(x-m) for a, b > 0.
```

**In Lean.** `RoughHeatKernel.integral_heatKernel_sub_mul_heatKernel_sub` in [Challenge/Reference/RoughHeatKernel/ChenDalang.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/ChenDalang.lean#L110): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem integral_heatKernel_sub_mul_heatKernel_sub {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (x m : ℝ) :
    ∫ y, heatKernel a (y - m) * heatKernel b (x - y) = heatKernel (a + b) (x - m)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Bochner integral below the lower integral

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For nonnegative f, ofReal(int f dmu) <= int^- ofReal(f) dmu, with no integrability hypothesis.
```

**In Lean.** `RoughHeatKernel.ofReal_integral_le_lintegral` in [Challenge/Reference/RoughHeatKernel/ChenDalang.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/ChenDalang.lean#L220): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Normal distribution function at most one

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
The standard normal distribution function is at most 1.
```

**In Lean.** `RoughHeatKernel.normalCDF_le_one` in [Challenge/Reference/RoughHeatKernel/Erf.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Erf.lean#L393): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem normalCDF_le_one (x : ℝ) : normalCDF x ≤ 1
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Monotonicity of the normal distribution function

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
The standard normal distribution function is monotone.
```

**In Lean.** `RoughHeatKernel.normalCDF_monotone` in [Challenge/Reference/RoughHeatKernel/Erf.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Erf.lean#L398): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem normalCDF_monotone : Monotone normalCDF
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Limit of the error function at infinity

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
erf x tends to 1 as x tends to infinity.
```

**In Lean.** `RoughHeatKernel.tendsto_erf_atTop` in [Challenge/Reference/RoughHeatKernel/Erf.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Erf.lean#L350): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem tendsto_erf_atTop : Filter.Tendsto erf Filter.atTop (nhds 1)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Derivative of the error function

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
erf has derivative (2/sqrt pi) e^(-x^2) at every x.
```

**In Lean.** `RoughHeatKernel.hasDerivAt_erf` in [Challenge/Reference/RoughHeatKernel/Erf.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/Erf.lean#L314): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem hasDerivAt_erf (x : ℝ) : HasDerivAt erf (2 / √π * exp (-x ^ 2)) x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Causal kernel squared norm

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For positive diffusivity, every real output time has the exact causal-kernel squared L2 norm, including zero norm at nonpositive time.
```

**In Lean.** `RoughHeatKernel.CausalHeatKernel.lintegral_heatK_sq` in [Challenge/Reference/RoughHeatKernel/CausalHeatKernel.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/CausalHeatKernel.lean#L159): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem lintegral_heatK_sq {ν : ℝ} (hν : 0 < ν) (t x : ℝ) :
    ∫⁻ w, ENNReal.ofReal (heatK ν t x w.1 w.2 ^ 2) ∂positiveTimeSpaceVolume =
      ENNReal.ofReal (Real.sqrt (t / (π * ν)))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Square-integrable causal sections

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Every causal heat-kernel section belongs to L2 over positive-time space for positive diffusivity.
```

**In Lean.** `RoughHeatKernel.CausalHeatKernel.memLp_heatK` in [Challenge/Reference/RoughHeatKernel/CausalHeatKernel.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/CausalHeatKernel.lean#L178): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem memLp_heatK {ν : ℝ} (hν : 0 < ν) (t x : ℝ) :
    MemLp (fun w : ℝ × ℝ => heatK ν t x w.1 w.2) 2 positiveTimeSpaceVolume
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Joint causal kernel L2 continuity

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Causal heat-kernel sections vary jointly continuously in output time and space in L2, including nonpositive output time.
```

**In Lean.** `RoughHeatKernel.CausalHeatKernel.tendsto_heatK_sq` in [Challenge/Reference/RoughHeatKernel/CausalHeatKernel.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/CausalHeatKernel.lean#L323): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem tendsto_heatK_sq {ν : ℝ} (hν : 0 < ν) (z : ℝ × ℝ) :
    Tendsto (fun z' : ℝ × ℝ => ∫⁻ w : ℝ × ℝ,
      ENNReal.ofReal ((heatK ν z'.1 z'.2 w.1 w.2 - heatK ν z.1 z.2 w.1 w.2) ^ 2)
        ∂positiveTimeSpaceVolume) (𝓝 z) (𝓝 0)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Sufficient far-space Gaussian margin

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
A fixed later-output Gaussian dominates nearby-output kernels outside the stated explicit spatial radius, at unchanged positive diffusivity.
```

**In Lean.** `RoughHeatKernel.WeightedCausalHeatKernel.heatKernel_sq_le_future_of_far` in [Challenge/Reference/RoughHeatKernel/WeightedCausalHeatKernel.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/WeightedCausalHeatKernel.lean#L87): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem heatKernel_sq_le_future_of_far {ν t t' x x' s y : ℝ}
    (hν : 0 < ν) (ht : 0 < t)
    (_ht'lo : 3 * t / 4 ≤ t') (ht'hi : t' ≤ 5 * t / 4)
    (hx : |x' - x| ≤ 1) (hslo : t / 4 ≤ s) (hshi : s < t')
    (hy : |x| + 8 * (1 + ν * t) ≤ |y|) :
    RoughHeatKernel.heatKernel (ν * (t' - s)) (x' - y) ^ 2 ≤
      RoughHeatKernel.heatKernel (ν * (2 * t - s)) (x - y) ^ 2
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Weighted causal kernel continuity

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
At positive output time, finite future weighted variance and a finite compact input-weight bound imply weighted squared-difference convergence; infinity is allowed outside the active region.
```

**In Lean.** `RoughHeatKernel.WeightedCausalHeatKernel.tendsto_weighted_sq_difference` in [Challenge/Reference/RoughHeatKernel/WeightedCausalHeatKernel.lean](https://github.com/chenle02/rough-heat-kernel-lean/blob/00b39962d3328088133a0b75c9f710b6834a463a/Challenge/Reference/RoughHeatKernel/WeightedCausalHeatKernel.lean#L172): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem tendsto_weighted_sq_difference {ν t x : ℝ}
    (hν : 0 < ν) (ht : 0 < t) (w : ℝ × ℝ → ℝ≥0∞) (hw : Measurable w)
    (hfuture : (∫⁻ q : ℝ × ℝ,
      ENNReal.ofReal (heatK ν (2 * t) x q.1 q.2 ^ 2) * w q ∂positiveTimeSpaceVolume) < ⊤)
    (hcompact : ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ q ∈ Icc (t / 4) (5 * t / 4) ×ˢ
        Icc (-(|x| + 8 * (1 + ν * t))) (|x| + 8 * (1 + ν * t)), w q ≤ B) :
    Tendsto (fun z : ℝ × ℝ => ∫⁻ q : ℝ × ℝ,
      ENNReal.ofReal ((heatK ν z.1 z.2 q.1 q.2 - heatK ν t x q.1 q.2) ^ 2) * w q
        ∂positiveTimeSpaceVolume) (𝓝 (t, x)) (𝓝 0)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

## What the checks establish

- **Every proof is checked by Lean.** The package builds; no `sorry` (an unfinished proof) remains; the only axioms used are `Classical.choice`, `Quot.sound`, `propext` (allowed: `propext`, `Quot.sound`, `Classical.choice`).
- **The statements shown are the ones proved.** For 56 statement(s), a second checker (comparator) confirmed that the proof proves exactly the statement shown, with only the permitted axioms, and independent Lean kernels replayed the proof.
- **Not checked by any tool:** that a title or note describes its Lean statement. A definition listed under *Definitions checked by a person* is compared by name and type only.

The full account of what each check covers and what it takes on trust is lean-pkg's [trust model](https://github.com/lean-pkg/lean-pkg/blob/main/docs/trust-model.md).

## How this was checked

- lean-pkg's claims ledger: **ready**, every required claim is closed by the recorded receipts; 56 of 56 required claim(s) verified (`sha256:d935b7df69404558…`).
- Build check (`lean-pkg gate`) at commit `00b39962d332`: `sorry` count 0; axioms used: `Classical.choice`, `Quot.sound`, `propext`.
- Axioms of every claim: read from the built environment (Lean's `collectAxioms`) for all 56 claim(s) in `claims.yaml`, not only the theorems the build prints; none uses an axiom beyond `propext`, `Quot.sound` and `Classical.choice`.
- Statement comparison (comparator) at commit `00b39962d332`: 1 configuration(s), 56 theorem(s) compared (each Challenge statement against its Solution proof); permitted axioms: `Classical.choice`, `Quot.sound`, `propext`; definitions compared by name only: none.

### Receipts

| Receipt | Check | Commit | Date | Job | SHA-256 |
|---|---|---|---|---|---|
| `.lean-receipts/00b3996-official-native.json` | build | `00b39962d332` | 2026-10-28 | — | `672036d51b0ae0911f99f290653b0482d7fe7ef337e06e6a2e515bdf7faac90f` |
| `.lean-receipts/00b39962d332-comparator.json` (used here) | statement comparison | `00b39962d332` | 2026-10-28 | — | `f61af29c140377bf4a008ebbeec8db153a575e5291b59282e540adddf0993b96` |
| `.lean-receipts/00b39962d332-systemd-user-rough-heat-kernel-coverage-20261028.service-e74e226401ba430eb1cdd5394138c0fa-h-2db2e0fa6029.json` (used here) | build | `00b39962d332` | 2026-10-28 | — | `672036d51b0ae0911f99f290653b0482d7fe7ef337e06e6a2e515bdf7faac90f` |
| `.lean-receipts/0ca762dbce91-comparator.json` | statement comparison | `0ca762dbce91` | 2026-10-26 | — | `073809f696e8928f11eae593d01fb7a8f96666366ed20f0c5b4fb8f9dd05290c` |
| `.lean-receipts/0ca762dbce91-systemd-user-rough-heat-kernel-v0100-p14s.service-01e3aee066f0489b8c9ee3ebdf69e091-h-2db2e0fa6029.json` | build | `0ca762dbce91` | 2026-10-26 | — | `a7622d63fc16b8c437fce5e72898d79cbd6c731e20eba8455b01259eb3c56da3` |
| `.lean-receipts/133f3aec2c12-comparator.json` | statement comparison | `133f3aec2c12` | 2026-10-19 | — | `30db14b96309aba3cf42554fe727add3521f099c42094160a3cba5eb2a2994a3` |
| `.lean-receipts/133f3aec2c12-systemd-user-rough-heat-kernel-v080-local2-20261019.service-d4ab772670254edebd6c0c1b12db247f-h-24e00fc5da6c.json` | build | `133f3aec2c12` | 2026-10-19 | — | `1f09392e95b179555ed4daaedcc30eff77a93c1255e6f5f000db010cd9c68463` |
| `.lean-receipts/3b16158a4974-comparator.json` | statement comparison | `3b16158a4974` | 2026-10-26 | — | `d8f17a81964ecacd8e709a6d066410955df914fea8c629f439fb575d22a0b038` |
| `.lean-receipts/3b16158a4974-systemd-user-rough-heat-kernel-v090-p14s-3.service-97086d43063c40a88fa4bbd3c083eb85-h-2db2e0fa6029.json` | build | `3b16158a4974` | 2026-10-26 | — | `760a848212ed328613a40a4ddf13b377ceac5cb2f7a83e84ce4a0f6ac25b3e9a` |
| `.lean-receipts/6a35f44f2d51-comparator.json` | statement comparison | `6a35f44f2d51` | 2026-10-26 | — | `a00616b5676d685e5a002d7ad7260ee53f3ff5c7ff896c5e27bab1816aeede15` |
| `.lean-receipts/6a35f44f2d51-systemd-user-rough-heat-kernel-v0110-p14s.service-11a0d698f32d4a27a624903fe1acdfb1-h-2db2e0fa6029.json` | build | `6a35f44f2d51` | 2026-10-26 | — | `7aadb5a95dc1a6dc5d693c261da250cbbd35fd22d9d2e6177c97415cb71dd61c` |
| `.lean-receipts/cc5a8dba012b-comparator.json` | statement comparison | `cc5a8dba012b` | 2026-10-19 | — | `9c29e2cb14b131c25813c79485a721e1dce8dfe0f87fe8864d3de839f0e91165` |
| `.lean-receipts/cc5a8dba012b-systemd-user-rough-heat-kernel-v070-local-20261019.service-f5cb65709f744525b784bcd5917d86e7-h-24e00fc5da6c.json` | build | `cc5a8dba012b` | 2026-10-19 | — | `118fe2fd8d74f2f80d07761fe64aeee26d15230d814941d8f295e6ff446847cd` |
| `.lean-receipts/d4b9322-official-native.json` | build | `d4b93224f565` | 2026-10-28 | — | `7d6bff3cd28b6cd6548fec713b8c20425f1275b8cf69a296f3db45a5b695a7a7` |
| `.lean-receipts/d4b93224f565-comparator.json` | statement comparison | `d4b93224f565` | 2026-10-28 | — | `d9851dfdada36a7a0cfe96d63e709384c9e4678ab254e603f76d6a053022cf2a` |
| `.lean-receipts/d4b93224f565-systemd-user-rough-heat-kernel-causal-20261028.service-78aeb7665cf84a2394d89cfab8cf914d-h-2db2e0fa6029.json` | build | `d4b93224f565` | 2026-10-28 | — | `7d6bff3cd28b6cd6548fec713b8c20425f1275b8cf69a296f3db45a5b695a7a7` |

*(used here)*: the receipt the lean-pkg registry holds for this package, which the lines above read. SHA-256 is of the file as committed.

### Reproduce

- Lean toolchain: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (lake-manifest.json).

```bash
git clone https://github.com/chenle02/rough-heat-kernel-lean
cd rough-heat-kernel-lean
git checkout 00b39962d3328088133a0b75c9f710b6834a463a   # the commit the build check binds
lake exe cache get
lake build
```

Expected: `#print axioms` on any declaration above reports a subset of {`Classical.choice`, `Quot.sound`, `propext`} (the union the build check records); `sorryAx` never appears.

## Citation

Le Chen. *RoughHeatKernel: the heat kernel and the heat flow of rough initial measures in Lean 4*. Version 0.11.0.

See [CITATION.cff](CITATION.cff).

## License

Released under `Apache-2.0`; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).

<!-- lean-pkg:page:end -->
