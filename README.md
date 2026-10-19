<div align="center">

<img src="docs/assets/mark.svg" width="88" height="88" alt="RoughHeatKernel abstract mark">

# RoughHeatKernel

[Documentation](https://chenle02.github.io/rough-heat-kernel-lean/) · [API](https://chenle02.github.io/rough-heat-kernel-lean/api.html) · [Verification](#verification-at-a-glance)

</div>

The one-dimensional heat kernel and the heat flow of rough positive and signed measures, formalized in Lean 4.

This library treats measures with Gaussian-tempered total variation: they may have infinite total mass, but their integral against every decaying Gaussian is finite. Dirac masses, finite signed measures and Lebesgue measure are examples. The results are standard analysis; no new mathematics is claimed.

**Source API 0.7.0.** This source contains 87 public theorems across 11 library modules and 33 curated reusable claims. Read [status](docs/status.md) for scope and the generated verification record below for exact source-bound evidence.

## What is proved

| Area | Results |
|---|---|
| Gaussian heat kernel | Positivity, mass one, convolution semigroup, Gaussian-density bridge, exact Lq norms including the supremum norm |
| Rough positive data | Absolute convergence, spatial continuity at fixed positive time, Gaussian growth, Gaussian-weighted integrability and local small-time bounds |
| Signed data | Jordan-pair rough measures, domination by total variation, Dirac and genuinely signed examples, finite Mathlib SignedMeasure interoperability |
| Kernel regularity | First spatial and time derivatives, Gaussian moments, spatial and forward-time L1 increment bounds |
| Convolution estimates | Chen–Dalang Gaussian quadratic bound, squared-kernel and arcsine identities, heat-flow semigroup, doubled-profile linear and quadratic bounds |

The [API guide](docs/modules.md) maps these results to modules. The [declaration index](docs/declarations.md) lists every public theorem, and [claims.yaml](claims.yaml) describes the reusable results currently registered.

## Scope and assumptions

The kernel has variance `t`, so its heat equation has diffusion coefficient `1/2`. Analytic statements assume positive time; at nonpositive times its definition has the junk value zero. Real-valued heat flows use Bochner integration and require the stated integrability hypotheses. Extended-real lower integrals are defined for arbitrary measures and may be infinite.

Heat-flow continuity here is spatial continuity for each fixed positive time. Joint time-space continuity, weak convergence to initial data, higher dimensions, higher derivatives, Fourier estimates and stochastic integration are outside this release. The finite SignedMeasure bridge goes into RoughMeasure; there is no general converse API yet. No stochastic PDE well-posedness theorem is claimed.

## Build and use

Install [elan](https://github.com/leanprover/elan), then use the toolchain pinned in [lean-toolchain](lean-toolchain): currently Lean `v4.35.0`, with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get
lake build
LIBRARY_AUDIT_DIR="$PWD/.lake/native-audit" bash verify.sh "$PWD/.lake/verify.log"
```

Use `import RoughHeatKernel`, or a narrower module such as `import RoughHeatKernel.Increments`. [Examples](RoughHeatKernelTest/Examples.lean) cover finite, signed and infinite-mass data. The [getting-started guide](docs/getting-started.md) and [dependency guide](docs/dependency.md) explain reproducibility and the planned public dependency interface.

## Verification

The current verifier checks source policy, the exact 87-theorem inventory, compiler-owned declaration axiom dependencies (including private/generated helpers), elaborated types, examples and nine strict negative fixtures with separately compiled witnesses. Its permitted axioms are `Classical.choice`, `Quot.sound` and `propext`. The [trust guide](docs/trust.md) distinguishes these existing checks from the independent replay and statement-comparison work required before publication. Proof checking does not validate this prose or remove hypotheses from a theorem.

## Attribution and AI assistance

The rough-data framework and convolution estimates are based on Le Chen and Robert C. Dalang, *Moments and growth indices for the nonlinear stochastic heat equation with rough initial conditions*, Annals of Probability 43 (2015), 3006–3051. General Gaussian and measure-theoretic foundations come from Mathlib. See [NOTICE](NOTICE).

The original Lean development used Anthropic Claude under the author's direction. Release documentation and review also used OpenAI Codex. Mathematical statements, trust claims and publication decisions remain the author's responsibility.

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html).

## Author, license and citation

Le Chen, Auburn University. Licensed under [Apache-2.0](LICENSE). Citation metadata is in [CITATION.cff](CITATION.cff); record the exact source commit used. See [contribution guidance](CONTRIBUTING.md) and [agent guidance](AGENTS.md).

See the [verification recipe](docs/verification.md) for the exact command, required output variables and retained evidence.

<!-- lean-pkg:page:begin -->
## Verification at a glance

No verification record has been generated for this staging source.
<!-- lean-pkg:page:end -->
