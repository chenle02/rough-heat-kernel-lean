# Mathematical scope and verification records

Source API 0.10.0 contains 120 inventoried public theorem/lemma declarations and 44 curated reusable claims across 15 library modules. Counts describe source inventory, not mathematical completion. New APIs give joint positive-time heat-flow continuity for positive and signed Gaussian-tempered data, and a uniform quarter-Hölder Gaussian envelope with constant 2*exp(1). Version 0.10.0 adds the real Beta integral on [0, t], squared-kernel and semigroup identities at diffusion scale ν, and an error-function API: erf, erfc, the standard normal density and distribution function, Φ(0) = 1/2, Φ' = density, Φ(x) = (1 + erf(x/√2))/2 and the series Σ z^k/Γ(k/2 + 1) = e^{z²}(1 + erf z) for z ≥ 0.

Verification of the 0.10.0 source is pending. Scientific source 3b16158a4974 (0.9.0) passed both verification tiers; scientific source 133f3aec2c12 passed complete fresh verification and all 37 independent three-kernel comparisons. Retained 0.7 receipts apply only to source cc5a8dba012b; the current receipts bind the additional scientific content. The generated README record and canonical receipts must identify the actual checked source.

No continuity at time zero, weak initial trace, stochastic sample-path modification or SPDE well-posedness is claimed.
