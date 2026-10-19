# Trust and reproducibility

Lean checks proof terms against their exact statements. It does not certify that a title, informal mathematical explanation or intended application describes that statement correctly. Hypotheses remain part of every claim.

## Existing verification script

`verify.sh LOG` performs a raw source policy scan, builds the library from fresh own outputs, checks import shadows, compares all 104 public source theorem/lemma names with the inventory and type/axiom test lists, prints each theorem's axiom closure, elaborates types, compiles usage examples and audits every compiler-owned production declaration, including private/generated helpers. Eleven disabled fixtures must each fail with exit 1, only unsolved-goal errors and the sole remaining goal False; each imports a separately compiled positive witness proving an actual counterexample. The original false mathematical mutations are retained as universal claims rather than asserting that every fixed parameter instance is false. The only permitted axiom names are Classical.choice, Quot.sound and propext.

The candidate content gate now also selects complete production/test and reference cones in separate environments, records exact first-provider object hashes, compiles three escape controls, and schedules per-module leanchecker replay. Actual execution and source-bound evidence are recorded in the README verification block and canonical receipts; scripts alone do not establish a pass. Statement comparison against the separately frozen references remains a distinct supported comparator gate. A lower receipt is not an independent comparator certificate.

The native inspection tool uses the pinned Apache-2.0 axiom-audit collector. Its project-wide forbidden-axiom union is the allowlist decision; per-declaration lists can undercount cyclic dependency clusters and are not advertised as canonical individual fingerprints. Inspection uses high-trust environment loading and is paired with separate kernel replay. See tools/axiom-audit/UPSTREAM.md for exact provenance and limits.

`verify.sh LOG` is the official receipt producer and must run only from the clean committed source to certify. The content runner `gate-content.sh` can be piloted against a source-file manifest without asserting that an old Git HEAD certifies uncommitted changes. Both require an absent `LIBRARY_AUDIT_DIR` for retained raw native reports.

## Required release checks

The publication gate must bind the exact final source, toolchain, dependency revisions, checker code and actual terminal result. Its complete owned-module/declaration audit must include private and generated declarations and explicit proof-escape controls. Independent statement comparison must cover the reusable theorem claims. Mathematical review checks assumptions and interpretation separately.

A fresh clean release tree must pass both a strict public-safety scan and independent human-style disclosure review. A published release tag identifies its scientific content and canonical receipts; rendered documentation is descriptive evidence, not another proof kernel.

## Reproduce current source

Use lean-toolchain and lake-manifest.json unchanged, then run the build and verifier commands in [getting started](getting-started.md). Record the exact source commit. Do not run lake update during a pristine replay: it changes dependency pins. A cache is a performance aid, not evidence by itself.

For the exact local command and required output variables, see [verification.md](verification.md).

Scientific source 133f3aec2c12 passed complete fresh verification and all 37 independent three-kernel comparisons. Earlier 0.7 receipts are historical authority only for their recorded source.
