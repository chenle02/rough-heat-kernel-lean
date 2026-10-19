# RoughHeatKernel agent guidance

Read README.md, docs/status.md and docs/trust.md before editing. Check Git status and preserve other contributors' work. Keep theorem scope deterministic: this package has no stochastic integration or SPDE well-posedness claim.

Use the pinned toolchain and Mathlib revision. Compile changed modules locally before any cluster submission; the cluster runs gates, not an edit-compile loop. Before a cluster gate, preflight every executable in the actual container and PATH. Use measured allocations and at most three Lean threads for Mathlib-heavy gates; system-wide file exhaustion calls for fewer threads, not excluding a node.

Retain exact theorem statements and assumptions. Keep the public theorem inventory, #check list and axiom list synchronized. Never fabricate a receipt, claim a historical receipt covers a changed scientific tree, or describe a comparator on selected statements as a whole-package independent replay.

Preserve existing copyright notices. Keep private paper labels, worker names, local paths and internal governance out of public documentation and history. Publication is coordinated by the repository owner after release checks.

After merged commits are durable on the remote, retire obsolete branches and isolated checkouts only after preserving unique source, uncommitted work, receipts, failed-run evidence and artifacts needed by active consumers. Confirm no live process uses a path before removal; record recovery evidence and measured reclaimed space.
