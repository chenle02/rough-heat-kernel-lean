# Contributing

Keep changes focused on the documented deterministic API. Include exact hypotheses and a small consumer example for an API change. Preserve source copyright notices and cite the primary source for imported mathematics. Distinguish a known-theorem formalization from a new mathematical claim.

Use the pinned Lean and Mathlib versions. Run `lake build` and `LIBRARY_AUDIT_DIR="$PWD/.lake/native-audit" bash verify.sh "$PWD/.lake/verify.log"` locally before requesting an expensive verification gate. Keep THEOREM_INVENTORY.txt, TypeCheck.lean and AxiomCheck.lean aligned when adding a public theorem. Add a meaningful expected-failure fixture when a missing hypothesis would make the result false.

Do not introduce unfinished proofs, project axioms or unchecked proof escapes. Standard axiom dependencies are limited to Classical.choice, Quot.sound and propext. Report the exact source commit and command output when discussing verification. A successful build alone does not constitute an independent replay or statement-comparison receipt.

Update the README and documentation when scope or assumptions change. Never place private manuscript material, machine paths, credentials or internal process notes in public source or history.
