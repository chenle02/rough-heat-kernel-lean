# Print the fully qualified name of every public `theorem` or `lemma` in the given Lean files,
# tracking `namespace X` / `end X` blocks. `private theorem` is skipped.
FNR == 1 { n = 0 }
/^namespace [A-Za-z0-9_.]+/ { n++; ns[n] = $2; next }
/^end [A-Za-z0-9_.]+/ { if (n > 0 && ns[n] == $2) n--; next }
/^(theorem|lemma) [A-Za-z0-9_.]+/ {
  name = $2; prefix = ""
  for (i = 1; i <= n; i++) prefix = prefix ns[i] "."
  print prefix name
}
