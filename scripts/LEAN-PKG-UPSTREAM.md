# Build-log guard provenance

lake_hygiene.py is copied byte-for-byte from lean-pkg 0.18.0's installed distribution, under Apache-2.0. Its LICENSE is retained in tools/lean-pkg/LICENSE. The SHA-256 of the copied source is 9a35fda016964cabef85205904d8d2b131deeb680c931a1b099a14eb8ef8d3f1.

fresh_build.py is a thin project adapter: it calls upstream job_lines/restored_jobs unchanged and additionally requires an actual Built event for every expected source module. A later replay is allowed only after the exact same module's earlier Built event; an early replay or missing build is refused. Complete unfiltered ordered build logs are retained.
