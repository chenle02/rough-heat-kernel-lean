# Receipts

## `d4b9322`: lower-tier receipt, systemd unit rough-heat-kernel-causal-20261028.service

- Receipt: `d4b9322-official-native.json`. systemd --user unit `rough-heat-kernel-causal-20261028.service`, invocation `78aeb7665cf84a2394d89cfab8cf914d` on `h-2db2e0fa6029`:
  Result success, exit `0`; runtime 00:06:22.37, CPU 00:07:57.93, memory peak 2.1 GiB; caps MemoryMax 12.0 GiB, MemorySwapMax 0 B, CPUQuota 200%, RuntimeMax 45min.
- Producer: lean-pkg 0.20.0 (installed), sources SHA-256 `558e6675cac80492b5ba57c2b12541b7cc408e6abf01b6cc7dc6b727fab8ea84`; unchanged from run start to collection.
- Checker: verify.sh (fresh complete library/reference/tests; all-owned/strict controls/native replay); sorry_count 0; axioms Classical.choice, Quot.sound, propext.
- Log: `d4b93224f565-systemd-user-rough-heat-kernel-causal-20261028.service-78aeb7665cf84a2394d89cfab8cf914d-h-2db2e0fa6029-verify.redacted.log.gz` (SHA-256 of decompressed log), SHA-256 `f633e27fa836c04407f767e1f30ac23b49289e052b312db7fc9949f1482a9c5b` (= `report_sha256`);
  raw log SHA-256 `86dbc4b3c21c19e90eb01b09b65f937475801a17aa3b35b02436b1abfe4b11c9` (1 line(s) differ: local paths redacted).
- Unit properties: `d4b93224f565-systemd-user-rough-heat-kernel-causal-20261028.service-78aeb7665cf84a2394d89cfab8cf914d-h-2db2e0fa6029-unit.properties`, SHA-256 `a5b7fb47e66f9217be421b7ce0f7ed06d91d08b107c7364d7dde96a31882b927` (captured before the unit was collected).
- Stored compressed: `d4b93224f565-systemd-user-rough-heat-kernel-causal-20261028.service-78aeb7665cf84a2394d89cfab8cf914d-h-2db2e0fa6029-verify.redacted.log.gz` (deterministic gzip, SHA-256 `6e57f406e0d0966e9db1a3b327248940fbc963a61c6143bb361453c1c416d615` = `report_compressed.sha256`; 3890972 bytes uncompressed). Restore: `gzip -dc d4b93224f565-systemd-user-rough-heat-kernel-causal-20261028.service-78aeb7665cf84a2394d89cfab8cf914d-h-2db2e0fa6029-verify.redacted.log.gz > d4b93224f565-systemd-user-rough-heat-kernel-causal-20261028.service-78aeb7665cf84a2394d89cfab8cf914d-h-2db2e0fa6029-verify.redacted.log`, then `sha256sum d4b93224f565-systemd-user-rough-heat-kernel-causal-20261028.service-78aeb7665cf84a2394d89cfab8cf914d-h-2db2e0fa6029-verify.redacted.log` prints `report_sha256`.
- Seal: job stdout SHA-256 `60722eaad858e590560a0a52d9649bbc025ed52c99f6647215cf7973ef8af717` carries verify-log-sha256 = raw log SHA-256 `86dbc4b3c21c19e90eb01b09b65f937475801a17aa3b35b02436b1abfe4b11c9`; lake-manifest.json SHA-256 `33928f37ec692b2b06a4da70ee2d832c381b1ed04218618fa3bccaf73a248494` (pre = post).
