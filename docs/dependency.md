# Use as a Lake dependency

Use the same lean-toolchain as this source, then add a require entry for package `RoughHeatKernel` from `https://github.com/chenle02/rough-heat-kernel-lean.git`. Select a published version tag or exact commit from the README verification record.

Run `lake update RoughHeatKernel` in your downstream project, obtain public dependency caches with `lake exe cache get`, and build your project. Import `RoughHeatKernel` or a narrower module. Inside a frozen verification replay, never run `lake update`: it changes the dependency pins.
