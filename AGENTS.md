# RAM library development

This is an independent research library, not part of NyaOJ-bench.

- Local checkout: `/tmp/ram-lean`. Durable server repository: `/home/vvauted/ram-lean`
  on `vvauted@100.65.196.6` (`HostKeyAlias=0v0`).
- Do not run Lean or Lake locally. Compile only on 0v0 with the pinned rc1 toolchain.
- Root coordinates remote compilation. At most two Lean processes at once.
- The completed checkpoint uses normal Lake artifacts. Run `lake env lean`
  from the server repository for later file checks; source-root `.olean` files
  were scratch outputs from development and are not the authoritative build.
- Use `apply_patch` for edits. Preserve other agents' files. No benchmark edits.
- No `sorry`, custom axioms, unsafe proof shortcuts, or unproved cost annotations in
  completed modules. Incomplete work must stay explicitly described as incomplete.
- The user goal is the whole programming-language layer, including ordinary
  functions/recursion and arrays, with result-preserving compilation and costs
  derived from target execution. A working expression compiler is a milestone,
  not completion of that goal.
- Fix a finite instruction vocabulary; every machine transition contributes one
  step. Do not define source operation costs by a user-supplied table or ticks.
- Prove reusable semantic properties and representative programs. Do not add
  unrelated test frameworks, checksum machinery, or deployment infrastructure.
- Keep references and model limitations in `docs/`. Existing libraries are
  references, not evidence that our code is verified.
- Current compatible mathlib baseline, if needed:
  `5352afccd6866369be9de43f5b7ec47203555f44` (Lean 4.28.0-rc1).
  Keep the machine kernel dependent only on Lean/Std when possible.
