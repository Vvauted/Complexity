# Execution measurements

The native `ram-demo` executable runs one fixed named RAM program that writes
`0, 1, ..., n-1` into memory and then sums those words in a second loop. Both
backends use the identical compiled instruction list, input, and budget. The
fast backend uses array instruction/register storage and a sparse balanced
tree map; the reference backend uses list fetch and functional update chains.
The `Fast.map_run` theorem proves equality of the complete decoded run result.

Measured on 0v0 with Lean 4.28.0-rc1 and the optimized default compiler, using
`lake build ram-demo` and the native
`.lake/build/bin/ram-demo` executable. Execution timing excludes compilation and
preparation but includes creation of the initial machine state. A non-inlined
IO boundary prevents pure execution from being moved past the end timestamp.
The initial timing attempt without that boundary was invalid and is excluded.

| Backend | Elements | Actual RAM steps | Output | Execution time |
| --- | ---: | ---: | ---: | ---: |
| Fast | 1,000 | 26,019 | 499,500 | 1.769903 ms |
| Reference | 1,000 | 26,019 | 499,500 | 233.804143 ms |
| Fast | 100,000 | 2,600,019 | 4,999,950,000 | 189.089122 ms |

All runs halted successfully. These are single-run observations on this server,
not universal speedup guarantees. The approximately 132-fold difference at
1,000 elements is specific to this workload, which exposes the reference
backend's historical lookup chains. RAM transition counts remain the formal
cost model; wall-clock timings describe the host interpreter implementation.

Reproduce on the server:

```sh
lake build ram-demo
.lake/build/bin/ram-demo fast 1000
.lake/build/bin/ram-demo reference 1000
.lake/build/bin/ram-demo fast 100000
```
