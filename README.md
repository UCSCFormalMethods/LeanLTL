# LeanLTL
A unifying framework for linear temporal logics in Lean

# Building

The project is pinned to Lean 4.33.1 and the matching mathlib release. With
[`elan`](https://github.com/leanprover/elan) installed, run:

```sh
lake exe cache get
lake build
```

The default build checks both the core `LeanLTL` library and all `LeanLTLExamples`.

# Repository structure
The core library implementation can be found under the `LeanLTL/Trace`, `LeanLTL/TraceFun`, and `LeanLTL/TraceSet` directories. Various automation and utilities can be found under `LeanLTL/Tactics` and `LeanLTL/Utils`.

The following examples can be found under the `LeanLTLExamples` directory:
- `TrafficLights.lean`: An example proving useful properties given assumptions about the behavior of a pair of traffic lights.
- `Induction.lean`: An example of a proof of a LeanLTL formula containing quantifiers using induction. 
- `TeaserITP2025.lean`: A short proof from the introduction of our ITP 2025 submission.

Proofs of logical embeddings for the following logics can be found under the `LeanLTL/Logics` directory: 
- Linear Temporal Logic (`LTL.lean`)
- Linear Temporal Logic over Finite Traces (`LTLf.lean`)
