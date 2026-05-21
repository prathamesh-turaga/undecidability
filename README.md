# DiagonaLean

**A compositional Lean 4 framework for Turing reductions, diagonalisation, and undecidability proofs.**

DiagonaLean is a research project building a reusable, tactic-driven
toolkit for mechanising computability theory in Lean 4. It provides a
framework of certified many-one reductions, a registered *reduction
graph*, and a proof-search tactic `by reduce_diag` that closes
undecidability goals by composing reductions back to a known anchor.

The development is built on [`cslib`](https://github.com/leanprover/cslib)'s
`Turing.SingleTapeTM` and Mathlib's `ContextFreeGrammar`.

* Forward-looking work plan — [`TODO.md`](TODO.md)
* Proof-chain architecture — [`ROADMAP.md`](ROADMAP.md)
* Halting-problem construction notes — [`Halt/ROADMAP.md`](Halt/ROADMAP.md)

---

## Headline result

```lean
-- The anchor: no Turing machine decides the self-halt problem
-- (proved from cslib's `Halt.halt_undecidable`, no postulate).
@[tm_undecidable_anchor]
theorem CanonicalSelfHalt_TMUndecidable :
    TMUndecidable CanonicalSelfHalt.predicate := …

-- Downstream undecidability, closed automatically by the tactic:
example : TMUndecidable HaltsOnEverything.predicate    := by reduce_diag
example : TMUndecidable EncodedCFGI_LB.predicate       := by reduce_diag
```

`by reduce_diag` reads the goal, searches the registered reduction
graph for a path from a known-undecidable anchor to the goal problem,
composes the reductions, and applies the undecidability-transfer
theorem. Every example in [`Reduction/Smoke.lean`](Reduction/Smoke.lean)
(13 of them) is closed this way.

---

## The reduction graph

The graph has **13 registered edges**. Its spine — the chain that
carries TM-undecidability from the halting problem to context-free
grammar intersection — is:

```
   Halt.halt_undecidable                    (cslib: no TM decides self-halt)
            │
            ▼
   selfHaltPred / CanonicalSelfHalt         TMUndecidable — PROVED, no postulate
            │
            ├─────────────────────────────────────────────┐
            ▼                                             ▼
   EncodedSelfHalt                            HaltsOnEverything   (Rice's theorem)
            │  encodedSelfHalt_to_encodedHalt
            ▼
   EncodedHalt
            │  encodedHalt_to_encodedHaltMPCP        (HUM normalising wrapper)
            ▼
   EncodedHaltMPCP
            │  encodedHaltMPCP_to_encodedMPCP_LB
            ▼
   EncodedMPCP_LB
            │  encodedMPCP_LB_to_encodedPCP_LB       (MPCP → PCP, flattenStack)
            ▼
   EncodedPCP_LB
            │  encodedPCP_LB_to_encodedCFGI_LB       (PCP → CFG-intersection)
            ▼
   EncodedCFGI_LB
```

Every node is a `Problem` with `Input = List Bool`; every edge is a
machine-checked `ManyOneReduction` tagged `@[reduction_graph]`.

---

## Project status

DiagonaLean is organised in three phases. **Phases 1 and 2 are
complete.**

### Phase 1 — Core framework ✅

| Component | Status |
|---|---|
| `Problem`, `ManyOneReduction`, classical `Decidable`/`Undecidable` | ✅ [`Reduction/Basic.lean`](Reduction/Basic.lean) |
| Composition laws `.id`, `.trans`, identity / associativity | ✅ [`Reduction/Composition.lean`](Reduction/Composition.lean) |
| Transfer theorems `Decidable.of_manyOne`, `Undecidable.of_manyOne` | ✅ [`Reduction/Transfer.lean`](Reduction/Transfer.lean) |
| Notation `≤ₘ`, `≡ₘ` | ✅ [`Reduction/Notation.lean`](Reduction/Notation.lean) |
| `@[reduction_graph]` attribute + persistent env extension | ✅ [`Reduction/Graph.lean`](Reduction/Graph.lean) |
| Anchors `@[undecidable_anchor]`, `@[tm_undecidable_anchor]` | ✅ [`Reduction/Graph.lean`](Reduction/Graph.lean) |
| Backward-DFS path search | ✅ [`Reduction/Search.lean`](Reduction/Search.lean) |
| `by reduce_diag` tactic (term emission) | ✅ [`Reduction/Tactic.lean`](Reduction/Tactic.lean) |
| TM-level `TMDecidable` / `TMUndecidable` / `TMComputable` | ✅ [`Reduction/TMDecidable.lean`](Reduction/TMDecidable.lean) |
| `TMComputable.id`/`.comp`, `TMUndecidable.of_TMReduction` — *proved* | ✅ [`Reduction/TMDecidable.lean`](Reduction/TMDecidable.lean) |

### Phase 2 — Canonical problems ✅

| Result | Status |
|---|---|
| `Halt.halt_undecidable` (no TM decides self-halt) | ✅ [`Halt/Undecidable.lean`](Halt/Undecidable.lean) |
| `Halt ≤ MPCP ≤ PCP` (HUM construction) | ✅ [`PCP/Reductions/`](PCP/Reductions/) |
| `PCP ≤ CFG-intersection-nonempty` | ✅ [`CFG/PcpReduction.lean`](CFG/PcpReduction.lean) |
| `List Bool`-input encoded variants of every problem | ✅ [`Reduction/Encoded*.lean`](Reduction/) |
| Bridge `halt_undecidable → TMUndecidable selfHaltPred` | ✅ [`Reduction/HaltUndecidable.lean`](Reduction/HaltUndecidable.lean) |
| HUM normalisation `EncodedHalt → EncodedHaltMPCP` | ✅ [`Reduction/EncodedHaltNormalised.lean`](Reduction/EncodedHaltNormalised.lean) |
| Rice's theorem (restricted), incl. the 4-phase extender bisimulation | ✅ [`Halt/Rice/`](Halt/Rice/) |

### Phase 3 — Standard reduction library 🚧

Textbook results from Hopcroft–Motwani–Ullman, Rogers, and Soare —
CFG universality/equivalence/ambiguity, ATM, LBA, Wang tilings, the
recursion theorem, etc. See [`TODO.md`](TODO.md).

The development is verified against `leanprover/lean4:v4.29.0-rc4` and
contains **no `sorry`**.

---

## Soundness and postulates

DiagonaLean keeps an honest, explicit ledger of what is *proved*
versus *postulated*. After the framework refactors, **6 axioms**
remain — all of them genuine, uncontroversial statements:

| Axiom | Kind | Location |
|---|---|---|
| `normalisingWrapper` | **HUM construction** — a wrapper TM (2-bit alphabet shift with a sentinel marker + synthetic blank) satisfying `NoBlankWrites`/`NoLeftBoundary`. Substantive; the wrapper TM is not yet built. | [`Halt/Normalise.lean`](Halt/Normalise.lean) |
| 5 × `<edge>_TMComputable` | **Church–Turing instances** — each asserts one concrete reduction function (`encodePair`, decoders, `riceConstTM`, …) has a Turing machine. All genuinely computable. | scattered |

Two earlier substantive postulates have since been **discharged**:

* The **TM-composition machinery** (`TMComputable.id`/`.comp`,
  `TMUndecidable.of_TMReduction`) is now *proved* — `TMComputable` is
  defined as `Nonempty (TimeComputable f)` over cslib's
  `SingleTapeTM.TimeComputable`, which already ships `.id`/`.comp`.
* The **Rice extender bisimulation** `semHalt_riceConstTM_dichotomy`
  is now *proved* in [`Halt/Rice/Bisim.lean`](Halt/Rice/Bisim.lean) by
  the full four-phase bisimulation.

> **Soundness note.** An earlier `EncodedHaltMPCP` baked
> `NoBlankWrites ∧ NoLeftBoundary` into its predicate, which forced a
> reduction to branch on the *undecidable* `NoLeftBoundary` — making
> its `TMComputable` witness a *false* axiom. This was found and fixed:
> the predicate is now the bare `MHasSolution`, the HUM side conditions
> are discharged on the `EncodedHalt ≤ EncodedHaltMPCP` edge via the
> wrapper's proof fields, and **no reduction branches on anything
> undecidable** — so all 5 `TMComputable` postulates are honest.

---

## Repository layout

```
Reduction/                 ← Phase 1 framework + the reduction graph
  Basic, Composition, Transfer, Notation     core: Problem, ManyOneReduction, …
  Graph, Search, Tactic                      the `by reduce_diag` tactic
  TMDecidable                                TM-level (un)decidability
  Instances, Encoded                         problem nodes + first edges
  HaltUndecidable                            halt_undecidable → TMUndecidable bridge
  StackMap, StackEncoding                    per-symbol / List Bool encodings
  EncodedPCP, EncodedHaltMPCP,
    EncodedHaltNormalised, EncodedCFG,
    EncodedLB                                the reduction-graph edges
  Smoke                                      #eval graph + `by reduce_diag` tests

Halt/                      ← halting-problem undecidability + Rice
  Diagonal, Basic, TMCode, Encoding,
    Pair, Helpers, CodeOf, Undecidable       the diagonal proof
  Normalise                                  postulated HUM wrapper
  Rice/Basic, TrivialTMs, Extender           Rice scaffolding
  Rice/Bisim                                 the 4-phase extender bisimulation
  Rice/Theorem                               restricted Rice + HaltsOnEverything

PCP/                       ← Halt ≤ MPCP ≤ PCP chain (HUM construction)
CFG/                       ← PCP ≤ CFG-intersection-nonempty

PCP.lean CFG.lean Halt.lean Reduction.lean   library roots
```

---

## Building

```sh
lake build                  # builds the four libraries + the `pcp` executable
lake build Reduction.Smoke  # runs the graph #eval + `by reduce_diag` tests
```

A cold build (including Mathlib) takes ~20–40 minutes; incremental
builds are seconds.

---

## Conventions

* Module-style headers: `module`, `public import`,
  `@[expose] public section` for ordinary code and `public meta
  section` for metaprogramming (the `@[reduction_graph]` machinery).
* The `Halt ≤ MPCP` reduction uses the Hopcroft–Ullman–Motwani
  one-sided-tape design, gated by `NoBlankWrites` / `NoLeftBoundary`;
  the `normalisingWrapper` lifts these for the end-to-end chain.
* Every commit keeps `lake build` clean — **no `sorry`**, no warnings.
  Each `axiom` is catalogued here and documented at its definition.

## License

Apache 2.0.
