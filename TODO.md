# DiagonaLean — TODO

Prioritised work plan. Tags: **P0** blocker, **P1** next deliverable,
**P2** after P1, **P3** nice-to-have.

For the vision see [`README.md`](README.md); for the architecture see
[`ROADMAP.md`](ROADMAP.md).

---

## Status

**Phase 1 (framework) and Phase 2 (canonical problems) are complete.**

* The framework, the `@[reduction_graph]` machinery, and the
  `by reduce_diag` tactic all work; the smoke test closes 13 examples.
* The reduction graph has 13 edges; the spine runs end-to-end from
  `halt_undecidable` to `EncodedCFGI_LB` and `HaltsOnEverything`.
* `lake build` is clean — no `sorry`, no warnings.

What remains for a fully axiom-free development is the **postulate
discharge** below, then the **Phase 3** library.

---

## Discharge the remaining postulates

Six axioms remain (see [`README.md`](README.md) for the ledger).

### Substantive

* [ ] **P1** `normalisingWrapper` ([`Halt/Normalise.lean`](Halt/Normalise.lean)).
  Build the HUM-normalising wrapper TM in Lean. Being built
  incrementally in [`Halt/Wrapper/`](Halt/Wrapper/) — realistically
  ~2000 LoC, the project's largest single construction:
  * [x] Step 1 — `Wrapper/Alphabet`: the 2-bit `Code` (synthetic blank
    + left-edge marker), `encSym`/`decSym`, round-trip.
  * [x] Step 2 — `Wrapper/Tape`: `encodeInput`, the wrapped input.
  * [ ] Step 3 — the simulator TM (2-bit-encoding step simulator).
  * [ ] Step 4 — tape folding for one-sidedness (`NoLeftBoundary`).
  * [ ] Step 5 — `NoBlankWrites` proof.
  * [ ] Step 6 — the `halts_iff` bisimulation.
  * [ ] Step 7 — assemble `normalisingWrapper`, remove the axiom.

### Mechanical — per-edge `TMComputable` witnesses

Each asserts a concrete reduction function has a Turing machine (true;
a Church–Turing instance). Discharging needs explicit cslib TM
constructions — `idComputer`/`compComputer` plus per-operation TMs
(bit-copy, length-prefix, …).

* [x] **P2** `encodedPCP_LB_to_encodedCFGI_LB` — proved (`= TMComputable.id`). ✅
* [ ] **P2** `encodedSelfHalt_to_encodedHalt` — `f = encodePair bits bits`.
* [ ] **P2** `encodedHaltMPCP_to_encodedMPCP_LB` — decode + `encodeAlpha`/`encodeTileStack`.
* [ ] **P2** `encodedMPCP_LB_to_encodedPCP_LB` — decode + `mpcpToPcp`/`flattenStack`.
* [ ] **P2** `encodedHalt_to_encodedHaltMPCP` — uses `normalisingWrapper` (blocked on it).
* [ ] **P2** `canonicalSelfHalt_to_haltsOnEverything` — uses `codeOf ∘ riceConstTM`.
* [ ] **P3** A small reusable `TimeComputable`-combinator library would
  let several of these share machinery.

### Discharged (for the record)

* [x] `TMComputable.id` / `.comp`, `TMUndecidable.of_TMReduction` —
  proved by rebasing `TMComputable` on cslib's `TimeComputable`.
* [x] `semHalt_riceConstTM_dichotomy` — proved by the four-phase Rice
  extender bisimulation ([`Halt/Rice/Bisim.lean`](Halt/Rice/Bisim.lean)).

---

## Phase 1 — framework polish

* [ ] **P2** Polymorphic edges in `composeReductions`
  ([`Reduction/Tactic.lean`](Reduction/Tactic.lean)): currently throws
  on edges with unresolved binders (e.g. `mpcpToPcp α`). Thread the
  search's metavariables through to term emission.
* [ ] **P2** Tactic ergonomics: `by reduce_diag via <edge>` hints,
  better "no path found" errors, a `#diagonalean_graph` command.
* [ ] **P2** `TuringReduction` (oracle-machine reductions) — needs an
  oracle-TM notion in cslib first.
* [ ] **P3** Graph visualisation export (Graphviz).

---

## Phase 2 — remaining canonical problems

* [ ] **P1** **TM acceptance (ATM)** — `Accepts tm w`, and `Halt ≤ ATM`.
  ~200 LoC.
* [ ] **P1** **`HALT_TM`** (pair-form) via `K ≤ HALT_TM` (a `dupTM`-style
  reduction). ~200 LoC.
* [ ] **P2** **CFG universality** undecidable, by reduction from PCP
  (complement-of-valid-encodings grammar). ~400 LoC.
* [ ] **P2** **CFG equivalence / ambiguity** undecidable (the former
  from universality).
* [ ] **P2** General-alphabet halting: `SingleTapeTM Symbol` for
  `[Fintype Symbol]`, `|Symbol| ≥ 2`, via binary-encoding simulation.

---

## Phase 3 — standard reduction library

A textbook-aligned reduction graph: every node certified, every edge
machine-checked.

### Hopcroft–Motwani–Ullman

* [ ] **P2** **Rice's theorem (general form)** — arbitrary non-trivial
  semantic properties (the restricted form is done). Needs an
  index-set generalisation.
* [ ] **P2** Rice corollaries: emptiness, finiteness, regularity, …
* [ ] **P3** **Linear bounded automaton** universality.
* [ ] **P3** **Two-counter machine** halting (Minsky encoding).

### Rogers / Soare

* [ ] **P3** Index-set theorem; Kleene's recursion theorem.
* [ ] **P3** Productive / creative sets.
* [ ] **P3** Friedberg–Muchnik (incomparable r.e. degrees) — major.

### Other

* [ ] **P3** **Wang tiling** undecidability via PCP. ~500 LoC.

---

## Engineering / documentation

* [ ] **P2** CI workflow (GitHub Actions) running `lake build`, with a
  no-`sorry` / no-warning gate.
* [ ] **P2** Worked-example walkthrough: trace one undecidability claim
  through the graph step by step.
* [ ] **P3** Per-module docstring review pass.

---

## Convention

Every commit keeps `lake build` clean — **no `sorry`**, no warnings.
Every `axiom` is catalogued in [`README.md`](README.md) and documented
at its definition site.
