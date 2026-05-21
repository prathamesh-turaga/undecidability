# Architecture and proof chain

How DiagonaLean is put together: the framework, the reduction graph,
the tactic, and the proofs behind each edge. For the project vision
see [`README.md`](README.md); for the forward plan see
[`TODO.md`](TODO.md).

---

## 1. The framework (`Reduction/Basic`–`Transfer`)

* **`Problem`** — a decision problem: an `Input` type plus a
  `predicate : Input → Prop`.
* **`ManyOneReduction P Q`** — a function `f : P.Input → Q.Input` with
  a proof `∀ x, P.predicate x ↔ Q.predicate (f x)`. Set-theoretic
  (no computability constraint at this layer).
* **`Decidable` / `Undecidable`** — classical Bool-valued decidability
  and its negation. Vacuous classically; meaningful only as a
  bookkeeping layer.
* **Composition** — `.id`, `.trans`, with identity and associativity
  lemmas; `ManyOneReduction` is a reflexive-transitive relation.
* **Transfer** — `Decidable.of_manyOne` (decidability pulls back) and
  `Undecidable.of_manyOne` (undecidability pushes forward).

### TM-level (un)decidability (`Reduction/TMDecidable`)

The classical layer is vacuous, so the *meaningful* claims live one
level down, grounded in cslib's `SingleTapeTM`:

* **`TMComputable f`** — `Nonempty (TimeComputable f)`, i.e. some
  `SingleTapeTM Bool` computes `f` within a length-indexed time bound.
* **`TMDecidable pred`** — `TMComputable (boolIndicator pred)`.
* **`TMUndecidable pred`** — `¬ TMDecidable pred`.

Because `TMComputable` is built on cslib's `TimeComputable` (which
ships `.id` and `.comp`), the composition machinery is **proved**:

* `TMComputable.id` — from `TimeComputable.id`.
* `TMComputable.comp` — from `TimeComputable.comp`, after
  `monotoniseTC` upgrades a time bound to its running supremum (cslib's
  `comp` needs a monotone bound).
* `TMUndecidable.of_TMReduction` — from `boolIndicator pred₁ =
  boolIndicator pred₂ ∘ f` and `TMComputable.comp`.

---

## 2. The tactic (`Reduction/Graph`–`Tactic`)

`by reduce_diag` is the headline deliverable, in three components:

| Component | File | Role |
|---|---|---|
| 1. Registration | `Reduction/Graph` | `@[reduction_graph]` records a `ManyOneReduction` as a graph `Edge`; `@[undecidable_anchor]` / `@[tm_undecidable_anchor]` mark known-undecidable nodes. All held in persistent env extensions. |
| 2. Search | `Reduction/Search` | Depth-bounded backward DFS from the goal `Problem` to an anchor, with cycle detection and metavariable instantiation for polymorphic edges. |
| 3. Emission | `Reduction/Tactic` | Folds the path via `ManyOneReduction.trans` and applies the transfer theorem. Dispatches on the goal: `Undecidable P` ⇒ `Undecidable.of_manyOne`; `TMUndecidable P.predicate` ⇒ composes the per-edge `TMComputable` witnesses and applies `TMUndecidable.of_TMReduction`. |

---

## 3. The reduction graph

13 edges. Spine (the `TMUndecidable`-carrying chain) plus the Rice
branch:

```
selfHaltPred / CanonicalSelfHalt   ── tm-anchors, PROVED from halt_undecidable
        │                                   │
        ▼                                   ▼
EncodedSelfHalt                      HaltsOnEverything
        │ encodedSelfHalt_to_encodedHalt   (canonicalSelfHalt_to_haltsOnEverything)
        ▼
EncodedHalt
        │ encodedHalt_to_encodedHaltMPCP        — HUM normalising wrapper
        ▼
EncodedHaltMPCP
        │ encodedHaltMPCP_to_encodedMPCP_LB     — encodeAlpha + encodeTileStack
        ▼
EncodedMPCP_LB
        │ encodedMPCP_LB_to_encodedPCP_LB       — mpcpToPcp + flattenStack
        ▼
EncodedPCP_LB
        │ encodedPCP_LB_to_encodedCFGI_LB       — identity (hasSolution ↔ ∩-nonempty)
        ▼
EncodedCFGI_LB
```

Other registered edges (`mpcpToPcp α`, `haltTM_to_haltTMCode`,
`haltTMCode_to_encodedHalt`, `encodedHalt_to_haltTMCode`,
`mpcpLB_to_encodedPCP`, `encodedHaltMPCP_to_mpcpLB`,
`encodedPCP_to_encodedCFGIntersection`) populate the classical
`Undecidable` graph and the non-`List Bool` problem nodes.

### Anchor nodes

**`halt_undecidable`** ([`Halt/Undecidable.lean`](Halt/Undecidable.lean))
— no `SingleTapeTM Bool` decides the self-halt problem. Proved by a
compositional diagonal: build `diagTM D` by inlining
"simulate-then-invert", apply `halts_codeOf_iff` and deterministic
confluence on `ReflTransGen`. See [`Halt/ROADMAP.md`](Halt/ROADMAP.md).

**`selfHaltPred_TMUndecidable`**
([`Reduction/HaltUndecidable.lean`](Reduction/HaltUndecidable.lean)) —
lifts `halt_undecidable` to the framework: a total TM-decider for
`selfHaltPred` would in particular be an `IsSelfHaltDecider`. No
postulate. `CanonicalSelfHalt_TMUndecidable`
([`Halt/Rice/Theorem.lean`](Halt/Rice/Theorem.lean)) is the canonical
variant used by the Rice reduction.

### Edges

* **`Halt ≤ MPCP`** ([`PCP/Reductions/HaltToMPCP.lean`](PCP/Reductions/HaltToMPCP.lean),
  ~4100 LoC) — the HUM tile construction, both directions, gated by
  `NoBlankWrites` / `NoLeftBoundary`.
* **`MPCP ≤ PCP`** ([`PCP/Reduction.lean`](PCP/Reduction.lean)) —
  Hopcroft–Ullman symbol-padding.
* **`PCP ≤ CFG-intersection`** ([`CFG/PcpReduction.lean`](CFG/PcpReduction.lean))
  — two grammars emitting the top/bottom of each tile, forced to agree.
* **HUM normalising wrapper** ([`Halt/Normalise.lean`](Halt/Normalise.lean),
  [`Reduction/EncodedHaltNormalised.lean`](Reduction/EncodedHaltNormalised.lean))
  — `normalisingWrapper` turns any `(c, w)` into a normalised
  `(c', w')` satisfying the HUM side conditions; the `EncodedHalt ≤
  EncodedHaltMPCP` edge feeds those proof fields into `halt_le_mpcp`.
* **Encoded variants** (`Reduction/Encoded*`, `StackMap`,
  `StackEncoding`) — `List Bool`-input wrappers giving the graph
  stable node identities, with full encoder/decoder round-trip lemmas.

---

## 4. Rice's theorem

`Halt/Rice/` proves Rice's theorem in restricted form — every semantic
property separating `Set.univ` from `∅` is TM-undecidable.

* **`Rice.Basic`** — `SemHalt`, `BehaviourEquiv`, `IsSemantic`,
  `IsPropDecider`, `NonTrivial`.
* **`Rice.TrivialTMs`** — witnesses `tm_alwaysHalt` (`SemHalt = univ`)
  and `tm_loop` (`SemHalt = ∅`).
* **`Rice.Extender`** — `riceConstTM : TMCode → SingleTapeTM Bool`, the
  four-phase TM: **erase** the input, **write** `encodeTMCode c`,
  **move back** to its start, **simulate** `c.toTM`.
* **`Rice.Bisim`** — the four-phase **bisimulation**, proving

      semHalt_riceConstTM_dichotomy :
        (Halts c.toTM (encodeTMCode c) → SemHalt (riceConstTM c) = univ) ∧
        (¬ Halts c.toTM (encodeTMCode c) → SemHalt (riceConstTM c) = ∅)

  | Phase | Lemma | Idea |
  |---|---|---|
  | erase | `erase_phase` | `StackTape` trims trailing blanks, so the blanked cell vanishes — `⟨erase, mk₁ w⟩ →* ⟨writeBit 0, ∅⟩` for *every* `w`. |
  | write | `write_phase` | `writtenTape` invariant; `encodeTMCode c` is laid down bit-by-bit (`List.take_add_one` induction). |
  | move-back | `moveBack_phase` | two-list `splitTape` invariant; `move_left` shifts one element from `pre` to `suf`. |
  | simulate | `step_liftCfg`, … | `liftCfg` (tag the state with `inC`) is a step-for-step bisimulation with `c.toTM`; a functional-relation confluence lemma factors the halt-trace through the setup phases. |

  This was formerly the postulate `semHalt_riceConstTM_dichotomy`; it
  is now fully proved.
* **`Rice.Theorem`** — `HaltsOnEverything` as a `List Bool` `Problem`
  and the reduction `canonicalSelfHalt_to_haltsOnEverything`.

---

## 5. Encoding infrastructure (`Halt/`)

* **`Halt.TMCode`** — normalised TM record (alphabet `Bool`, states
  `Fin (n + 1)`), `toTM : TMCode → SingleTapeTM Bool`.
* **`Halt.Encoding`** — `encodeTMCode : TMCode → List Bool`, a
  self-delimiting bit encoding with round-trip lemmas at every layer.
* **`Halt.Pair`** — pair encoding `encodePair`.
* **`Halt.CodeOf`** — `codeOf : SingleTapeTM Bool → TMCode` with the
  bisimulation `halts_codeOf_iff`.
* **`Halt.Diagonal`** — the model-independent diagonal kernel (Cantor +
  the abstract self-referential contradiction).

---

## 6. Remaining postulates

| Postulate | Status |
|---|---|
| `normalisingWrapper` | the HUM wrapper TM — substantive; the 2-bit-alphabet-shift TM is not yet built (~1000+ LoC). |
| 5 × `<edge>_TMComputable` | each is a Church–Turing instance: a specific, genuinely computable reduction function has a TM. Mechanical; needs explicit cslib TM constructions. |

After the soundness fix every reduction function in the graph is
genuinely computable, so all five `TMComputable` postulates are honest.

---

## Build invariant

Every commit keeps `lake build` clean with **no `sorry`** and no
warnings. Postulates are catalogued in [`README.md`](README.md).
