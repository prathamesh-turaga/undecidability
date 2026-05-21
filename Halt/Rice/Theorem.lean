/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Rice.Basic
public import Halt.Rice.TrivialTMs
public import Halt.Rice.Extender
public import Halt.Rice.Bisim
public import Halt.CodeOf
public import Reduction.TMDecidable
public import Reduction.HaltUndecidable
public import Reduction.Graph

@[expose] public section

/-!
# Rice's theorem (restricted form)

This file finishes the Rice scaffolding from `Halt.Rice.Basic`,
`TrivialTMs`, and `Extender`. The headline behaviour theorem for
`riceConstTM`:

```lean
SemHalt (riceConstTM c) = Set.univ  iff  Halts c.toTM (encodeTMCode c)
SemHalt (riceConstTM c) = ∅         iff  ¬ Halts c.toTM (encodeTMCode c)
```

is **postulated** here. The four-phase bisimulation (erase / write /
move-back / simulate) is a standard textbook construction (~1000 LoC in
Lean by analogy with `PCP/Reductions/HaltToMPCP.lean`), and we follow
the project's pattern of postulating standard TM-level facts when the
formalisation cost outweighs the conceptual content. A direct proof is
on the long-term TODO.

With the postulate, restricted Rice — every semantic property that
distinguishes `Set.univ` from `∅` is TM-undecidable — follows by
reducing from `selfHaltPred_TMUndecidable` via
`c ↦ encodeTMCode (codeOf (riceConstTM c))`.

## Output

* `axiom semHalt_riceConstTM` — the bisimulation.
* `Problems.HaltsOnEverything` — "the TMCode halts on every input" as
  a `List Bool`-input `Problem`.
* `Reductions.canonicalSelfHalt_to_haltsOnEverything` — the Rice
  reduction at the canonical "univ vs ∅" instance.
* `HaltsOnEverything_TMUndecidable` — derived via the postulated TM
  composition + the postulated bisimulation.
-/

namespace Halt.Rice

open Turing PCP DiagonaLean DiagonaLean.Problems

/-! ## The behaviour theorem

`semHalt_riceConstTM_dichotomy` — formerly postulated — is now **proved**
in `Halt.Rice.Bisim` by the four-phase bisimulation (erase / write /
move-back / simulate). It is re-exported here for the rest of the Rice
development. -/

/-! ## `codeOf` corollary -/

/-- The behaviour theorem transferred through `codeOf`: a TMCode wrapper. -/
lemma semHalt_codeOf_riceConstTM_dichotomy (c : Halt.TMCode) :
    (PCP.Halts c.toTM (Halt.Encoding.encodeTMCode c) →
      SemHalt (codeOf (riceConstTM c)).toTM = Set.univ) ∧
    (¬ PCP.Halts c.toTM (Halt.Encoding.encodeTMCode c) →
      SemHalt (codeOf (riceConstTM c)).toTM = ∅) := by
  have h_equiv : SemHalt (codeOf (riceConstTM c)).toTM = SemHalt (riceConstTM c) := by
    ext w
    exact halts_codeOf_iff (riceConstTM c) w
  rw [h_equiv]
  exact semHalt_riceConstTM_dichotomy c

end Halt.Rice

/-! ## Canonical self-halt predicate (canonical-form `selfHaltPred`)

This variant ensures the second arg of `Halts` is `encodeTMCode c` (the
canonical encoding) rather than the original input bits. It coincides
with `selfHaltPred` on canonical inputs (`bits = encodeTMCode c`).
Used as the anchor for the Rice reduction — the regular `selfHaltPred`
doesn't align cleanly because non-canonical bits create a mismatch
between `Halts c.toTM bits` and `Halts c.toTM (encodeTMCode c)`. -/

namespace DiagonaLean

open Halt Halt.Encoding PCP Turing

/-- Canonical self-halt: `decode bits` to `c`, ask whether `c.toTM`
halts on the canonical encoding `encodeTMCode c`. -/
def canonicalSelfHaltPred (bits : List Bool) : Prop :=
  match decodeTMCode bits with
  | none => False
  | some c => PCP.Halts c.toTM (encodeTMCode c)

@[simp] lemma canonicalSelfHaltPred_encodeTMCode (c : Halt.TMCode) :
    canonicalSelfHaltPred (encodeTMCode c) ↔
      PCP.Halts c.toTM (encodeTMCode c) := by
  unfold canonicalSelfHaltPred
  rw [decodeTMCode_encodeTMCode]

/-- A TM-decider for `canonicalSelfHaltPred` is an `IsSelfHaltDecider`. -/
theorem tmDecides_canonicalSelfHaltPred_isSelfHaltDecider
    {D : SingleTapeTM Bool} (h : TMDecides D canonicalSelfHaltPred) :
    IsSelfHaltDecider D := by
  intro c
  have h_c := h (encodeTMCode c)
  rw [canonicalSelfHaltPred_encodeTMCode] at h_c
  exact h_c

theorem canonicalSelfHaltPred_TMUndecidable :
    TMUndecidable canonicalSelfHaltPred := by
  intro h_dec
  obtain ⟨D, hD⟩ := h_dec.exists_TMDecides
  exact Halt.halt_undecidable
    ⟨D, tmDecides_canonicalSelfHaltPred_isSelfHaltDecider hD⟩

end DiagonaLean

namespace DiagonaLean.Problems

open Halt Halt.Encoding PCP Halt.Rice

/-- The canonical self-halt problem as a `Problem`, registered as an
additional `@[tm_undecidable_anchor]`. -/
def CanonicalSelfHalt : Problem where
  Input := List Bool
  predicate := canonicalSelfHaltPred

@[tm_undecidable_anchor]
theorem CanonicalSelfHalt_TMUndecidable :
    TMUndecidable CanonicalSelfHalt.predicate :=
  canonicalSelfHaltPred_TMUndecidable

/-! ## `HaltsOnEverything`: the canonical Rice-style problem -/

/-- "The TMCode encoded by these bits halts on every input." A
canonical example of a non-trivial semantic property. -/
def HaltsOnEverything : Problem where
  Input := List Bool
  predicate := fun bits =>
    match decodeTMCode bits with
    | none => False
    | some c => SemHalt c.toTM = Set.univ

end DiagonaLean.Problems

namespace DiagonaLean.Reductions

open Halt Halt.Rice PCP DiagonaLean DiagonaLean.Problems

/-! ## The Rice reduction: `CanonicalSelfHalt ≤ₘ HaltsOnEverything` -/

/-- The reducing function: decode `c`, output the canonical encoding of
`codeOf (riceConstTM c)`. -/
noncomputable def canonicalSelfHalt_to_haltsOnEverything_f
    (bits : List Bool) : List Bool :=
  match Halt.Encoding.decodeTMCode bits with
  | none => []
  | some c => Halt.Encoding.encodeTMCode (codeOf (riceConstTM c))

@[reduction_graph]
noncomputable def canonicalSelfHalt_to_haltsOnEverything :
    ManyOneReduction CanonicalSelfHalt HaltsOnEverything where
  f := canonicalSelfHalt_to_haltsOnEverything_f
  spec := fun bits => by
    show canonicalSelfHaltPred bits ↔
      (match Halt.Encoding.decodeTMCode
              (canonicalSelfHalt_to_haltsOnEverything_f bits) with
        | none => False
        | some c => SemHalt c.toTM = Set.univ)
    unfold canonicalSelfHaltPred canonicalSelfHalt_to_haltsOnEverything_f
    cases h_dec : Halt.Encoding.decodeTMCode bits with
    | none =>
      -- Both sides are `match none with | none => False | _ => _` = False.
      show False ↔
        (match Halt.Encoding.decodeTMCode ([] : List Bool) with
          | none => False
          | some c => SemHalt c.toTM = Set.univ)
      rw [show Halt.Encoding.decodeTMCode ([] : List Bool) = none from rfl]
    | some c =>
      show PCP.Halts c.toTM (Halt.Encoding.encodeTMCode c) ↔
        (match Halt.Encoding.decodeTMCode
                (Halt.Encoding.encodeTMCode (codeOf (riceConstTM c))) with
          | none => False
          | some c' => SemHalt c'.toTM = Set.univ)
      rw [Halt.Encoding.decodeTMCode_encodeTMCode]
      change PCP.Halts c.toTM (Halt.Encoding.encodeTMCode c) ↔
        SemHalt (codeOf (riceConstTM c)).toTM = Set.univ
      have ⟨h_uni, h_emp⟩ := semHalt_codeOf_riceConstTM_dichotomy c
      refine ⟨h_uni, fun h_sem => ?_⟩
      by_contra h_neg
      have h_empty := h_emp h_neg
      rw [h_empty] at h_sem
      exact Set.empty_ne_univ h_sem

/-- Postulate: TM-computability of the Rice reduction. The function is
"decode TMCode, run riceConstTM (a constant-template TM construction),
re-encode" — a standard transformation. -/
axiom canonicalSelfHalt_to_haltsOnEverything_TMComputable :
    TMComputable canonicalSelfHalt_to_haltsOnEverything.f

end DiagonaLean.Reductions
