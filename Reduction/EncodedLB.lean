/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Graph
public import Reduction.StackEncoding
public import Reduction.EncodedHaltMPCP
public import Reduction.EncodedPCP
public import Reduction.EncodedCFG

@[expose] public section

/-!
# `List Bool`-input variants for the downstream PCP/CFG chain

The existing `MPCP_LB`, `EncodedPCP`, `EncodedCFGIntersection` have
input types `Tile × Stack`, `Stack`, and CFG-pair respectively. To
make them compatible with `TMComputable` (`List Bool → List Bool`), we
wrap each predicate behind `decodeTileStack` / `decodeStack` so the
input type becomes `List Bool`.

* `EncodedMPCP_LB`   — `Input List Bool`; decode `(c, P)` and check
                       `MHasSolution`.
* `EncodedPCP_LB`    — `Input List Bool`; decode `P` and check
                       `HasSolution`.
* `EncodedCFGI_LB`   — `Input List Bool`; decode `P` and check
                       `∃ w, w ∈ topCFG P.language ∧ w ∈ botCFG P.language`.

The bridge `EncodedPCP_LB ≤ₘ EncodedCFGI_LB` is the identity reduction —
the input bits encode the same `Stack`, and the predicate equivalence
is `hasSolution_iff_intersectionNonempty`. The `EncodedHaltMPCP ≤ₘ
EncodedMPCP_LB` and `EncodedMPCP_LB ≤ₘ EncodedPCP_LB` edges compose
the existing reductions with the encoder/decoder layer.

Each edge is registered with `@[reduction_graph]` and ships with a
postulated `<edgeName>_TMComputable` axiom so `by reduce_diag` closes
`TMUndecidable EncodedCFGI_LB.predicate` end-to-end.
-/

namespace DiagonaLean.Problems

open PCP DiagonaLean.StackEncoding CFG.PcpReduction Mathlib

/-- The MPCP problem at `List Bool` input. Decodes bits to
`(c : Tile (List Bool), P : Stack (List Bool))`; positive iff the
decoded instance has an `MHasSolution`. -/
def EncodedMPCP_LB : Problem where
  Input := List Bool
  predicate := fun bits =>
    match decodeTileStack bits with
    | none => False
    | some ((c, P), _) => MHasSolution c P

/-- The PCP problem at `List Bool` input. -/
def EncodedPCP_LB : Problem where
  Input := List Bool
  predicate := fun bits =>
    match decodeStack bits with
    | none => False
    | some (P, _) => HasSolution P

/-- The CFG-intersection problem at `List Bool` input. Same decoding as
`EncodedPCP_LB` but the predicate is intersection-nonempty for the
derived `(topCFG, botCFG)` pair. -/
def EncodedCFGI_LB : Problem where
  Input := List Bool
  predicate := fun bits =>
    match decodeStack bits with
    | none => False
    | some (P, _) =>
      ∃ w : List (Term (List Bool)),
        w ∈ (topCFG P).language ∧ w ∈ (botCFG P).language

end DiagonaLean.Problems

namespace DiagonaLean.Reductions

open DiagonaLean DiagonaLean.Problems DiagonaLean.StackEncoding PCP
open CFG.PcpReduction

/-! ## `EncodedHaltMPCP ≤ₘ EncodedMPCP_LB`: encode the existing edge -/

/-- The reducing function: take the existing `EncodedHaltMPCP → MPCP_LB`
output and encode it as bits. -/
noncomputable def encodedHaltMPCP_to_encodedMPCP_LB_f
    (bits : List Bool) : List Bool :=
  encodeTileStack (encodedHaltMPCP_to_mpcpLB.f bits)

@[reduction_graph]
noncomputable def encodedHaltMPCP_to_encodedMPCP_LB :
    ManyOneReduction EncodedHaltMPCP EncodedMPCP_LB where
  f := encodedHaltMPCP_to_encodedMPCP_LB_f
  spec := fun bits => by
    show EncodedHaltMPCP.predicate bits ↔
      (match decodeTileStack (encodedHaltMPCP_to_encodedMPCP_LB_f bits) with
        | none => False
        | some ((c, P), _) => MHasSolution c P)
    unfold encodedHaltMPCP_to_encodedMPCP_LB_f
    have h_decode := decodeTileStack_encodeTileStack
      (encodedHaltMPCP_to_mpcpLB.f bits)
    rw [h_decode]
    exact encodedHaltMPCP_to_mpcpLB.spec bits

/-- Postulate: TM-computability of the encoding wrapper. -/
axiom encodedHaltMPCP_to_encodedMPCP_LB_TMComputable :
    TMComputable encodedHaltMPCP_to_encodedMPCP_LB.f

/-! ## `EncodedMPCP_LB ≤ₘ EncodedPCP_LB`: decode-transform-encode -/

/-- The reducing function: decode `(c, P)`, run `mpcpToPcp` + `flattenStack`,
encode the resulting `Stack`. On malformed input, return the encoding of an
empty stack (predicate is `False` on both sides). -/
def encodedMPCP_LB_to_encodedPCP_LB_f (bits : List Bool) : List Bool :=
  match decodeTileStack bits with
  | none => encodeStack []
  | some ((c, P), _) => encodeStack (flattenStack (PCP.mpcpToPcp c P))

@[reduction_graph]
def encodedMPCP_LB_to_encodedPCP_LB :
    ManyOneReduction EncodedMPCP_LB EncodedPCP_LB where
  f := encodedMPCP_LB_to_encodedPCP_LB_f
  spec := fun bits => by
    show (match decodeTileStack bits with
            | none => False
            | some ((c, P), _) => MHasSolution c P) ↔
      (match decodeStack (encodedMPCP_LB_to_encodedPCP_LB_f bits) with
        | none => False
        | some (P, _) => HasSolution P)
    unfold encodedMPCP_LB_to_encodedPCP_LB_f
    cases decodeTileStack bits with
    | none =>
      simp only [decodeStack_encodeStack]
      refine ⟨False.elim, fun ⟨A, h_ne, h_in, _⟩ => ?_⟩
      cases A with
      | nil => exact h_ne rfl
      | cons t _ => exact (List.not_mem_nil (h_in t List.mem_cons_self))
    | some pair =>
      obtain ⟨⟨c, P⟩, _⟩ := pair
      simp only [decodeStack_encodeStack]
      rw [hasSolution_flattenStack_iff]
      exact PCP.mpcp_iff_pcp c P

/-- Postulate: TM-computability. -/
axiom encodedMPCP_LB_to_encodedPCP_LB_TMComputable :
    TMComputable encodedMPCP_LB_to_encodedPCP_LB.f

/-! ## `EncodedPCP_LB ≤ₘ EncodedCFGI_LB`: identity reduction -/

@[reduction_graph]
def encodedPCP_LB_to_encodedCFGI_LB :
    ManyOneReduction EncodedPCP_LB EncodedCFGI_LB where
  f := id
  spec := fun bits => by
    show EncodedPCP_LB.predicate bits ↔ EncodedCFGI_LB.predicate (id bits)
    show (match decodeStack bits with
            | none => False
            | some (P, _) => HasSolution P) ↔
      (match decodeStack bits with
        | none => False
        | some (P, _) =>
          ∃ w : List (Term (List Bool)),
            w ∈ (topCFG P).language ∧ w ∈ (botCFG P).language)
    cases decodeStack bits with
    | none => exact Iff.rfl
    | some pair =>
      obtain ⟨P, _⟩ := pair
      exact hasSolution_iff_intersectionNonempty P

/-- TM-computability of the identity reduction — **proved**, not
postulated, since `encodedPCP_LB_to_encodedCFGI_LB.f` is `id`. Named
under the `<edge>_TMComputable` convention for the tactic's witness
lookup. -/
theorem encodedPCP_LB_to_encodedCFGI_LB_TMComputable :
    TMComputable encodedPCP_LB_to_encodedCFGI_LB.f :=
  TMComputable.id

end DiagonaLean.Reductions
