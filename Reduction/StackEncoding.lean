/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Encoding
public import PCP.Basic

@[expose] public section

/-!
# `Stack (List Bool)` ↔ `List Bool` encoding

To make the PCP-side problems (`MPCP_LB`, `EncodedPCP`,
`EncodedCFGIntersection`) compatible with `TMComputable` (which is
`List Bool → List Bool`), we need to encode their non-`List Bool`
inputs into `List Bool`.

The encoding is built from `Halt.Encoding.encodeNat` (unary with a
`false` terminator) and runs three nested layers:

* `encodeBitstring` — a single `Word α = List Bool` with a length
  prefix.
* `encodeBitstringList` — a `List (List Bool)` (a list of words),
  length-prefixed.
* `encodeTile` / `encodeStack` — `Tile (List Bool)` and
  `Stack (List Bool)` as nested length-prefix structures.

Each comes with a `decode*` and a round-trip lemma. The encoders are
injective by construction.

## Output

* `encodeStack` / `decodeStack` for `Stack (List Bool)`.
* `encodeTileStack` / `decodeTileStack` for `Tile (List Bool) × Stack (List Bool)`.

These are used downstream to define `EncodedPCP_LB`, `EncodedMPCP_LB`,
`EncodedCFGI_LB` problems whose `Input = List Bool`.
-/

namespace DiagonaLean.StackEncoding

open Halt.Encoding PCP

/-! ## `encodeBitstring`: a single `List Bool` with length prefix -/

/-- Encode a bit-string as `encodeNat |bits| ++ bits`. -/
def encodeBitstring (bits : List Bool) : List Bool :=
  encodeNat bits.length ++ bits

/-- Decode a length-prefixed bit-string. -/
def decodeBitstring (l : List Bool) : Option (List Bool × List Bool) :=
  match decodeNat l with
  | none => none
  | some (n, rest) =>
    if n ≤ rest.length then
      some (rest.take n, rest.drop n)
    else
      none

@[simp] lemma decodeBitstring_encodeBitstring_append (bits rest : List Bool) :
    decodeBitstring (encodeBitstring bits ++ rest) = some (bits, rest) := by
  unfold decodeBitstring encodeBitstring
  rw [List.append_assoc, decodeNat_encodeNat_append]
  simp

/-! ## `encodeBitstringList`: `List (List Bool)` with length prefix -/

/-- Encode a list of bit-strings: count, then each bit-string with its
own length prefix. -/
def encodeBitstringList (l : List (List Bool)) : List Bool :=
  encodeNat l.length ++ (l.flatMap encodeBitstring)

/-- Decode a list of `n` bit-strings from the prefix of `l`. -/
def decodeBitstringListAux : Nat → List Bool → Option (List (List Bool) × List Bool)
  | 0, rest => some ([], rest)
  | n + 1, l =>
    match decodeBitstring l with
    | none => none
    | some (bits, rest) =>
      match decodeBitstringListAux n rest with
      | none => none
      | some (l', rest') => some (bits :: l', rest')

/-- Decode a length-prefixed list of bit-strings. -/
def decodeBitstringList (l : List Bool) : Option (List (List Bool) × List Bool) :=
  match decodeNat l with
  | none => none
  | some (n, rest) => decodeBitstringListAux n rest

private lemma decodeBitstringListAux_flatMap (l : List (List Bool)) (rest : List Bool) :
    decodeBitstringListAux l.length (l.flatMap encodeBitstring ++ rest) =
      some (l, rest) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
               decodeBitstringListAux, decodeBitstring_encodeBitstring_append,
               ih]

@[simp] lemma decodeBitstringList_encodeBitstringList_append
    (l : List (List Bool)) (rest : List Bool) :
    decodeBitstringList (encodeBitstringList l ++ rest) = some (l, rest) := by
  unfold decodeBitstringList encodeBitstringList
  rw [List.append_assoc, decodeNat_encodeNat_append]
  exact decodeBitstringListAux_flatMap l rest

/-! ## `Tile (List Bool)` -/

/-- Encode a tile as `encodeBitstringList top ++ encodeBitstringList bot`. -/
def encodeTile (t : Tile (List Bool)) : List Bool :=
  encodeBitstringList t.top ++ encodeBitstringList t.bot

/-- Decode a tile: decode top then bot. -/
def decodeTile (l : List Bool) : Option (Tile (List Bool) × List Bool) :=
  match decodeBitstringList l with
  | none => none
  | some (top, rest) =>
    match decodeBitstringList rest with
    | none => none
    | some (bot, rest') => some (⟨top, bot⟩, rest')

@[simp] lemma decodeTile_encodeTile_append (t : Tile (List Bool)) (rest : List Bool) :
    decodeTile (encodeTile t ++ rest) = some (t, rest) := by
  obtain ⟨top, bot⟩ := t
  simp only [encodeTile, decodeTile, List.append_assoc,
             decodeBitstringList_encodeBitstringList_append]

/-! ## `Stack (List Bool)` -/

/-- Encode a stack: length prefix + each tile's encoding. -/
def encodeStack (P : Stack (List Bool)) : List Bool :=
  encodeNat P.length ++ (P.flatMap encodeTile)

/-- Auxiliary decoder for `n` tiles. -/
def decodeStackAux : Nat → List Bool → Option (Stack (List Bool) × List Bool)
  | 0, rest => some ([], rest)
  | n + 1, l =>
    match decodeTile l with
    | none => none
    | some (t, rest) =>
      match decodeStackAux n rest with
      | none => none
      | some (P, rest') => some (t :: P, rest')

/-- Decode a length-prefixed stack. -/
def decodeStack (l : List Bool) : Option (Stack (List Bool) × List Bool) :=
  match decodeNat l with
  | none => none
  | some (n, rest) => decodeStackAux n rest

private lemma decodeStackAux_flatMap (P : Stack (List Bool)) (rest : List Bool) :
    decodeStackAux P.length (P.flatMap encodeTile ++ rest) = some (P, rest) := by
  induction P with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
               decodeStackAux, decodeTile_encodeTile_append, ih]

@[simp] lemma decodeStack_encodeStack_append (P : Stack (List Bool)) (rest : List Bool) :
    decodeStack (encodeStack P ++ rest) = some (P, rest) := by
  unfold decodeStack encodeStack
  rw [List.append_assoc, decodeNat_encodeNat_append]
  exact decodeStackAux_flatMap P rest

lemma decodeStack_encodeStack (P : Stack (List Bool)) :
    decodeStack (encodeStack P) = some (P, []) := by
  have := decodeStack_encodeStack_append P []
  simpa using this

/-! ## `Tile × Stack` for the MPCP_LB input -/

/-- Encode a `(Tile, Stack)` pair as `encodeTile c ++ encodeStack P`. -/
def encodeTileStack (cP : Tile (List Bool) × Stack (List Bool)) : List Bool :=
  encodeTile cP.1 ++ encodeStack cP.2

/-- Decode a `(Tile, Stack)` pair. -/
def decodeTileStack (l : List Bool) :
    Option ((Tile (List Bool) × Stack (List Bool)) × List Bool) :=
  match decodeTile l with
  | none => none
  | some (c, rest) =>
    match decodeStack rest with
    | none => none
    | some (P, rest') => some ((c, P), rest')

@[simp] lemma decodeTileStack_encodeTileStack_append
    (cP : Tile (List Bool) × Stack (List Bool)) (rest : List Bool) :
    decodeTileStack (encodeTileStack cP ++ rest) = some (cP, rest) := by
  obtain ⟨c, P⟩ := cP
  simp only [encodeTileStack, decodeTileStack, List.append_assoc,
             decodeTile_encodeTile_append, decodeStack_encodeStack_append]

lemma decodeTileStack_encodeTileStack
    (cP : Tile (List Bool) × Stack (List Bool)) :
    decodeTileStack (encodeTileStack cP) = some (cP, []) := by
  have := decodeTileStack_encodeTileStack_append cP []
  simpa using this

end DiagonaLean.StackEncoding
