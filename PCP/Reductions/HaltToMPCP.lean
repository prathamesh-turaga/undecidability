/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import PCP.Halt
public import PCP.MPCP

@[expose] public section

/-!
# Halt ≤_m MPCP

This file builds the reduction from the Halting Problem (`Halts`, see
`PCP.Halt`) to the Modified Post Correspondence Problem (`MHasSolution`).

## High-level idea

Given a Turing machine `tm` and an input `w`, we construct an MPCP
instance whose solutions encode accepting computation histories of `tm`
on `w`. The classical Hopcroft–Ullman construction uses an alphabet that
extends the TM tape alphabet with the TM state labels, a configuration
separator `#`, and a synthetic `halt` symbol. A configuration

  `⟨q, tape⟩` with tape contents `… b₋₁ b₀ b₁ …`

is encoded as the finite string

  `# b₋ₖ … b₋₁ q b₀ b₁ … bₖ #`

with the state symbol `q` placed immediately before the head symbol.

The reduction produces an MPCP instance with five families of tiles:

| Family       | Effect                                                  |
|--------------|---------------------------------------------------------|
| start tile   | seeds the bottom string with the initial configuration  |
| copy tiles   | copy a tape symbol from one configuration to the next   |
| separator    | copy `#` between configurations                         |
| transition   | rewrite the local window around the head per `tm.tr`    |
| halt-shrink  | absorb tape symbols once the TM has halted              |

A solution to the resulting MPCP instance must trace a halting
computation of `tm` on `w`, and conversely every halting computation
yields a solution.

## Simulation invariant

Throughout a matching solution, the bottom string is **one configuration
ahead** of the top:

  `bot = top ++ "encoded next configuration ++ #"`.

The start tile establishes this offset with `top = [#]` and
`bot = # :: encodeCfg(C₀) ++ [#]`. Each TM step `Cⱼ → Cⱼ₊₁` is realised
by a tile sub-sequence whose `tau1 = encodeCfg(Cⱼ) ++ [#]` reproduces
the *current* lookahead and whose `tau2 = encodeCfg(Cⱼ₊₁) ++ [#]`
extends it with the next configuration. After halt, the absorb tiles
shrink the lookahead one tape symbol at a time until only `h⊥` remains,
then the final tile equalises top and bot.

## HUM side conditions

The reduction is stated under the Hopcroft–Ullman–Motwani one-sided-tape
side conditions:

* `NoBlankWrites tm` — `tm.tr` never writes the blank symbol; this keeps
  the tape encoding finite and avoids `StackTape.cons` ambiguity.
* `NoLeftBoundary tm w` — no reachable cfg from `initCfg tm w` invokes
  a left-move at the left tape boundary. This removes the
  `leftMoveBoundaryTile` case from the tile set, making each
  configuration's transition tile sequence unambiguous.

Lifting these to a generic TM (the standard sentinel-shift construction)
is left for a future `PCP.Normalize` module.

## Contents

* Alphabet `Alpha` and configuration encoding (`encodeRunningCfg`,
  `encodeHaltedCfg`, `encodeCfg`, `block`, `initBlock`).
* All tile constructors (`startTile`, `copyTile`, `sepTile`, the
  transition-tile constructors, `absorbLeftTile`, `absorbRightTile`,
  `finalTile`).
* Tile enumeration (`copyTiles`, `absorbTiles`, `transitionTiles`,
  `haltTiles`) and the reduction function `haltToMpcp`.
* Step-simulation lemmas for all four reachable TM-step cases (no-move,
  right-interior, right-boundary, left-interior).
* Halt-absorption iteration lemmas culminating in
  `absorbAndFinish_matching`.
* `forward_aux` and `halts_implies_mhasSolution` — the forward
  direction.
* `mem_haltTiles_top`, `copy_prefix_forced`, `transition_forced`,
  `sep_forced`, `no_tile_for_state_sharp` and their queue-aware variants
  — the structural forcing lemmas used by the backward proof.
* Per-step backward lemmas `starts_with_stepTiles*` (canonical) and
  their `_weak_ext` queue-aware versions.
* `tau1_no_state_marker_then_sharp` — the structural property that rules
  out the alternative `rightMoveTile` decomposition in the right-boundary
  case.
* `backward_aux_weak` — the main backward driver, strong induction on
  `A.length` with a chain-tracked cfg queue.
* `halt_le_mpcp` — the canonical `Halts ↔ MHasSolution` iff (top-level
  theorem of this file).

See `ROADMAP.md` at the project root for the dependency tree.
-/

namespace PCP.HaltToMPCP

open Turing PCP

/-! ## Alphabet of the reduced MPCP instance -/

/-- The alphabet of the reduced MPCP instance.

* `tape`   lifts a tape symbol of the original TM (an `Option Symbol`,
  where `none` is the blank).
* `state`  lifts a TM state (used to mark the head position in a
  configuration encoding).
* `halt`   marks the halted TM (CSLib's halting state is `none`, which
  has no tag — we introduce `halt` as the encoding's marker).
* `sep`    is the `#` configuration separator.
-/
inductive Alpha (Q : Type) (S : Type) where
  | tape  : Option S → Alpha Q S
  | state : Q → Alpha Q S
  | halt  : Alpha Q S
  | sep   : Alpha Q S
  deriving DecidableEq

@[inherit_doc Alpha.tape]  prefix:max "↟ₜ" => Alpha.tape
@[inherit_doc Alpha.state] prefix:max "↟ₛ" => Alpha.state
@[inherit_doc Alpha.sep]   notation "#"   => Alpha.sep
@[inherit_doc Alpha.halt]  notation "h⊥"  => Alpha.halt

/-! ## Encoding configurations -/

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Lift a list of TM tape symbols to a list over the reduced alphabet. -/
def liftTape (tm : SingleTapeTM Symbol) (l : List (Option Symbol)) :
    List (Alpha tm.State Symbol) :=
  l.map Alpha.tape

@[simp] lemma liftTape_nil (tm : SingleTapeTM Symbol) :
    liftTape tm ([] : List (Option Symbol)) = [] := rfl

@[simp] lemma liftTape_cons (tm : SingleTapeTM Symbol) (a : Option Symbol)
    (l : List (Option Symbol)) :
    liftTape tm (a :: l) = ↟ₜa :: liftTape tm l := rfl

@[simp] lemma liftTape_append (tm : SingleTapeTM Symbol) (l₁ l₂ : List (Option Symbol)) :
    liftTape tm (l₁ ++ l₂) = liftTape tm l₁ ++ liftTape tm l₂ := by
  simp [liftTape, List.map_append]

/-- Encode a `BiTape` as the finite word
    `left.reverse ++ [head] ++ right`
    over `Option Symbol`. This captures exactly the non-blank window of
    the tape (with the head symbol in the middle). -/
def biTapeToList (t : BiTape Symbol) : List (Option Symbol) :=
  t.left.toList.reverse ++ t.head :: t.right.toList

/-- Encode a non-halted configuration `⟨some q, t⟩` as
    `left.reverse ++ ↟ₛq :: ↟ₜhead :: right`,
    placing the state marker immediately before the head symbol. -/
def encodeRunningCfg (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    List (Alpha tm.State Symbol) :=
  liftTape tm t.left.toList.reverse ++ ↟ₛq :: liftTape tm (t.head :: t.right.toList)

/-- Encode a halted configuration `⟨none, t⟩` using the synthetic `halt`
    marker in place of a state symbol. -/
def encodeHaltedCfg (tm : SingleTapeTM Symbol) (t : BiTape Symbol) :
    List (Alpha tm.State Symbol) :=
  liftTape tm t.left.toList.reverse ++ h⊥ :: liftTape tm (t.head :: t.right.toList)

/-- Encode an arbitrary configuration. -/
def encodeCfg (tm : SingleTapeTM Symbol) : tm.Cfg → List (Alpha tm.State Symbol)
  | ⟨some q, t⟩ => encodeRunningCfg tm q t
  | ⟨none,   t⟩ => encodeHaltedCfg tm t

/-- Wrap a configuration encoding in `#…#` separators (one full block). -/
def block (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) :
    List (Alpha tm.State Symbol) :=
  # :: encodeCfg tm cfg ++ [#]

/-- The encoding of the initial configuration on input `w`. -/
def initBlock (tm : SingleTapeTM Symbol) (w : List Symbol) :
    List (Alpha tm.State Symbol) :=
  block tm (SingleTapeTM.initCfg tm w)

@[simp] lemma encodeCfg_running (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) :
    encodeCfg tm { state := some q, BiTape := t } = encodeRunningCfg tm q t := rfl

@[simp] lemma encodeCfg_halted (tm : SingleTapeTM Symbol) (t : BiTape Symbol) :
    encodeCfg tm { state := none, BiTape := t } = encodeHaltedCfg tm t := rfl

/-! ## Tile constructors

These are the building blocks of the reduced MPCP instance. The simulation
invariant maintained throughout a matching solution is:

  `bot = top ++ "lookahead by one configuration"`.

The start tile establishes this offset with `top = #` and
`bot = # initBlock #`. Copy tiles and the separator tile preserve the
offset. Transition tiles advance the bot by one TM step relative to the
top. Halt-absorb tiles and the final tile let the top catch up once the
TM has halted. -/

/-- The *start* tile: forces every solution to begin by seeding the bottom
    string with the encoded initial configuration `# C₀ #`, while the top
    is just `#`. The resulting offset is the simulation lookahead. -/
def startTile (tm : SingleTapeTM Symbol) (w : List Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [#]
  bot := # :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#]

/-- A *copy* tile for tape symbol `a`. Replicating these advances the
    portion of a configuration that is unchanged by the current step. -/
def copyTile (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₜa]
  bot := [↟ₜa]

/-- The *separator-copy* tile, used between configurations. -/
def sepTile (tm : SingleTapeTM Symbol) : Tile (Alpha tm.State Symbol) where
  top := [#]
  bot := [#]

/-! ### Transition tiles

For each transition `tm.tr q a = ((w, dir), q?)` the reduction provides one
or more tiles realising the local rewrite around the head. The new state
`q?` is `Option tm.State`: `some q'` if the TM continues, `none` if the
TM halts (in which case the encoded bot uses the synthetic `h⊥` marker
in place of a state symbol).

Below, each tile constructor takes the *new state encoding* `qNew :
Alpha tm.State Symbol` directly. This is either `↟ₛq'` for a continuing
transition or `h⊥` for a halting one — see `stateMarker` below. -/

/-- The encoding of a possibly-halting next state as a single alphabet
    symbol: `↟ₛq'` if the TM continues to state `q'`, otherwise `h⊥`. -/
def stateMarker (tm : SingleTapeTM Symbol) :
    Option tm.State → Alpha tm.State Symbol
  | some q' => ↟ₛq'
  | none    => h⊥

/-- Transition tile for a *no-move* step `q a → qNew w (no movement)`.
    Local rewrite: `↟ₛq ↟ₜa  →  qNew ↟ₜw`. -/
def noMoveTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa]
  bot := [stateMarker tm qNew, ↟ₜw]

/-- Transition tile for a *right-move* step `q a → qNew w right`, in the
    interior of the encoded tape.
    Local rewrite: `↟ₛq ↟ₜa  →  ↟ₜw qNew`. -/
def rightMoveTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa]
  bot := [↟ₜw, stateMarker tm qNew]

/-- Right-move transition at the *right boundary* of the encoded tape:
    the head moves into a previously blank cell, requiring an explicit
    `none` (blank) symbol to be inserted before the closing `#`.
    Local rewrite: `↟ₛq ↟ₜa #  →  ↟ₜw qNew ↟ₜnone #`. -/
def rightMoveBoundaryTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa, #]
  bot := [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol), #]

/-- Transition tile for a *left-move* step `q a → qNew w left`, in the
    interior of the encoded tape, with `b` the symbol immediately to the
    left of the head.
    Local rewrite: `↟ₜb ↟ₛq ↟ₜa  →  qNew ↟ₜb ↟ₜw`. -/
def leftMoveTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol)
    (b : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₜb, ↟ₛq, ↟ₜa]
  bot := [stateMarker tm qNew, ↟ₜb, ↟ₜw]

/-- Left-move transition at the *left boundary* of the encoded tape:
    the head moves into a previously blank cell, requiring an explicit
    `none` (blank) symbol to be inserted as the new head.
    Local rewrite: `↟ₛq ↟ₜa  →  qNew ↟ₜnone ↟ₜw`. The opening `#` of
    the block is NOT included here; it is the closing `#` of the
    previous block (already produced by the previous step's `sepTile`
    or the `startTile`). The new tile has top length 2 and bot
    length 3, the `none` extending the encoded window leftward. -/
def leftMoveBoundaryTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa]
  bot := [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw]

/-! ### Halt-absorb tiles

After the TM halts the bot ends in `# … h⊥ … #`. The top must catch up.
Each absorb tile extends the top by *two* alphabet symbols and the bot by
*one* (`h⊥`), shrinking the tape window around `h⊥` until only `h⊥`
remains adjacent to the surrounding `#`s. -/

/-- Absorb a tape symbol immediately to the *left* of the halt marker:
    `↟ₜa h⊥  →  h⊥`. -/
def absorbLeftTile (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₜa, h⊥]
  bot := [h⊥]

/-- Absorb a tape symbol immediately to the *right* of the halt marker:
    `h⊥ ↟ₜa  →  h⊥`. -/
def absorbRightTile (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [h⊥, ↟ₜa]
  bot := [h⊥]

/-- The *final* tile, closing the matching. After all tape symbols have
    been absorbed, the bot ends in `# h⊥ #` and the top lags by `h⊥ # #`.
    Applying `(h⊥ # #, #)` extends the top by `h⊥ # #` and the bot by
    `#`, equalising the two. -/
def finalTile (tm : SingleTapeTM Symbol) : Tile (Alpha tm.State Symbol) where
  top := [h⊥, #, #]
  bot := [#]

/-! ### Tile-projection simp lemmas -/

@[simp] lemma copyTile_top (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (copyTile tm a).top = [↟ₜa] := rfl

@[simp] lemma copyTile_bot (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (copyTile tm a).bot = [↟ₜa] := rfl

@[simp] lemma sepTile_top (tm : SingleTapeTM Symbol) :
    (sepTile tm).top = [#] := rfl

@[simp] lemma sepTile_bot (tm : SingleTapeTM Symbol) :
    (sepTile tm).bot = [#] := rfl

@[simp] lemma stateMarker_some (tm : SingleTapeTM Symbol) (q' : tm.State) :
    stateMarker tm (some q') = ↟ₛq' := rfl

@[simp] lemma stateMarker_none (tm : SingleTapeTM Symbol) :
    stateMarker tm (none : Option tm.State) = h⊥ := rfl

@[simp] lemma finalTile_top (tm : SingleTapeTM Symbol) :
    (finalTile tm).top = [h⊥, #, #] := rfl

@[simp] lemma finalTile_bot (tm : SingleTapeTM Symbol) :
    (finalTile tm).bot = [#] := rfl

/-! ## Tile enumeration

We enumerate the regular MPCP tiles arising from a TM. The start tile is
*not* in this list — it is the dedicated `MHasSolution` start argument. -/

/-- All copy tiles, one per tape symbol (`Option Symbol`, including the
    blank). -/
noncomputable def copyTiles (tm : SingleTapeTM Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (Finset.univ : Finset (Option Symbol)).toList.map (copyTile tm)

/-- The two halt-absorb tiles for a given tape symbol. -/
def absorbTilesFor (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  [absorbLeftTile tm a, absorbRightTile tm a]

/-- All halt-absorb tiles, two per tape symbol. -/
noncomputable def absorbTiles (tm : SingleTapeTM Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (Finset.univ : Finset (Option Symbol)).toList.flatMap (absorbTilesFor tm)

/-- The transition tiles for a single `(q, a)` pair: depending on the
    movement direction, this is either a single tile (no movement),
    two tiles (right move + boundary), or `1 + |Option Symbol|` tiles
    (left move at boundary + one per possible left-neighbour symbol). -/
noncomputable def transitionTilesFor (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) : List (Tile (Alpha tm.State Symbol)) :=
  match tm.tr q a with
  | (⟨w, none⟩, qNew) =>
      [noMoveTile tm q a qNew w]
  | (⟨w, some Dir.right⟩, qNew) =>
      [rightMoveTile tm q a qNew w, rightMoveBoundaryTile tm q a qNew w]
  | (⟨w, some Dir.left⟩, qNew) =>
      -- Following Hopcroft–Ullman–Motwani's one-sided-tape design, we
      -- do *not* include `leftMoveBoundaryTile` here. The forward
      -- direction is gated by `NoLeftBoundary`, which ensures the
      -- TM never invokes a left-move at the left boundary, so no
      -- boundary tile is ever needed in the simulation.
      (Finset.univ : Finset (Option Symbol)).toList.map
        (fun b => leftMoveTile tm q a qNew w b)

/-- All transition tiles, ranging over every `(q, a)` input pair. -/
noncomputable def transitionTiles (tm : SingleTapeTM Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (Finset.univ : Finset (tm.State × Option Symbol)).toList.flatMap
    (fun qa => transitionTilesFor tm qa.1 qa.2)

/-- The full list of MPCP tiles for the reduction (excluding the start
    tile, which is the dedicated start argument of `MHasSolution`).

    This is `noncomputable` because it relies on `Finset.toList`, which is
    noncomputable in Lean. The underlying enumeration is conceptually a
    finite set of tiles — we use it only as a mathematical object inside
    `MHasSolution`. -/
noncomputable def haltTiles (tm : SingleTapeTM Symbol) :
    Stack (Alpha tm.State Symbol) :=
  copyTiles tm ++
  [sepTile tm] ++
  transitionTiles tm ++
  absorbTiles tm ++
  [finalTile tm]

/-! ## The reduction

Pair the start tile with the rest of the tiles. The MPCP instance for
`Halts tm w` is `MHasSolution (startTile tm w) (haltTiles tm)`. -/

/-- The reduction `Halt ≤_m MPCP` packaged as a function from
    `(tm, w)` to an MPCP instance `(start, rest)`. -/
noncomputable def haltToMpcp (tm : SingleTapeTM Symbol) (w : List Symbol) :
    Tile (Alpha tm.State Symbol) × Stack (Alpha tm.State Symbol) :=
  (startTile tm w, haltTiles tm)

/-! ## Tile-membership lemmas

These are the basic facts that the constructed tiles actually belong to
`haltTiles tm`. They form the bookkeeping backbone of both directions of
the main theorem (the start-tile is *not* in `haltTiles` — it is the
forced start argument of `MHasSolution`). -/

/-- The copy tile for `a` is in `haltTiles`. -/
lemma copyTile_mem_haltTiles (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    copyTile tm a ∈ haltTiles tm := by
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  exact List.mem_map.mpr ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), rfl⟩

/-- The separator-copy tile is in `haltTiles`. -/
lemma sepTile_mem_haltTiles (tm : SingleTapeTM Symbol) :
    sepTile tm ∈ haltTiles tm := by
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- The final tile is in `haltTiles`. -/
lemma finalTile_mem_haltTiles (tm : SingleTapeTM Symbol) :
    finalTile tm ∈ haltTiles tm := by
  refine List.mem_append_right _ ?_
  exact List.mem_singleton.mpr rfl

/-- The left halt-absorb tile for `a` is in `haltTiles`. -/
lemma absorbLeftTile_mem_haltTiles (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    absorbLeftTile tm a ∈ haltTiles tm := by
  refine List.mem_append_left _ ?_
  refine List.mem_append_right _ ?_
  refine List.mem_flatMap.mpr ?_
  refine ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), ?_⟩
  exact List.mem_cons_self

/-- The right halt-absorb tile for `a` is in `haltTiles`. -/
lemma absorbRightTile_mem_haltTiles (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    absorbRightTile tm a ∈ haltTiles tm := by
  refine List.mem_append_left _ ?_
  refine List.mem_append_right _ ?_
  refine List.mem_flatMap.mpr ?_
  refine ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), ?_⟩
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Helper: every tile produced by `transitionTilesFor tm q a` belongs to
    `transitionTiles tm`. -/
lemma transitionTilesFor_subset_transitionTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (t : Tile (Alpha tm.State Symbol))
    (ht : t ∈ transitionTilesFor tm q a) :
    t ∈ transitionTiles tm := by
  refine List.mem_flatMap.mpr ⟨(q, a), ?_, ht⟩
  exact Finset.mem_toList.mpr (Finset.mem_univ _)

/-- Every transition tile is in `haltTiles`. -/
lemma transitionTile_mem_haltTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (t : Tile (Alpha tm.State Symbol))
    (ht : t ∈ transitionTilesFor tm q a) :
    t ∈ haltTiles tm := by
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  refine List.mem_append_right _ ?_
  exact transitionTilesFor_subset_transitionTiles tm q a t ht

/-! ## Concatenation lemmas for sequences of copy tiles

The forward direction of the main reduction repeatedly concatenates copy
tiles to walk through the unchanged portion of a configuration. These
lemmas reduce `tau1`/`tau2` of such sequences to the underlying lifted
tape list. -/

/-- The top of a sequence of copy tiles is the lifted tape list. -/
@[simp]
lemma tau1_map_copyTile (tm : SingleTapeTM Symbol) (syms : List (Option Symbol)) :
    tau1 (syms.map (copyTile tm)) = liftTape tm syms := by
  induction syms with
  | nil => rfl
  | cons a syms ih => simp [tau1_cons, ih, liftTape]

/-- The bottom of a sequence of copy tiles is the lifted tape list. -/
@[simp]
lemma tau2_map_copyTile (tm : SingleTapeTM Symbol) (syms : List (Option Symbol)) :
    tau2 (syms.map (copyTile tm)) = liftTape tm syms := by
  induction syms with
  | nil => rfl
  | cons a syms ih => simp [tau2_cons, ih, liftTape]

/-- The top of a single-tile stack is just that tile's top. -/
@[simp]
lemma tau1_singleton (tm : SingleTapeTM Symbol) (t : Tile (Alpha tm.State Symbol)) :
    tau1 [t] = t.top := by
  simp [tau1_cons]

/-- The bottom of a single-tile stack is just that tile's bottom. -/
@[simp]
lemma tau2_singleton (tm : SingleTapeTM Symbol) (t : Tile (Alpha tm.State Symbol)) :
    tau2 [t] = t.bot := by
  simp [tau2_cons]

/-- A list of copy tiles consists entirely of tiles from `haltTiles`. -/
lemma map_copyTile_subset_haltTiles (tm : SingleTapeTM Symbol)
    (syms : List (Option Symbol)) (t : Tile (Alpha tm.State Symbol))
    (ht : t ∈ syms.map (copyTile tm)) :
    t ∈ haltTiles tm := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
  exact copyTile_mem_haltTiles tm a

/-! ## Structural facts about `startTile` and `block` -/

@[simp]
lemma startTile_top (tm : SingleTapeTM Symbol) (w : List Symbol) :
    (startTile tm w).top = [#] := rfl

@[simp]
lemma startTile_bot (tm : SingleTapeTM Symbol) (w : List Symbol) :
    (startTile tm w).bot =
      # :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] := rfl

@[simp]
lemma block_eq (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) :
    block tm cfg = # :: encodeCfg tm cfg ++ [#] := rfl

/-! ## Simulation tiles for one TM step (no-move case)

For a TM step `(q, t.head) → ((w, none), qNew)` where `none` is the
no-move direction, the simulation tile sequence is:

  copy l_n … copy l_1   transition   copy r_1 … copy r_m   sepTile

with `tau1` reproducing the *old* configuration block and `tau2`
producing the *new* configuration block. -/

/-- Tile sequence simulating a single no-move TM step. -/
def stepTilesNoMove (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.toList.reverse.map (copyTile tm)) ++
  [noMoveTile tm q t.head qNew w] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

@[simp] lemma noMoveTile_top (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    (noMoveTile tm q a qNew w).top = [↟ₛq, ↟ₜa] := rfl

@[simp] lemma noMoveTile_bot (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    (noMoveTile tm q a qNew w).bot = [stateMarker tm qNew, ↟ₜw] := rfl

/-- The top concatenation of `stepTilesNoMove` reproduces the *current*
    configuration block (modulo the leading `#` which is shared with the
    previous block). -/
lemma tau1_stepTilesNoMove (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau1 (stepTilesNoMove tm q qNew t w) =
      encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesNoMove, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, noMoveTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, liftTape_cons]
  simp [List.append_assoc]

/-- The bottom concatenation of `stepTilesNoMove` produces the *next*
    configuration block — the one obtained by writing `w` and not moving,
    with new state `qNew`. -/
lemma tau2_stepTilesNoMove (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau2 (stepTilesNoMove tm q qNew t w) =
      liftTape tm t.left.toList.reverse ++
      [stateMarker tm qNew] ++
      liftTape tm (w :: t.right.toList) ++
      [#] := by
  simp only [stepTilesNoMove, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, noMoveTile_bot, sepTile_bot,
             List.append_nil, liftTape_cons]
  simp [List.append_assoc]

/-- Every tile in `stepTilesNoMove` is a member of `haltTiles`. -/
lemma stepTilesNoMove_subset_haltTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, none⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesNoMove tm q qNew t w) :
    tile ∈ haltTiles tm := by
  simp only [stepTilesNoMove, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · -- copy of a left symbol
    exact map_copyTile_subset_haltTiles tm _ tile hl
  · -- the transition tile itself
    refine transitionTile_mem_haltTiles tm q a _ ?_
    simp only [transitionTilesFor]
    rw [show tm.tr q a = (⟨w, none⟩, qNew) from htr]
    subst hhead
    exact List.mem_cons_self
  · -- copy of a right symbol
    exact map_copyTile_subset_haltTiles tm _ tile hr
  · -- the separator tile
    exact sepTile_mem_haltTiles tm

/-! ## Simulation tiles for one TM step (right-move, interior case)

For a TM step `tm.tr q t.head = (⟨w, some right⟩, qNew)` where
`t.right.toList ≠ []` (the head is not at the right boundary of the
encoded window), the simulation tile sequence is:

  copy l_n … copy l_1   rightMoveTile   copy r_1 … copy r_m   sepTile

The `tau1` reproduces the *current* configuration block (modulo the
leading `#` shared with the previous block). The `tau2` extends
`bot` by an explicit list expression which agrees with
`encodeCfg(next config) ++ [#]` whenever the move does not run into
the cslib `StackTape.cons` blank-stripping degenerate case
(`w = none ∧ t.left.toList = []`). -/

/-- Tile sequence simulating a single right-move TM step in the
    *interior* (when `t.right` is non-empty). -/
def stepTilesRightInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.toList.reverse.map (copyTile tm)) ++
  [rightMoveTile tm q t.head qNew w] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

@[simp] lemma rightMoveTile_top (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    (rightMoveTile tm q a qNew w).top = [↟ₛq, ↟ₜa] := rfl

@[simp] lemma rightMoveTile_bot (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    (rightMoveTile tm q a qNew w).bot = [↟ₜw, stateMarker tm qNew] := rfl

/-- The top concatenation of `stepTilesRightInterior` reproduces the
    *current* configuration block — exactly as in the no-move case,
    since the top side of the transition tile records `q` and the
    head symbol identically in both cases. -/
lemma tau1_stepTilesRightInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau1 (stepTilesRightInterior tm q qNew t w) =
      encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesRightInterior, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, rightMoveTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, liftTape_cons]
  simp [List.append_assoc]

/-- The bottom concatenation of `stepTilesRightInterior`, in explicit
    list form. The connection to `encodeCfg` of the post-step
    configuration requires non-degeneracy
    (`w = some _ ∨ t.left.toList ≠ []`) — see
    `encodeCfg_after_right_move_eq` below. -/
lemma tau2_stepTilesRightInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau2 (stepTilesRightInterior tm q qNew t w) =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew] ++
      liftTape tm t.right.toList ++
      [#] := by
  simp only [stepTilesRightInterior, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, rightMoveTile_bot, sepTile_bot,
             List.append_nil]

/-- Every tile in `stepTilesRightInterior` is a member of `haltTiles`. -/
lemma stepTilesRightInterior_subset_haltTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Dir.right⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesRightInterior tm q qNew t w) :
    tile ∈ haltTiles tm := by
  simp only [stepTilesRightInterior, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · -- copy of a left symbol
    exact map_copyTile_subset_haltTiles tm _ tile hl
  · -- the transition tile itself
    refine transitionTile_mem_haltTiles tm q a _ ?_
    simp only [transitionTilesFor]
    rw [show tm.tr q a = (⟨w, some Dir.right⟩, qNew) from htr]
    subst hhead
    exact List.mem_cons_self
  · -- copy of a right symbol
    exact map_copyTile_subset_haltTiles tm _ tile hr
  · -- the separator tile
    exact sepTile_mem_haltTiles tm

/-! ### Connecting `tau2_stepTilesRightInterior` to `encodeCfg` of the
    post-step configuration (non-degenerate case). -/

omit [Inhabited Symbol] [Fintype Symbol] in
/-- In the non-degenerate case (`w ≠ none ∨ xs.toList ≠ []`),
    the cslib `StackTape.cons` does *not* strip blanks, so the new
    `toList` is exactly `w :: xs.toList`. -/
lemma cons_toList_of_nondeg (w : Option Symbol)
    (xs : Turing.StackTape Symbol)
    (h : w ≠ none ∨ xs.toList ≠ []) :
    (Turing.StackTape.cons w xs).toList = w :: xs.toList := by
  obtain ⟨tl, hLast⟩ := xs
  cases tl with
  | nil =>
    cases w with
    | none =>
      rcases h with h | h
      · exact absurd rfl h
      · exact absurd rfl h
    | some s => rfl
  | cons hd tl' =>
    cases w with
    | none => rfl
    | some _ => rfl

omit [Inhabited Symbol] [Fintype Symbol] in
/-- For a non-empty `StackTape`, `head :: tail.toList = toList`. This
    is the `toList`-projection of cslib's `cons_head_tail`, valid
    whenever `xs.toList` is non-empty (so that `cons xs.head xs.tail`
    does not degenerate). -/
lemma head_cons_tail_toList (xs : Turing.StackTape Symbol)
    (h : xs.toList ≠ []) :
    xs.head :: xs.tail.toList = xs.toList := by
  obtain ⟨tl, hLast⟩ := xs
  cases tl with
  | nil => exact absurd rfl h
  | cons a rest => rfl

/-- Lifted form of `head_cons_tail_toList`: when `xs.toList ≠ []`,
    rewriting `↟ₜxs.head :: liftTape tm xs.tail.toList` to
    `liftTape tm xs.toList`. -/
lemma liftTape_head_cons_tail_toList (tm : SingleTapeTM Symbol)
    (xs : Turing.StackTape Symbol) (h : xs.toList ≠ []) :
    ↟ₜxs.head :: liftTape tm xs.tail.toList = liftTape tm xs.toList := by
  rw [show (↟ₜxs.head : Alpha tm.State Symbol) :: liftTape tm xs.tail.toList
       = liftTape tm (xs.head :: xs.tail.toList) from rfl,
      head_cons_tail_toList _ h]

/-- The encoding of the configuration after one right-move step,
    in the non-degenerate case (so the new left side really is
    `w :: t.left.toList`). -/
lemma encodeCfg_after_right_move_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (h_right_ne : t.right.toList ≠ []) :
    encodeCfg tm ⟨qNew, (t.write w).move_right⟩ =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew] ++
      liftTape tm t.right.toList := by
  -- Unfold the cslib step on the BiTape side.
  have h_left :
      ((t.write w).move_right).left.toList = w :: t.left.toList := by
    show (Turing.StackTape.cons _ _).toList = _
    exact cons_toList_of_nondeg w t.left h_nondeg
  have h_head : ((t.write w).move_right).head = t.right.head := rfl
  have h_right :
      ((t.write w).move_right).right.toList = t.right.tail.toList := rfl
  -- Now compute the encoding.
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_none]
    rw [liftTape_head_cons_tail_toList _ _ h_right_ne]
    simp [List.append_assoc]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_some]
    rw [liftTape_head_cons_tail_toList _ _ h_right_ne]
    simp [List.append_assoc]

/-- Combined statement: in the non-degenerate, interior right-move
    case, `tau2 = encodeCfg(post-step config) ++ [#]`, matching the
    simulation invariant. -/
lemma tau2_stepTilesRightInterior_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (h_right_ne : t.right.toList ≠ []) :
    tau2 (stepTilesRightInterior tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).move_right⟩ ++ [#] := by
  rw [tau2_stepTilesRightInterior,
      encodeCfg_after_right_move_eq tm qNew t w h_nondeg h_right_ne]

/-! ## Simulation tiles for one TM step (right-move, boundary case)

When the head is at the right boundary of the encoded window
(`t.right.toList = []`), the right-move transition uses
`rightMoveBoundaryTile`, which packages the local rewrite together
with the closing `#` and the explicit blank for the new head:

  copy l_n … copy l_1   rightMoveBoundaryTile

The boundary tile already contains the closing `#`, so no separate
`sepTile` is appended. -/

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The `head` of a `StackTape` whose `toList` is empty is `none`. -/
lemma head_of_toList_eq_nil (xs : Turing.StackTape Symbol)
    (h : xs.toList = []) : xs.head = none := by
  obtain ⟨tl, hLast⟩ := xs
  simp only at h
  subst h
  rfl

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The `tail` of an empty `StackTape` is also empty. -/
lemma tail_toList_of_toList_eq_nil (xs : Turing.StackTape Symbol)
    (h : xs.toList = []) : xs.tail.toList = [] := by
  obtain ⟨tl, hLast⟩ := xs
  simp only at h
  subst h
  rfl

/-- Tile sequence simulating a single right-move TM step in the
    *boundary* case (`t.right.toList = []`). -/
def stepTilesRightBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.toList.reverse.map (copyTile tm)) ++
  [rightMoveBoundaryTile tm q t.head qNew w]

@[simp] lemma rightMoveBoundaryTile_top (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (w : Option Symbol) :
    (rightMoveBoundaryTile tm q a qNew w).top = [↟ₛq, ↟ₜa, #] := rfl

@[simp] lemma rightMoveBoundaryTile_bot (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (w : Option Symbol) :
    (rightMoveBoundaryTile tm q a qNew w).bot =
      [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol), #] := rfl

/-- The top concatenation of `stepTilesRightBoundary` reproduces the
    *current* configuration block. The hypothesis
    `t.right.toList = []` is used to simplify the encoding (no right
    symbols to copy after the transition tile). -/
lemma tau1_stepTilesRightBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_right_empty : t.right.toList = []) :
    tau1 (stepTilesRightBoundary tm q qNew t w) =
      encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesRightBoundary, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, rightMoveBoundaryTile_top,
             List.append_nil, encodeRunningCfg, h_right_empty,
             liftTape_cons, liftTape_nil]
  simp [List.append_assoc]

/-- The bottom concatenation of `stepTilesRightBoundary`, in explicit
    list form. -/
lemma tau2_stepTilesRightBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau2 (stepTilesRightBoundary tm q qNew t w) =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol), #] := by
  simp only [stepTilesRightBoundary, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, rightMoveBoundaryTile_bot,
             List.append_nil]

/-- Every tile in `stepTilesRightBoundary` is a member of `haltTiles`. -/
lemma stepTilesRightBoundary_subset_haltTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Dir.right⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesRightBoundary tm q qNew t w) :
    tile ∈ haltTiles tm := by
  simp only [stepTilesRightBoundary, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with hl | rfl
  · -- copy of a left symbol
    exact map_copyTile_subset_haltTiles tm _ tile hl
  · -- the right-move boundary tile
    refine transitionTile_mem_haltTiles tm q a _ ?_
    simp only [transitionTilesFor]
    rw [show tm.tr q a = (⟨w, some Dir.right⟩, qNew) from htr]
    subst hhead
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The encoding of the configuration after one right-move step at
    the right boundary, in the non-degenerate case. -/
lemma encodeCfg_after_right_move_boundary_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (h_right_empty : t.right.toList = []) :
    encodeCfg tm ⟨qNew, (t.write w).move_right⟩ =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol)] := by
  have h_left :
      ((t.write w).move_right).left.toList = w :: t.left.toList := by
    show (Turing.StackTape.cons _ _).toList = _
    exact cons_toList_of_nondeg w t.left h_nondeg
  have h_head : ((t.write w).move_right).head = none := by
    show t.right.head = _
    exact head_of_toList_eq_nil _ h_right_empty
  have h_right :
      ((t.write w).move_right).right.toList = [] := by
    show t.right.tail.toList = _
    exact tail_toList_of_toList_eq_nil _ h_right_empty
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_none]
    simp [List.append_assoc]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_some]
    simp [List.append_assoc]

/-- Combined statement: in the non-degenerate right-move boundary
    case, `tau2 = encodeCfg(post-step config) ++ [#]`. -/
lemma tau2_stepTilesRightBoundary_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (h_right_empty : t.right.toList = []) :
    tau2 (stepTilesRightBoundary tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).move_right⟩ ++ [#] := by
  rw [tau2_stepTilesRightBoundary,
      encodeCfg_after_right_move_boundary_eq tm qNew t w h_nondeg h_right_empty]
  simp [List.append_assoc]

/-! ## Simulation tiles for one TM step (left-move, interior case)

For a TM step `tm.tr q t.head = (⟨w, some left⟩, qNew)` where the head
is *not* at the left boundary (`t.left.toList ≠ []`), the simulation
tile sequence is:

  copy l_n … copy l_2   leftMoveTile (b = l_1)   copy r_1 … copy r_m   sepTile

The `leftMoveTile` swaps the local window
`l_1 q t.head  →  qNew l_1 w`, where `l_1 = t.left.head` is the symbol
that becomes the new head after moving left. -/

/-- The `leftMoveTile` for any "left-neighbour" symbol `b` belongs to
    `transitionTilesFor q a` whenever the TM transition there is a
    left move. -/
lemma leftMoveTile_mem_transitionTilesFor (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (w : Option Symbol)
    (qNew : Option tm.State) (b : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Dir.left⟩, qNew)) :
    leftMoveTile tm q a qNew w b ∈ transitionTilesFor tm q a := by
  simp only [transitionTilesFor]
  rw [htr]
  exact List.mem_map.mpr
    ⟨b, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩

/-- Tile sequence simulating a single left-move TM step in the
    *interior* (when `t.left` is non-empty). -/
def stepTilesLeftInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.tail.toList.reverse.map (copyTile tm)) ++
  [leftMoveTile tm q t.head qNew w t.left.head] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

@[simp] lemma leftMoveTile_top (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol)
    (b : Option Symbol) :
    (leftMoveTile tm q a qNew w b).top = [↟ₜb, ↟ₛq, ↟ₜa] := rfl

@[simp] lemma leftMoveTile_bot (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol)
    (b : Option Symbol) :
    (leftMoveTile tm q a qNew w b).bot =
      [stateMarker tm qNew, ↟ₜb, ↟ₜw] := rfl

/-- The top concatenation of `stepTilesLeftInterior` reproduces the
    *current* configuration block. The hypothesis
    `t.left.toList ≠ []` is used to splice the head of `t.left` back
    into the encoding via `head_cons_tail_toList`. -/
lemma tau1_stepTilesLeftInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_left_ne : t.left.toList ≠ []) :
    tau1 (stepTilesLeftInterior tm q qNew t w) =
      encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesLeftInterior, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, leftMoveTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, liftTape_cons]
  have h_split :
      t.left.toList.reverse = t.left.tail.toList.reverse ++ [t.left.head] := by
    conv_lhs => rw [← head_cons_tail_toList t.left h_left_ne]
    simp [List.reverse_cons]
  rw [h_split, liftTape_append, liftTape_cons, liftTape_nil]
  simp [List.append_assoc]

/-- The bottom concatenation of `stepTilesLeftInterior`, in explicit
    list form. -/
lemma tau2_stepTilesLeftInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau2 (stepTilesLeftInterior tm q qNew t w) =
      liftTape tm t.left.tail.toList.reverse ++
      [stateMarker tm qNew, ↟ₜt.left.head, ↟ₜw] ++
      liftTape tm t.right.toList ++
      [#] := by
  simp only [stepTilesLeftInterior, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, leftMoveTile_bot, sepTile_bot,
             List.append_nil]

/-- Every tile in `stepTilesLeftInterior` is a member of `haltTiles`. -/
lemma stepTilesLeftInterior_subset_haltTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Dir.left⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesLeftInterior tm q qNew t w) :
    tile ∈ haltTiles tm := by
  simp only [stepTilesLeftInterior, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_haltTiles tm _ tile hl
  · refine transitionTile_mem_haltTiles tm q a _ ?_
    subst hhead
    exact leftMoveTile_mem_transitionTilesFor tm q t.head w qNew t.left.head htr
  · exact map_copyTile_subset_haltTiles tm _ tile hr
  · exact sepTile_mem_haltTiles tm

/-- The encoding of the configuration after one left-move step,
    in the non-degenerate case (so the new right side really is
    `w :: t.right.toList`). Note: this holds regardless of whether
    `t.left` is empty — when `t.left` is empty, `tail` is empty and
    `head` is `none`, so both sides reduce to the same expression. -/
lemma encodeCfg_after_left_move_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ []) :
    encodeCfg tm ⟨qNew, (t.write w).move_left⟩ =
      liftTape tm t.left.tail.toList.reverse ++
      [stateMarker tm qNew, ↟ₜt.left.head, ↟ₜw] ++
      liftTape tm t.right.toList := by
  have h_left :
      ((t.write w).move_left).left.toList = t.left.tail.toList := rfl
  have h_head : ((t.write w).move_left).head = t.left.head := rfl
  have h_right :
      ((t.write w).move_left).right.toList = w :: t.right.toList := by
    show (Turing.StackTape.cons _ _).toList = _
    exact cons_toList_of_nondeg w t.right h_nondeg
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               liftTape_cons, stateMarker_none]
    simp [List.append_assoc]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               liftTape_cons, stateMarker_some]
    simp [List.append_assoc]

/-- Combined statement: in the non-degenerate left-move interior
    case, `tau2 = encodeCfg(post-step config) ++ [#]`. -/
lemma tau2_stepTilesLeftInterior_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ []) :
    tau2 (stepTilesLeftInterior tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).move_left⟩ ++ [#] := by
  rw [tau2_stepTilesLeftInterior,
      encodeCfg_after_left_move_eq tm qNew t w h_nondeg]

/-! ## Simulation tiles for one TM step (left-move, boundary case)

When the head is at the left boundary of the encoded window
(`t.left.toList = []`), the left-move transition uses
`leftMoveBoundaryTile`, which inserts an explicit `none` for the new
head (extending the encoded window leftward by one blank). The
opening `#` of the block stays with the previous step's `sepTile`
(or `startTile`), so the boundary tile here, like the no-move and
right-interior tiles, contains no leading or trailing `#`. -/

/-- Tile sequence simulating a single left-move TM step in the
    *boundary* case (`t.left.toList = []`). -/
def stepTilesLeftBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  [leftMoveBoundaryTile tm q t.head qNew w] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

@[simp] lemma leftMoveBoundaryTile_top (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (w : Option Symbol) :
    (leftMoveBoundaryTile tm q a qNew w).top = [↟ₛq, ↟ₜa] := rfl

@[simp] lemma leftMoveBoundaryTile_bot (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (w : Option Symbol) :
    (leftMoveBoundaryTile tm q a qNew w).bot =
      [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw] := rfl

/-- The top concatenation of `stepTilesLeftBoundary` reproduces the
    *current* configuration block. Uses `t.left.toList = []` to
    simplify the encoding. -/
lemma tau1_stepTilesLeftBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_left_empty : t.left.toList = []) :
    tau1 (stepTilesLeftBoundary tm q qNew t w) =
      encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesLeftBoundary, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, leftMoveBoundaryTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, h_left_empty,
             liftTape_cons, liftTape_nil, List.reverse_nil]
  simp

/-- The bottom concatenation of `stepTilesLeftBoundary`, in explicit
    list form. -/
lemma tau2_stepTilesLeftBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau2 (stepTilesLeftBoundary tm q qNew t w) =
      [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw] ++
      liftTape tm t.right.toList ++
      [#] := by
  simp only [stepTilesLeftBoundary, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, leftMoveBoundaryTile_bot, sepTile_bot,
             List.append_nil]

-- NOTE: `stepTilesLeftBoundary_subset_haltTiles` is intentionally not
-- provided. Following Hopcroft–Ullman–Motwani's one-sided tape design,
-- `leftMoveBoundaryTile` is *not* in `haltTiles`, so the sequence
-- `stepTilesLeftBoundary` is not a sub-sequence of `haltTiles` either.
-- The forward direction is gated by `NoLeftBoundary`, which ensures
-- the dispatcher (`stepTilesAux`) never enters the left-boundary branch
-- in a reachable configuration.

/-- The encoding of the configuration after one left-move step at the
    left boundary, in the non-degenerate case. -/
lemma encodeCfg_after_left_move_boundary_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ [])
    (h_left_empty : t.left.toList = []) :
    encodeCfg tm ⟨qNew, (t.write w).move_left⟩ =
      [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw] ++
      liftTape tm t.right.toList := by
  have h_left :
      ((t.write w).move_left).left.toList = [] := by
    show t.left.tail.toList = _
    exact tail_toList_of_toList_eq_nil _ h_left_empty
  have h_head : ((t.write w).move_left).head = none := by
    show t.left.head = _
    exact head_of_toList_eq_nil _ h_left_empty
  have h_right :
      ((t.write w).move_left).right.toList = w :: t.right.toList := by
    show (Turing.StackTape.cons _ _).toList = _
    exact cons_toList_of_nondeg w t.right h_nondeg
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               List.reverse_nil, liftTape_cons, liftTape_nil,
               stateMarker_none, List.nil_append, List.cons_append]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               List.reverse_nil, liftTape_cons, liftTape_nil,
               stateMarker_some, List.nil_append, List.cons_append]

/-- Combined statement: in the non-degenerate left-move boundary
    case, `tau2 = encodeCfg(post-step config) ++ [#]`. -/
lemma tau2_stepTilesLeftBoundary_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ [])
    (h_left_empty : t.left.toList = []) :
    tau2 (stepTilesLeftBoundary tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).move_left⟩ ++ [#] := by
  rw [tau2_stepTilesLeftBoundary,
      encodeCfg_after_left_move_boundary_eq tm qNew t w h_nondeg h_left_empty]

/-! ## Halt-absorption phase

After the TM halts the lookahead in `bot` ends with the encoded halt
configuration

  `[l_n … l_1, h⊥, head, r_1 … r_m, #]`.

We catch `top` up by repeatedly applying *absorb-left* and
*absorb-right* iterations, each shrinking the encoded window by
exactly one tape symbol. After all `n + (m+1)` iterations the
remaining lookahead is `[h⊥, #]`, which the `finalTile` then closes:
`(h⊥ # #, #)` makes `top` and `bot` equal.

Because the absorption phase eventually shrinks past the BiTape head
itself (which always has a value, even when blank), it is cleanest to
parameterise the iteration on raw `List (Option Symbol)` rather than
on `BiTape`. -/

/-- The *list-parameterised* halted encoding: `# ... l_n … l_1 h⊥ r ... #`
    (without the surrounding `#`s; those appear in the calling context). -/
def encodeHaltList (tm : SingleTapeTM Symbol)
    (left right : List (Option Symbol)) : List (Alpha tm.State Symbol) :=
  liftTape tm left.reverse ++ [h⊥] ++ liftTape tm right

/-- Bridge: the BiTape-based halted encoding equals the list-parameterised
    one with `left = t.left.toList` and `right = t.head :: t.right.toList`. -/
lemma encodeHaltedCfg_eq_encodeHaltList (tm : SingleTapeTM Symbol)
    (t : BiTape Symbol) :
    encodeHaltedCfg tm t =
      encodeHaltList tm t.left.toList (t.head :: t.right.toList) := by
  simp [encodeHaltedCfg, encodeHaltList, List.append_assoc]

@[simp] lemma absorbLeftTile_top (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (absorbLeftTile tm a).top = [↟ₜa, h⊥] := rfl

@[simp] lemma absorbLeftTile_bot (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (absorbLeftTile tm a).bot = [h⊥] := rfl

@[simp] lemma absorbRightTile_top (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (absorbRightTile tm a).top = [h⊥, ↟ₜa] := rfl

@[simp] lemma absorbRightTile_bot (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (absorbRightTile tm a).bot = [h⊥] := rfl

/-- Tile sequence for one *absorb-left* iteration. Removes the
    innermost left symbol `l` from the encoding `encodeHaltList (l :: rest) right`,
    yielding `encodeHaltList rest right`. -/
def stepTilesAbsorbLeft (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol)) :
    List (Tile (Alpha tm.State Symbol)) :=
  rest.reverse.map (copyTile tm) ++
  [absorbLeftTile tm l] ++
  right.map (copyTile tm) ++
  [sepTile tm]

/-- Tile sequence for one *absorb-right* iteration. Removes the
    leftmost right symbol `r` from the encoding `encodeHaltList left (r :: rest)`,
    yielding `encodeHaltList left rest`. -/
def stepTilesAbsorbRight (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol)
    (rest : List (Option Symbol)) :
    List (Tile (Alpha tm.State Symbol)) :=
  left.reverse.map (copyTile tm) ++
  [absorbRightTile tm r] ++
  rest.map (copyTile tm) ++
  [sepTile tm]

/-! ### `tau1` / `tau2` for one absorption iteration -/

lemma tau1_stepTilesAbsorbLeft (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol)) :
    tau1 (stepTilesAbsorbLeft tm l rest right) =
      encodeHaltList tm (l :: rest) right ++ [#] := by
  simp only [stepTilesAbsorbLeft, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, absorbLeftTile_top, sepTile_top,
             List.append_nil, encodeHaltList,
             List.reverse_cons, liftTape_append, liftTape_cons, liftTape_nil]
  simp [List.append_assoc]

lemma tau2_stepTilesAbsorbLeft (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol)) :
    tau2 (stepTilesAbsorbLeft tm l rest right) =
      encodeHaltList tm rest right ++ [#] := by
  simp only [stepTilesAbsorbLeft, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, absorbLeftTile_bot, sepTile_bot,
             List.append_nil, encodeHaltList]

lemma tau1_stepTilesAbsorbRight (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol)
    (rest : List (Option Symbol)) :
    tau1 (stepTilesAbsorbRight tm left r rest) =
      encodeHaltList tm left (r :: rest) ++ [#] := by
  simp only [stepTilesAbsorbRight, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, absorbRightTile_top, sepTile_top,
             List.append_nil, encodeHaltList, liftTape_cons]
  simp [List.append_assoc]

lemma tau2_stepTilesAbsorbRight (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol)
    (rest : List (Option Symbol)) :
    tau2 (stepTilesAbsorbRight tm left r rest) =
      encodeHaltList tm left rest ++ [#] := by
  simp only [stepTilesAbsorbRight, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, absorbRightTile_bot, sepTile_bot,
             List.append_nil, encodeHaltList]

/-! ### Membership of absorption iterations in `haltTiles` -/

lemma stepTilesAbsorbLeft_subset_haltTiles (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol))
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesAbsorbLeft tm l rest right) :
    tile ∈ haltTiles tm := by
  simp only [stepTilesAbsorbLeft, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_haltTiles tm _ tile hl
  · exact absorbLeftTile_mem_haltTiles tm l
  · exact map_copyTile_subset_haltTiles tm _ tile hr
  · exact sepTile_mem_haltTiles tm

lemma stepTilesAbsorbRight_subset_haltTiles (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol)
    (rest : List (Option Symbol))
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesAbsorbRight tm left r rest) :
    tile ∈ haltTiles tm := by
  simp only [stepTilesAbsorbRight, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_haltTiles tm _ tile hl
  · exact absorbRightTile_mem_haltTiles tm r
  · exact map_copyTile_subset_haltTiles tm _ tile hr
  · exact sepTile_mem_haltTiles tm

/-! ### `absorbAndFinish`: the absorption-phase tile suffix

Given a halt config presented as raw lists `(left, right)`, produce
the full tile sequence that:
1. Iteratively absorbs each left symbol (innermost first), then each
   right symbol (leftmost first), shrinking the encoded window down
   to `[h⊥]`.
2. Ends with `finalTile`.

The matching invariant
  `tau1 = encodeHaltList tm left right ++ [#] ++ tau2`
holds for every `(left, right)`, by structural induction. -/
def absorbAndFinish (tm : SingleTapeTM Symbol) :
    List (Option Symbol) → List (Option Symbol) →
      Stack (Alpha tm.State Symbol)
  | [],         []          => [finalTile tm]
  | [],         r :: rest   => stepTilesAbsorbRight tm [] r rest ++
                                 absorbAndFinish tm [] rest
  | l :: rest,  right       => stepTilesAbsorbLeft tm l rest right ++
                                 absorbAndFinish tm rest right

/-- The matching invariant for `absorbAndFinish`. -/
lemma absorbAndFinish_matching (tm : SingleTapeTM Symbol)
    (left right : List (Option Symbol)) :
    tau1 (absorbAndFinish tm left right) =
      encodeHaltList tm left right ++ [#] ++
        tau2 (absorbAndFinish tm left right) := by
  induction left, right using absorbAndFinish.induct with
  | case1 =>
    -- left = [], right = []
    simp [absorbAndFinish, finalTile, encodeHaltList, liftTape]
  | case2 r rest ih =>
    -- left = [], right = r :: rest
    simp only [absorbAndFinish, tau1_append, tau2_append,
               tau1_stepTilesAbsorbRight, tau2_stepTilesAbsorbRight, ih,
               List.append_assoc]
  | case3 l rest right ih =>
    -- left = l :: rest, right = right
    simp only [absorbAndFinish, tau1_append, tau2_append,
               tau1_stepTilesAbsorbLeft, tau2_stepTilesAbsorbLeft, ih,
               List.append_assoc]

/-- Every tile in `absorbAndFinish` belongs to `haltTiles`. -/
lemma absorbAndFinish_subset_haltTiles (tm : SingleTapeTM Symbol)
    (left right : List (Option Symbol))
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ absorbAndFinish tm left right) :
    tile ∈ haltTiles tm := by
  induction left, right using absorbAndFinish.induct with
  | case1 =>
    simp only [absorbAndFinish, List.mem_singleton] at htile
    rw [htile]
    exact finalTile_mem_haltTiles tm
  | case2 r rest ih =>
    simp only [absorbAndFinish, List.mem_append] at htile
    rcases htile with hL | hR
    · exact stepTilesAbsorbRight_subset_haltTiles tm [] r rest tile hL
    · exact ih hR
  | case3 l rest right ih =>
    simp only [absorbAndFinish, List.mem_append] at htile
    rcases htile with hL | hR
    · exact stepTilesAbsorbLeft_subset_haltTiles tm l rest right tile hL
    · exact ih hR

/-! ## Dispatch over a single TM step

Given a running configuration `⟨some q, t⟩`, this section produces the
corresponding tile sequence and proves its `tau1`/`tau2`/membership
properties — dispatching on the direction and on the relevant
emptiness sub-case. The `tau2 = encodeCfg(post-step) ++ [#]`
identity holds under `NoBlankWrites`, which sidesteps the cslib
`StackTape.cons` blank-stripping degenerate sub-case where the TM
writes a blank and the corresponding side of the tape is empty. -/

/-- A TM is *blank-write free* iff its transition function never writes
    the blank symbol. This sidesteps the cslib `BiTape` stripping
    issue that arises in the `Halt ≤_m MPCP` simulation when a blank is
    written into a previously-empty boundary side. -/
def NoBlankWrites (tm : SingleTapeTM Symbol) : Prop :=
  ∀ q : tm.State, ∀ a : Option Symbol, ((tm.tr q a).1).symbol ≠ none

/-- A TM is *no-left-boundary* on input `w` iff no configuration reachable
    from `initCfg tm w` ever invokes a left-move while the left tape is
    empty. This mirrors Hopcroft–Ullman–Motwani's one-sided tape
    convention and lets us drop `leftMoveBoundaryTile` from the MPCP
    tile set (it would otherwise admit an alternative decomposition in
    the backward direction that does not correspond to any TM trace). -/
def NoLeftBoundary (tm : SingleTapeTM Symbol) (w : List Symbol) : Prop :=
  ∀ (cfg : tm.Cfg), Relation.ReflTransGen tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) cfg →
    ∀ (q : tm.State) (t : BiTape Symbol),
      cfg = ⟨some q, t⟩ → t.left.toList = [] →
      (tm.tr q t.head).1.movement ≠ some Dir.left

/-- The configuration reached by a single TM step from `⟨some q, t⟩`. -/
def stepResult (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    tm.Cfg :=
  ⟨(tm.tr q t.head).2,
    (t.write (tm.tr q t.head).1.symbol).optionMove (tm.tr q t.head).1.movement⟩

@[simp] lemma tm_step_running (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) :
    tm.step ⟨some q, t⟩ = some (stepResult tm q t) := by
  simp only [SingleTapeTM.step, stepResult]

/-- Auxiliary dispatcher: given the destructured pieces of one TM step
    `(w, mov, qNew)` (the symbol to write, the direction, and the new
    state) plus the current tape `t`, produce the simulation tile
    sequence. -/
def stepTilesAux (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol)
    (w : Option Symbol) (mov : Option Dir) (qNew : Option tm.State) :
    Stack (Alpha tm.State Symbol) :=
  match mov with
  | none           => stepTilesNoMove tm q qNew t w
  | some Dir.right =>
      match t.right.toList with
      | []       => stepTilesRightBoundary tm q qNew t w
      | _ :: _   => stepTilesRightInterior tm q qNew t w
  | some Dir.left  =>
      match t.left.toList with
      | []       => stepTilesLeftBoundary tm q qNew t w
      | _ :: _   => stepTilesLeftInterior tm q qNew t w

/-- The simulation tile sequence for one running TM step. -/
def stepTiles (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    Stack (Alpha tm.State Symbol) :=
  stepTilesAux tm q t (tm.tr q t.head).1.symbol
    (tm.tr q t.head).1.movement (tm.tr q t.head).2

/-! ### Lemmas about `stepTilesAux`

These lemmas dispatch on the explicit `mov` parameter and the relevant
emptiness sub-case. Because `mov`, `t.left.toList`, and `t.right.toList`
are simple types (`Option Dir`, `List _`), case analysis is direct. -/

lemma tau1_stepTilesAux (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) (w : Option Symbol) (mov : Option Dir)
    (qNew : Option tm.State) :
    tau1 (stepTilesAux tm q t w mov qNew) = encodeRunningCfg tm q t ++ [#] := by
  unfold stepTilesAux
  cases mov with
  | none => exact tau1_stepTilesNoMove tm q qNew t w
  | some dir =>
    cases dir with
    | right =>
      cases h_right : t.right.toList with
      | nil => exact tau1_stepTilesRightBoundary tm q qNew t w h_right
      | cons _ _ => exact tau1_stepTilesRightInterior tm q qNew t w
    | left =>
      cases h_left : t.left.toList with
      | nil => exact tau1_stepTilesLeftBoundary tm q qNew t w h_left
      | cons _ _ =>
        refine tau1_stepTilesLeftInterior tm q qNew t w ?_
        rw [h_left]; exact List.cons_ne_nil _ _

lemma stepTilesAux_subset_haltTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (t : BiTape Symbol) (w : Option Symbol)
    (mov : Option Dir) (qNew : Option tm.State)
    (htr : tm.tr q a = (⟨w, mov⟩, qNew))
    (hhead : t.head = a)
    (h_no_lb : mov = some Dir.left → t.left.toList ≠ [])
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesAux tm q t w mov qNew) :
    tile ∈ haltTiles tm := by
  unfold stepTilesAux at htile
  cases mov with
  | none => exact stepTilesNoMove_subset_haltTiles tm q a qNew t w htr hhead tile htile
  | some dir =>
    cases dir with
    | right =>
      cases h_right : t.right.toList with
      | nil =>
        rw [h_right] at htile
        exact stepTilesRightBoundary_subset_haltTiles tm q a qNew t w htr hhead tile htile
      | cons _ _ =>
        rw [h_right] at htile
        exact stepTilesRightInterior_subset_haltTiles tm q a qNew t w htr hhead tile htile
    | left =>
      cases h_left : t.left.toList with
      | nil =>
        -- Impossible under `NoLeftBoundary`: caller must have ensured
        -- `mov = some Dir.left → t.left.toList ≠ []`.
        exact absurd h_left (h_no_lb rfl)
      | cons _ _ =>
        rw [h_left] at htile
        exact stepTilesLeftInterior_subset_haltTiles tm q a qNew t w htr hhead tile htile

lemma tau2_stepTilesAux (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) (w : Option Symbol) (mov : Option Dir)
    (qNew : Option tm.State) (h_w_ne : w ≠ none) :
    tau2 (stepTilesAux tm q t w mov qNew) =
      encodeCfg tm ⟨qNew, (t.write w).optionMove mov⟩ ++ [#] := by
  unfold stepTilesAux
  cases mov with
  | none =>
    -- optionMove _ none = id; new tape is t.write w
    rw [tau2_stepTilesNoMove]
    show _ = encodeCfg tm ⟨qNew, t.write w⟩ ++ [#]
    cases qNew with
    | none =>
      simp only [encodeCfg_halted, encodeHaltedCfg, BiTape.write,
                 stateMarker_none, liftTape_cons, List.append_assoc,
                 List.cons_append, List.nil_append]
    | some q' =>
      simp only [encodeCfg_running, encodeRunningCfg, BiTape.write,
                 stateMarker_some, liftTape_cons, List.append_assoc,
                 List.cons_append, List.nil_append]
  | some dir =>
    cases dir with
    | right =>
      cases h_right : t.right.toList with
      | nil =>
        exact tau2_stepTilesRightBoundary_eq_encodeCfg tm q qNew t w
          (Or.inl h_w_ne) h_right
      | cons _ _ =>
        refine tau2_stepTilesRightInterior_eq_encodeCfg tm q qNew t w
          (Or.inl h_w_ne) ?_
        rw [h_right]; exact List.cons_ne_nil _ _
    | left =>
      cases h_left : t.left.toList with
      | nil =>
        exact tau2_stepTilesLeftBoundary_eq_encodeCfg tm q qNew t w
          (Or.inl h_w_ne) h_left
      | cons _ _ =>
        exact tau2_stepTilesLeftInterior_eq_encodeCfg tm q qNew t w
          (Or.inl h_w_ne)

/-! ### Main `stepTiles` lemmas (derived from `stepTilesAux`) -/

/-- The top concatenation of `stepTiles` is the encoded current
    configuration block. -/
lemma tau1_stepTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) :
    tau1 (stepTiles tm q t) = encodeRunningCfg tm q t ++ [#] := by
  unfold stepTiles
  exact tau1_stepTilesAux tm q t _ _ _

/-- Every tile in `stepTiles` is a member of `haltTiles`, provided the
TM does not invoke a left-move at the left boundary in this cfg. -/
lemma stepTiles_subset_haltTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol)
    (h_no_lb : (tm.tr q t.head).1.movement = some Dir.left →
        t.left.toList ≠ [])
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTiles tm q t) :
    tile ∈ haltTiles tm := by
  unfold stepTiles at htile
  have htr : tm.tr q t.head =
      (⟨(tm.tr q t.head).1.symbol, (tm.tr q t.head).1.movement⟩, (tm.tr q t.head).2) := by
    rcases tm.tr q t.head with ⟨⟨_, _⟩, _⟩; rfl
  exact stepTilesAux_subset_haltTiles tm q t.head t _ _ _ htr rfl h_no_lb tile htile

/-- The bottom concatenation of `stepTiles` is the encoded *next*
    configuration block. Requires `NoBlankWrites` to rule out the
    cslib `BiTape` blank-stripping sub-cases. -/
lemma tau2_stepTiles (tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm)
    (q : tm.State) (t : BiTape Symbol) :
    tau2 (stepTiles tm q t) = encodeCfg tm (stepResult tm q t) ++ [#] := by
  unfold stepTiles stepResult
  exact tau2_stepTilesAux tm q t _ _ _ (h_nbw q t.head)

/-! ## Forward direction: `Halts → MHasSolution`

The forward-direction proof proceeds by induction on the length `n`
of the halting computation `cfg →ⁿ ⟨none, target_tape⟩`. The base
case (`n = 0`, i.e., `cfg` is already halted) uses `absorbAndFinish`
to shrink the encoded halt configuration down to `[h⊥]` and close
with `finalTile`. The inductive step prepends one `stepTiles`
sub-sequence and invokes the IH on the residual chain. -/

/-- The auxiliary forward lemma, indexed by the chain length `n`.
The `NoLeftBoundary` hypothesis lets us discharge the left-boundary
sub-case of `stepTilesAux_subset_haltTiles` at every reachable cfg. -/
lemma forward_aux (tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm)
    (w : List Symbol) (h_nlb : NoLeftBoundary tm w)
    (target_tape : BiTape Symbol) :
    ∀ (cfg : tm.Cfg) (n : ℕ),
      Relation.ReflTransGen tm.TransitionRelation
          (SingleTapeTM.initCfg tm w) cfg →
      Relation.RelatesInSteps tm.TransitionRelation cfg
        ⟨none, target_tape⟩ n →
      ∃ A : Stack (Alpha tm.State Symbol),
        (∀ tile ∈ A, tile ∈ haltTiles tm) ∧
        tau1 A = encodeCfg tm cfg ++ [#] ++ tau2 A := by
  intro cfg n h_reach h_chain
  induction n generalizing cfg with
  | zero =>
    have hzero : cfg = ⟨none, target_tape⟩ := h_chain.zero
    subst hzero
    refine ⟨absorbAndFinish tm target_tape.left.toList
              (target_tape.head :: target_tape.right.toList),
            ?_, ?_⟩
    · intro tile htile
      exact absorbAndFinish_subset_haltTiles tm _ _ tile htile
    · rw [show
          encodeCfg tm (⟨none, target_tape⟩ : tm.Cfg) = encodeHaltedCfg tm target_tape from rfl,
          encodeHaltedCfg_eq_encodeHaltList]
      exact absorbAndFinish_matching tm _ _
  | succ n ih =>
    obtain ⟨cfg', h_step, h_rest⟩ := h_chain.succ'
    cases hcfg : cfg with
    | mk state tape =>
      cases state with
      | none =>
        rw [hcfg] at h_step
        unfold SingleTapeTM.TransitionRelation at h_step
        simp [SingleTapeTM.step] at h_step
      | some q =>
        rw [hcfg] at h_step
        unfold SingleTapeTM.TransitionRelation at h_step
        rw [tm_step_running] at h_step
        have h_cfg' : cfg' = stepResult tm q tape := (Option.some.inj h_step).symm
        subst h_cfg'
        -- Derive the local left-boundary side condition for `stepTiles`.
        have h_no_lb : (tm.tr q tape.head).1.movement = some Dir.left →
            tape.left.toList ≠ [] := by
          intro h_mov h_empty
          have := h_nlb cfg (by simpa [hcfg] using h_reach) q tape hcfg h_empty
          exact this h_mov
        -- Extend reachability by one TM step for the IH.
        have h_reach' : Relation.ReflTransGen tm.TransitionRelation
            (SingleTapeTM.initCfg tm w) (stepResult tm q tape) := by
          refine h_reach.tail ?_
          show tm.step cfg = some (stepResult tm q tape)
          rw [hcfg]; exact tm_step_running tm q tape
        obtain ⟨A', hA'_mem, hA'_match⟩ :=
          ih (stepResult tm q tape) h_reach' h_rest
        refine ⟨stepTiles tm q tape ++ A', ?_, ?_⟩
        · intro tile htile
          rw [List.mem_append] at htile
          rcases htile with hL | hR
          · exact stepTiles_subset_haltTiles tm q tape h_no_lb tile hL
          · exact hA'_mem tile hR
        · rw [tau1_append, tau2_append,
              tau1_stepTiles, tau2_stepTiles tm h_nbw, hA'_match]
          rw [encodeCfg_running]

/-- **Forward direction**: if `Halts tm w`, then the reduced MPCP
    instance `(startTile tm w, haltTiles tm)` has a solution. Requires
    `NoBlankWrites` (the TM never writes a blank) and `NoLeftBoundary`
    (the TM never invokes a left-move at the left boundary, HUM's
    one-sided-tape convention). -/
theorem halts_implies_mhasSolution (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol)
    (h_nlb : NoLeftBoundary tm w) (h : Halts tm w) :
    MHasSolution (startTile tm w) (haltTiles tm) := by
  obtain ⟨target_tape, h_chain⟩ := h
  obtain ⟨n, h_chain_n⟩ := h_chain.relatesInSteps
  obtain ⟨A, hA_mem, hA_match⟩ :=
    forward_aux tm h_nbw w h_nlb target_tape
      (SingleTapeTM.initCfg tm w) n Relation.ReflTransGen.refl h_chain_n
  refine ⟨A, ?_, ?_⟩
  · intro tile htile
    exact List.mem_cons_of_mem _ (hA_mem tile htile)
  · show (startTile tm w).top ++ tau1 A = (startTile tm w).bot ++ tau2 A
    rw [startTile_top, startTile_bot, hA_match]
    show
      [#] ++ (encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A) =
      (# :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#]) ++ tau2 A
    simp [List.append_assoc]

/-! ## Backward direction: `MHasSolution → Halts`

The backward direction is established in two layers:

1. A **strong-A form** (`halt_le_mpcp_strong`, proved via `backward_aux`)
   handles `A ⊆ haltTiles tm`. It performs strong induction on `A.length`,
   peeling one canonical "block" off the front per TM step:
   * `copy_prefix_forced` consumes the left-tape prefix.
   * `transition_forced` selects the unique transition tile for the
     current `(q, a)`.
   * `copy_prefix_forced_state_lead` consumes the right-tape suffix.
   * `sep_forced` consumes the `#` separator.
   The halted-cfg base case returns `ReflTransGen.refl`; the halt-now
   sub-case (`qNew = none` at the right boundary) is handled with a
   single TM step via `tm_step_running`.

   Note: there is *no* `starts_with_absorbAndFinish` lemma — the
   absorption-phase decomposition is non-unique (e.g. with `left = [l]`,
   `right = [r]`, both `[absorbLeftTile l, copyTile r, sepTile,
   absorbRightTile r, sepTile, finalTile]` and `[copyTile l,
   absorbRightTile r, sepTile, absorbLeftTile l, sepTile, finalTile]`
   are valid), so the canonical decomposition cannot be forced. The
   halt-now sub-case sidesteps the absorption phase entirely.

2. A **canonical form** (`halt_le_mpcp`, proved via `backward_aux_weak`)
   handles `A ⊆ startTile :: haltTiles tm`. It threads a chain-tracked
   cfg queue `List (Σ' c, ReflTransGen ... initCfg c)`: each queued cfg
   carries its own `ReflTransGen` chain from `initCfg`. When `startTile`
   appears mid-stream in `A`, it pushes an extra `initCfg` (with a
   `refl` chain) onto the queue, in addition to the natural `stepResult`
   advancement. The right-boundary alternative `rightMoveTile` path is
   ruled out by `tau1_no_state_marker_then_sharp`, a structural property
   showing that `tau1 A` never contains `↟ₛq :: # :: …` as a sublist.

See `ROADMAP.md` for the detailed dependency tree. -/

/-! ## Step 1: Characterise every tile of `haltTiles` -/

/-- Every tile `t` in `haltTiles tm` is one of eight concrete tiles
(copy, separator, no-move/right/left transition, absorb-left/right,
or final). For each case we also expose the relevant TM-transition
equation so the bot of a transition tile is determined. -/
private lemma mem_haltTiles_top (tm : SingleTapeTM Symbol)
    (t : Tile (Alpha tm.State Symbol)) (ht : t ∈ haltTiles tm) :
    (∃ a : Option Symbol, t = copyTile tm a) ∨
    t = sepTile tm ∨
    (∃ (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
       (w : Option Symbol),
        tm.tr q a = (⟨w, none⟩, qNew) ∧ t = noMoveTile tm q a qNew w) ∨
    (∃ (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
       (w : Option Symbol),
        tm.tr q a = (⟨w, some Dir.right⟩, qNew) ∧
          (t = rightMoveTile tm q a qNew w ∨
           t = rightMoveBoundaryTile tm q a qNew w)) ∨
    (∃ (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
       (w : Option Symbol),
        tm.tr q a = (⟨w, some Dir.left⟩, qNew) ∧
          ∃ b : Option Symbol, t = leftMoveTile tm q a qNew w b) ∨
    (∃ a : Option Symbol, t = absorbLeftTile tm a) ∨
    (∃ a : Option Symbol, t = absorbRightTile tm a) ∨
    t = finalTile tm := by
  simp only [haltTiles, List.mem_append, List.mem_singleton] at ht
  -- ht has left-nested shape: (((copyTiles ∨ sepTile) ∨ transitionTiles) ∨ absorbTiles) ∨ finalTile
  rcases ht with ((((ht | rfl) | ht) | ht) | rfl)
  · -- t ∈ copyTiles tm = Finset.univ.toList.map (copyTile tm)
    simp only [copyTiles, List.mem_map] at ht
    obtain ⟨a, _, rfl⟩ := ht
    exact Or.inl ⟨a, rfl⟩
  · -- t = sepTile tm
    exact Or.inr (Or.inl rfl)
  · -- t ∈ transitionTiles tm
    simp only [transitionTiles, List.mem_flatMap] at ht
    obtain ⟨⟨q, a⟩, _, ht⟩ := ht
    rcases h_tr : tm.tr q a with ⟨⟨w, dir⟩, qNew⟩
    cases dir with
    | none =>
      simp only [transitionTilesFor] at ht
      rw [h_tr] at ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact Or.inr (Or.inr (Or.inl ⟨q, a, qNew, w, h_tr, rfl⟩))
    | some d =>
      cases d with
      | right =>
        simp only [transitionTilesFor] at ht
        rw [h_tr] at ht
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
        rcases ht with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨q, a, qNew, w, h_tr, Or.inl rfl⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨q, a, qNew, w, h_tr, Or.inr rfl⟩)))
      | left =>
        simp only [transitionTilesFor] at ht
        rw [h_tr] at ht
        simp only [List.mem_map] at ht
        obtain ⟨b, _, rfl⟩ := ht
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨q, a, qNew, w, h_tr, b, rfl⟩))))
  · -- t ∈ absorbTiles tm
    simp only [absorbTiles, List.mem_flatMap, absorbTilesFor,
               List.mem_cons, List.mem_nil_iff, or_false] at ht
    obtain ⟨a, _, (rfl | rfl)⟩ := ht
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))))))
  · -- t = finalTile tm
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

/-! ## Step 2: `copy_prefix_forced` — tape-lift prefix forces copy tiles -/

/-- The `liftTape tm L`-prefix of `tau1 A` forces `A` to begin with copy
tiles for `L`, provided `tail` does not start with `h⊥` (which would let
an `absorbLeftTile` consume the last lift) or with a state symbol `↟ₛq`
(which would let a `leftMoveTile` consume the last lift). Both `tau1` and
`tau2` are transparent through the forced copy prefix. -/
private lemma copy_prefix_forced (tm : SingleTapeTM Symbol) :
    ∀ (L : List (Option Symbol)) (A : Stack (Alpha tm.State Symbol))
      (tail : List (Alpha tm.State Symbol)),
      (∀ t ∈ A, t ∈ haltTiles tm) →
      tau1 A = liftTape tm L ++ tail →
      (∀ x : List (Alpha tm.State Symbol), tail ≠ h⊥ :: x) →
      (∀ (q : tm.State) (x : List (Alpha tm.State Symbol)),
          tail ≠ ↟ₛq :: x) →
      ∃ A' : Stack (Alpha tm.State Symbol),
          A = L.map (copyTile tm) ++ A' ∧
          (∀ t ∈ A', t ∈ haltTiles tm) ∧
          tau1 A' = tail ∧
          tau2 A = liftTape tm L ++ tau2 A' := by
  intro L
  induction L with
  | nil =>
    intro A tail h_mem h_eq _ _
    exact ⟨A, by simp, h_mem, by simpa using h_eq, by simp⟩
  | cons a L ih =>
    intro A tail h_mem h_eq h_not_halt h_not_state
    cases A with
    | nil => simp [liftTape_cons] at h_eq
    | cons t A_rest =>
      have h_t_mem : t ∈ haltTiles tm := h_mem t (List.mem_cons_self ..)
      have h_rest_mem : ∀ s ∈ A_rest, s ∈ haltTiles tm :=
        fun s hs => h_mem s (List.mem_cons_of_mem t hs)
      rw [tau1_cons, liftTape_cons, List.cons_append] at h_eq
      -- Cases of `mem_haltTiles_top`, in order: copy, sep, noMove,
      -- right (interior/boundary), left (only interior under HUM),
      -- absorbLeft, absorbRight, final.
      rcases mem_haltTiles_top tm t h_t_mem with
          ⟨a', rfl⟩
        | rfl
        | ⟨_, _, _, _, _, rfl⟩
        | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨q', _, _, _, _, _, rfl⟩
        | ⟨_, rfl⟩
        | ⟨_, rfl⟩
        | rfl
      · -- copyTile a': peel off and recurse.
        simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_head h_tail
        injection h_head with h_a
        subst h_a
        obtain ⟨A', hA, hA_mem, hA_tau1, hA_tau2⟩ :=
          ih A_rest tail h_rest_mem h_tail h_not_halt h_not_state
        refine ⟨A', ?_, hA_mem, hA_tau1, ?_⟩
        · simp [List.map_cons, hA]
        · simp [tau2_cons, copyTile_bot, hA_tau2, liftTape_cons]
      · simp at h_eq                      -- sepTile
      · simp at h_eq                      -- noMoveTile
      · simp at h_eq                      -- rightMoveTile
      · simp at h_eq                      -- rightMoveBoundaryTile
      · -- leftMoveTile: the *second* character of the top is `↟ₛq'`. It
        -- must match the next character of `liftTape tm L ++ tail`, which
        -- is a tape lift if `L ≠ []` (constructor mismatch) and ruled out
        -- by `h_not_state` if `L = []`.
        simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with _ h_rest
        cases L with
        | nil =>
          simp only [liftTape_nil, List.nil_append] at h_rest
          exact (h_not_state q' _ h_rest.symm).elim
        | cons _ _ =>
          simp only [liftTape_cons, List.cons_append] at h_rest
          injection h_rest with h_h
          cases h_h
      · -- absorbLeftTile: same idea, with second character `h⊥`.
        simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with _ h_rest
        cases L with
        | nil =>
          simp only [liftTape_nil, List.nil_append] at h_rest
          exact (h_not_halt _ h_rest.symm).elim
        | cons _ _ =>
          simp only [liftTape_cons, List.cons_append] at h_rest
          injection h_rest with h_h
          cases h_h
      · simp at h_eq                      -- absorbRightTile
      · simp at h_eq                      -- finalTile

/-! ## Step 3: `transition_forced` — state-marker forces a transition tile -/

/-- When the lead of `tau1 A` is the two-character prefix `↟ₛq ↟ₜa`, the
first tile of `A` is a transition tile for the pair `(q, a)`. Together
with `mem_haltTiles_top`, this rules out every non-transition tile (their
tops do not start with `↟ₛq`) and pins down `q'` and `a'` of the chosen
tile constructor as `q` and `a` respectively. The `leftMoveTile` case is
excluded because its top starts with a tape symbol `↟ₜb`, not `↟ₛq`. -/
private lemma transition_forced (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol)
    (rest : List (Alpha tm.State Symbol))
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ t ∈ A, t ∈ haltTiles tm)
    (h_eq : tau1 A = ↟ₛq :: ↟ₜa :: rest) :
    ∃ (tile : Tile (Alpha tm.State Symbol))
      (A' : Stack (Alpha tm.State Symbol)),
      A = tile :: A' ∧
      tile ∈ transitionTilesFor tm q a ∧
      (∀ s ∈ A', s ∈ haltTiles tm) := by
  cases A with
  | nil => simp at h_eq
  | cons t A_rest =>
    have h_t_mem : t ∈ haltTiles tm := h_mem t (List.mem_cons_self ..)
    have h_rest_mem : ∀ s ∈ A_rest, s ∈ haltTiles tm :=
      fun s hs => h_mem s (List.mem_cons_of_mem t hs)
    refine ⟨t, A_rest, rfl, ?_, h_rest_mem⟩
    rw [tau1_cons] at h_eq
    -- The eight cases of `mem_haltTiles_top`, in the same order as
    -- `copy_prefix_forced` above.
    rcases mem_haltTiles_top tm t h_t_mem with
        ⟨_, rfl⟩
      | rfl
      | ⟨q', a', qNew, w, h_tr, rfl⟩
      | ⟨q', a', qNew, w, h_tr, rfl | rfl⟩
      | ⟨_, _, _, _, _, _, rfl⟩
      | ⟨_, rfl⟩
      | ⟨_, rfl⟩
      | rfl
    · -- copyTile: top = [↟ₜ_]. First char is a tape lift, not `↟ₛq`.
      simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _
      cases h_h
    · -- sepTile: top = [#].
      simp only [sepTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _
      cases h_h
    · -- noMoveTile q' a' qNew w with tm.tr q' a' = (⟨w, none⟩, qNew).
      simp only [noMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h h_rest
      injection h_h with h_q'
      subst h_q'
      injection h_rest with h_a _
      injection h_a with h_a'
      subst h_a'
      simp only [transitionTilesFor]
      rw [h_tr]
      exact List.mem_singleton.mpr rfl
    · -- rightMoveTile q' a' qNew w with right-move transition.
      simp only [rightMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h h_rest
      injection h_h with h_q'
      subst h_q'
      injection h_rest with h_a _
      injection h_a with h_a'
      subst h_a'
      simp only [transitionTilesFor]
      rw [h_tr]
      exact List.mem_cons_self
    · -- rightMoveBoundaryTile q' a' qNew w with right-move transition.
      simp only [rightMoveBoundaryTile_top, List.cons_append,
                 List.nil_append] at h_eq
      injection h_eq with h_h h_rest
      injection h_h with h_q'
      subst h_q'
      injection h_rest with h_a _
      injection h_a with h_a'
      subst h_a'
      simp only [transitionTilesFor]
      rw [h_tr]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · -- leftMoveTile q' a' qNew w b: top = [↟ₜb, …]. First char is a
      -- tape lift, not `↟ₛq`.
      simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _
      cases h_h
    · -- absorbLeftTile a': top = [↟ₜa', h⊥]. First char is a tape lift.
      simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _
      cases h_h
    · -- absorbRightTile a': top = [h⊥, ↟ₜa']. First char is `h⊥`.
      simp only [absorbRightTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _
      cases h_h
    · -- finalTile: top = [h⊥, #, #]. First char is `h⊥`.
      simp only [finalTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _
      cases h_h

/-! ## Step 4 helpers: copy prefix that extends up to a state marker -/

/-- Strengthening of `copy_prefix_forced` for the no-move and right-move
cases: when the lead following `liftTape tm L` is a state marker `↟ₛq`
and the TM transition `tm.tr q a` (`a` being the tape symbol immediately
after `↟ₛq`) is *not* a left move, no `leftMoveTile` can swallow the
last `L`-symbol together with `↟ₛq`.  Hence the copy prefix extends all
the way to `↟ₛq`. -/
private lemma copy_prefix_forced_state_lead (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol)
    (h_not_left : ∀ (qNew : Option tm.State) (w : Option Symbol),
        tm.tr q a ≠ (⟨w, some Dir.left⟩, qNew)) :
    ∀ (L : List (Option Symbol)) (A : Stack (Alpha tm.State Symbol))
      (rest : List (Alpha tm.State Symbol)),
      (∀ s ∈ A, s ∈ haltTiles tm) →
      tau1 A = liftTape tm L ++ ↟ₛq :: ↟ₜa :: rest →
      ∃ A' : Stack (Alpha tm.State Symbol),
          A = L.map (copyTile tm) ++ A' ∧
          (∀ s ∈ A', s ∈ haltTiles tm) ∧
          tau1 A' = ↟ₛq :: ↟ₜa :: rest ∧
          tau2 A = liftTape tm L ++ tau2 A' := by
  intro L
  induction L with
  | nil =>
    intro A rest h_mem h_eq
    exact ⟨A, by simp, h_mem, by simpa using h_eq, by simp⟩
  | cons a' L ih =>
    intro A rest h_mem h_eq
    cases A with
    | nil => simp [liftTape_cons] at h_eq
    | cons t A_rest =>
      have h_t_mem : t ∈ haltTiles tm := h_mem t (List.mem_cons_self ..)
      have h_rest_mem : ∀ s ∈ A_rest, s ∈ haltTiles tm :=
        fun s hs => h_mem s (List.mem_cons_of_mem t hs)
      rw [tau1_cons, liftTape_cons, List.cons_append] at h_eq
      rcases mem_haltTiles_top tm t h_t_mem with
          ⟨_, rfl⟩
        | rfl
        | ⟨_, _, _, _, _, rfl⟩
        | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨q', a'', _, _, h_tr, b, rfl⟩
        | ⟨_, rfl⟩
        | ⟨_, rfl⟩
        | rfl
      · -- copyTile a'': peel off and recurse.
        simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_head h_tail
        injection h_head with h_a
        subst h_a
        obtain ⟨A', hA, hA_mem, hA_tau1, hA_tau2⟩ :=
          ih A_rest rest h_rest_mem h_tail
        refine ⟨A', ?_, hA_mem, hA_tau1, ?_⟩
        · simp [List.map_cons, hA]
        · simp [tau2_cons, copyTile_bot, hA_tau2, liftTape_cons]
      · simp at h_eq                      -- sepTile
      · simp at h_eq                      -- noMoveTile
      · simp at h_eq                      -- rightMoveTile
      · simp at h_eq                      -- rightMoveBoundaryTile
      · -- leftMoveTile q' a'' qNew' w' b: top = [↟ₜb, ↟ₛq', ↟ₜa''].
        -- Match against ↟ₜa' :: liftTape L ++ ↟ₛq :: ↟ₜa :: rest.
        simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with _ h_rest1
        cases L with
        | nil =>
          simp only [liftTape_nil, List.nil_append] at h_rest1
          injection h_rest1 with h_q_eq h_rest2
          injection h_q_eq with h_q_eq'
          subst h_q_eq'
          injection h_rest2 with h_a_eq _
          injection h_a_eq with h_a_eq'
          subst h_a_eq'
          exact (h_not_left _ _ h_tr).elim
        | cons _ _ =>
          simp only [liftTape_cons, List.cons_append] at h_rest1
          injection h_rest1 with h_h
          cases h_h
      · -- absorbLeftTile a'': top = [↟ₜa'', h⊥].
        simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with _ h_rest
        cases L with
        | nil =>
          simp only [liftTape_nil, List.nil_append] at h_rest
          injection h_rest with h_h
          cases h_h
        | cons _ _ =>
          simp only [liftTape_cons, List.cons_append] at h_rest
          injection h_rest with h_h
          cases h_h
      · simp at h_eq                      -- absorbRightTile
      · simp at h_eq                      -- finalTile

/-- If the lead of `tau1 A` is the separator `#`, the head tile of `A`
must be `sepTile`. -/
private lemma sep_forced (tm : SingleTapeTM Symbol)
    (rest : List (Alpha tm.State Symbol))
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : tau1 A = # :: rest) :
    ∃ A' : Stack (Alpha tm.State Symbol),
      A = sepTile tm :: A' ∧
      tau1 A' = rest ∧
      (∀ s ∈ A', s ∈ haltTiles tm) := by
  cases A with
  | nil => simp at h_eq
  | cons t A_rest =>
    have h_t_mem : t ∈ haltTiles tm := h_mem t (List.mem_cons_self ..)
    have h_rest_mem : ∀ s ∈ A_rest, s ∈ haltTiles tm :=
      fun s hs => h_mem s (List.mem_cons_of_mem t hs)
    rw [tau1_cons] at h_eq
    rcases mem_haltTiles_top tm t h_t_mem with
        ⟨_, rfl⟩
      | rfl
      | ⟨_, _, _, _, _, rfl⟩
      | ⟨_, _, _, _, _, rfl | rfl⟩
      | ⟨_, _, _, _, _, _, rfl⟩
      | ⟨_, rfl⟩
      | ⟨_, rfl⟩
      | rfl
    · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · -- sepTile: this is the only matching case.
      simp only [sepTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with _ h_tail
      exact ⟨A_rest, rfl, h_tail, h_rest_mem⟩
    · simp only [noMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [rightMoveBoundaryTile_top, List.cons_append,
                 List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [absorbRightTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h
    · simp only [finalTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h _; cases h

/-! ## Weak-hypothesis forcing lemmas (entry path for the canonical iff)

The strong-hypothesis forcing lemmas above (`copy_prefix_forced`,
`transition_forced`, `copy_prefix_forced_state_lead`, `sep_forced`)
require `∀ s ∈ A, s ∈ haltTiles tm`. The canonical
`Halts ↔ MHasSolution` iff begins with `A` drawn from
`startTile :: haltTiles tm`, so we need _weak_ variants that admit
`startTile` in `A`. For the prefix / transition / state-lead lemmas,
`startTile.top = [#]` is ruled out by the lookahead's first character
(`↟ₜ_` or `↟ₛq`). At the sep position the lookahead's first character
*is* `#`, so `startTile` cannot be ruled out locally — the conclusion
of `sep_forced_weak` is therefore a disjunction that distinguishes
the two cases by the residual's `tau2`. -/

/-- Weak variant of `copy_prefix_forced`. Identical to the strong version
except `A`'s tiles may be drawn from `startTile :: haltTiles tm`; the
`startTile.top = [#]` case is ruled out by character mismatch with
`liftTape tm (a :: L)`'s leading `↟ₜa`. -/
private lemma copy_prefix_forced_weak (tm : SingleTapeTM Symbol)
    (w_in : List Symbol) :
    ∀ (L : List (Option Symbol)) (A : Stack (Alpha tm.State Symbol))
      (tail : List (Alpha tm.State Symbol)),
      (∀ t ∈ A, t ∈ startTile tm w_in :: haltTiles tm) →
      tau1 A = liftTape tm L ++ tail →
      (∀ x : List (Alpha tm.State Symbol), tail ≠ h⊥ :: x) →
      (∀ (q : tm.State) (x : List (Alpha tm.State Symbol)),
          tail ≠ ↟ₛq :: x) →
      ∃ A' : Stack (Alpha tm.State Symbol),
          A = L.map (copyTile tm) ++ A' ∧
          (∀ t ∈ A', t ∈ startTile tm w_in :: haltTiles tm) ∧
          tau1 A' = tail ∧
          tau2 A = liftTape tm L ++ tau2 A' := by
  intro L
  induction L with
  | nil =>
    intro A tail h_mem h_eq _ _
    exact ⟨A, by simp, h_mem, by simpa using h_eq, by simp⟩
  | cons a L ih =>
    intro A tail h_mem h_eq h_not_halt h_not_state
    cases A with
    | nil => simp [liftTape_cons] at h_eq
    | cons t A_rest =>
      have h_t_in : t ∈ startTile tm w_in :: haltTiles tm :=
        h_mem t (List.mem_cons_self ..)
      have h_rest_in : ∀ s ∈ A_rest, s ∈ startTile tm w_in :: haltTiles tm :=
        fun s hs => h_mem s (List.mem_cons_of_mem t hs)
      rw [tau1_cons, liftTape_cons, List.cons_append] at h_eq
      rcases List.mem_cons.mp h_t_in with rfl | h_t_lu
      · -- t = startTile: top first char is `#`, lookahead first is `↟ₜa`.
        simp only [startTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _
        cases h_h
      · rcases mem_haltTiles_top tm t h_t_lu with
            ⟨a', rfl⟩
          | rfl
          | ⟨_, _, _, _, _, rfl⟩
          | ⟨_, _, _, _, _, rfl | rfl⟩
          | ⟨q', _, _, _, _, _, rfl⟩
          | ⟨_, rfl⟩
          | ⟨_, rfl⟩
          | rfl
        · -- copyTile a': peel and recurse.
          simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with h_head h_tail
          injection h_head with h_a
          subst h_a
          obtain ⟨A', hA, hA_mem, hA_tau1, hA_tau2⟩ :=
            ih A_rest tail h_rest_in h_tail h_not_halt h_not_state
          refine ⟨A', ?_, hA_mem, hA_tau1, ?_⟩
          · simp [List.map_cons, hA]
          · simp [tau2_cons, copyTile_bot, hA_tau2, liftTape_cons]
        · simp at h_eq
        · simp at h_eq
        · simp at h_eq
        · simp at h_eq
        · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with _ h_rest
          cases L with
          | nil =>
            simp only [liftTape_nil, List.nil_append] at h_rest
            exact (h_not_state q' _ h_rest.symm).elim
          | cons _ _ =>
            simp only [liftTape_cons, List.cons_append] at h_rest
            injection h_rest with h_h
            cases h_h
        · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with _ h_rest
          cases L with
          | nil =>
            simp only [liftTape_nil, List.nil_append] at h_rest
            exact (h_not_halt _ h_rest.symm).elim
          | cons _ _ =>
            simp only [liftTape_cons, List.cons_append] at h_rest
            injection h_rest with h_h
            cases h_h
        · simp at h_eq
        · simp at h_eq

/-- Weak variant of `transition_forced`: rules out `startTile` by the
lookahead's leading `↟ₛq`. -/
private lemma transition_forced_weak (tm : SingleTapeTM Symbol)
    (w_in : List Symbol)
    (q : tm.State) (a : Option Symbol)
    (rest : List (Alpha tm.State Symbol))
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ t ∈ A, t ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : tau1 A = ↟ₛq :: ↟ₜa :: rest) :
    ∃ (tile : Tile (Alpha tm.State Symbol))
      (A' : Stack (Alpha tm.State Symbol)),
      A = tile :: A' ∧
      tile ∈ transitionTilesFor tm q a ∧
      (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) := by
  cases A with
  | nil => simp at h_eq
  | cons t A_rest =>
    have h_t_in : t ∈ startTile tm w_in :: haltTiles tm :=
      h_mem t (List.mem_cons_self ..)
    have h_rest_in : ∀ s ∈ A_rest, s ∈ startTile tm w_in :: haltTiles tm :=
      fun s hs => h_mem s (List.mem_cons_of_mem t hs)
    refine ⟨t, A_rest, rfl, ?_, h_rest_in⟩
    rw [tau1_cons] at h_eq
    rcases List.mem_cons.mp h_t_in with rfl | h_t_lu
    · -- t = startTile: top first char is `#`, lookahead first is `↟ₛq`.
      simp only [startTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with h_h _
      cases h_h
    · rcases mem_haltTiles_top tm t h_t_lu with
          ⟨_, rfl⟩
        | rfl
        | ⟨q', a', qNew, w, h_tr, rfl⟩
        | ⟨q', a', qNew, w, h_tr, rfl | rfl⟩
        | ⟨_, _, _, _, _, _, rfl⟩
        | ⟨_, rfl⟩
        | ⟨_, rfl⟩
        | rfl
      · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _
        cases h_h
      · simp only [sepTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _
        cases h_h
      · simp only [noMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h h_rest
        injection h_h with h_q'
        subst h_q'
        injection h_rest with h_a _
        injection h_a with h_a'
        subst h_a'
        simp only [transitionTilesFor]
        rw [h_tr]
        exact List.mem_singleton.mpr rfl
      · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h h_rest
        injection h_h with h_q'
        subst h_q'
        injection h_rest with h_a _
        injection h_a with h_a'
        subst h_a'
        simp only [transitionTilesFor]
        rw [h_tr]
        exact List.mem_cons_self
      · simp only [rightMoveBoundaryTile_top, List.cons_append,
                   List.nil_append] at h_eq
        injection h_eq with h_h h_rest
        injection h_h with h_q'
        subst h_q'
        injection h_rest with h_a _
        injection h_a with h_a'
        subst h_a'
        simp only [transitionTilesFor]
        rw [h_tr]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _
        cases h_h
      · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _
        cases h_h
      · simp only [absorbRightTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _
        cases h_h
      · simp only [finalTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _
        cases h_h

/-- Weak variant of `copy_prefix_forced_state_lead`: rules out `startTile`
by the leading `↟ₜa'` of `liftTape tm (a' :: L)`. -/
private lemma copy_prefix_forced_state_lead_weak (tm : SingleTapeTM Symbol)
    (w_in : List Symbol)
    (q : tm.State) (a : Option Symbol)
    (h_not_left : ∀ (qNew : Option tm.State) (w : Option Symbol),
        tm.tr q a ≠ (⟨w, some Dir.left⟩, qNew)) :
    ∀ (L : List (Option Symbol)) (A : Stack (Alpha tm.State Symbol))
      (rest : List (Alpha tm.State Symbol)),
      (∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm) →
      tau1 A = liftTape tm L ++ ↟ₛq :: ↟ₜa :: rest →
      ∃ A' : Stack (Alpha tm.State Symbol),
          A = L.map (copyTile tm) ++ A' ∧
          (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) ∧
          tau1 A' = ↟ₛq :: ↟ₜa :: rest ∧
          tau2 A = liftTape tm L ++ tau2 A' := by
  intro L
  induction L with
  | nil =>
    intro A rest h_mem h_eq
    exact ⟨A, by simp, h_mem, by simpa using h_eq, by simp⟩
  | cons a' L ih =>
    intro A rest h_mem h_eq
    cases A with
    | nil => simp [liftTape_cons] at h_eq
    | cons t A_rest =>
      have h_t_in : t ∈ startTile tm w_in :: haltTiles tm :=
        h_mem t (List.mem_cons_self ..)
      have h_rest_in : ∀ s ∈ A_rest, s ∈ startTile tm w_in :: haltTiles tm :=
        fun s hs => h_mem s (List.mem_cons_of_mem t hs)
      rw [tau1_cons, liftTape_cons, List.cons_append] at h_eq
      rcases List.mem_cons.mp h_t_in with rfl | h_t_lu
      · -- t = startTile: ruled out by char.
        simp only [startTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h_h _
        cases h_h
      · rcases mem_haltTiles_top tm t h_t_lu with
            ⟨_, rfl⟩
          | rfl
          | ⟨_, _, _, _, _, rfl⟩
          | ⟨_, _, _, _, _, rfl | rfl⟩
          | ⟨q', a'', _, _, h_tr, b, rfl⟩
          | ⟨_, rfl⟩
          | ⟨_, rfl⟩
          | rfl
        · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with h_head h_tail
          injection h_head with h_a
          subst h_a
          obtain ⟨A', hA, hA_mem, hA_tau1, hA_tau2⟩ :=
            ih A_rest rest h_rest_in h_tail
          refine ⟨A', ?_, hA_mem, hA_tau1, ?_⟩
          · simp [List.map_cons, hA]
          · simp [tau2_cons, copyTile_bot, hA_tau2, liftTape_cons]
        · simp at h_eq
        · simp at h_eq
        · simp at h_eq
        · simp at h_eq
        · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with _ h_rest1
          cases L with
          | nil =>
            simp only [liftTape_nil, List.nil_append] at h_rest1
            injection h_rest1 with h_q_eq h_rest2
            injection h_q_eq with h_q_eq'
            subst h_q_eq'
            injection h_rest2 with h_a_eq _
            injection h_a_eq with h_a_eq'
            subst h_a_eq'
            exact (h_not_left _ _ h_tr).elim
          | cons _ _ =>
            simp only [liftTape_cons, List.cons_append] at h_rest1
            injection h_rest1 with h_h
            cases h_h
        · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
          injection h_eq with _ h_rest
          cases L with
          | nil =>
            simp only [liftTape_nil, List.nil_append] at h_rest
            injection h_rest with h_h
            cases h_h
          | cons _ _ =>
            simp only [liftTape_cons, List.cons_append] at h_rest
            injection h_rest with h_h
            cases h_h
        · simp at h_eq
        · simp at h_eq

/-- Weak variant of `sep_forced`: when `tau1 A` starts with `#` and
every tile of `A` lies in `startTile :: haltTiles tm`, the head tile is
either `sepTile` or `startTile`. The two cases differ in the value of
`tau2 A`: the `sepTile` case contributes `[#]`, while the `startTile`
case contributes `# :: encodeCfg(initCfg) ++ [#]`. -/
private lemma sep_forced_weak (tm : SingleTapeTM Symbol) (w_in : List Symbol)
    (rest : List (Alpha tm.State Symbol))
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : tau1 A = # :: rest) :
    ∃ A' : Stack (Alpha tm.State Symbol),
      ((A = sepTile tm :: A' ∧
        tau2 A = # :: tau2 A') ∨
       (A = startTile tm w_in :: A' ∧
        tau2 A = # :: encodeCfg tm (SingleTapeTM.initCfg tm w_in) ++ [#] ++ tau2 A')) ∧
      tau1 A' = rest ∧
      (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) := by
  cases A with
  | nil => simp at h_eq
  | cons t A_rest =>
    have h_t_in : t ∈ startTile tm w_in :: haltTiles tm :=
      h_mem t (List.mem_cons_self ..)
    have h_rest_in : ∀ s ∈ A_rest, s ∈ startTile tm w_in :: haltTiles tm :=
      fun s hs => h_mem s (List.mem_cons_of_mem t hs)
    rw [tau1_cons] at h_eq
    rcases List.mem_cons.mp h_t_in with rfl | h_t_lu
    · -- t = startTile: top = [#] matches.
      simp only [startTile_top, List.cons_append, List.nil_append] at h_eq
      injection h_eq with _ h_tail
      refine ⟨A_rest, Or.inr ⟨rfl, ?_⟩, h_tail, h_rest_in⟩
      simp [tau2_cons, startTile_bot, List.append_assoc]
    · -- t ∈ haltTiles: only sepTile matches; rule out the other 7.
      rcases mem_haltTiles_top tm t h_t_lu with
          ⟨_, rfl⟩
        | rfl
        | ⟨_, _, _, _, _, rfl⟩
        | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨_, _, _, _, _, _, rfl⟩
        | ⟨_, rfl⟩
        | ⟨_, rfl⟩
        | rfl
      · simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · -- sepTile.
        simp only [sepTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with _ h_tail
        refine ⟨A_rest, Or.inl ⟨rfl, ?_⟩, h_tail, h_rest_in⟩
        simp [tau2_cons, sepTile_bot]
      · simp only [noMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [rightMoveBoundaryTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [absorbRightTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h
      · simp only [finalTile_top, List.cons_append, List.nil_append] at h_eq
        injection h_eq with h _; cases h

/-! ## Step 4: `starts_with_stepTiles` — running cfg forces a step group -/

/-- No-move case. -/
private lemma starts_with_stepTilesNoMove (tm : SingleTapeTM Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew : Option tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, none⟩, qNew))
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : tau1 A = encodeRunningCfg tm q t ++ [#] ++ tau2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A = stepTilesNoMove tm q qNew t w ++ A' ∧
        (∀ s ∈ A', s ∈ haltTiles tm) ∧
        tau1 A' = encodeCfg tm ⟨qNew, t.write w⟩ ++ [#] ++ tau2 A' := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Dir.left⟩, qN) := by
    intro qN w' h
    rw [htr] at h
    injection h with h1 _
    injection h1 with _ h_dir
    cases h_dir
  have h_eq' : tau1 A =
      liftTape tm t.left.toList.reverse ++ ↟ₛq :: ↟ₜt.head ::
        (liftTape tm t.right.toList ++ [#] ++ tau2 A) := by
    simpa [encodeRunningCfg, liftTape_cons, List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_tau1, hA_tau2⟩ :=
    copy_prefix_forced_state_lead tm q t.head h_not_left
      t.left.toList.reverse A
      (liftTape tm t.right.toList ++ [#] ++ tau2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced tm q t.head
      (liftTape tm t.right.toList ++ [#] ++ tau2 A) A1
      hA_mem hA_tau1
  have h_tile_eq : tile = noMoveTile tm q t.head qNew w := by
    simp only [transitionTilesFor] at h_tile_in
    rw [htr] at h_tile_in
    exact List.mem_singleton.mp h_tile_in
  subst h_tile_eq
  have hA2_tau1 : tau1 A2 = liftTape tm t.right.toList ++ [#] ++ tau2 A := by
    have key := hA_tau1
    rw [hA1_decomp, tau1_cons, noMoveTile_top] at key
    simpa using key
  obtain ⟨A3, hA2, hA3_mem, hA3_tau1, hA3_tau2⟩ :=
    copy_prefix_forced tm t.right.toList A2
      ([#] ++ tau2 A) hA2_mem
      (by simpa [List.append_assoc] using hA2_tau1)
      (by intro x h; injection h with h1 _; cases h1)
      (by intro q' x h; injection h with h1 _; cases h1)
  obtain ⟨A4, hA3_decomp, hA4_tau1, hA4_mem⟩ :=
    sep_forced tm (tau2 A) A3 hA3_mem (by simpa using hA3_tau1)
  refine ⟨A4, ?_, hA4_mem, ?_⟩
  · rw [hA, hA1_decomp, hA2, hA3_decomp]
    simp only [stepTilesNoMove, List.append_assoc, List.cons_append,
               List.nil_append]
  · rw [hA4_tau1, hA_tau2, hA1_decomp, tau2_cons, noMoveTile_bot, hA3_tau2,
        hA3_decomp, tau2_cons, sepTile_bot]
    cases qNew with
    | none =>
      simp [encodeCfg_halted, encodeHaltedCfg, BiTape.write,
            stateMarker_none, liftTape_cons, List.append_assoc]
    | some q' =>
      simp [encodeCfg_running, encodeRunningCfg, BiTape.write,
            stateMarker_some, liftTape_cons, List.append_assoc]

/-- Right-move interior case. -/
private lemma starts_with_stepTilesRightInterior (tm : SingleTapeTM Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew : Option tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, some Dir.right⟩, qNew))
    (h_right_ne : t.right.toList ≠ [])
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : tau1 A = encodeRunningCfg tm q t ++ [#] ++ tau2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A = stepTilesRightInterior tm q qNew t w ++ A' ∧
        (∀ s ∈ A', s ∈ haltTiles tm) ∧
        tau1 A' = encodeCfg tm ⟨qNew, (t.write w).move_right⟩ ++ [#] ++ tau2 A' := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Dir.left⟩, qN) := by
    intro qN w' h
    rw [htr] at h
    injection h with h1 _
    injection h1 with _ h_dir
    injection h_dir with h_dir2
    cases h_dir2
  have h_eq' : tau1 A = liftTape tm t.left.toList.reverse ++ ↟ₛq :: ↟ₜt.head ::
      (liftTape tm t.right.toList ++ [#] ++ tau2 A) := by
    simpa [encodeRunningCfg, liftTape_cons, List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_tau1, hA_tau2⟩ :=
    copy_prefix_forced_state_lead tm q t.head h_not_left
      t.left.toList.reverse A
      (liftTape tm t.right.toList ++ [#] ++ tau2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced tm q t.head
      (liftTape tm t.right.toList ++ [#] ++ tau2 A) A1
      hA_mem hA_tau1
  simp only [transitionTilesFor] at h_tile_in
  rw [htr] at h_tile_in
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_tile_in
  rcases h_tile_in with rfl | rfl
  · -- tile = rightMoveTile (intended)
    have hA2_tau1 : tau1 A2 = liftTape tm t.right.toList ++ [#] ++ tau2 A := by
      have key := hA_tau1
      rw [hA1_decomp, tau1_cons, rightMoveTile_top] at key
      simpa using key
    obtain ⟨A3, hA2, hA3_mem, hA3_tau1, hA3_tau2⟩ :=
      copy_prefix_forced tm t.right.toList A2
        ([#] ++ tau2 A) hA2_mem
        (by simpa [List.append_assoc] using hA2_tau1)
        (by intro x h; injection h with h1 _; cases h1)
        (by intro q' x h; injection h with h1 _; cases h1)
    obtain ⟨A4, hA3_decomp, hA4_tau1, hA4_mem⟩ :=
      sep_forced tm (tau2 A) A3 hA3_mem (by simpa using hA3_tau1)
    refine ⟨A4, ?_, hA4_mem, ?_⟩
    · rw [hA, hA1_decomp, hA2, hA3_decomp]
      simp only [stepTilesRightInterior, List.append_assoc, List.cons_append,
                 List.nil_append]
    · rw [hA4_tau1, hA_tau2, hA1_decomp, tau2_cons, rightMoveTile_bot,
          hA3_tau2, hA3_decomp, tau2_cons, sepTile_bot,
          encodeCfg_after_right_move_eq tm qNew t w h_nondeg h_right_ne]
      simp [List.append_assoc]
  · -- tile = rightMoveBoundaryTile (must be ruled out: t.right ≠ []).
    exfalso
    have key := hA_tau1
    rw [hA1_decomp, tau1_cons, rightMoveBoundaryTile_top] at key
    cases h_rt : t.right.toList with
    | nil => exact h_right_ne h_rt
    | cons c cs =>
      rw [h_rt] at key
      simp only [liftTape_cons, List.cons_append, List.nil_append] at key
      injection key with _ key
      injection key with _ key
      injection key with h_third _
      cases h_third

-- NOTE: `starts_with_stepTilesLeftBoundary` is intentionally not
-- provided. Following Hopcroft–Ullman–Motwani's one-sided tape design
-- (the `NoLeftBoundary` constraint), the configuration
-- `⟨some q, t⟩` with `t.left.toList = []` and `tm.tr q t.head` a
-- left-move never arises in a reachable cfg, so this sub-lemma of the
-- backward direction would have no callers.

/-! ### Step 4 helper: rule out the alternative right-boundary decomposition

The right-boundary case has a structural ambiguity not present in the
interior case: `rightMoveTile` (top length 2) and `rightMoveBoundaryTile`
(top length 3 ending in `#`) both fit the lookahead
`[↟ₛq, ↟ₜt.head, #, …]` when `t.right = []`. The helper below proves
that under the non-halting hypothesis `qNew = some _`, the alternative
forces a residual lookahead containing `↟ₛqNew_q :: # :: …`, which no
`haltTiles` tile can consume — every transition tile's second character
is a tape lift, never `#`. -/

/-- If `tau1 A` begins `↟ₛq :: # :: …` (state marker immediately
followed by the separator), no tile of `haltTiles` can be the head of
`A`. -/
private lemma no_tile_for_state_sharp (tm : SingleTapeTM Symbol) (q : tm.State)
    (rest : List (Alpha tm.State Symbol))
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : tau1 A = ↟ₛq :: # :: rest) :
    False := by
  cases A with
  | nil => simp at h_eq
  | cons t A_rest =>
    have h_t_mem : t ∈ haltTiles tm := h_mem t (List.mem_cons_self ..)
    rw [tau1_cons] at h_eq
    rcases mem_haltTiles_top tm t h_t_mem with
        ⟨_, rfl⟩
      | rfl
      | ⟨_, _, _, _, _, rfl⟩
      | ⟨_, _, _, _, _, rfl | rfl⟩
      | ⟨_, _, _, _, _, _, rfl⟩
      | ⟨_, rfl⟩
      | ⟨_, rfl⟩
      | rfl
    all_goals simp at h_eq

/-- Right-move boundary case (`t.right` empty), under the non-halting
hypothesis `qNew = some _`.

Following Hopcroft–Ullman–Motwani's proof style: the alternative
`rightMoveTile :: sepTile :: …` decomposition eventually exposes a
residual lookahead `↟ₛqNew_q :: # :: …`, which `no_tile_for_state_sharp`
proves impossible. When `qNew = none` (this step is the halting one)
the alternative becomes admissible — `backward_aux` will handle that
halt-now branch directly via `Halts` reachability, without invoking
this lemma. -/
private lemma starts_with_stepTilesRightBoundary (tm : SingleTapeTM Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew_q : tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, some Dir.right⟩, some qNew_q))
    (h_right_empty : t.right.toList = [])
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : tau1 A = encodeRunningCfg tm q t ++ [#] ++ tau2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A = stepTilesRightBoundary tm q (some qNew_q) t w ++ A' ∧
        (∀ s ∈ A', s ∈ haltTiles tm) ∧
        tau1 A' = encodeCfg tm ⟨some qNew_q, (t.write w).move_right⟩
                    ++ [#] ++ tau2 A' := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Dir.left⟩, qN) := by
    intro qN w' h
    rw [htr] at h
    injection h with h1 _
    injection h1 with _ h_dir
    injection h_dir with h_dir2
    cases h_dir2
  have h_eq' : tau1 A = liftTape tm t.left.toList.reverse ++
      ↟ₛq :: ↟ₜt.head :: ([#] ++ tau2 A) := by
    simpa [encodeRunningCfg, h_right_empty, liftTape_nil,
           List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_tau1, hA_tau2⟩ :=
    copy_prefix_forced_state_lead tm q t.head h_not_left
      t.left.toList.reverse A ([#] ++ tau2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced tm q t.head ([#] ++ tau2 A) A1 hA_mem hA_tau1
  simp only [transitionTilesFor] at h_tile_in
  rw [htr] at h_tile_in
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_tile_in
  rcases h_tile_in with rfl | rfl
  · -- Alternative case: `rightMoveTile` — ruled out under `qNew = some _`.
    exfalso
    have hA2_tau1 : tau1 A2 = [#] ++ tau2 A := by
      have key := hA_tau1
      rw [hA1_decomp, tau1_cons, rightMoveTile_top] at key
      simpa using key
    obtain ⟨A3, hA2_decomp, hA3_tau1, hA3_mem⟩ :=
      sep_forced tm (tau2 A) A2 hA2_mem (by simpa using hA2_tau1)
    have hA3_tau1_full :
        tau1 A3 = liftTape tm t.left.toList.reverse ++
          [↟ₜw, ↟ₛqNew_q, #] ++ tau2 A3 := by
      rw [hA3_tau1, hA_tau2, hA1_decomp, hA2_decomp]
      simp [tau2_cons, rightMoveTile_bot, sepTile_bot, stateMarker_some,
            List.append_assoc]
    obtain ⟨A4, _, hA4_mem, hA4_tau1, _⟩ :=
      copy_prefix_forced tm t.left.toList.reverse A3
        ([↟ₜw, ↟ₛqNew_q, #] ++ tau2 A3) hA3_mem
        (by simpa [List.append_assoc] using hA3_tau1_full)
        (by intro x h; injection h with h1 _; cases h1)
        (by intro q' x h; injection h with h1 _; cases h1)
    cases A4 with
    | nil => simp at hA4_tau1
    | cons t4 A4_rest =>
      have h_t4_mem : t4 ∈ haltTiles tm := hA4_mem t4 (List.mem_cons_self ..)
      have h_t4_rest_mem : ∀ s ∈ A4_rest, s ∈ haltTiles tm :=
        fun s hs => hA4_mem s (List.mem_cons_of_mem t4 hs)
      rw [tau1_cons] at hA4_tau1
      rcases mem_haltTiles_top tm t4 h_t4_mem with
          ⟨_, rfl⟩
        | rfl
        | ⟨_, _, _, _, _, rfl⟩
        | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨_, _, _, _, _, _, rfl⟩
        | ⟨_, rfl⟩
        | ⟨_, rfl⟩
        | rfl
      · -- copyTile a' (only viable; `a' = w` forced by first char).
        simp only [copyTile_top, List.cons_append, List.nil_append] at hA4_tau1
        injection hA4_tau1 with _ h_rest
        exact no_tile_for_state_sharp tm qNew_q (tau2 A3) A4_rest
          h_t4_rest_mem h_rest
      · simp at hA4_tau1   -- sepTile
      · simp at hA4_tau1   -- noMoveTile
      · simp at hA4_tau1   -- rightMoveTile
      · simp at hA4_tau1   -- rightMoveBoundaryTile
      · -- leftMoveTile: third char of top `↟ₜa'` must match `#`.
        simp only [leftMoveTile_top, List.cons_append,
                   List.nil_append] at hA4_tau1
        injection hA4_tau1 with _ h
        injection h with _ h2
        injection h2 with h3 _
        cases h3
      · -- absorbLeftTile: second char `h⊥` must match `↟ₛqNew_q`.
        simp only [absorbLeftTile_top, List.cons_append,
                   List.nil_append] at hA4_tau1
        injection hA4_tau1 with _ h
        injection h with h2 _
        cases h2
      · simp at hA4_tau1   -- absorbRightTile
      · simp at hA4_tau1   -- finalTile
  · -- Intended case: `rightMoveBoundaryTile`.
    have hA2_tau1 : tau1 A2 = tau2 A := by
      have key := hA_tau1
      rw [hA1_decomp, tau1_cons, rightMoveBoundaryTile_top] at key
      simpa using key
    refine ⟨A2, ?_, hA2_mem, ?_⟩
    · rw [hA, hA1_decomp]
      simp only [stepTilesRightBoundary, List.append_assoc, List.cons_append,
                 List.nil_append]
    · rw [hA2_tau1, hA_tau2, hA1_decomp, tau2_cons,
          rightMoveBoundaryTile_bot, stateMarker_some,
          encodeCfg_after_right_move_boundary_eq tm (some qNew_q) t w
            h_nondeg h_right_empty]
      simp [List.append_assoc]

/-! ## Step 4: backward step for left-move in the interior

Under the HUM refactor (no `leftMoveBoundaryTile` in `haltTiles`) the
left-interior case is no longer ambiguous: after stripping the
`bs.reverse` copies (where `bs = t.left.tail`), the only tile that
can match the lookahead `[↟ₜb, ↟ₛq, ↟ₜt.head, …]` is
`leftMoveTile q t.head qNew w b`.

The `copyTile` "alternative" (which under the old design would peel
the last left lift and then use `leftMoveBoundaryTile`) is ruled out
here by `transition_forced`: after the `copyTile` peel the residual
lookahead begins `↟ₛq :: ↟ₜt.head :: …`, and the only transition
tiles for `(q, t.head)` are now `leftMoveTile` variants whose top
begins with `↟ₜb'` (not `↟ₛq`) — a direct constructor mismatch. -/

/-- Left-move interior case (`t.left.toList ≠ []`). -/
private lemma starts_with_stepTilesLeftInterior (tm : SingleTapeTM Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew : Option tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, some Dir.left⟩, qNew))
    (h_left_ne : t.left.toList ≠ [])
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ [])
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ haltTiles tm)
    (h_eq : tau1 A = encodeRunningCfg tm q t ++ [#] ++ tau2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A = stepTilesLeftInterior tm q qNew t w ++ A' ∧
        (∀ s ∈ A', s ∈ haltTiles tm) ∧
        tau1 A' = encodeCfg tm ⟨qNew, (t.write w).move_left⟩
                    ++ [#] ++ tau2 A' := by
  -- Reshape the lookahead: peel off the innermost left-tape symbol.
  have h_split : t.left.toList.reverse =
      t.left.tail.toList.reverse ++ [t.left.head] := by
    conv_lhs => rw [← head_cons_tail_toList t.left h_left_ne]
    simp [List.reverse_cons]
  have h_eq' : tau1 A = liftTape tm t.left.tail.toList.reverse ++
      ↟ₜt.left.head :: ↟ₛq :: ↟ₜt.head ::
      (liftTape tm t.right.toList ++ [#] ++ tau2 A) := by
    rw [h_eq, encodeRunningCfg, h_split,
        liftTape_append, liftTape_cons, liftTape_nil, liftTape_cons]
    simp [List.append_assoc]
  -- Strip the `bs.reverse` copy prefix (everything before the
  -- innermost left symbol `t.left.head`).
  obtain ⟨A1, hA, hA_mem, hA_tau1, hA_tau2⟩ :=
    copy_prefix_forced tm t.left.tail.toList.reverse A
      (↟ₜt.left.head :: ↟ₛq :: ↟ₜt.head ::
        (liftTape tm t.right.toList ++ [#] ++ tau2 A))
      h_mem h_eq'
      (by intro x h; injection h with h1 _; cases h1)
      (by intro q' x h; injection h with h1 _; cases h1)
  -- A1's first tile must be `leftMoveTile q t.head qNew w t.left.head`.
  cases A1 with
  | nil => simp at hA_tau1
  | cons t1 A1_rest =>
    have h_t1_mem : t1 ∈ haltTiles tm := hA_mem t1 (List.mem_cons_self ..)
    have h_a1_rest_mem : ∀ s ∈ A1_rest, s ∈ haltTiles tm :=
      fun s hs => hA_mem s (List.mem_cons_of_mem t1 hs)
    rw [tau1_cons] at hA_tau1
    rcases mem_haltTiles_top tm t1 h_t1_mem with
        ⟨_, rfl⟩
      | rfl
      | ⟨_, _, _, _, _, rfl⟩
      | ⟨_, _, _, _, _, rfl | rfl⟩
      | ⟨q', a', qNew', w', h_tr', b', rfl⟩
      | ⟨_, rfl⟩
      | ⟨_, rfl⟩
      | rfl
    · -- copyTile a': peel; the residual then starts with `↟ₛq :: ↟ₜt.head`.
      -- `transition_forced` returns a `leftMoveTile` (whose top begins
      -- `↟ₜb'`), contradicting the `↟ₛq` lead.
      simp only [copyTile_top, List.cons_append, List.nil_append] at hA_tau1
      injection hA_tau1 with h_head h_tail
      injection h_head with h_a; subst h_a
      obtain ⟨tile', _, hA1_rest_decomp, h_tile_in, _⟩ :=
        transition_forced tm q t.head
          (liftTape tm t.right.toList ++ [#] ++ tau2 A) A1_rest
          h_a1_rest_mem (by simpa using h_tail)
      simp only [transitionTilesFor] at h_tile_in
      rw [htr] at h_tile_in
      simp only [List.mem_map] at h_tile_in
      obtain ⟨_, _, rfl⟩ := h_tile_in
      have key := h_tail
      rw [hA1_rest_decomp, tau1_cons, leftMoveTile_top] at key
      simp only [List.cons_append, List.nil_append] at key
      injection key with h_h _
      cases h_h
    · simp only [sepTile_top, List.cons_append, List.nil_append] at hA_tau1
      injection hA_tau1 with h _; cases h
    · simp only [noMoveTile_top, List.cons_append, List.nil_append] at hA_tau1
      injection hA_tau1 with h _; cases h
    · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at hA_tau1
      injection hA_tau1 with h _; cases h
    · simp only [rightMoveBoundaryTile_top, List.cons_append,
                 List.nil_append] at hA_tau1
      injection hA_tau1 with h _; cases h
    · -- Canonical: `leftMoveTile q' a' qNew' w' b'`. Identify the
      -- parameters: `b' = t.left.head`, `q' = q`, `a' = t.head`, and
      -- then `htr` + `h_tr'` give `w' = w`, `qNew' = qNew`.
      simp only [leftMoveTile_top, List.cons_append, List.nil_append] at hA_tau1
      injection hA_tau1 with h_b h_rest1
      injection h_b with h_b'
      subst h_b'
      injection h_rest1 with h_q h_rest2
      injection h_q with h_q'
      subst h_q'
      injection h_rest2 with h_a h_rest3
      injection h_a with h_a'
      subst h_a'
      have h_tr_eq := h_tr'.symm.trans htr
      injection h_tr_eq with h_w_eq h_qNew_eq
      injection h_w_eq with h_w'
      subst w'
      subst qNew'
      -- `h_rest3 : tau1 A1_rest = liftTape t.right ++ [#] ++ tau2 A`.
      -- Strip the right-tape copies.
      obtain ⟨A2, hA1_rest_decomp, hA2_mem, hA2_tau1, hA2_tau2⟩ :=
        copy_prefix_forced tm t.right.toList A1_rest
          ([#] ++ tau2 A) h_a1_rest_mem
          (by simpa [List.append_assoc] using h_rest3)
          (by intro x h; injection h with h1 _; cases h1)
          (by intro q' x h; injection h with h1 _; cases h1)
      -- Peel the closing `sepTile`.
      obtain ⟨A3, hA2_decomp, hA3_tau1, hA3_mem⟩ :=
        sep_forced tm (tau2 A) A2 hA2_mem (by simpa using hA2_tau1)
      refine ⟨A3, ?_, hA3_mem, ?_⟩
      · rw [hA, hA1_rest_decomp, hA2_decomp]
        simp only [stepTilesLeftInterior, List.append_assoc,
                   List.cons_append, List.nil_append]
      · rw [hA3_tau1, hA_tau2, tau2_cons, leftMoveTile_bot,
            hA2_tau2, hA2_decomp, tau2_cons, sepTile_bot,
            encodeCfg_after_left_move_eq tm qNew t w h_nondeg]
        simp [List.append_assoc]
    · simp only [absorbLeftTile_top, List.cons_append,
                 List.nil_append] at hA_tau1
      injection hA_tau1 with _ h
      injection h with h2 _
      cases h2
    · simp only [absorbRightTile_top, List.cons_append,
                 List.nil_append] at hA_tau1
      injection hA_tau1 with h _; cases h
    · simp only [finalTile_top, List.cons_append, List.nil_append] at hA_tau1
      injection hA_tau1 with h _; cases h

/-! ## Queue-based extras encoding for the canonical iff

`queueEncoding tm cfgs` concatenates `encodeCfg tm c ++ [#]` for each
`c ∈ cfgs`. The canonical `backward_aux_weak` maintains the matching
invariant
  `tau1 A = encodeCfg tm cfg ++ [#] ++ queueEncoding tm rest_cfgs ++ tau2 A`
where `(cfg, rest_cfgs)` is the head + tail of a queue tracking
simulations still to be processed. The current cfg's chain
`initCfg →* cfg` is threaded separately. -/

private def queueEncoding (tm : SingleTapeTM Symbol) :
    List tm.Cfg → List (Alpha tm.State Symbol)
  | []        => []
  | c :: rest => encodeCfg tm c ++ [#] ++ queueEncoding tm rest

@[simp] private lemma queueEncoding_nil (tm : SingleTapeTM Symbol) :
    queueEncoding tm [] = [] := rfl

@[simp] private lemma queueEncoding_cons (tm : SingleTapeTM Symbol)
    (c : tm.Cfg) (rest : List tm.Cfg) :
    queueEncoding tm (c :: rest) =
      encodeCfg tm c ++ [#] ++ queueEncoding tm rest := rfl

private lemma queueEncoding_append_single (tm : SingleTapeTM Symbol)
    (cfgs : List tm.Cfg) (c : tm.Cfg) :
    queueEncoding tm (cfgs ++ [c]) =
      queueEncoding tm cfgs ++ encodeCfg tm c ++ [#] := by
  induction cfgs with
  | nil => simp [queueEncoding]
  | cons _ _ ih => simp [queueEncoding, ih, List.append_assoc]

private lemma queueEncoding_append_pair (tm : SingleTapeTM Symbol)
    (cfgs : List tm.Cfg) (c1 c2 : tm.Cfg) :
    queueEncoding tm (cfgs ++ [c1, c2]) =
      queueEncoding tm cfgs ++ encodeCfg tm c1 ++ [#] ++
        encodeCfg tm c2 ++ [#] := by
  induction cfgs with
  | nil => simp [queueEncoding]
  | cons _ _ ih => simp [queueEncoding, ih, List.append_assoc]

/-! ## Step 4 (extras-aware): step lemmas threading a queue of pending cfgs

Each lemma is the queue-aware counterpart of its `_weak` predecessor.
The matching invariant carries an explicit `rest_cfgs` queue of cfgs
whose encodings sit between `[#]` (after the current cfg) and `tau2 A`.
After peeling one canonical step block (for the current cfg), the
residual's invariant has the queue augmented by `[stepResult]`
(sepTile case) or `[stepResult, initCfg]` (startTile case). -/

private lemma starts_with_stepTilesNoMove_weak_ext (tm : SingleTapeTM Symbol)
    (w_in : List Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew : Option tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, none⟩, qNew))
    (rest_cfgs : List tm.Cfg)
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : tau1 A = encodeRunningCfg tm q t ++ [#] ++
              queueEncoding tm rest_cfgs ++ tau2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A'.length < A.length ∧
        (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) ∧
        ((tau1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, t.write w⟩]) ++ tau2 A') ∨
         (tau1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, t.write w⟩,
              SingleTapeTM.initCfg tm w_in]) ++ tau2 A')) := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Dir.left⟩, qN) := by
    intro qN w' h
    rw [htr] at h
    injection h with h1 _
    injection h1 with _ h_dir
    cases h_dir
  have h_eq' : tau1 A =
      liftTape tm t.left.toList.reverse ++ ↟ₛq :: ↟ₜt.head ::
        (liftTape tm t.right.toList ++ [#] ++
          queueEncoding tm rest_cfgs ++ tau2 A) := by
    simpa [encodeRunningCfg, liftTape_cons, List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_tau1, hA_tau2⟩ :=
    copy_prefix_forced_state_lead_weak tm w_in q t.head h_not_left
      t.left.toList.reverse A
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ tau2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced_weak tm w_in q t.head
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ tau2 A) A1 hA_mem hA_tau1
  have h_tile_eq : tile = noMoveTile tm q t.head qNew w := by
    simp only [transitionTilesFor] at h_tile_in
    rw [htr] at h_tile_in
    exact List.mem_singleton.mp h_tile_in
  subst h_tile_eq
  have hA2_tau1 : tau1 A2 = liftTape tm t.right.toList ++ [#] ++
      queueEncoding tm rest_cfgs ++ tau2 A := by
    have key := hA_tau1
    rw [hA1_decomp, tau1_cons, noMoveTile_top] at key
    simpa using key
  obtain ⟨A3, hA2, hA3_mem, hA3_tau1, hA3_tau2⟩ :=
    copy_prefix_forced_weak tm w_in t.right.toList A2
      ([#] ++ queueEncoding tm rest_cfgs ++ tau2 A) hA2_mem
      (by simpa [List.append_assoc] using hA2_tau1)
      (by intro x h; injection h with h1 _; cases h1)
      (by intro q' x h; injection h with h1 _; cases h1)
  obtain ⟨A4, hA3_decomp_disj, hA4_tau1, hA4_mem⟩ :=
    sep_forced_weak tm w_in (queueEncoding tm rest_cfgs ++ tau2 A) A3
      hA3_mem (by simpa using hA3_tau1)
  refine ⟨A4, ?_, hA4_mem, ?_⟩
  · rcases hA3_decomp_disj with ⟨hA3_decomp, _⟩ | ⟨hA3_decomp, _⟩
    all_goals
      rw [hA, hA1_decomp, hA2, hA3_decomp]
      simp [List.length_append, List.length_map, List.length_reverse]
      omega
  · rcases hA3_decomp_disj with ⟨hA3_decomp, _⟩ | ⟨hA3_decomp, _⟩
    · left
      rw [hA4_tau1, hA_tau2, hA1_decomp, tau2_cons, noMoveTile_bot, hA3_tau2,
          hA3_decomp, tau2_cons, sepTile_bot, queueEncoding_append_single]
      cases qNew with
      | none =>
        simp [encodeCfg_halted, encodeHaltedCfg, BiTape.write,
              stateMarker_none, liftTape_cons, List.append_assoc]
      | some q' =>
        simp [encodeCfg_running, encodeRunningCfg, BiTape.write,
              stateMarker_some, liftTape_cons, List.append_assoc]
    · right
      rw [hA4_tau1, hA_tau2, hA1_decomp, tau2_cons, noMoveTile_bot, hA3_tau2,
          hA3_decomp, tau2_cons, startTile_bot, queueEncoding_append_pair]
      cases qNew with
      | none =>
        simp [encodeCfg_halted, encodeHaltedCfg, BiTape.write,
              stateMarker_none, liftTape_cons, List.append_assoc]
      | some q' =>
        simp [encodeCfg_running, encodeRunningCfg, BiTape.write,
              stateMarker_some, liftTape_cons, List.append_assoc]

private lemma starts_with_stepTilesRightInterior_weak_ext (tm : SingleTapeTM Symbol)
    (w_in : List Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew : Option tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, some Dir.right⟩, qNew))
    (h_right_ne : t.right.toList ≠ [])
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (rest_cfgs : List tm.Cfg)
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : tau1 A = encodeRunningCfg tm q t ++ [#] ++
              queueEncoding tm rest_cfgs ++ tau2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A'.length < A.length ∧
        (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) ∧
        ((tau1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, (t.write w).move_right⟩]) ++ tau2 A') ∨
         (tau1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, (t.write w).move_right⟩,
              SingleTapeTM.initCfg tm w_in]) ++ tau2 A')) := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Dir.left⟩, qN) := by
    intro qN w' h
    rw [htr] at h
    injection h with h1 _
    injection h1 with _ h_dir
    injection h_dir with h_dir2
    cases h_dir2
  have h_eq' : tau1 A = liftTape tm t.left.toList.reverse ++ ↟ₛq :: ↟ₜt.head ::
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ tau2 A) := by
    simpa [encodeRunningCfg, liftTape_cons, List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_tau1, hA_tau2⟩ :=
    copy_prefix_forced_state_lead_weak tm w_in q t.head h_not_left
      t.left.toList.reverse A
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ tau2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced_weak tm w_in q t.head
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ tau2 A) A1 hA_mem hA_tau1
  simp only [transitionTilesFor] at h_tile_in
  rw [htr] at h_tile_in
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_tile_in
  rcases h_tile_in with rfl | rfl
  · -- rightMoveTile (intended).
    have hA2_tau1 : tau1 A2 = liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ tau2 A := by
      have key := hA_tau1
      rw [hA1_decomp, tau1_cons, rightMoveTile_top] at key
      simpa using key
    obtain ⟨A3, hA2, hA3_mem, hA3_tau1, hA3_tau2⟩ :=
      copy_prefix_forced_weak tm w_in t.right.toList A2
        ([#] ++ queueEncoding tm rest_cfgs ++ tau2 A) hA2_mem
        (by simpa [List.append_assoc] using hA2_tau1)
        (by intro x h; injection h with h1 _; cases h1)
        (by intro q' x h; injection h with h1 _; cases h1)
    obtain ⟨A4, hA3_decomp_disj, hA4_tau1, hA4_mem⟩ :=
      sep_forced_weak tm w_in (queueEncoding tm rest_cfgs ++ tau2 A) A3
        hA3_mem (by simpa using hA3_tau1)
    refine ⟨A4, ?_, hA4_mem, ?_⟩
    · rcases hA3_decomp_disj with ⟨hA3_decomp, _⟩ | ⟨hA3_decomp, _⟩
      all_goals
        rw [hA, hA1_decomp, hA2, hA3_decomp]
        simp [List.length_append, List.length_map, List.length_reverse]
        omega
    · rcases hA3_decomp_disj with ⟨hA3_decomp, _⟩ | ⟨hA3_decomp, _⟩
      · left
        rw [hA4_tau1, hA_tau2, hA1_decomp, tau2_cons, rightMoveTile_bot,
            hA3_tau2, hA3_decomp, tau2_cons, sepTile_bot,
            queueEncoding_append_single,
            encodeCfg_after_right_move_eq tm qNew t w h_nondeg h_right_ne]
        simp [List.append_assoc]
      · right
        rw [hA4_tau1, hA_tau2, hA1_decomp, tau2_cons, rightMoveTile_bot,
            hA3_tau2, hA3_decomp, tau2_cons, startTile_bot,
            queueEncoding_append_pair,
            encodeCfg_after_right_move_eq tm qNew t w h_nondeg h_right_ne]
        simp [List.append_assoc]
  · -- rightMoveBoundaryTile (ruled out: t.right ≠ []).
    exfalso
    have key := hA_tau1
    rw [hA1_decomp, tau1_cons, rightMoveBoundaryTile_top] at key
    cases h_rt : t.right.toList with
    | nil => exact h_right_ne h_rt
    | cons c cs =>
      rw [h_rt] at key
      simp only [liftTape_cons, List.cons_append, List.nil_append] at key
      injection key with _ key
      injection key with _ key
      injection key with h_third _
      cases h_third

/-- Structural property: `tau1 A` never contains `↟ₛq :: # :: …` as a
sublist, for any `q`. This is because (a) within any tile's top, the
character following `↟ₛq` is always a tape lift `↟ₜa` (never `#`), and
(b) no tile's top ends with `↟ₛq`, so the offending substring cannot
straddle a tile boundary. Used to discharge the alternative
`rightMoveTile` path in `starts_with_stepTilesRightBoundary_weak_ext`
even with non-empty `rest_cfgs`. -/
private lemma tau1_no_state_marker_then_sharp
    (tm : SingleTapeTM Symbol) (w_in : List Symbol) (q : tm.State) :
    ∀ (A : Stack (Alpha tm.State Symbol))
       (l1 l2 : List (Alpha tm.State Symbol)),
      (∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm) →
      tau1 A = l1 ++ ↟ₛq :: # :: l2 → False := by
  intro A
  induction A with
  | nil =>
    intro l1 l2 _ h
    rw [tau1_nil] at h
    cases l1 <;> simp at h
  | cons t A_rest ih =>
    intro l1 l2 h_mem h_eq
    have h_t_in : t ∈ startTile tm w_in :: haltTiles tm :=
      h_mem t (List.mem_cons_self ..)
    have h_rest_in : ∀ s ∈ A_rest, s ∈ startTile tm w_in :: haltTiles tm :=
      fun s hs => h_mem s (List.mem_cons_of_mem t hs)
    rw [tau1_cons] at h_eq
    rcases List.mem_cons.mp h_t_in with rfl | h_t_lu
    · -- t = startTile, top = [#].
      simp only [startTile_top, List.cons_append, List.nil_append] at h_eq
      cases l1 with
      | nil => injection h_eq with h _; cases h
      | cons _ l1' =>
        simp only [List.cons_append] at h_eq
        injection h_eq with _ h_tail
        exact ih l1' l2 h_rest_in h_tail
    · rcases mem_haltTiles_top tm t h_t_lu with
          ⟨a, rfl⟩
        | rfl
        | ⟨q', a, _, _, _, rfl⟩
        | ⟨q', a, _, _, _, rfl | rfl⟩
        | ⟨_, _, _, _, _, b, rfl⟩
        | ⟨a, rfl⟩
        | ⟨a, rfl⟩
        | rfl
      · -- copyTile a, top = [↟ₜa] (length 1).
        simp only [copyTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' =>
          simp only [List.cons_append] at h_eq
          injection h_eq with _ h_tail
          exact ih l1' l2 h_rest_in h_tail
      · -- sepTile, top = [#] (length 1).
        simp only [sepTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' =>
          simp only [List.cons_append] at h_eq
          injection h_eq with _ h_tail
          exact ih l1' l2 h_rest_in h_tail
      · -- noMoveTile q' a _ _, top = [↟ₛq', ↟ₜa].
        simp only [noMoveTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil =>
          injection h_eq with _ h2
          injection h2 with h _; cases h
        | cons _ l1' =>
          cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' =>
            simp only [List.cons_append] at h_eq
            injection h_eq with _ h2
            injection h2 with _ h_tail
            exact ih l1'' l2 h_rest_in h_tail
      · -- rightMoveTile q' a _ _, top = [↟ₛq', ↟ₜa].
        simp only [rightMoveTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil =>
          injection h_eq with _ h2
          injection h2 with h _; cases h
        | cons _ l1' =>
          cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' =>
            simp only [List.cons_append] at h_eq
            injection h_eq with _ h2
            injection h2 with _ h_tail
            exact ih l1'' l2 h_rest_in h_tail
      · -- rightMoveBoundaryTile q' a _ _, top = [↟ₛq', ↟ₜa, #].
        simp only [rightMoveBoundaryTile_top, List.cons_append,
                   List.nil_append] at h_eq
        cases l1 with
        | nil =>
          injection h_eq with _ h2
          injection h2 with h _; cases h
        | cons _ l1' =>
          cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' =>
            cases l1'' with
            | nil => injection h_eq with _ h2; injection h2 with _ h3; injection h3 with h _; cases h
            | cons _ l1''' =>
              simp only [List.cons_append] at h_eq
              injection h_eq with _ h2
              injection h2 with _ h3
              injection h3 with _ h_tail
              exact ih l1''' l2 h_rest_in h_tail
      · -- leftMoveTile q' a _ _ b, top = [↟ₜb, ↟ₛq', ↟ₜa].
        -- At l1 = [_], the second injection gives `↟ₛq' = ↟ₛq` (same
        -- constructor; only gives `q' = q`), so we need a third
        -- injection to reach `↟ₜa = #`.
        simp only [leftMoveTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' =>
          cases l1' with
          | nil =>
            injection h_eq with _ h2
            injection h2 with _ h3
            injection h3 with h _; cases h
          | cons _ l1'' =>
            cases l1'' with
            | nil => injection h_eq with _ h2; injection h2 with _ h3; injection h3 with h _; cases h
            | cons _ l1''' =>
              simp only [List.cons_append] at h_eq
              injection h_eq with _ h2
              injection h2 with _ h3
              injection h3 with _ h_tail
              exact ih l1''' l2 h_rest_in h_tail
      · -- absorbLeftTile a, top = [↟ₜa, h⊥].
        simp only [absorbLeftTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' =>
          cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' =>
            simp only [List.cons_append] at h_eq
            injection h_eq with _ h2
            injection h2 with _ h_tail
            exact ih l1'' l2 h_rest_in h_tail
      · -- absorbRightTile a, top = [h⊥, ↟ₜa].
        simp only [absorbRightTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' =>
          cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' =>
            simp only [List.cons_append] at h_eq
            injection h_eq with _ h2
            injection h2 with _ h_tail
            exact ih l1'' l2 h_rest_in h_tail
      · -- finalTile, top = [h⊥, #, #].
        simp only [finalTile_top, List.cons_append, List.nil_append] at h_eq
        cases l1 with
        | nil => injection h_eq with h _; cases h
        | cons _ l1' =>
          cases l1' with
          | nil => injection h_eq with _ h2; injection h2 with h _; cases h
          | cons _ l1'' =>
            cases l1'' with
            | nil => injection h_eq with _ h2; injection h2 with _ h3; injection h3 with h _; cases h
            | cons _ l1''' =>
              simp only [List.cons_append] at h_eq
              injection h_eq with _ h2
              injection h2 with _ h3
              injection h3 with _ h_tail
              exact ih l1''' l2 h_rest_in h_tail

/-- Extras-aware right-boundary step lemma. The alternative
`rightMoveTile` path is discharged via `tau1_no_state_marker_then_sharp`:
after `sep_forced_weak` (in either branch), the residual `A3` has
`↟ₛqNew_q :: # :: …` somewhere in `tau1 A3`, which is structurally
impossible. -/
private lemma starts_with_stepTilesRightBoundary_weak_ext (tm : SingleTapeTM Symbol)
    (w_in : List Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew_q : tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, some Dir.right⟩, some qNew_q))
    (h_right_empty : t.right.toList = [])
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (rest_cfgs : List tm.Cfg)
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : tau1 A = encodeRunningCfg tm q t ++ [#] ++
              queueEncoding tm rest_cfgs ++ tau2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A'.length < A.length ∧
        (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) ∧
        tau1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨some qNew_q, (t.write w).move_right⟩]) ++ tau2 A' := by
  have h_not_left : ∀ (qN : Option tm.State) (w' : Option Symbol),
      tm.tr q t.head ≠ (⟨w', some Dir.left⟩, qN) := by
    intro qN w' h
    rw [htr] at h
    injection h with h1 _
    injection h1 with _ h_dir
    injection h_dir with h_dir2
    cases h_dir2
  have h_eq' : tau1 A = liftTape tm t.left.toList.reverse ++
      ↟ₛq :: ↟ₜt.head :: ([#] ++ queueEncoding tm rest_cfgs ++ tau2 A) := by
    simpa [encodeRunningCfg, h_right_empty, liftTape_nil,
           List.append_assoc] using h_eq
  obtain ⟨A1, hA, hA_mem, hA_tau1, hA_tau2⟩ :=
    copy_prefix_forced_state_lead_weak tm w_in q t.head h_not_left
      t.left.toList.reverse A
      ([#] ++ queueEncoding tm rest_cfgs ++ tau2 A) h_mem h_eq'
  obtain ⟨tile, A2, hA1_decomp, h_tile_in, hA2_mem⟩ :=
    transition_forced_weak tm w_in q t.head
      ([#] ++ queueEncoding tm rest_cfgs ++ tau2 A) A1 hA_mem hA_tau1
  simp only [transitionTilesFor] at h_tile_in
  rw [htr] at h_tile_in
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_tile_in
  rcases h_tile_in with rfl | rfl
  · -- rightMoveTile alternative — ruled out via tau1_no_state_marker_then_sharp.
    exfalso
    have hA2_tau1 : tau1 A2 = [#] ++ queueEncoding tm rest_cfgs ++ tau2 A := by
      have key := hA_tau1
      rw [hA1_decomp, tau1_cons, rightMoveTile_top] at key
      simpa using key
    obtain ⟨A3, hA2_decomp_disj, hA3_tau1, hA3_mem⟩ :=
      sep_forced_weak tm w_in (queueEncoding tm rest_cfgs ++ tau2 A) A2
        hA2_mem (by simpa using hA2_tau1)
    rcases hA2_decomp_disj with ⟨hA2_decomp, _⟩ | ⟨hA2_decomp, _⟩
    · -- sepTile branch.
      have hA3_tau1_full :
          tau1 A3 = (queueEncoding tm rest_cfgs ++
              liftTape tm t.left.toList.reverse ++ [↟ₜw]) ++
            ↟ₛqNew_q :: # :: tau2 A3 := by
        rw [hA3_tau1, hA_tau2, hA1_decomp, tau2_cons, rightMoveTile_bot,
            hA2_decomp, tau2_cons, sepTile_bot, stateMarker_some]
        simp [List.append_assoc]
      exact tau1_no_state_marker_then_sharp tm w_in qNew_q A3 _ (tau2 A3)
        hA3_mem hA3_tau1_full
    · -- startTile branch.
      have hA3_tau1_full :
          tau1 A3 = (queueEncoding tm rest_cfgs ++
              liftTape tm t.left.toList.reverse ++ [↟ₜw]) ++
            ↟ₛqNew_q :: # ::
              (encodeCfg tm (SingleTapeTM.initCfg tm w_in) ++
                [#] ++ tau2 A3) := by
        rw [hA3_tau1, hA_tau2, hA1_decomp, tau2_cons, rightMoveTile_bot,
            hA2_decomp, tau2_cons, startTile_bot, stateMarker_some]
        simp [List.append_assoc]
      exact tau1_no_state_marker_then_sharp tm w_in qNew_q A3 _ _
        hA3_mem hA3_tau1_full
  · -- Canonical: rightMoveBoundaryTile.
    have hA2_tau1 : tau1 A2 = queueEncoding tm rest_cfgs ++ tau2 A := by
      have key := hA_tau1
      rw [hA1_decomp, tau1_cons, rightMoveBoundaryTile_top] at key
      simpa using key
    refine ⟨A2, ?_, hA2_mem, ?_⟩
    · rw [hA, hA1_decomp]
      simp [List.length_append, List.length_map, List.length_reverse]
      omega
    · rw [hA2_tau1, hA_tau2, hA1_decomp, tau2_cons,
          rightMoveBoundaryTile_bot, stateMarker_some,
          queueEncoding_append_single,
          encodeCfg_after_right_move_boundary_eq tm (some qNew_q) t w
            h_nondeg h_right_empty]
      simp [List.append_assoc]

private lemma starts_with_stepTilesLeftInterior_weak_ext (tm : SingleTapeTM Symbol)
    (w_in : List Symbol)
    (q : tm.State) (t : BiTape Symbol)
    (qNew : Option tm.State) (w : Option Symbol)
    (htr : tm.tr q t.head = (⟨w, some Dir.left⟩, qNew))
    (h_left_ne : t.left.toList ≠ [])
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ [])
    (rest_cfgs : List tm.Cfg)
    (A : Stack (Alpha tm.State Symbol))
    (h_mem : ∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm)
    (h_eq : tau1 A = encodeRunningCfg tm q t ++ [#] ++
              queueEncoding tm rest_cfgs ++ tau2 A) :
    ∃ A' : Stack (Alpha tm.State Symbol),
        A'.length < A.length ∧
        (∀ s ∈ A', s ∈ startTile tm w_in :: haltTiles tm) ∧
        ((tau1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, (t.write w).move_left⟩]) ++ tau2 A') ∨
         (tau1 A' = queueEncoding tm
            (rest_cfgs ++ [⟨qNew, (t.write w).move_left⟩,
              SingleTapeTM.initCfg tm w_in]) ++ tau2 A')) := by
  have h_split : t.left.toList.reverse =
      t.left.tail.toList.reverse ++ [t.left.head] := by
    conv_lhs => rw [← head_cons_tail_toList t.left h_left_ne]
    simp [List.reverse_cons]
  have h_eq' : tau1 A = liftTape tm t.left.tail.toList.reverse ++
      ↟ₜt.left.head :: ↟ₛq :: ↟ₜt.head ::
      (liftTape tm t.right.toList ++ [#] ++
        queueEncoding tm rest_cfgs ++ tau2 A) := by
    rw [h_eq, encodeRunningCfg, h_split,
        liftTape_append, liftTape_cons, liftTape_nil, liftTape_cons]
    simp [List.append_assoc]
  obtain ⟨A1, hA, hA_mem, hA_tau1, hA_tau2⟩ :=
    copy_prefix_forced_weak tm w_in t.left.tail.toList.reverse A
      (↟ₜt.left.head :: ↟ₛq :: ↟ₜt.head ::
        (liftTape tm t.right.toList ++ [#] ++
          queueEncoding tm rest_cfgs ++ tau2 A))
      h_mem h_eq'
      (by intro x h; injection h with h1 _; cases h1)
      (by intro q' x h; injection h with h1 _; cases h1)
  cases A1 with
  | nil => simp at hA_tau1
  | cons t1 A1_rest =>
    have h_t1_in : t1 ∈ startTile tm w_in :: haltTiles tm :=
      hA_mem t1 (List.mem_cons_self ..)
    have h_a1_rest_in : ∀ s ∈ A1_rest, s ∈ startTile tm w_in :: haltTiles tm :=
      fun s hs => hA_mem s (List.mem_cons_of_mem t1 hs)
    rw [tau1_cons] at hA_tau1
    rcases List.mem_cons.mp h_t1_in with rfl | h_t1_lu
    · simp only [startTile_top, List.cons_append, List.nil_append] at hA_tau1
      injection hA_tau1 with h _; cases h
    · rcases mem_haltTiles_top tm t1 h_t1_lu with
          ⟨_, rfl⟩
        | rfl
        | ⟨_, _, _, _, _, rfl⟩
        | ⟨_, _, _, _, _, rfl | rfl⟩
        | ⟨q', a', qNew', w', h_tr', b', rfl⟩
        | ⟨_, rfl⟩
        | ⟨_, rfl⟩
        | rfl
      · simp only [copyTile_top, List.cons_append, List.nil_append] at hA_tau1
        injection hA_tau1 with h_head h_tail
        injection h_head with h_a; subst h_a
        obtain ⟨tile', _, hA1_rest_decomp, h_tile_in, _⟩ :=
          transition_forced_weak tm w_in q t.head
            (liftTape tm t.right.toList ++ [#] ++
              queueEncoding tm rest_cfgs ++ tau2 A) A1_rest
            h_a1_rest_in (by simpa using h_tail)
        simp only [transitionTilesFor] at h_tile_in
        rw [htr] at h_tile_in
        simp only [List.mem_map] at h_tile_in
        obtain ⟨_, _, rfl⟩ := h_tile_in
        have key := h_tail
        rw [hA1_rest_decomp, tau1_cons, leftMoveTile_top] at key
        simp only [List.cons_append, List.nil_append] at key
        injection key with h_h _
        cases h_h
      · simp only [sepTile_top, List.cons_append, List.nil_append] at hA_tau1
        injection hA_tau1 with h _; cases h
      · simp only [noMoveTile_top, List.cons_append, List.nil_append] at hA_tau1
        injection hA_tau1 with h _; cases h
      · simp only [rightMoveTile_top, List.cons_append, List.nil_append] at hA_tau1
        injection hA_tau1 with h _; cases h
      · simp only [rightMoveBoundaryTile_top, List.cons_append,
                   List.nil_append] at hA_tau1
        injection hA_tau1 with h _; cases h
      · -- Canonical: leftMoveTile.
        simp only [leftMoveTile_top, List.cons_append, List.nil_append] at hA_tau1
        injection hA_tau1 with h_b h_rest1
        injection h_b with h_b'
        subst h_b'
        injection h_rest1 with h_q h_rest2
        injection h_q with h_q'
        subst h_q'
        injection h_rest2 with h_a h_rest3
        injection h_a with h_a'
        subst h_a'
        have h_tr_eq := h_tr'.symm.trans htr
        injection h_tr_eq with h_w_eq h_qNew_eq
        injection h_w_eq with h_w'
        subst w'
        subst qNew'
        obtain ⟨A2, hA1_rest_decomp, hA2_mem, hA2_tau1, hA2_tau2⟩ :=
          copy_prefix_forced_weak tm w_in t.right.toList A1_rest
            ([#] ++ queueEncoding tm rest_cfgs ++ tau2 A) h_a1_rest_in
            (by simpa [List.append_assoc] using h_rest3)
            (by intro x h; injection h with h1 _; cases h1)
            (by intro q' x h; injection h with h1 _; cases h1)
        obtain ⟨A3, hA2_decomp_disj, hA3_tau1, hA3_mem⟩ :=
          sep_forced_weak tm w_in (queueEncoding tm rest_cfgs ++ tau2 A) A2
            hA2_mem (by simpa using hA2_tau1)
        refine ⟨A3, ?_, hA3_mem, ?_⟩
        · rcases hA2_decomp_disj with ⟨hA2_decomp, _⟩ | ⟨hA2_decomp, _⟩
          all_goals
            rw [hA, hA1_rest_decomp, hA2_decomp]
            simp [List.length_append, List.length_map, List.length_reverse,
                  List.length_cons]
            omega
        · rcases hA2_decomp_disj with ⟨hA2_decomp, _⟩ | ⟨hA2_decomp, _⟩
          · left
            rw [hA3_tau1, hA_tau2, tau2_cons, leftMoveTile_bot,
                hA2_tau2, hA2_decomp, tau2_cons, sepTile_bot,
                queueEncoding_append_single,
                encodeCfg_after_left_move_eq tm qNew t w h_nondeg]
            simp [List.append_assoc]
          · right
            rw [hA3_tau1, hA_tau2, tau2_cons, leftMoveTile_bot,
                hA2_tau2, hA2_decomp, tau2_cons, startTile_bot,
                queueEncoding_append_pair,
                encodeCfg_after_left_move_eq tm qNew t w h_nondeg]
            simp [List.append_assoc]
      · simp only [absorbLeftTile_top, List.cons_append,
                   List.nil_append] at hA_tau1
        injection hA_tau1 with _ h
        injection h with h2 _
        cases h2
      · simp only [absorbRightTile_top, List.cons_append,
                   List.nil_append] at hA_tau1
        injection hA_tau1 with h _; cases h
      · simp only [finalTile_top, List.cons_append, List.nil_append] at hA_tau1
        injection hA_tau1 with h _; cases h

/-! ## Step 6: `backward_aux` — main strong induction

The main strong-induction lemma for the backward direction. Given a stack
`A` whose tiles are drawn from `haltTiles tm` and which carries the matching
invariant `tau1 A = encodeCfg tm cfg ++ [#] ++ tau2 A`, produce a halting
trace `cfg →* ⟨none, tape⟩`.

The induction is on a strict bound `A.length ≤ n`. At each level we case
on `cfg.state`:
* `none` — `cfg` is already halted: return `ReflTransGen.refl`.
* `some q` — destructure `tm.tr q tape.head = (⟨w', mov⟩, qNew)` and
  dispatch on `(mov, tape.right/left empty)`:
  - The non-degenerate branches apply the corresponding
    `starts_with_stepTiles*` lemma to peel a canonical step block off
    the front of `A`, chain a single TM transition (`tm_step_running`),
    and recurse via the IH.
  - The right-boundary halt-now sub-case (`qNew = none`,
    `tape.right.toList = []`) bypasses the step lemma — the single TM
    step already reaches a halted cfg, so we close the trace directly.
  - The left-boundary sub-case is ruled out by `NoLeftBoundary`. -/

private lemma backward_aux (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w_in : List Symbol)
    (h_nlb : NoLeftBoundary tm w_in) :
    ∀ (n : ℕ) (A : Stack (Alpha tm.State Symbol)) (cfg : tm.Cfg),
      A.length ≤ n →
      Relation.ReflTransGen tm.TransitionRelation
          (SingleTapeTM.initCfg tm w_in) cfg →
      (∀ s ∈ A, s ∈ haltTiles tm) →
      tau1 A = encodeCfg tm cfg ++ [#] ++ tau2 A →
      ∃ tape : BiTape Symbol,
        Relation.ReflTransGen tm.TransitionRelation cfg
            ⟨none, tape⟩ := by
  intro n
  induction n with
  | zero =>
    intro A cfg hLen _ _ hMatch
    -- A = []; matching invariant gives [] = encodeCfg ++ [#] ++ [], contradicts the trailing #.
    have hA_nil : A = [] := by
      cases A with
      | nil => rfl
      | cons _ _ => simp at hLen
    subst hA_nil
    exfalso
    simp only [tau1_nil, tau2_nil, List.append_nil] at hMatch
    -- hMatch : [] = encodeCfg tm cfg ++ [#]
    have h_len_zero : (encodeCfg tm cfg ++ [#]).length = 0 := by
      have := congrArg List.length hMatch
      simpa using this.symm
    simp [List.length_append] at h_len_zero
  | succ n ih =>
    intro A cfg hLen hReach hMem hMatch
    cases hcfg : cfg with
    | mk state tape =>
      cases state with
      | none =>
        -- cfg = ⟨none, tape⟩ is already halted.
        exact ⟨tape, Relation.ReflTransGen.refl⟩
      | some q =>
        -- cfg = ⟨some q, tape⟩. Destructure the transition.
        rcases h_tr : tm.tr q tape.head with ⟨⟨w', mov⟩, qNew⟩
        have hMatch' : tau1 A = encodeRunningCfg tm q tape ++ [#] ++ tau2 A := by
          rw [hcfg] at hMatch; exact hMatch
        have h_w_ne : w' ≠ none := by
          have := h_nbw q tape.head; rw [h_tr] at this; exact this
        have h_reach' : Relation.ReflTransGen tm.TransitionRelation
            (SingleTapeTM.initCfg tm w_in) (stepResult tm q tape) := by
          refine hReach.tail ?_
          show tm.step cfg = some (stepResult tm q tape)
          rw [hcfg]; exact tm_step_running tm q tape
        cases mov with
        | none =>
          -- No-move case.
          obtain ⟨A', hA', hA'_mem, hA'_match⟩ :=
            starts_with_stepTilesNoMove tm q tape qNew w' h_tr A hMem hMatch'
          have hA'_len : A'.length ≤ n := by
            have h_split : A.length =
                (stepTilesNoMove tm q qNew tape w').length + A'.length := by
              rw [hA']; simp
            have h_step_pos :
                0 < (stepTilesNoMove tm q qNew tape w').length := by
              simp [stepTilesNoMove]
            omega
          have h_stepRes : stepResult tm q tape = ⟨qNew, tape.write w'⟩ := by
            simp [stepResult, h_tr, BiTape.optionMove]
          have hA'_match' :
              tau1 A' = encodeCfg tm (stepResult tm q tape) ++ [#] ++ tau2 A' := by
            rw [h_stepRes]; exact hA'_match
          obtain ⟨tape_h, h_h⟩ :=
            ih A' (stepResult tm q tape) hA'_len h_reach' hA'_mem hA'_match'
          exact ⟨tape_h, .head (tm_step_running tm q tape) h_h⟩
        | some dir =>
          cases dir with
          | right =>
            cases h_right : tape.right.toList with
            | nil =>
              cases qNew with
              | none =>
                -- Right-boundary halt-now: single TM step reaches halted cfg.
                refine ⟨(tape.write w').move_right, ?_⟩
                refine Relation.ReflTransGen.single ?_
                show tm.step ⟨some q, tape⟩ = some _
                rw [tm_step_running]
                congr 1
                simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
              | some qNew_q =>
                obtain ⟨A', hA', hA'_mem, hA'_match⟩ :=
                  starts_with_stepTilesRightBoundary tm q tape qNew_q w' h_tr
                    h_right (Or.inl h_w_ne) A hMem hMatch'
                have hA'_len : A'.length ≤ n := by
                  have h_split : A.length =
                      (stepTilesRightBoundary tm q (some qNew_q) tape w').length +
                        A'.length := by rw [hA']; simp
                  have h_step_pos :
                      0 < (stepTilesRightBoundary tm q (some qNew_q) tape w').length := by
                    simp [stepTilesRightBoundary]
                  omega
                have h_stepRes :
                    stepResult tm q tape = ⟨some qNew_q, (tape.write w').move_right⟩ := by
                  simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
                have hA'_match' :
                    tau1 A' = encodeCfg tm (stepResult tm q tape) ++ [#] ++ tau2 A' := by
                  rw [h_stepRes]; exact hA'_match
                obtain ⟨tape_h, h_h⟩ :=
                  ih A' (stepResult tm q tape) hA'_len h_reach' hA'_mem hA'_match'
                exact ⟨tape_h, .head (tm_step_running tm q tape) h_h⟩
            | cons _ _ =>
              -- Right-interior case.
              have h_right_ne : tape.right.toList ≠ [] := by
                rw [h_right]; exact List.cons_ne_nil _ _
              obtain ⟨A', hA', hA'_mem, hA'_match⟩ :=
                starts_with_stepTilesRightInterior tm q tape qNew w' h_tr
                  h_right_ne (Or.inl h_w_ne) A hMem hMatch'
              have hA'_len : A'.length ≤ n := by
                have h_split : A.length =
                    (stepTilesRightInterior tm q qNew tape w').length + A'.length := by
                  rw [hA']; simp
                have h_step_pos :
                    0 < (stepTilesRightInterior tm q qNew tape w').length := by
                  simp [stepTilesRightInterior]
                omega
              have h_stepRes :
                  stepResult tm q tape = ⟨qNew, (tape.write w').move_right⟩ := by
                simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
              have hA'_match' :
                  tau1 A' = encodeCfg tm (stepResult tm q tape) ++ [#] ++ tau2 A' := by
                rw [h_stepRes]; exact hA'_match
              obtain ⟨tape_h, h_h⟩ :=
                ih A' (stepResult tm q tape) hA'_len h_reach' hA'_mem hA'_match'
              exact ⟨tape_h, .head (tm_step_running tm q tape) h_h⟩
          | left =>
            cases h_left : tape.left.toList with
            | nil =>
              -- Ruled out by NoLeftBoundary.
              exfalso
              have h_no_lb := h_nlb cfg hReach q tape hcfg h_left
              apply h_no_lb
              rw [h_tr]
            | cons _ _ =>
              -- Left-interior case.
              have h_left_ne : tape.left.toList ≠ [] := by
                rw [h_left]; exact List.cons_ne_nil _ _
              obtain ⟨A', hA', hA'_mem, hA'_match⟩ :=
                starts_with_stepTilesLeftInterior tm q tape qNew w' h_tr
                  h_left_ne (Or.inl h_w_ne) A hMem hMatch'
              have hA'_len : A'.length ≤ n := by
                have h_split : A.length =
                    (stepTilesLeftInterior tm q qNew tape w').length + A'.length := by
                  rw [hA']; simp
                have h_step_pos :
                    0 < (stepTilesLeftInterior tm q qNew tape w').length := by
                  simp [stepTilesLeftInterior]
                omega
              have h_stepRes :
                  stepResult tm q tape = ⟨qNew, (tape.write w').move_left⟩ := by
                simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
              have hA'_match' :
                  tau1 A' = encodeCfg tm (stepResult tm q tape) ++ [#] ++ tau2 A' := by
                rw [h_stepRes]; exact hA'_match
              obtain ⟨tape_h, h_h⟩ :=
                ih A' (stepResult tm q tape) hA'_len h_reach' hA'_mem hA'_match'
              exact ⟨tape_h, .head (tm_step_running tm q tape) h_h⟩

/-! ## Step 7: `halt_le_mpcp_strong` — the equivalence (strong-A form)

The reduction `Halt ≤_m MPCP` packaged as an `Iff` using a strengthened
formulation: solutions are drawn from `haltTiles tm` alone (rather than
`startTile :: haltTiles tm`). The forward direction uses the existing
`forward_aux`; the backward direction re-packages `backward_aux` after
cancelling the leading `#` separator.

Both directions assume `NoBlankWrites tm` and `NoLeftBoundary tm w`, the
two HUM side conditions described in `Basic.lean`.

The fully general statement `Halts tm w ↔ MHasSolution …` (which allows
solutions to include the start tile mid-stream) is `halt_le_mpcp` below,
established via `backward_aux_weak` with a chain-tracked cfg queue. -/

/-- **`Halt ≤_m MPCP`** (strong-A form, auxiliary): `Halts tm w` is
equivalent to the existence of a stack `A` whose tiles all belong to
`haltTiles tm` (no use of the start tile in the rest) and that satisfies
the MPCP matching equation with the canonical `startTile`. The
canonical form, using `MHasSolution` directly, is `halt_le_mpcp` below. -/
theorem halt_le_mpcp_strong (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol)
    (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    ∃ A : Stack (Alpha tm.State Symbol),
      (∀ t ∈ A, t ∈ haltTiles tm) ∧
      [#] ++ tau1 A = # :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A := by
  constructor
  · -- Forward: extract from `Halts` a halting trace, then construct A.
    intro h
    obtain ⟨target_tape, h_chain⟩ := h
    obtain ⟨n, h_chain_n⟩ := h_chain.relatesInSteps
    obtain ⟨A, hA_mem, hA_match⟩ :=
      forward_aux tm h_nbw w h_nlb target_tape
        (SingleTapeTM.initCfg tm w) n Relation.ReflTransGen.refl h_chain_n
    refine ⟨A, hA_mem, ?_⟩
    rw [hA_match]
    show [#] ++ (encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A) =
         # :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A
    simp [List.append_assoc]
  · -- Backward: cancel leading `#`, apply `backward_aux`.
    rintro ⟨A, h_mem, h_match⟩
    have h_match' :
        tau1 A = encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A := by
      have h_step : # :: tau1 A =
          # :: (encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A) := by
        have h_lhs : ([#] : List (Alpha tm.State Symbol)) ++ tau1 A
                   = # :: tau1 A := rfl
        have h_rhs :
            # :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A
              = # :: (encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A) := by
          simp [List.append_assoc]
        rw [h_lhs, h_rhs] at h_match
        exact h_match
      exact (List.cons.injEq _ _ _ _ |>.mp h_step).2
    obtain ⟨tape, h_trace⟩ :=
      backward_aux tm h_nbw w h_nlb A.length A (SingleTapeTM.initCfg tm w)
        (le_refl _) Relation.ReflTransGen.refl h_mem h_match'
    exact ⟨tape, h_trace⟩

/-! ## Step 6 (canonical): `backward_aux_weak` — strong induction with
chain-tracked queue

Generalises `backward_aux` to admit `A` drawn from
`startTile :: haltTiles tm`. The matching invariant carries a `queue` of
cfgs whose encodings appear in `tau1 A` (concatenated via
`queueEncoding`). The `chains` parameter associates each cfg in the
queue with a reachability proof from `initCfg`. At each iteration we
pop the head `cfg`, peel its step block via the appropriate
extras-aware step lemma, and push the new cfg(s) onto the tail of the
queue — one (`stepResult`) for `sepTile`, two (`stepResult` + `initCfg`)
for `startTile`. When the popped cfg's state is `none`, the
accompanying chain is the halt witness for `initCfg →* halted`. -/

private lemma backward_aux_weak (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w_in : List Symbol)
    (h_nlb : NoLeftBoundary tm w_in) :
    ∀ (n : ℕ) (A : Stack (Alpha tm.State Symbol))
       (queue : List tm.Cfg)
       (_chains : ∀ c ∈ queue, Relation.ReflTransGen tm.TransitionRelation
          (SingleTapeTM.initCfg tm w_in) c),
      A.length ≤ n →
      queue ≠ [] →
      (∀ s ∈ A, s ∈ startTile tm w_in :: haltTiles tm) →
      tau1 A = queueEncoding tm queue ++ tau2 A →
      ∃ tape : BiTape Symbol,
        Relation.ReflTransGen tm.TransitionRelation
          (SingleTapeTM.initCfg tm w_in) ⟨none, tape⟩ := by
  intro n
  induction n with
  | zero =>
    intro A queue _chains hLen hQ_ne _ hMatch
    exfalso
    have hA_nil : A = [] := by
      cases A with | nil => rfl | cons _ _ => simp at hLen
    subst hA_nil
    simp only [tau1_nil, tau2_nil, List.append_nil] at hMatch
    cases queue with
    | nil => exact hQ_ne rfl
    | cons head rest =>
      simp [queueEncoding] at hMatch
  | succ n ih =>
    intro A queue chains hLen hQ_ne h_mem hMatch
    cases queue with
    | nil => exact (hQ_ne rfl).elim
    | cons cfg rest_cfgs =>
      have hMatch' : tau1 A = encodeCfg tm cfg ++ [#] ++
                       queueEncoding tm rest_cfgs ++ tau2 A := by
        rw [hMatch, queueEncoding_cons, List.append_assoc]
      have chain_cfg : Relation.ReflTransGen tm.TransitionRelation
          (SingleTapeTM.initCfg tm w_in) cfg :=
        chains cfg (List.mem_cons_self ..)
      have rest_chains :
          ∀ c ∈ rest_cfgs,
            Relation.ReflTransGen tm.TransitionRelation
              (SingleTapeTM.initCfg tm w_in) c :=
        fun c hc => chains c (List.mem_cons_of_mem cfg hc)
      cases hcfg : cfg with
      | mk state tape =>
        cases state with
        | none =>
          refine ⟨tape, ?_⟩
          rw [← hcfg]; exact chain_cfg
        | some q =>
          rcases h_tr : tm.tr q tape.head with ⟨⟨w', mov⟩, qNew⟩
          have h_w_ne : w' ≠ none := by
            have := h_nbw q tape.head; rw [h_tr] at this; exact this
          have hMatch'' : tau1 A = encodeRunningCfg tm q tape ++ [#] ++
                            queueEncoding tm rest_cfgs ++ tau2 A := by
            rw [hcfg] at hMatch'; exact hMatch'
          have h_step_cfg : tm.step cfg = some (stepResult tm q tape) := by
            rw [hcfg]; exact tm_step_running tm q tape
          have new_chain_step : Relation.ReflTransGen tm.TransitionRelation
              (SingleTapeTM.initCfg tm w_in) (stepResult tm q tape) :=
            chain_cfg.tail h_step_cfg
          -- Build the IH-application helper: given the disjunction's
          -- chosen branch (new queue value + matching), recurse.
          -- Common logic for all non-halt-now cases.
          cases mov with
          | none =>
            -- No-move case.
            obtain ⟨A', hLen', hMem', hTau1Disj⟩ :=
              starts_with_stepTilesNoMove_weak_ext tm w_in q tape qNew w' h_tr
                rest_cfgs A h_mem hMatch''
            have hA'_len : A'.length ≤ n := by omega
            have h_stepRes : stepResult tm q tape = ⟨qNew, tape.write w'⟩ := by
              simp [stepResult, h_tr, BiTape.optionMove]
            have new_chain' : Relation.ReflTransGen tm.TransitionRelation
                (SingleTapeTM.initCfg tm w_in) ⟨qNew, tape.write w'⟩ := by
              rw [← h_stepRes]; exact new_chain_step
            rcases hTau1Disj with hSep | hStart
            · refine ih A' (rest_cfgs ++ [⟨qNew, tape.write w'⟩]) ?_ hA'_len
                ?_ hMem' hSep
              · intro c hc
                rcases List.mem_append.mp hc with hr | hr
                · exact rest_chains c hr
                · rw [List.mem_singleton] at hr; subst hr; exact new_chain'
              · intro h_empty
                have := congrArg List.length h_empty
                simp [List.length_append] at this
            · refine ih A' (rest_cfgs ++ [⟨qNew, tape.write w'⟩,
                SingleTapeTM.initCfg tm w_in]) ?_ hA'_len ?_ hMem' hStart
              · intro c hc
                rcases List.mem_append.mp hc with hr | hr
                · exact rest_chains c hr
                · rcases List.mem_cons.mp hr with rfl | hr2
                  · exact new_chain'
                  · rw [List.mem_singleton] at hr2; subst hr2
                    exact Relation.ReflTransGen.refl
              · intro h_empty
                have := congrArg List.length h_empty
                simp [List.length_append] at this
          | some dir =>
            cases dir with
            | right =>
              cases h_right : tape.right.toList with
              | nil =>
                cases qNew with
                | none =>
                  -- Right-boundary halt-now: single TM step reaches halted cfg.
                  refine ⟨(tape.write w').move_right, ?_⟩
                  refine chain_cfg.tail ?_
                  show tm.step cfg = some _
                  rw [hcfg, tm_step_running]
                  congr 1
                  simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
                | some qNew_q =>
                  obtain ⟨A', hLen', hMem', hTau1⟩ :=
                    starts_with_stepTilesRightBoundary_weak_ext tm w_in q tape
                      qNew_q w' h_tr h_right (Or.inl h_w_ne) rest_cfgs A h_mem hMatch''
                  have hA'_len : A'.length ≤ n := by omega
                  have h_stepRes :
                      stepResult tm q tape =
                        ⟨some qNew_q, (tape.write w').move_right⟩ := by
                    simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
                  have new_chain' : Relation.ReflTransGen tm.TransitionRelation
                      (SingleTapeTM.initCfg tm w_in)
                      ⟨some qNew_q, (tape.write w').move_right⟩ := by
                    rw [← h_stepRes]; exact new_chain_step
                  refine ih A' (rest_cfgs ++ [⟨some qNew_q,
                    (tape.write w').move_right⟩]) ?_ hA'_len ?_ hMem' hTau1
                  · intro c hc
                    rcases List.mem_append.mp hc with hr | hr
                    · exact rest_chains c hr
                    · rw [List.mem_singleton] at hr; subst hr; exact new_chain'
                  · intro h_empty
                    have := congrArg List.length h_empty
                    simp [List.length_append] at this
              | cons _ _ =>
                have h_right_ne : tape.right.toList ≠ [] := by
                  rw [h_right]; exact List.cons_ne_nil _ _
                obtain ⟨A', hLen', hMem', hTau1Disj⟩ :=
                  starts_with_stepTilesRightInterior_weak_ext tm w_in q tape
                    qNew w' h_tr h_right_ne (Or.inl h_w_ne) rest_cfgs A h_mem hMatch''
                have hA'_len : A'.length ≤ n := by omega
                have h_stepRes :
                    stepResult tm q tape = ⟨qNew, (tape.write w').move_right⟩ := by
                  simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
                have new_chain' : Relation.ReflTransGen tm.TransitionRelation
                    (SingleTapeTM.initCfg tm w_in)
                    ⟨qNew, (tape.write w').move_right⟩ := by
                  rw [← h_stepRes]; exact new_chain_step
                rcases hTau1Disj with hSep | hStart
                · refine ih A' (rest_cfgs ++ [⟨qNew, (tape.write w').move_right⟩])
                    ?_ hA'_len ?_ hMem' hSep
                  · intro c hc
                    rcases List.mem_append.mp hc with hr | hr
                    · exact rest_chains c hr
                    · rw [List.mem_singleton] at hr; subst hr; exact new_chain'
                  · intro h_empty
                    have := congrArg List.length h_empty
                    simp [List.length_append] at this
                · refine ih A' (rest_cfgs ++ [⟨qNew, (tape.write w').move_right⟩,
                    SingleTapeTM.initCfg tm w_in]) ?_ hA'_len ?_ hMem' hStart
                  · intro c hc
                    rcases List.mem_append.mp hc with hr | hr
                    · exact rest_chains c hr
                    · rcases List.mem_cons.mp hr with rfl | hr2
                      · exact new_chain'
                      · rw [List.mem_singleton] at hr2; subst hr2
                        exact Relation.ReflTransGen.refl
                  · intro h_empty
                    have := congrArg List.length h_empty
                    simp [List.length_append] at this
            | left =>
              cases h_left : tape.left.toList with
              | nil =>
                exfalso
                have h_no_lb := h_nlb cfg chain_cfg q tape hcfg h_left
                apply h_no_lb
                rw [h_tr]
              | cons _ _ =>
                have h_left_ne : tape.left.toList ≠ [] := by
                  rw [h_left]; exact List.cons_ne_nil _ _
                obtain ⟨A', hLen', hMem', hTau1Disj⟩ :=
                  starts_with_stepTilesLeftInterior_weak_ext tm w_in q tape
                    qNew w' h_tr h_left_ne (Or.inl h_w_ne) rest_cfgs A h_mem hMatch''
                have hA'_len : A'.length ≤ n := by omega
                have h_stepRes :
                    stepResult tm q tape = ⟨qNew, (tape.write w').move_left⟩ := by
                  simp [stepResult, h_tr, BiTape.optionMove, BiTape.move]
                have new_chain' : Relation.ReflTransGen tm.TransitionRelation
                    (SingleTapeTM.initCfg tm w_in)
                    ⟨qNew, (tape.write w').move_left⟩ := by
                  rw [← h_stepRes]; exact new_chain_step
                rcases hTau1Disj with hSep | hStart
                · refine ih A' (rest_cfgs ++ [⟨qNew, (tape.write w').move_left⟩])
                    ?_ hA'_len ?_ hMem' hSep
                  · intro c hc
                    rcases List.mem_append.mp hc with hr | hr
                    · exact rest_chains c hr
                    · rw [List.mem_singleton] at hr; subst hr; exact new_chain'
                  · intro h_empty
                    have := congrArg List.length h_empty
                    simp [List.length_append] at this
                · refine ih A' (rest_cfgs ++ [⟨qNew, (tape.write w').move_left⟩,
                    SingleTapeTM.initCfg tm w_in]) ?_ hA'_len ?_ hMem' hStart
                  · intro c hc
                    rcases List.mem_append.mp hc with hr | hr
                    · exact rest_chains c hr
                    · rcases List.mem_cons.mp hr with rfl | hr2
                      · exact new_chain'
                      · rw [List.mem_singleton] at hr2; subst hr2
                        exact Relation.ReflTransGen.refl
                  · intro h_empty
                    have := congrArg List.length h_empty
                    simp [List.length_append] at this

/-! ## Step 7 (canonical): `mhasSolution_implies_halts` and the full iff -/

/-- The backward direction of the canonical iff: from an MPCP solution
for the encoded TM-halting instance, recover `Halts tm w`. Initialises
`backward_aux_weak`'s queue with `[initCfg]` (chain = `refl`). -/
theorem mhasSolution_implies_halts (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol)
    (h_nlb : NoLeftBoundary tm w)
    (h : MHasSolution (startTile tm w) (haltTiles tm)) :
    Halts tm w := by
  obtain ⟨A, h_mem, h_match⟩ := h
  -- Cancel leading `[#]` from the MHasSolution matching equation.
  have h_match_cfg :
      tau1 A = encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A := by
    have h_step : # :: tau1 A =
        # :: (encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A) := by
      have h_lhs : (startTile tm w).top ++ tau1 A = # :: tau1 A := by
        simp [startTile_top]
      have h_rhs :
          (startTile tm w).bot ++ tau2 A
            = # :: (encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A) := by
        simp [startTile_bot, List.append_assoc]
      rw [h_lhs, h_rhs] at h_match
      exact h_match
    exact (List.cons.injEq _ _ _ _ |>.mp h_step).2
  -- Repackage into the `queueEncoding [initCfg]` form.
  have h_match_queue :
      tau1 A = queueEncoding tm [SingleTapeTM.initCfg tm w] ++ tau2 A := by
    rw [h_match_cfg]
    simp [queueEncoding, List.append_assoc]
  exact backward_aux_weak tm h_nbw w h_nlb A.length A
    [SingleTapeTM.initCfg tm w]
    (fun c hc => by
      rw [List.mem_singleton] at hc; subst hc
      exact Relation.ReflTransGen.refl)
    (le_refl _)
    (List.cons_ne_nil _ _)
    h_mem
    h_match_queue

/-- **Canonical `Halt ≤_m MPCP` iff**. The forward direction is
`halts_implies_mhasSolution`; the backward direction is the new
`mhasSolution_implies_halts` (which threads a chain-tracked cfg queue
through `backward_aux_weak`). -/
theorem halt_le_mpcp (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol)
    (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔ MHasSolution (startTile tm w) (haltTiles tm) :=
  ⟨halts_implies_mhasSolution tm h_nbw w h_nlb,
   mhasSolution_implies_halts tm h_nbw w h_nlb⟩

end PCP.HaltToMPCP
