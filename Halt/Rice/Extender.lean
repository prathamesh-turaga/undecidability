/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Rice.Basic
public import Halt.Rice.TrivialTMs
public import Halt.CodeOf

@[expose] public section

/-!
# Rice extender — the constant-Sem reduction TM

For Rice's theorem (restricted form), we need a uniform construction
that takes a `TMCode` `c` and produces a `SingleTapeTM Bool` whose
halting behaviour encodes the self-halt question on `c`:

  `SemHalt (riceConstTM c) = univ`  iff  `c.toTM` halts on `encodeTMCode c`,
  `SemHalt (riceConstTM c) = ∅`     otherwise.

## Construction

`riceConstTM c` on input `w` proceeds in four phases:

1. **Erase** phase: scan right while writing blanks. This erases `w`
   from the tape and positions the head at the first cell past `w`.
   (For `w = []` the head is already at a blank cell; no scanning.)
2. **Write** phase (states `writeBit i` for `i < N`, where
   `N = (encodeTMCode c).length`): on each step, write the i-th bit of
   `encodeTMCode c` to the current cell, move right, transition to
   `writeBit (i+1)`. After the last bit, transition to `moveBack`.
3. **Move-back** phase (states `moveBack j` for `j ≤ N`): each step
   preserves the current head symbol, moves left, decrements the
   counter. At `j = 0`, transitions (without moving) to `inC c.q₀`.
4. **Simulate** phase (states `inC q` for `q ∈ Fin (c.numStates + 1)`):
   uses `c.tr` directly. Halts when `c.tr` returns `none`.

After phase 3, the head is at the first cell of `encodeTMCode c` and
the tape is `mk₁ (encodeTMCode c)` shifted by `|w|` cells (with blanks
in the shifted positions). Since `c.toTM` is position-relative, this
is behaviourally identical to running `c.toTM` on `encodeTMCode c`.

## Spec

```lean
theorem semHalt_riceConstTM (c : Halt.TMCode) :
    SemHalt (riceConstTM c) = univ ↔
      PCP.Halts c.toTM (Halt.Encoding.encodeTMCode c)
```

The corresponding `∅`-Sem characterisation is the contrapositive.

This file defines `riceConstTM` and basic structural lemmas. The
behaviour theorem `semHalt_riceConstTM` is proved in
`Halt.Rice.Theorem`.
-/

namespace Halt.Rice

open Turing PCP

variable (c : Halt.TMCode)

/-! ## Encoded length -/

/-- The length of the Gödel encoding of `c`. Always positive because
`encodeTMCode` starts with `encodeNat c.numStates` (length
`c.numStates + 1`). -/
def encodedLen (c : Halt.TMCode) : ℕ :=
  (Halt.Encoding.encodeTMCode c).length

lemma encodedLen_pos : 0 < encodedLen c := by
  unfold encodedLen Halt.Encoding.encodeTMCode
  show 0 < (Halt.Encoding.encodeNat c.numStates ++
              Halt.Encoding.encodeFin c.q₀ ++
              Halt.Encoding.encodeTrTable c.tr).length
  simp only [List.length_append, Halt.Encoding.encodeNat,
             List.length_append, List.length_singleton,
             List.length_replicate]
  omega

/-- The bits of `encodeTMCode c`, indexed by `Fin (encodedLen c)`. -/
def encodedBit (c : Halt.TMCode) (i : Fin (encodedLen c)) : Bool :=
  (Halt.Encoding.encodeTMCode c).get ⟨i.val, by
    have := i.isLt
    unfold encodedLen at this
    exact this⟩

/-! ## State space of the extender -/

/-- States of `riceConstTM c`. -/
inductive RiceState (c : Halt.TMCode) where
  /-- Erase phase: scan right writing blanks until first blank. -/
  | erase
  /-- Write the i-th bit of `encodeTMCode c`. -/
  | writeBit (i : Fin (encodedLen c))
  /-- Move head back to the start of `encodeTMCode c` with counter
  `j` steps remaining. -/
  | moveBack (j : Fin (encodedLen c + 1))
  /-- Simulate `c.toTM` in state `q`. -/
  | inC (q : Fin (c.numStates + 1))
  deriving DecidableEq

/-- Sum-type encoding for the `Fintype` instance. -/
def RiceState.toSum (s : RiceState c) :
    Unit ⊕ Fin (encodedLen c) ⊕ Fin (encodedLen c + 1) ⊕ Fin (c.numStates + 1) :=
  match s with
  | .erase      => .inl ()
  | .writeBit i => .inr (.inl i)
  | .moveBack j => .inr (.inr (.inl j))
  | .inC q      => .inr (.inr (.inr q))

def RiceState.fromSum
    (s : Unit ⊕ Fin (encodedLen c) ⊕ Fin (encodedLen c + 1)
            ⊕ Fin (c.numStates + 1)) :
    RiceState c :=
  match s with
  | .inl ()              => .erase
  | .inr (.inl i)        => .writeBit i
  | .inr (.inr (.inl j)) => .moveBack j
  | .inr (.inr (.inr q)) => .inC q

def RiceState.equivSum :
    RiceState c ≃
      Unit ⊕ Fin (encodedLen c) ⊕ Fin (encodedLen c + 1)
        ⊕ Fin (c.numStates + 1) where
  toFun := RiceState.toSum c
  invFun := RiceState.fromSum c
  left_inv s := by cases s <;> rfl
  right_inv s := by
    rcases s with _ | _ | s
    · rfl
    · rfl
    rcases s with _ | _ <;> rfl

instance : Fintype (RiceState c) :=
  Fintype.ofEquiv _ (RiceState.equivSum c).symm

instance : Inhabited (RiceState c) := ⟨.inC c.q₀⟩

/-! ## The transition function -/

/-- One step of `riceConstTM`: dispatch on the current state. -/
def riceTr (c : Halt.TMCode) (q : RiceState c) (sym : Option Bool) :
    SingleTapeTM.Stmt Bool × Option (RiceState c) :=
  match q with
  | .erase =>
    -- Scan right while reading data; once blank, transition to writeBit 0.
    match sym with
    | some _ => (⟨none, some Dir.right⟩, some .erase)
    | none   => (⟨none, none⟩, some (.writeBit ⟨0, encodedLen_pos c⟩))
  | .writeBit i =>
    -- Write bit_i, move right.
    let bit := encodedBit c i
    if h : i.val + 1 < encodedLen c then
      (⟨some bit, some Dir.right⟩, some (.writeBit ⟨i.val + 1, h⟩))
    else
      -- Last bit; transition to moveBack ⟨encodedLen c, _⟩.
      (⟨some bit, some Dir.right⟩,
        some (.moveBack ⟨encodedLen c, Nat.lt_succ_self _⟩))
  | .moveBack j =>
    -- Preserve current symbol, move left, decrement counter.
    if j.val = 0 then
      -- At the start of encodeTMCode c; transition to c.toTM.q₀.
      (⟨sym, none⟩, some (.inC c.q₀))
    else
      have h : j.val - 1 < encodedLen c + 1 := by
        have := j.isLt; omega
      (⟨sym, some Dir.left⟩, some (.moveBack ⟨j.val - 1, h⟩))
  | .inC q' =>
    -- Run c.tr.
    let (stmt, next) := c.tr q' sym
    (stmt, next.map .inC)

/-- The Rice extender for `c`: on any input, erases the input, writes
`encodeTMCode c`, repositions the head, then simulates `c.toTM`. -/
def riceConstTM (c : Halt.TMCode) : SingleTapeTM Bool where
  State := RiceState c
  q₀ := .erase
  tr := riceTr c

/-! ## Basic structural lemmas -/

@[simp] lemma riceConstTM_State :
    (riceConstTM c).State = RiceState c := rfl

@[simp] lemma riceConstTM_q₀ :
    (riceConstTM c).q₀ = (.erase : RiceState c) := rfl

@[simp] lemma riceConstTM_tr (q : RiceState c) (sym : Option Bool) :
    (riceConstTM c).tr q sym = riceTr c q sym := rfl

end Halt.Rice
