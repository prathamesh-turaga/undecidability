/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import PCP.MPCP

@[expose] public section

/-!
# MPCP ≤_m PCP

This file proves that the Modified Post Correspondence Problem (MPCP) is
many-one reducible to PCP. The proof follows the standard textbook
construction (Hopcroft–Ullman) and the Coq formalisation by Forster,
Heiter, and Smolka.

## Proof structure

1. **Alphabet extension** — extend `α` with two markers `⋕` (hash) and `＄`
   (dollar). Disjointness is enforced by the type `Ext α`.

2. **Interleaving functions** `hashL`, `hashR` — `hashL` puts `⋕` *before*
   each symbol; `hashR` puts `⋕` *after*. Their key duality
   (`hashL_snoc_eq`) is what allows the end tile to close a solution.

3. **Tile classes** — three roles:
   * `tileStart c`  — forces every solution to begin with this tile.
   * `tileReg t`    — interleaved version of an MPCP card.
   * `tileEnd`      — the unique closing tile.

4. **The reduction** `mpcpToPcp` — assembles the above into a PCP instance.

5. **Forward** (`mpcp_to_pcp_solution`) — every MPCP solution lifts to a
   PCP solution.

6. **Backward** (`pcp_to_mpcp_solution`) — every PCP solution to the
   reduced instance descends to an MPCP solution.

7. **Main equivalence** (`mpcp_iff_pcp`).
-/

namespace PCP

/-! ## Alphabet extension -/

/-- Extend alphabet `α` with two distinguished markers `⋕` (hash) and `＄`
    (dollar). The disjointness from the original alphabet is a *type fact*. -/
inductive Ext (α : Type) : Type
  | sym    : α → Ext α
  | hash   : Ext α
  | dollar : Ext α
  deriving DecidableEq

@[inherit_doc Ext.hash]   notation "⋕"  => Ext.hash
@[inherit_doc Ext.dollar] notation "＄"  => Ext.dollar
@[inherit_doc Ext.sym]    prefix:max "↟" => Ext.sym

/-! ## Interleaving functions

The two interleaving functions are *duals*:

| Function | Pattern per symbol `a` |
|----------|------------------------|
| `hashL`  | `⋕ · ↟a`               |
| `hashR`  | `↟a · ⋕`               |

Their key duality is `hashL_snoc_eq`: `hashL x ++ [⋕] = ⋕ :: hashR x`.
-/

variable {α : Type}

/-- Interleave with `⋕` *before* each symbol. -/
def hashL : Word α → Word (Ext α)
  | []      => []
  | a :: x  => ⋕ :: ↟a :: hashL x

/-- Interleave with `⋕` *after* each symbol. -/
def hashR : Word α → Word (Ext α)
  | []      => []
  | a :: x  => ↟a :: ⋕ :: hashR x

@[simp] theorem hashL_nil : hashL ([] : Word α) = [] := rfl
@[simp] theorem hashR_nil : hashR ([] : Word α) = [] := rfl

@[simp] theorem hashL_cons (a : α) (x : Word α) :
    hashL (a :: x) = ⋕ :: ↟a :: hashL x := rfl

@[simp] theorem hashR_cons (a : α) (x : Word α) :
    hashR (a :: x) = ↟a :: ⋕ :: hashR x := rfl

@[simp] theorem hashL_append (x y : Word α) :
    hashL (x ++ y) = hashL x ++ hashL y := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih]

@[simp] theorem hashR_append (x y : Word α) :
    hashR (x ++ y) = hashR x ++ hashR y := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih]

/-- Key duality: `hashL x ++ [⋕] = ⋕ :: hashR x`.

    This is what allows the end tile to close a solution. -/
theorem hashL_snoc_eq (x : Word α) :
    hashL x ++ [⋕] = ⋕ :: hashR x := by
  induction x with
  | nil => rfl
  | cons a x ih => simp [ih]

/-- `hashL` cannot match a `⋕`-prefixed `hashR` — used in `match_start`. -/
theorem hashL_ne_hash_hashR (x y : Word α) :
    hashL x ≠ ⋕ :: hashR y := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    simp
    intro h
    cases y with
    | nil => simp at h
    | cons b y =>
      simp at h
      grind

/-! ## Tile classes -/

/-- The start tile: forces every solution to begin with it. -/
def tileStart (c : Tile α) : Tile (Ext α) where
  top := ＄ :: hashL c.top
  bot := ＄ :: ⋕ :: hashR c.bot

/-- A regular tile: interleaved version of an MPCP card. -/
def tileReg (t : Tile α) : Tile (Ext α) where
  top := hashL t.top
  bot := hashR t.bot

/-- The end tile: the unique way to close a solution. -/
def tileEnd : Tile (Ext α) where
  top := [⋕, ＄]
  bot := [＄]

/-! ## The reduction -/

/-- Build the reduced PCP instance from an MPCP instance `(c, R)`.

    Layout:  `tileStart c :: regulars ++ [tileEnd]`,
    where `regulars` are the `tileReg`-encoded cards from `c :: R`,
    *with empty pairs filtered out*. The filter is essential: an empty
    regular card would supply a trivial PCP solution that does not
    correspond to any MPCP solution. -/
def mpcpToPcp (c : Tile α) (R : Stack α) : Stack (Ext α) :=
  tileStart c ::
  ((c :: R).filterMap (fun t =>
    if t.top ≠ [] ∨ t.bot ≠ [] then some (tileReg t) else none)) ++
  [tileEnd]

/-! ## Membership in `mpcpToPcp` -/

/-- Characterisation: every tile in `mpcpToPcp c R` is the start tile, the
    end tile, or a `tileReg` of some non-empty card from `c :: R`. -/
theorem mem_mpcpToPcp_iff (c : Tile α) (R : Stack α) (t : Tile (Ext α)) :
    t ∈ mpcpToPcp c R ↔
    t = tileStart c ∨
    t = tileEnd ∨
    ∃ s, s ∈ c :: R ∧ (s.top ≠ [] ∨ s.bot ≠ []) ∧ t = tileReg s := by
  unfold mpcpToPcp
  simp only [List.cons_append, List.mem_cons, List.mem_append,
             List.mem_filterMap, List.not_mem_nil,
             Option.ite_none_right_eq_some, Option.some.injEq, or_false]
  constructor
  · rintro (rfl | ⟨s, hmem, hne, hrfl⟩ | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨s, hmem, hne, hrfl.symm⟩)
    · exact Or.inr (Or.inl rfl)
  · rintro (rfl | rfl | ⟨s, hmem, hne, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl ⟨s, hmem, hne, rfl⟩)

/-- No tile in `mpcpToPcp c R` has top starting with a lifted symbol `↟a`.
    All tile tops begin with either `＄` (start tile), `⋕` (regular or end
    tile), or are empty. -/
theorem not_sym_head_top (c : Tile α) (R : Stack α) (a : α) (w u : Word (Ext α)) :
    Tile.mk (↟a :: w) u ∉ mpcpToPcp c R := by
  rw [mem_mpcpToPcp_iff]
  rintro (h | h | ⟨s, _, _, hk⟩)
  · simp [tileStart, Tile.mk.injEq] at h
  · simp [tileEnd, Tile.mk.injEq] at h
  · simp only [tileReg, Tile.mk.injEq] at hk
    obtain ⟨hk1, _⟩ := hk
    cases hxs : s.top with
    | nil =>
      rw [hxs, hashL_nil] at hk1
      exact List.cons_ne_nil _ _ hk1
    | cons b bs =>
      rw [hxs, hashL_cons] at hk1
      simp at hk1

/-- No tile in `mpcpToPcp c R` has bottom starting with `⋕`.
    All tile bottoms begin with either `＄` (start tile or end tile),
    `↟a` (regular tile), or are empty. -/
theorem not_hash_head_bot (c : Tile α) (R : Stack α) (v w : Word (Ext α)) :
    Tile.mk v (⋕ :: w) ∉ mpcpToPcp c R := by
  rw [mem_mpcpToPcp_iff]
  rintro (h | h | ⟨s, _, _, hk⟩)
  · simp [tileStart, Tile.mk.injEq] at h
  · simp [tileEnd, Tile.mk.injEq] at h
  · simp only [tileReg, Tile.mk.injEq] at hk
    obtain ⟨_, hk2⟩ := hk
    cases hys : s.bot with
    | nil =>
      rw [hys, hashR_nil] at hk2
      exact List.cons_ne_nil _ _ hk2
    | cons b bs =>
      rw [hys, hashR_cons] at hk2
      simp at hk2

/-! ## Stack-level invariants

These extend the pointwise lemmas to entire concatenations along a stack. -/

/-- Concatenation of tops never starts with a lifted symbol `↟a`. -/
theorem tau1_ne_sym_head (c : Tile α) (R : Stack α) (B : Stack (Ext α))
    (a : α) (w : Word (Ext α))
    (hmem : ∀ t ∈ B, t ∈ mpcpToPcp c R) :
    tau1 B ≠ ↟a :: w := by
  induction B generalizing w with
  | nil => simp
  | cons d B ih =>
    intro h
    have hd : d ∈ mpcpToPcp c R := hmem d (List.mem_cons_self)
    have hB : ∀ t ∈ B, t ∈ mpcpToPcp c R :=
      fun t ht => hmem t (List.mem_cons_of_mem _ ht)
    simp only [tau1_cons] at h
    cases hd_top : d.top with
    | nil =>
      rw [hd_top] at h
      simp only [List.nil_append] at h
      exact ih w hB h
    | cons e es =>
      rw [hd_top] at h
      simp only [List.cons_append] at h
      have he : e = ↟a := by injection h
      subst he
      exact not_sym_head_top c R a es d.bot
        (by cases d; simp_all)

/-- Concatenation of bottoms never starts with `⋕`. -/
theorem tau2_ne_hash_head (c : Tile α) (R : Stack α) (B : Stack (Ext α))
    (w : Word (Ext α))
    (hmem : ∀ t ∈ B, t ∈ mpcpToPcp c R) :
    tau2 B ≠ ⋕ :: w := by
  induction B generalizing w with
  | nil => simp
  | cons d B ih =>
    intro h
    have hd : d ∈ mpcpToPcp c R := hmem d (List.mem_cons_self)
    have hB : ∀ t ∈ B, t ∈ mpcpToPcp c R :=
      fun t ht => hmem t (List.mem_cons_of_mem _ ht)
    simp only [tau2_cons] at h
    cases hd_bot : d.bot with
    | nil =>
      rw [hd_bot] at h
      simp only [List.nil_append] at h
      exact ih w hB h
    | cons e es =>
      rw [hd_bot] at h
      simp only [List.cons_append] at h
      have he : e = ⋕ := by injection h
      subst he
      exact not_hash_head_bot c R d.top es
        (by cases d; simp_all)

/-- **Match start**: any non-empty matching solution to the reduced PCP
    instance must begin with the start tile.

    This is the key invariant for the backward direction. -/
theorem match_start (c : Tile α) (R : Stack α)
    (d : Tile (Ext α)) (B : Stack (Ext α))
    (hmem : ∀ t ∈ d :: B, t ∈ mpcpToPcp c R)
    (heq  : tau1 (d :: B) = tau2 (d :: B)) :
    d = tileStart c := by
  have hd : d ∈ mpcpToPcp c R := hmem d (List.mem_cons_self)
  have hB : ∀ t ∈ B, t ∈ mpcpToPcp c R :=
    fun t ht => hmem t (List.mem_cons_of_mem _ ht)
  rw [mem_mpcpToPcp_iff] at hd
  rcases hd with rfl | rfl | ⟨s, _, hne, rfl⟩
  -- start tile: done
  · rfl
  -- end tile: derive contradiction
  · simp only [tileEnd, tau1_cons, tau2_cons] at heq
    grind
  -- regular tile: derive contradiction via head-character analysis
  · simp only [tileReg, tau1_cons, tau2_cons] at heq
    cases hx : s.top with
    | nil =>
      cases hy : s.bot with
      | nil =>
        rcases hne with h | h
        · exact absurd hx h
        · exact absurd hy h
      | cons b ys =>
        rw [hx, hy] at heq
        simp only [hashL_nil, hashR_cons, List.nil_append, List.cons_append] at heq
        exact absurd heq (tau1_ne_sym_head c R B b (⋕ :: hashR ys ++ tau2 B) hB)
    | cons a xs =>
      cases hy : s.bot with
      | nil =>
        rw [hx, hy] at heq
        simp only [hashL_cons, hashR_nil, List.cons_append, List.nil_append] at heq
        exact absurd heq.symm
          (tau2_ne_hash_head c R B (↟a :: hashL xs ++ tau1 B) hB)
      | cons b ys =>
        rw [hx, hy] at heq
        simp only [hashL_cons, hashR_cons, List.cons_append] at heq
        grind

/-! ## Forward direction: MPCP solution → PCP solution -/

/-- The list of regular tiles obtained by interleaving every non-empty card
    of `A`. -/
private def regsOf (A : Stack α) : Stack (Ext α) :=
  A.filterMap fun t =>
    if t.top ≠ [] ∨ t.bot ≠ [] then some (tileReg t) else none

private theorem tau1_regsOf (A : Stack α) :
    tau1 (regsOf A) = hashL (tau1 A) := by
  induction A with
  | nil => rfl
  | cons s A ih =>
    show tau1 (List.filterMap _ (s :: A)) = hashL (tau1 (s :: A))
    rw [List.filterMap_cons, tau1_cons, hashL_append]
    by_cases h : s.top ≠ [] ∨ s.bot ≠ []
    · rw [if_pos h]
      change (tileReg s).top ++ tau1 (regsOf A) = _
      rw [ih]; simp [tileReg]
    · rw [if_neg h]
      change tau1 (regsOf A) = _
      push_neg at h
      rw [h.1, hashL_nil, List.nil_append, ih]

private theorem tau2_regsOf (A : Stack α) :
    tau2 (regsOf A) = hashR (tau2 A) := by
  induction A with
  | nil => rfl
  | cons s A ih =>
    show tau2 (List.filterMap _ (s :: A)) = hashR (tau2 (s :: A))
    rw [List.filterMap_cons, tau2_cons, hashR_append]
    by_cases h : s.top ≠ [] ∨ s.bot ≠ []
    · rw [if_pos h]
      change (tileReg s).bot ++ tau2 (regsOf A) = _
      rw [ih]; simp [tileReg]
    · rw [if_neg h]
      change tau2 (regsOf A) = _
      push_neg at h
      rw [h.2, hashR_nil, List.nil_append, ih]

private theorem mem_regsOf (A : Stack α) (t : Tile (Ext α))
    (ht : t ∈ regsOf A) :
    ∃ s ∈ A, (s.top ≠ [] ∨ s.bot ≠ []) ∧ t = tileReg s := by
  simp only [regsOf, List.mem_filterMap, Option.ite_none_right_eq_some,
             Option.some.injEq] at ht
  obtain ⟨s, hsmem, hne, hrfl⟩ := ht
  exact ⟨s, hsmem, hne, hrfl.symm⟩

/-- If `(c, R)` admits an MPCP solution, then `mpcpToPcp c R` admits a PCP
    solution. -/
theorem mpcp_to_pcp_solution (c : Tile α) (R : Stack α)
    (A : Stack α)
    (hA  : ∀ t ∈ A, t ∈ c :: R)
    (heq : c.top ++ tau1 A = c.bot ++ tau2 A) :
    ∃ B : Stack (Ext α),
      B ≠ [] ∧
      (∀ t ∈ B, t ∈ mpcpToPcp c R) ∧
      tau1 B = tau2 B := by
  refine ⟨tileStart c :: regsOf A ++ [tileEnd], ?_, ?_, ?_⟩
  · simp
  · intro t ht
    simp only [List.cons_append, List.mem_cons, List.mem_append,
               List.not_mem_nil, or_false] at ht
    rw [mem_mpcpToPcp_iff]
    rcases ht with rfl | hreg | rfl
    · exact Or.inl rfl
    · obtain ⟨s, hsmem, hne, rfl⟩ := mem_regsOf A t hreg
      exact Or.inr (Or.inr ⟨s, hA s hsmem, hne, rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · -- Compute `tau1` and `tau2` of the assembled solution and reduce.
    have h1 := tau1_regsOf A
    have h2 := tau2_regsOf A
    have h1_eval :
        tau1 (tileStart c :: regsOf A ++ [tileEnd]) =
          ＄ :: hashL (c.top ++ tau1 A) ++ [⋕, ＄] := by
      simp only [tau1_cons, tau1_append, tileStart, tileEnd, tau1_nil,
                 List.append_nil, h1]
      simp only [List.cons_append, ← hashL_append]
    have h2_eval :
        tau2 (tileStart c :: regsOf A ++ [tileEnd]) =
          ＄ :: ⋕ :: hashR (c.bot ++ tau2 A) ++ [＄] := by
      simp only [tau2_cons, tau2_append, tileStart, tileEnd, tau2_nil,
                 List.append_nil, h2]
      simp only [List.cons_append, ← hashR_append]
    rw [h1_eval, h2_eval, heq]
    have hclose : ∀ w : Word α, hashL w ++ [⋕, ＄] = ⋕ :: hashR w ++ [＄] := by
      intro w
      have : hashL w ++ [⋕, ＄] = (hashL w ++ [⋕]) ++ [＄] := by simp
      rw [this, hashL_snoc_eq]
    grind

/-! ## Backward direction: PCP solution → MPCP solution -/

/-- Two interleaved words separated by `＄` cannot match. -/
theorem hashL_append_dollar_ne (x y : Word α) (w₁ w₂ : Word (Ext α)) :
    hashL x ++ ＄ :: w₁ ≠ ⋕ :: hashR y ++ ＄ :: w₂ := by
  induction x generalizing y with
  | nil =>
    cases y <;> intro h <;> simp at h
  | cons a x ih =>
    cases y with
    | nil => intro h; simp at h
    | cons b y =>
      intro h
      simp at h
      exact ih y h.2

/-- `hashR` followed by `＄` is injective. -/
theorem hashR_append_dollar_inj (x y : Word α) (w₁ w₂ : Word (Ext α))
    (h : hashR x ++ ＄ :: w₁ = hashR y ++ ＄ :: w₂) : x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons b y => simp at h
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, ih y h2]

/-- Generalised backward direction: given a stack `B` whose tiles are drawn
    from the reduced PCP instance, and a "matching state" `(u, v)` capturing
    progress through the original cards, we can reconstruct an MPCP-style
    matching of the cards. -/
theorem pcp_to_mpcp_solution_gen (c : Tile α) (R : Stack α)
    (B : Stack (Ext α)) (u v : Word α)
    (hB  : ∀ t ∈ B, t ∈ mpcpToPcp c R)
    (hmatch : hashL u ++ tau1 B = ⋕ :: hashR v ++ tau2 B) :
    ∃ A : Stack α, (∀ t ∈ A, t ∈ c :: R) ∧
      u ++ tau1 A = v ++ tau2 A := by
  induction B generalizing u v with
  | nil =>
    simp only [tau1_nil, tau2_nil, List.append_nil] at hmatch
    exact absurd hmatch (hashL_ne_hash_hashR _ _)
  | cons d B ih =>
    have hd : d ∈ mpcpToPcp c R := hB d (List.mem_cons_self)
    have hB' : ∀ t ∈ B, t ∈ mpcpToPcp c R :=
      fun t ht => hB t (List.mem_cons_of_mem _ ht)
    rw [mem_mpcpToPcp_iff] at hd
    rcases hd with rfl | rfl | ⟨s, hsmem, _, rfl⟩
    · -- start tile encountered mid-stream — impossible
      simp only [tileStart, tau1_cons, tau2_cons] at hmatch
      exact absurd hmatch (hashL_append_dollar_ne u v _ _)
    · -- end tile: must close the match exactly
      simp only [tileEnd, tau1_cons, tau2_cons] at hmatch
      have h_lhs : hashL u ++ ([⋕, ＄] ++ tau1 B) = ⋕ :: hashR u ++ ＄ :: tau1 B := by
        have h1 : hashL u ++ ([⋕, ＄] ++ tau1 B) = (hashL u ++ [⋕]) ++ (＄ :: tau1 B) :=
          by grind
        rw [h1, hashL_snoc_eq]
      rw [h_lhs] at hmatch
      have hmatch_tail : hashR u ++ ＄ :: tau1 B = hashR v ++ ＄ :: tau2 B := by
        injection hmatch
      have huv := hashR_append_dollar_inj u v _ _ hmatch_tail
      subst huv
      exact ⟨[], by simp, by simp⟩
    · -- regular tile: extend the matching state and recurse
      simp only [tileReg, tau1_cons, tau2_cons] at hmatch
      have h_lhs : hashL u ++ (hashL s.top ++ tau1 B) =
          hashL (u ++ s.top) ++ tau1 B := by
        rw [← List.append_assoc, ← hashL_append]
      have h_rhs : ⋕ :: hashR v ++ (hashR s.bot ++ tau2 B) =
          ⋕ :: hashR (v ++ s.bot) ++ tau2 B := by
        simp [← List.append_assoc, ← hashR_append]
      rw [h_lhs, h_rhs] at hmatch
      obtain ⟨A, hA, heq⟩ := ih (u ++ s.top) (v ++ s.bot) hB' hmatch
      refine ⟨s :: A, ?_, ?_⟩
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hsmem
        · exact hA t ht
      · simp only [tau1_cons, tau2_cons]
        rw [← List.append_assoc u s.top, ← List.append_assoc v s.bot]
        exact heq

/-- If the reduced PCP instance has a solution, the original MPCP instance
    has a solution. -/
theorem pcp_to_mpcp_solution (c : Tile α) (R : Stack α)
    (B : Stack (Ext α))
    (hne  : B ≠ [])
    (hB   : ∀ t ∈ B, t ∈ mpcpToPcp c R)
    (heq  : tau1 B = tau2 B) :
    ∃ A : Stack α, (∀ t ∈ A, t ∈ c :: R) ∧
      c.top ++ tau1 A = c.bot ++ tau2 A := by
  -- B is non-empty and matches, so its head is the start tile.
  cases B with
  | nil => contradiction
  | cons d B' =>
    have hfirst : d = tileStart c := match_start c R d B' hB heq
    subst hfirst
    -- Strip the start tile and feed the residual into the generalised lemma.
    have hB' : ∀ t ∈ B', t ∈ mpcpToPcp c R :=
      fun t ht => hB t (List.mem_cons_of_mem _ ht)
    have htail : hashL c.top ++ tau1 B' = ⋕ :: hashR c.bot ++ tau2 B' := by
      have := heq
      simp only [tileStart, tau1_cons, tau2_cons] at this
      grind
    exact pcp_to_mpcp_solution_gen c R B' c.top c.bot hB' htail

/-! ## Main equivalence -/

/-- **MPCP ≤_m PCP**: the two problems are equivalent under `mpcpToPcp`. -/
theorem mpcp_iff_pcp (c : Tile α) (R : Stack α) :
    MHasSolution c R ↔ HasSolution (mpcpToPcp c R) := by
  constructor
  · rintro ⟨A, hA, heq⟩
    obtain ⟨B, hne, hB, heqB⟩ := mpcp_to_pcp_solution c R A hA heq
    exact ⟨B, hne, hB, heqB⟩
  · rintro ⟨B, hne, hB, heq⟩
    obtain ⟨A, hA, heqA⟩ := pcp_to_mpcp_solution c R B hne hB heq
    exact ⟨A, hA, heqA⟩

/-- The reduction packaged as the canonical statement. -/
theorem reduction (c : Tile α) (R : Stack α) :
    MHasSolution c R ↔ HasSolution (mpcpToPcp c R) :=
  mpcp_iff_pcp c R

end PCP
