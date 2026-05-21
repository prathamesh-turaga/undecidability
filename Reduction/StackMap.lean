/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Notation
public import PCP.Basic
public import PCP.MPCP

@[expose] public section

/-!
# Generic per-symbol encoding of PCP / MPCP instances

A common pattern across DiagonaLean's encoded reductions is: take a
PCP / MPCP instance over alphabet `α` and re-express it over alphabet
`β`, via an injective per-symbol function `σ : α → β`. This file
collects the bookkeeping:

* `mapTile σ`, `mapStack σ` — apply `σ` symbol-wise to a tile / stack.
* `tau1_mapStack`, `tau2_mapStack` — `tau` commutes with `mapStack`.
* `mapTile_injective`, `mapStack_injective` — injectivity lifts from `σ`.
* `hasSolution_mapStack_iff` — `HasSolution` is preserved iff.
* `mhasSolution_mapStack_iff` — `MHasSolution` is preserved iff.

Specialising at `σ = flattenExt` (for `MPCP α ≤ₘ PCP α'`) or
`σ = encodeAlpha` (for the `Halt ≤ₘ MPCP_LB` wrapping) avoids
duplicating the same bisimulation-style proof.
-/

namespace DiagonaLean.StackMap

open PCP

variable {α β : Type}

/-- Apply `σ` symbol-wise to each side of a tile. -/
def mapTile (σ : α → β) (t : Tile α) : Tile β where
  top := t.top.map σ
  bot := t.bot.map σ

@[simp] lemma mapTile_top (σ : α → β) (t : Tile α) :
    (mapTile σ t).top = t.top.map σ := rfl

@[simp] lemma mapTile_bot (σ : α → β) (t : Tile α) :
    (mapTile σ t).bot = t.bot.map σ := rfl

/-- Apply `mapTile σ` to each tile in a stack. -/
def mapStack (σ : α → β) (P : Stack α) : Stack β :=
  P.map (mapTile σ)

@[simp] lemma mapStack_nil (σ : α → β) : mapStack σ ([] : Stack α) = [] := rfl

@[simp] lemma mapStack_cons (σ : α → β) (t : Tile α) (ts : Stack α) :
    mapStack σ (t :: ts) = mapTile σ t :: mapStack σ ts := rfl

/-! ## Injectivity -/

lemma mapTile_injective {σ : α → β} (h : Function.Injective σ) :
    Function.Injective (mapTile σ) := by
  intro a b h_eq
  obtain ⟨at_top, at_bot⟩ := a
  obtain ⟨bt_top, bt_bot⟩ := b
  simp [mapTile] at h_eq
  obtain ⟨h_top, h_bot⟩ := h_eq
  rw [List.map_injective_iff.mpr h h_top,
      List.map_injective_iff.mpr h h_bot]

lemma mapStack_injective {σ : α → β} (h : Function.Injective σ) :
    Function.Injective (mapStack σ) := by
  intro P P' h_eq
  exact List.map_injective_iff.mpr (mapTile_injective h) h_eq

/-! ## `tau` commutativity -/

@[simp] lemma tau1_mapStack (σ : α → β) (P : Stack α) :
    tau1 (mapStack σ P) = (tau1 P).map σ := by
  induction P with
  | nil => rfl
  | cons t ts ih =>
    show tau1 (mapTile σ t :: mapStack σ ts) = _
    rw [tau1_cons, tau1_cons, List.map_append, mapTile_top, ih]

@[simp] lemma tau2_mapStack (σ : α → β) (P : Stack α) :
    tau2 (mapStack σ P) = (tau2 P).map σ := by
  induction P with
  | nil => rfl
  | cons t ts ih =>
    show tau2 (mapTile σ t :: mapStack σ ts) = _
    rw [tau2_cons, tau2_cons, List.map_append, mapTile_bot, ih]

/-! ## `HasSolution` preservation -/

private lemma hasSolution_mapStack_of_hasSolution
    {σ : α → β} (P : Stack α) (h : HasSolution P) :
    HasSolution (mapStack σ P) := by
  obtain ⟨A, h_ne, h_in, h_eq⟩ := h
  refine ⟨mapStack σ A, ?_, ?_, ?_⟩
  · intro h_empty
    apply h_ne
    have : mapStack σ A = [] := h_empty
    unfold mapStack at this
    exact List.map_eq_nil_iff.mp this
  · intro t ht
    rcases List.mem_map.mp ht with ⟨t', ht'_mem, ht'_eq⟩
    subst ht'_eq
    exact List.mem_map_of_mem (h_in t' ht'_mem)
  · rw [tau1_mapStack, tau2_mapStack, h_eq]

private lemma hasSolution_of_hasSolution_mapStack
    {σ : α → β} (h_inj : Function.Injective σ)
    {P : Stack α} (h : HasSolution (mapStack σ P)) :
    HasSolution P := by
  obtain ⟨flatA, h_ne, h_in, h_eq⟩ := h
  have h_pre : ∀ t ∈ flatA, ∃ t', t' ∈ P ∧ mapTile σ t' = t :=
    fun t ht => List.mem_map.mp (h_in t ht)
  let pick : (t : Tile β) → t ∈ flatA → Tile α :=
    fun t ht => Classical.choose (h_pre t ht)
  have h_pick_mem : ∀ t (ht : t ∈ flatA), pick t ht ∈ P :=
    fun t ht => (Classical.choose_spec (h_pre t ht)).1
  have h_pick_eq : ∀ t (ht : t ∈ flatA), mapTile σ (pick t ht) = t :=
    fun t ht => (Classical.choose_spec (h_pre t ht)).2
  let A : Stack α := flatA.attach.map (fun s => pick s.1 s.2)
  have h_flat : mapStack σ A = flatA := by
    have : mapStack σ A
        = flatA.attach.map (fun s => mapTile σ (pick s.1 s.2)) := by
      simp [mapStack, A, List.map_map, Function.comp]
    rw [this]
    have h_fn : (fun (s : {t // t ∈ flatA}) => mapTile σ (pick s.1 s.2)) =
        Subtype.val := by
      funext s
      exact h_pick_eq s.1 s.2
    rw [h_fn, List.attach_map_subtype_val]
  refine ⟨A, ?_, ?_, ?_⟩
  · intro h_e
    apply h_ne
    rw [← h_flat, h_e]
    rfl
  · intro t ht
    simp only [A, List.mem_map, List.mem_attach, true_and] at ht
    obtain ⟨⟨t', ht'_mem⟩, ht'_eq⟩ := ht
    rw [← ht'_eq]
    exact h_pick_mem t' ht'_mem
  · have h_tau : (tau1 A).map σ = (tau2 A).map σ := by
      rw [← tau1_mapStack, ← tau2_mapStack, h_flat]
      exact h_eq
    exact List.map_injective_iff.mpr h_inj h_tau

/-- **Generic `HasSolution` preservation**: for any injective `σ : α → β`,
`HasSolution (mapStack σ P) ↔ HasSolution P`. -/
theorem hasSolution_mapStack_iff
    {σ : α → β} (h_inj : Function.Injective σ) (P : Stack α) :
    HasSolution (mapStack σ P) ↔ HasSolution P :=
  ⟨hasSolution_of_hasSolution_mapStack h_inj,
   hasSolution_mapStack_of_hasSolution P⟩

/-! ## `MHasSolution` preservation -/

private lemma mhasSolution_mapStack_of_mhasSolution
    {σ : α → β} {c : Tile α} {P : Stack α} (h : MHasSolution c P) :
    MHasSolution (mapTile σ c) (mapStack σ P) := by
  obtain ⟨A, h_in, h_eq⟩ := h
  refine ⟨mapStack σ A, ?_, ?_⟩
  · intro t ht
    rcases List.mem_map.mp ht with ⟨t', ht'_mem, ht'_eq⟩
    subst ht'_eq
    simp only [List.mem_cons] at h_in ⊢
    rcases h_in t' ht'_mem with rfl | h_t'
    · left; rfl
    · right; exact List.mem_map_of_mem h_t'
  · rw [tau1_mapStack, tau2_mapStack, mapTile_top, mapTile_bot,
        ← List.map_append, ← List.map_append, h_eq]

private lemma mhasSolution_of_mhasSolution_mapStack
    {σ : α → β} (h_inj : Function.Injective σ)
    {c : Tile α} {P : Stack α}
    (h : MHasSolution (mapTile σ c) (mapStack σ P)) :
    MHasSolution c P := by
  obtain ⟨flatA, h_in, h_eq⟩ := h
  have h_pre : ∀ t ∈ flatA, ∃ t', t' ∈ c :: P ∧ mapTile σ t' = t := by
    intro t ht
    have h_t_in : t ∈ mapTile σ c :: mapStack σ P := h_in t ht
    rw [List.mem_cons] at h_t_in
    cases h_t_in with
    | inl h_eq_c =>
      exact ⟨c, List.mem_cons_self, h_eq_c.symm⟩
    | inr h_in_P =>
      rcases List.mem_map.mp h_in_P with ⟨t', ht'_mem, ht'_eq⟩
      exact ⟨t', List.mem_cons_of_mem _ ht'_mem, ht'_eq⟩
  let pick : (t : Tile β) → t ∈ flatA → Tile α :=
    fun t ht => Classical.choose (h_pre t ht)
  have h_pick_mem : ∀ t (ht : t ∈ flatA), pick t ht ∈ c :: P :=
    fun t ht => (Classical.choose_spec (h_pre t ht)).1
  have h_pick_eq : ∀ t (ht : t ∈ flatA), mapTile σ (pick t ht) = t :=
    fun t ht => (Classical.choose_spec (h_pre t ht)).2
  let A : Stack α := flatA.attach.map (fun s => pick s.1 s.2)
  have h_flat : mapStack σ A = flatA := by
    have : mapStack σ A
        = flatA.attach.map (fun s => mapTile σ (pick s.1 s.2)) := by
      simp [mapStack, A, List.map_map, Function.comp]
    rw [this]
    have h_fn : (fun (s : {t // t ∈ flatA}) => mapTile σ (pick s.1 s.2)) =
        Subtype.val := by
      funext s
      exact h_pick_eq s.1 s.2
    rw [h_fn, List.attach_map_subtype_val]
  refine ⟨A, ?_, ?_⟩
  · intro t ht
    simp only [A, List.mem_map, List.mem_attach, true_and] at ht
    obtain ⟨⟨t', ht'_mem⟩, ht'_eq⟩ := ht
    rw [← ht'_eq]
    exact h_pick_mem t' ht'_mem
  · have h_tau : (c.top ++ tau1 A).map σ = (c.bot ++ tau2 A).map σ := by
      simp only [List.map_append, ← tau1_mapStack, ← tau2_mapStack, h_flat]
      have h_ct : c.top.map σ = (mapTile σ c).top := rfl
      have h_cb : c.bot.map σ = (mapTile σ c).bot := rfl
      rw [h_ct, h_cb]
      exact h_eq
    exact List.map_injective_iff.mpr h_inj h_tau

/-- **Generic `MHasSolution` preservation**: for any injective `σ : α → β`,
`MHasSolution (mapTile σ c) (mapStack σ P) ↔ MHasSolution c P`. -/
theorem mhasSolution_mapStack_iff
    {σ : α → β} (h_inj : Function.Injective σ)
    (c : Tile α) (P : Stack α) :
    MHasSolution (mapTile σ c) (mapStack σ P) ↔ MHasSolution c P :=
  ⟨mhasSolution_of_mhasSolution_mapStack h_inj,
   mhasSolution_mapStack_of_mhasSolution⟩

end DiagonaLean.StackMap
