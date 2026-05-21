/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import CFG.Basic
public import CFG.PcpReduction

@[expose] public section

/-!
# CFG-Intersection Emptiness — library root

This module re-exports the public CFG-intersection-emptiness API:

* `CFG.Basic`         — the decision predicates `IntersectionEmpty` and
  `IntersectionNonempty`.
* `CFG.PcpReduction`  — the reduction `PCP ≤_m CFG-Intersection-Nonempty`
  via the construction of two single-nonterminal grammars from a PCP
  instance.
-/
