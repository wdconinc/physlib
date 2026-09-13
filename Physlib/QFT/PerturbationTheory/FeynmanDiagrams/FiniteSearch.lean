/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Data.List.Basic

/-!
# Finite search helpers

This module provides small reusable list-search utilities for finite graph
and topology enumeration workflows.
-/

@[expose] public section

noncomputable section

namespace Physlib
namespace QFT
namespace PerturbationTheory
namespace FeynmanDiagrams

/-- Enumerate all lists of a fixed length over a finite alphabet. -/
def allListsOfLength : Nat → List α → List (List α)
  | 0, _ => [[]]
  | Nat.succ n, alphabet =>
      let tails := allListsOfLength n alphabet
      let rec go : List (List α) → List (List α)
        | [] => []
        | tail :: rest =>
            (alphabet.map fun head => head :: tail) ++ go rest
      go tails

/-- Return the first element of a list that satisfies a predicate. -/
def firstMatching : List α → (α → Bool) → Option α
  | [], _ => none
  | x :: xs, p =>
      if p x then
        some x
      else
        firstMatching xs p

end FeynmanDiagrams
end PerturbationTheory
end QFT
end Physlib
