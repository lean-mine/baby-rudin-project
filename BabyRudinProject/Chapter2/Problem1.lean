import Mathlib.Data.Set.Basic

/-!
desc: Prove that the empty set is a subset of every set.
difficulty: 0.5
author: Alexander Hicks
-/

theorem empty_subset_of_all {α : Type} (A : Set α) : ∅ ⊆ A := by
  -- Proving ∅ ⊆ A means proving ∀x, x ∈ ∅ → x ∈ A
  -- Introduce a generic  x and the hypothesis x ∈ ∅
  intro x h
  -- Our goal is now reduced to showing x ∈ A
  -- Contradiction: by definition of empty set, there cannot exist any x ∈ ∅
  -- We can prove x ∈ A from the contradiction by the principle of explosion
  contradiction
