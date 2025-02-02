import Mathlib.Data.Real.Cardinality
import Mathlib.Algebra.AlgebraicCard

/-!
desc: Prove that there exist real numbers which are not algebraic.
difficulty: 1
author: Alexander Hicks
-/

/-- There exists ∃ x : ℝ such that x is not algebraic  -/
theorem exists_reals_not_algebraic : ∃ x : ℝ, ¬IsAlgebraic ℚ x := by
  -- We can prove this by contradiction
  by_contra h
  -- Assume all reals are algebraic
  have reals_all_algebraic : ∀ x : ℝ, IsAlgebraic ℚ x := by
    -- Introduce a generic x ∈ ℝ
    intro x
    -- If our contradiction assumption is true, then any such x is algebraic
    by_contra h'
    exact h ⟨x, h'⟩

  -- Now, define the set of all real algebraic numbers
  let A : Set ℝ := {x : ℝ | IsAlgebraic ℚ x}
  -- Show that ℝ ⊆ A
  have subset_reals : Set.univ ⊆ A := by
    -- Introduce a generic x ∈ ℝ and the (trivial) hypothesis x ∈ Set.univ
    intro x h
    -- Use the fact that we've shown above that any x ∈ ℝ is algebraic
    exact reals_all_algebraic x

  -- We will reach our contradiction by using the fact that
  -- The reals are uncountable
  have reals_uncountable : ¬Countable (Set.univ : Set ℝ) := by
    exact Cardinal.not_countable_real
  -- The algebraic numbers are countable
  have algebraic_countable : Countable A := by
    apply Algebraic.countable
  -- A subset of a countable set is countable
  have univ_countable : Countable (Set.univ : Set ℝ) := by
    exact Set.Countable.mono subset_reals algebraic_countable
  -- This would imply that the reals must be countable
  -- We have reached a contradiction
  exact reals_uncountable univ_countable
