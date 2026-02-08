module

public import Mathlib.Data.Set.Countable

@[expose] public section

class CountableChainCondition (α : Type*) [PartialOrder α] [OrderBot α] where
  ccc : ∀ (s : Set α), s.Pairwise Disjoint → s.Countable

theorem CountableChainCondition.mk' {α : Type*} [PartialOrder α] [OrderBot α]
    (ccc : ∀ (s : Set α), ⊥ ∉ s → s.Pairwise Disjoint → s.Countable) : CountableChainCondition α :=
  { ccc s hs := .of_diff (ccc _ (by simp) (hs.mono (by simp))) (Set.countable_singleton ⊥) }
