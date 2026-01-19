import Mathlib.Data.Set.Countable

class CountableChainCondition (α : Type*) [PartialOrder α] [OrderBot α] where
  ccc : ∀ (s : Set α), s.Pairwise Disjoint → s.Countable
