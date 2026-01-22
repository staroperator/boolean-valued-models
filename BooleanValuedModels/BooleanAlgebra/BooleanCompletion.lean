import BooleanValuedModels.BooleanAlgebra.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic

class BooleanCompletion (α : Type*) [Preorder α] (β : Type*) [LE β] [OrderBot β] where
  embed : α ↪o β
  embed_ne_bot : ∀ p, embed p ≠ ⊥
  exists_embed_le : ∀ a ≠ ⊥, ∃ p, embed p ≤ a

variable {α} [Preorder α] {β} [CompleteBooleanAlgebra β] [BooleanCompletion α β]

open BooleanCompletion

def Forces (p : α) (a : β) :=
  embed p ≤ a

infix:50 " ⊩ " => Forces

variable {p q : α} {a b c : β}

theorem Forces.le : p ⊩ a → q ≤ p → q ⊩ a := by
  rw [← (embed (α := α) (β := β)).le_iff_le]
  exact le_trans'

@[simp]
theorem forces_top : p ⊩ (⊤ : β) := by
  simp [Forces]

@[simp]
theorem forces_bot : ¬ p ⊩ (⊥ : β) := by
  simpa [Forces] using embed_ne_bot p

@[simp]
theorem forces_compl : p ⊩ aᶜ ↔ ¬ ∃ q ≤ p, q ⊩ a := by
  simp only [Forces, not_exists, not_and]
  constructor
  · intro h q hq hq'
    apply embed_ne_bot (β := β) q
    simpa using le_inf ((embed.le_iff_le.2 hq).trans h) hq'
  · intro h
    by_contra hp
    rw [← inf_compl_le_bot, compl_compl, le_bot_iff] at hp
    rcases exists_embed_le (α := α) _ hp with ⟨q, hq⟩
    rw [le_inf_iff, embed.le_iff_le] at hq
    exact h _ hq.1 hq.2

@[simp]
theorem forces_inf : p ⊩ a ⊓ b ↔ p ⊩ a ∧ p ⊩ b := by
  simp [Forces]

@[simp]
theorem forces_sup : p ⊩ a ⊔ b ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩ a ∨ r ⊩ b := by
  rw [← compl_compl (a ⊔ b)]
  grind [compl_sup, forces_compl, forces_inf]

@[simp]
theorem forces_himp : p ⊩ a ⇨ b ↔ ∀ q ≤ p, q ⊩ a → ∃ r ≤ q, r ⊩ b := by
  rw [himp_eq]
  grind [compl_compl, forces_compl, forces_sup]

theorem forces_iInf {ι} {f : ι → β} : p ⊩ ⨅ x, f x ↔ ∀ x, p ⊩ f x := by
  simp [Forces]

theorem forces_iSup {ι} {f : ι → β} : p ⊩ ⨆ x, f x ↔ ∀ q ≤ p, ∃ r ≤ q, ∃ x, r ⊩ f x := by
  rw [← compl_compl (⨆ x, f x), compl_iSup]
  simp only [forces_compl, forces_iInf]
  grind

theorem eq_bot_iff_forall_not_forces : a = ⊥ ↔ ∀ p : α, ¬ p ⊩ a := by
  constructor
  · simp +contextual
  · intro h
    by_contra ha
    rcases exists_embed_le (α := α) a ha with ⟨p, hp⟩
    exact h p hp

theorem eq_top_iff_forall_forces : a = ⊤ ↔ ∀ p : α, p ⊩ a := by
  constructor
  · simp +contextual
  · intro h
    by_contra ha
    rw [← compl_eq_bot] at ha
    rcases exists_embed_le (α := α) _ ha with ⟨p, hp⟩
    apply embed_ne_bot (β := β) p
    simpa using le_inf (h p) hp

theorem exists_forces_or_forces_compl (p : α) : ∃ q ≤ p, q ⊩ a ∨ q ⊩ aᶜ := by
  by_cases hp : p ⊩ a
  · exact ⟨p, le_rfl, Or.inl hp⟩
  · rw [Forces, ← inf_compl_le_bot, le_bot_iff] at hp
    rcases exists_embed_le (α := α) _ hp with ⟨q, hq⟩
    rw [le_inf_iff, embed.le_iff_le] at hq
    exact ⟨q, hq.1, Or.inr hq.2⟩

theorem Forces.not_forces_compl : p ⊩ a → ¬ p ⊩ aᶜ := by
  intro hp
  simp only [forces_compl, not_not]
  exact ⟨p, le_rfl, hp⟩
