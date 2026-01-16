import BooleanValuedModels.BVSet.Defs
import Mathlib.SetTheory.ZFC.Basic

universe u v

variable {B : Type u} [CompleteBooleanAlgebra B]

namespace ZFSet

def toBVSet (x : ZFSet.{v}) : BVSet.{u, v} B :=
  ⟨Shrink x, fun y => ((equivShrink x).symm y).1.toBVSet, fun _ => ⊤⟩
termination_by x

theorem mem_toBVSet {x : ZFSet.{v}} {u : BVSet.{u, v} B} :
    u ∈ᴮ x.toBVSet = ⨆ y : x, u =ᴮ y.1.toBVSet := by
  rw [toBVSet]
  simp [BVSet.mem_def, ← (equivShrink x).symm.iSup_comp]

theorem toBVSet_subset {x : ZFSet.{v}} {u : BVSet.{u, v} B} :
    x.toBVSet ⊆ᴮ u = ⨅ y : x, y.1.toBVSet ∈ᴮ u:= by
  rw [toBVSet]
  simp [BVSet.subset_def, ← (equivShrink x).symm.iInf_comp]

open Classical in
private theorem toBVSet_aux (x : ZFSet.{v}) :
    (∀ y : ZFSet, x.toBVSet ∈ᴮ y.toBVSet = if x ∈ y then (⊤ : B) else ⊥)
    ∧ (∀ y, y.toBVSet ∈ᴮ x.toBVSet = if y ∈ x then (⊤ : B) else ⊥)
    ∧ (∀ y, x.toBVSet =ᴮ y.toBVSet = if x = y then (⊤ : B) else ⊥) := by
  induction x using inductionOn with | _ x ih
  have h₁ : ∀ y, y.toBVSet ∈ᴮ x.toBVSet = if y ∈ x then (⊤ : B) else ⊥ := by
    intro y
    rw [mem_toBVSet]
    simp_rw [fun z : x => BVSet.eq_symm (B := B) y.toBVSet z.1.toBVSet, fun z : x => ih z z.2]
    by_cases h : y ∈ x <;> simp only [h, ↓reduceIte]
    · rw [eq_top_iff]
      apply le_iSup_of_le ⟨y, h⟩
      simp
    · aesop
  have h₂ : ∀ y, x.toBVSet =ᴮ y.toBVSet = if x = y then (⊤ : B) else ⊥ := by
    intro y
    by_cases h : x = y <;> simp only [h, ↓reduceIte, BVSet.eq_refl]
    simp only [ZFSet.ext_iff, iff_def, not_forall, not_and_iff_not_or_not, exists_prop] at h
    rcases h with ⟨z, ⟨hz, hz'⟩ | ⟨hz, hz'⟩⟩ <;> rw [BVSet.eq_def, eq_bot_iff]
    · apply inf_le_of_left_le
      rw [toBVSet_subset]
      apply iInf_le_of_le ⟨z, hz⟩
      simp [ih z hz, hz']
    · apply inf_le_of_right_le
      rw [toBVSet_subset]
      apply iInf_le_of_le ⟨z, hz⟩
      simp [h₁, hz']
  have h₃ : ∀ y : ZFSet, x.toBVSet ∈ᴮ y.toBVSet = if x ∈ y then (⊤ : B) else ⊥ := by
    intro y
    simp only [mem_toBVSet, h₂]
    by_cases h : x ∈ y <;> simp only [h, ↓reduceIte]
    · rw [eq_top_iff]
      apply le_iSup_of_le ⟨x, h⟩
      simp
    · aesop
  exact ⟨h₃, h₁, h₂⟩

theorem toBVSet_mem_toBVSet {x y : ZFSet.{v}} [Decidable (x ∈ y)] :
    x.toBVSet ∈ᴮ y.toBVSet = if x ∈ y then (⊤ : B) else ⊥ := by
  convert (toBVSet_aux x).1 y

theorem toBVSet_mem_toBVSet_of_mem {x y : ZFSet.{v}} (h : x ∈ y) :
    x.toBVSet ∈ᴮ y.toBVSet = (⊤ : B) := by
  classical
  simp [toBVSet_mem_toBVSet, h]

theorem toBVSet_eq_toBVSet {x y : ZFSet.{v}} [Decidable (x = y)] :
    x.toBVSet =ᴮ y.toBVSet = if x = y then (⊤ : B) else ⊥ := by
  convert (toBVSet_aux x).2.2 y

theorem toBVSet_eq_toBVSet_of_ne {x y : ZFSet.{v}} (h : x ≠ y) :
    x.toBVSet =ᴮ y.toBVSet = (⊥ : B) := by
  classical
  simp [toBVSet_eq_toBVSet, h]

theorem toBVSet_injective [Nontrivial B] : Function.Injective (toBVSet (B := B)) := by
  classical
  intro x y h
  simpa [h, BVSet.eq_refl] using toBVSet_eq_toBVSet (B := B) (x := x) (y := y)

theorem _root_.BVSet.IsExtentional.iInf_mem_toBVSet_himp {x : ZFSet.{v}} {f : BVSet B → B}
    (hf : BVSet.IsExtentional f) : ⨅ y, y ∈ᴮ x.toBVSet ⇨ f y = ⨅ y : x, f y.1.toBVSet := by
  simp_rw [mem_toBVSet, iSup_himp_eq]
  rw [iInf_comm]
  congr! with ⟨y, hy⟩
  simp only
  rw [hf.iInf_eq_himp]

theorem _root_.BVSet.IsExtentional.iSup_mem_toBVSet_inf {x : ZFSet.{v}} {f : BVSet B → B}
    (hf : BVSet.IsExtentional f) : ⨆ y, y ∈ᴮ x.toBVSet ⊓ f y = ⨆ y : x, f y.1.toBVSet := by
  simp_rw [mem_toBVSet, iSup_inf_eq]
  rw [iSup_comm]
  congr! with ⟨y, hy⟩
  simp only
  rw [hf.iSup_eq_inf]

theorem toBVSet_subset_toBVSet_of_subset {x y : ZFSet.{v}} (h : x ⊆ y) :
    x.toBVSet ⊆ᴮ y.toBVSet = (⊤ : B) := by
  rw [BVSet.subset_def', BVSet.IsExtentional.iInf_mem_toBVSet_himp (by fun_prop)]
  simp only [iInf_eq_top, Subtype.forall]
  intro z hz
  exact toBVSet_mem_toBVSet_of_mem (h hz)

theorem toBVSet_empty : toBVSet (B := B) ∅ ≈ ∅ := by
  apply BVSet.ext
  simp [mem_toBVSet]

theorem toBVSet_insert {x y} : toBVSet (B := B) (insert x y) ≈ insert (toBVSet x) (toBVSet y) := by
  apply BVSet.ext
  simp only [mem_toBVSet, BVSet.mem_insert]
  intro z
  apply le_antisymm
  · simp only [iSup_le_iff, Subtype.forall, mem_insert_iff, forall_eq_or_imp, le_sup_left,
    true_and]
    intro a ha
    apply le_sup_of_le_right
    apply le_iSup_of_le ⟨a, ha⟩
    simp
  · simp only [sup_le_iff, iSup_le_iff, Subtype.forall]
    constructor
    · apply le_iSup_of_le ⟨x, by simp⟩
      simp
    · intro a ha
      apply le_iSup_of_le ⟨a, by simp [ha]⟩
      simp

end ZFSet
