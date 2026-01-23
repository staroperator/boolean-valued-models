import BooleanValuedModels.BVSet.Defs
import Mathlib.SetTheory.ZFC.Basic

universe u v

variable {B : Type u} [CompleteBooleanAlgebra B] {u : BVSet.{u, v} B} {x y z : ZFSet.{v}}

namespace ZFSet

def toBVSet (x : ZFSet.{v}) : BVSet.{u, v} B :=
  ⟨Shrink x, fun y => ((equivShrink x).symm y).1.toBVSet, fun _ => ⊤⟩
termination_by x

theorem mem_toBVSet :
    u ∈ᴮ x.toBVSet = ⨆ y : x, u =ᴮ y.1.toBVSet := by
  rw [toBVSet]
  simp [BVSet.mem_def, ← (equivShrink x).symm.iSup_comp]

theorem toBVSet_subset :
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

theorem toBVSet_mem_toBVSet_of_mem (h : x ∈ y) :
    x.toBVSet ∈ᴮ y.toBVSet = (⊤ : B) := by
  convert (toBVSet_aux x).1 y
  simp [h]

theorem toBVSet_mem_toBVSet_of_notMem (h : x ∉ y) :
    x.toBVSet ∈ᴮ y.toBVSet = (⊥ : B) := by
  convert (toBVSet_aux x).1 y
  simp [h]

theorem toBVSet_eq_toBVSet_of_ne (h : x ≠ y) :
    x.toBVSet =ᴮ y.toBVSet = (⊥ : B) := by
  convert (toBVSet_aux x).2.2 y
  simp [h]

theorem toBVSet_injective [Nontrivial B] : Function.Injective (toBVSet (B := B)) := by
  classical
  intro x y h
  simpa [h] using (toBVSet_aux (B := B) x).2.2 y

theorem _root_.BVSet.IsExtentional.iInf_mem_toBVSet_himp {f : BVSet B → B}
    (hf : BVSet.IsExtentional f) : ⨅ y, y ∈ᴮ x.toBVSet ⇨ f y = ⨅ y : x, f y.1.toBVSet := by
  simp_rw [mem_toBVSet, iSup_himp_eq]
  rw [iInf_comm]
  congr! with ⟨y, hy⟩
  simp only
  rw [hf.iInf_eq_himp]

theorem _root_.BVSet.IsExtentional.iSup_mem_toBVSet_inf {f : BVSet B → B}
    (hf : BVSet.IsExtentional f) : ⨆ y, y ∈ᴮ x.toBVSet ⊓ f y = ⨆ y : x, f y.1.toBVSet := by
  simp_rw [mem_toBVSet, iSup_inf_eq]
  rw [iSup_comm]
  congr! with ⟨y, hy⟩
  simp only
  rw [hf.iSup_eq_inf]

theorem toBVSet_subset_toBVSet_of_subset (h : x ⊆ y) :
    x.toBVSet ⊆ᴮ y.toBVSet = (⊤ : B) := by
  rw [BVSet.subset_def', BVSet.IsExtentional.iInf_mem_toBVSet_himp (by fun_prop)]
  simp only [iInf_eq_top, Subtype.forall]
  intro z hz
  exact toBVSet_mem_toBVSet_of_mem (h hz)

theorem toBVSet_empty : (toBVSet ∅ : BVSet B) ≈ ∅ := by
  apply BVSet.ext
  simp [mem_toBVSet]

theorem toBVSet_insert : (insert x y).toBVSet ≈ insert (x.toBVSet : BVSet B) (y.toBVSet : BVSet B) := by
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

theorem toBVSet_singleton : (({x} : ZFSet).toBVSet : BVSet B) ≈ {(x.toBVSet : BVSet B)} := by
  change toBVSet (insert x ∅) ≈ insert (toBVSet x) ∅
  grw [toBVSet_insert, toBVSet_empty]

theorem toBVSet_sUnion : (⋃₀ x).toBVSet ≈ ⋃ᴮ (x.toBVSet : BVSet B) := by
  apply BVSet.ext
  intro u
  rw [mem_toBVSet]
  simp only [BVSet.mem_sUnion]
  apply le_antisymm
  · apply iSup_le
    intro ⟨z, hz⟩
    simp only [mem_sUnion] at hz
    rcases hz with ⟨y, hy, hz⟩
    apply le_iSup_of_le (toBVSet y)
    simp only [toBVSet_mem_toBVSet_of_mem hy, top_inf_eq]
    grw [← BVSet.mem_congr_left z.toBVSet, BVSet.eq_symm]
    simp [toBVSet_mem_toBVSet_of_mem hz]
  · simp only [iSup_le_iff]
    intro v
    rw [mem_toBVSet, iSup_inf_eq]
    apply iSup_le
    intro ⟨y, hy⟩
    simp only
    rw [inf_comm]
    apply BVSet.IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) v y.toBVSet
    rw [mem_toBVSet]
    apply iSup_le
    intro ⟨z, hz⟩
    apply le_iSup_of_le ⟨z, mem_sUnion_of_mem hz hy⟩
    simp

theorem toBVSet_union : (x ∪ y).toBVSet ≈ (x.toBVSet : BVSet B) ∪ y.toBVSet := by
  change (⋃₀ {x, y}).toBVSet ≈ ⋃ᴮ {x.toBVSet, y.toBVSet}
  grw [toBVSet_sUnion, toBVSet_insert, toBVSet_singleton]

end ZFSet
