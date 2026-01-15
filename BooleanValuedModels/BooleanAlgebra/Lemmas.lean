import Mathlib.Order.CompleteBooleanAlgebra

@[gcongr] theorem sup_congr {α : Type*} [Max α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⊔ b = c ⊔ d :=
  congr_arg₂ Max.max h₁ h₂

@[gcongr] theorem inf_congr {α : Type*} [Min α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⊓ b = c ⊓ d :=
  congr_arg₂ Min.min h₁ h₂

@[gcongr] theorem himp_congr {α : Type*} [HImp α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⇨ b = c ⇨ d :=
  congr_arg₂ HImp.himp h₁ h₂

attribute [gcongr] himp_le_himp

theorem iSup_himp_eq {α ι : Type*} [CompleteBooleanAlgebra α] {f : ι → α} {a} :
    (⨆ x, f x) ⇨ a = ⨅ x, f x ⇨ a := by
  refine eq_of_forall_le_iff fun b => ?_
  simp [inf_iSup_eq]

theorem himp_iInf_eq {α ι : Type*} [CompleteBooleanAlgebra α] {f : ι → α} {a} :
    a ⇨ (⨅ x, f x) = ⨅ x, a ⇨ f x := by
  simp [himp_eq, iInf_sup_eq]

lemma biSup_lt_eq_biSup_lt_biSup_le {α ι} [CompleteLattice α] [Preorder ι] {f : ι → α} {i} :
    ⨆ j < i, f j = ⨆ j < i, ⨆ k ≤ j, f k := by
  apply le_antisymm
  · exact iSup₂_le fun j hj => le_iSup₂_of_le j hj (le_biSup f (le_refl j))
  · exact iSup₂_le fun j hj => iSup₂_le fun k hk => le_biSup f (hk.trans_lt hj)
