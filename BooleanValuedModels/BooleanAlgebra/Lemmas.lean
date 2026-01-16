import Mathlib.Order.CompleteBooleanAlgebra

@[gcongr] theorem sup_congr {α : Type*} [Max α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⊔ b = c ⊔ d :=
  congr_arg₂ Max.max h₁ h₂

@[gcongr] theorem inf_congr {α : Type*} [Min α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⊓ b = c ⊓ d :=
  congr_arg₂ Min.min h₁ h₂

@[gcongr] theorem himp_congr {α : Type*} [HImp α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⇨ b = c ⇨ d :=
  congr_arg₂ HImp.himp h₁ h₂

attribute [gcongr] himp_le_himp

theorem compl_himp_eq {α : Type*} [BooleanAlgebra α] {a b : α} :
    aᶜ ⇨ b = a ⊔ b := by
  rw [himp_eq, compl_compl, sup_comm]

theorem compl_himp_eq' {α : Type*} [BooleanAlgebra α] {a b : α} :
    aᶜ ⇨ b = b ⊔ a := by
  rw [compl_himp_eq, sup_comm]

theorem compl_inf' {α : Type*} [BooleanAlgebra α] {a b : α} :
    (a ⊓ b)ᶜ = a ⇨ bᶜ := by
  rw [inf_comm]
  simp [himp_eq]

theorem le_of_inf_le {α : Type*} [BooleanAlgebra α] {a b c : α} :
    a ≤ b → a ⊓ b ≤ c → a ≤ c := by
  intro h₁ h₂
  grw [← h₂, inf_eq_left.2 h₁]

theorem inf_compl_le_bot {α : Type*} [BooleanAlgebra α] {a b : α} :
    a ⊓ bᶜ ≤ ⊥ ↔ a ≤ b := by
  conv_rhs => rw [← compl_compl b, ← himp_bot, le_himp_iff]

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
