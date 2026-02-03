import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.CompleteBooleanAlgebra

@[gcongr] theorem compl_congr {α} [HasCompl α] {a b : α} (h : a = b) : aᶜ = bᶜ :=
  congr_arg HasCompl.compl h

@[gcongr] theorem sup_congr {α} [Max α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⊔ b = c ⊔ d :=
  congr_arg₂ Max.max h₁ h₂

@[gcongr] theorem inf_congr {α} [Min α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⊓ b = c ⊓ d :=
  congr_arg₂ Min.min h₁ h₂

@[gcongr] theorem himp_congr {α} [HImp α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⇨ b = c ⇨ d :=
  congr_arg₂ HImp.himp h₁ h₂

attribute [gcongr] himp_le_himp

theorem compl_himp_eq {α} [BooleanAlgebra α] {a b : α} :
    aᶜ ⇨ b = a ⊔ b := by
  rw [himp_eq, compl_compl, sup_comm]

theorem compl_himp_eq' {α} [BooleanAlgebra α] {a b : α} :
    aᶜ ⇨ b = b ⊔ a := by
  rw [compl_himp_eq, sup_comm]

theorem compl_inf' {α} [BooleanAlgebra α] {a b : α} :
    (a ⊓ b)ᶜ = a ⇨ bᶜ := by
  rw [inf_comm]
  simp [himp_eq]

theorem le_of_inf_le {α} [SemilatticeInf α] {a : α} (b) {c} :
    a ≤ b → a ⊓ b ≤ c → a ≤ c := by
  intro h₁ h₂
  grw [← h₂, inf_eq_left.2 h₁]

theorem inf_compl_le_bot {α} [BooleanAlgebra α] {a b : α} :
    a ⊓ bᶜ ≤ ⊥ ↔ a ≤ b := by
  conv_rhs => rw [← compl_compl b, ← himp_bot, le_himp_iff]

theorem le_of_inf_le_of_compl_le {α} [BooleanAlgebra α] {a : α} (b) {c} :
    a ⊓ b ≤ c → a ⊓ bᶜ ≤ c → a ≤ c := by
  intro h₁ h₂
  grw [← inf_top_eq a, ← sup_compl_eq_top (x := b), inf_sup_left, h₁, h₂, sup_idem]

theorem iSup_himp_eq {α ι} [Order.Frame α] {f : ι → α} {a} :
    (⨆ x, f x) ⇨ a = ⨅ x, f x ⇨ a := by
  refine eq_of_forall_le_iff fun b => ?_
  simp [inf_iSup_eq]

theorem himp_iInf_eq {α ι} [Order.Frame α] {f : ι → α} {a} :
    a ⇨ (⨅ x, f x) = ⨅ x, a ⇨ f x := by
  refine eq_of_forall_le_iff fun b => ?_
  simp

lemma biSup_lt_eq_biSup_lt_biSup_le {α ι} [CompleteLattice α] [Preorder ι] {f : ι → α} {i} :
    ⨆ j < i, f j = ⨆ j < i, ⨆ k ≤ j, f k :=
  le_antisymm (iSup₂_le fun j hj => le_iSup₂_of_le j hj (le_biSup f (le_refl j)))
    (iSup₂_le fun _ hj => iSup₂_le fun _ hk => le_biSup f (hk.trans_lt hj))

theorem forall_lt_of_lt_iInf {α ι} [CompleteLattice α] {f : ι → α} {a} :
    a < ⨅ i, f i → ∀ i, a < f i := by
  rw [lt_iInf_iff]
  intro ⟨b, hb, h⟩ i
  exact hb.trans_le (h i)

theorem Set.Finite.biInf_iSup_eq {α ι} {κ : ι → Sort*} [Nonempty (∀ a, κ a)] [Order.Frame α] {s : Set ι}
    (hs : s.Finite) {f : ∀ a, κ a → α} :
    ⨅ a ∈ s, ⨆ b, f a b = ⨆ g : ∀ a, κ a, ⨅ a ∈ s, f a (g a) := by
  classical
  induction s, hs using Finite.induction_on with
  | empty => simp [iSup_const]
  | @insert a s ha _ ih =>
    simp_rw [iInf_insert, ih, iSup_inf_eq, inf_iSup_eq]
    refine le_antisymm (iSup_le fun b => iSup_le fun g => ?_) (iSup_le fun g => ?_)
    · refine le_iSup_of_le (Function.update g a b) (inf_le_inf ?_ (iInf₂_mono fun a' ha' => ?_))
      · simp
      · rw [Function.update_of_ne]
        rintro rfl
        exact ha ha'
    · exact le_iSup_of_le (g a) (le_iSup_of_le g le_rfl)

theorem iInf_iSup_eq_of_finite {α ι} {κ : ι → Sort*} [Order.Frame α] [Finite ι]
    {f : ∀ a, κ a → α} : ⨅ a, ⨆ b, f a b = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a) := by
  by_cases h : ∀ a, Nonempty (κ a)
  · simpa [← Equiv.plift.symm.iInf_comp, ← (Equiv.plift.piCongrLeft' _).symm.iSup_comp]
      using Set.Finite.biInf_iSup_eq (f := (f <| PLift.down ·)) Set.finite_univ
  · simp only [not_forall, not_nonempty_iff] at h
    haveI : IsEmpty (∀ a, κ a) := by simpa
    rcases h with ⟨a, h⟩
    grw [iSup_of_empty, eq_bot_iff, iInf_le _ a, iSup_of_empty]

theorem iSup_fin_succ {α n} {f : Fin (n + 1) → α} [CompleteLattice α] :
    ⨆ x, f x = f 0 ⊔ ⨆ x : Fin n, f x.succ :=
  le_antisymm (iSup_le (Fin.cases le_sup_left (fun i => le_sup_of_le_right <| le_iSup_of_le i le_rfl)))
    (sup_le (le_iSup f 0) (iSup_le fun i => le_iSup_of_le i.succ le_rfl))

theorem iInf_fin_succ {α n} {f : Fin (n + 1) → α} [CompleteLattice α] :
    ⨅ x, f x = f 0 ⊓ ⨅ x : Fin n, f x.succ :=
  le_antisymm (le_inf (iInf_le f 0) (le_iInf fun i => iInf_le_of_le i.succ le_rfl))
    (le_iInf (Fin.cases inf_le_left (fun i => inf_le_of_right_le <| iInf_le_of_le i le_rfl)))
