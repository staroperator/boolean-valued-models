import BooleanValuedModels.BooleanAlgebra.CountableChainCondition
import Mathlib.Topology.Bases
import Mathlib.Topology.Clopen

variable {X : Type*} [TopologicalSpace X]

private lemma IsOpen.inter_interior_closure_subset {s t : Set X} (hs : IsOpen s) :
    s ∩ interior (closure t) ⊆ interior (closure (s ∩ t)) := by
  grw [← hs.inter_closure, interior_inter, hs.interior_eq]

private lemma IsOpen.interior_closure_inter_subset {s t : Set X} (ht : IsOpen t) :
    interior (closure s) ∩ t ⊆ interior (closure (s ∩ t)) := by
  rw [Set.inter_comm (interior (closure s)), Set.inter_comm s t]
  exact ht.inter_interior_closure_subset

theorem IsOpen.interior_closure_inter {s t : Set X} (hs : IsOpen s) :
    interior (closure (s ∩ t)) = interior (closure s) ∩ interior (closure t) := by
  apply subset_antisymm
  · grw [closure_inter_subset, interior_inter]
  · grw [isOpen_interior.interior_closure_inter_subset, hs.inter_interior_closure_subset,
      interior_closure_idem]

theorem IsOpen.interior_closure_inter' {s t : Set X} (ht : IsOpen t) :
    interior (closure (s ∩ t)) = interior (closure s) ∩ interior (closure t) := by
  rw [Set.inter_comm s t, ht.interior_closure_inter, Set.inter_comm]

def IsRegularOpen (s : Set X) :=
  interior (closure s) = s

variable {s t : Set X}

theorem isRegularOpen_iff : IsRegularOpen s ↔ interior (closure s) = s := Iff.rfl

theorem isRegularOpen_of_isClopen (hs : IsClopen s) : IsRegularOpen s := by
  rw [isRegularOpen_iff, hs.isClosed.closure_eq, hs.isOpen.interior_eq]

theorem isRegularOpen_univ : IsRegularOpen (Set.univ : Set X) :=
  isRegularOpen_of_isClopen isClopen_univ

theorem isRegularOpen_empty : IsRegularOpen (∅ : Set X) :=
  isRegularOpen_of_isClopen isClopen_empty

theorem isRegularOpen_interior_closure : IsRegularOpen (interior (closure s)) := by
  rw [isRegularOpen_iff, interior_closure_idem]

theorem IsClosed.isRegularOpen_interior (hs : IsClosed s) : IsRegularOpen (interior s) := by
  rw [← hs.closure_eq]
  exact isRegularOpen_interior_closure

namespace IsRegularOpen

theorem interior_closure_eq (hs : IsRegularOpen s) : interior (closure s) = s := hs

theorem isOpen (hs : IsRegularOpen s) : IsOpen s := by
  rw [← hs.interior_closure_eq]
  exact isOpen_interior

theorem frontier_closure_eq (hs : IsRegularOpen s) : frontier (closure s) = frontier s := by
  apply frontier_closure_subset.antisymm
  conv_lhs => rw [← hs.interior_closure_eq]
  exact frontier_interior_subset

theorem inter (hs : IsRegularOpen s) (ht : IsRegularOpen t) : IsRegularOpen (s ∩ t) := by
  rw [isRegularOpen_iff, hs.isOpen.interior_closure_inter, hs.interior_closure_eq,
    ht.interior_closure_eq]

end IsRegularOpen

structure RegularOpenSet (X : Type*) [TopologicalSpace X] where
  carrier : Set X
  isRegularOpen' : IsRegularOpen carrier

namespace RegularOpenSet

instance : SetLike (RegularOpenSet X) X :=
  ⟨carrier, fun s t _ => by cases s; cases t; congr⟩

variable {s t : RegularOpenSet X}

theorem isRegularOpen : IsRegularOpen (s : Set X) :=
  s.isRegularOpen'

theorem isOpen : IsOpen (s : Set X) :=
  s.isRegularOpen.isOpen

instance : BooleanAlgebra (RegularOpenSet X) where
  top := ⟨Set.univ, isRegularOpen_univ⟩
  le_top _ := Set.subset_univ _
  bot := ⟨∅, isRegularOpen_empty⟩
  bot_le _ := Set.empty_subset _
  sup s t := ⟨interior (closure (s ∪ t)), isRegularOpen_interior_closure⟩
  le_sup_left s t := by
    change (s : Set X) ⊆ interior (closure (s ∪ t))
    conv_lhs => rw [← s.isRegularOpen.interior_closure_eq]
    gcongr
    exact Set.subset_union_left
  le_sup_right s t := by
    change (t : Set X) ⊆ interior (closure (s ∪ t))
    conv_lhs => rw [← t.isRegularOpen.interior_closure_eq]
    gcongr
    exact Set.subset_union_right
  sup_le s t u hs ht := by
    rw [← SetLike.coe_subset_coe] at hs ht
    change interior (closure (s ∪ t)) ⊆ (u : Set X)
    grw [hs, ht, Set.union_self, u.isRegularOpen.interior_closure_eq]
  inf s t := ⟨s ∩ t, s.isRegularOpen.inter t.isRegularOpen⟩
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  le_sup_inf s t u := by
    change interior (closure (s ∪ t)) ∩ interior (closure (s ∪ u))
      ⊆ interior (closure (s ∪ t ∩ (u : Set X)))
    rw [← (s.isOpen.union t.isOpen).interior_closure_inter]
    gcongr
    rw [Set.union_inter_distrib_left]
  compl s := ⟨interior sᶜ, s.isOpen.isClosed_compl.isRegularOpen_interior⟩
  inf_compl_le_bot s := by
    change (s : Set X) ∩ interior sᶜ ⊆ ∅
    grw [interior_subset, Set.inter_compl_self]
  top_le_sup_compl s := by
    change Set.univ ⊆ interior (closure ((s : Set X) ∪ interior sᶜ))
    rw [closure_union, interior_compl, closure_compl, s.isRegularOpen.interior_closure_eq]
    grw [← subset_closure]
    rw [Set.union_compl_self, interior_univ]

@[simp] theorem coe_top : ((⊤ : RegularOpenSet X) : Set X) = Set.univ :=
  rfl

@[simp] theorem coe_bot : ((⊥ : RegularOpenSet X) : Set X) = ∅ :=
  rfl

@[simp] theorem coe_sup :
    ((s ⊔ t : RegularOpenSet X) : Set X) = interior (closure ((s : Set X) ∪ t)) :=
  rfl

@[simp] theorem coe_inf : ((s ⊓ t : RegularOpenSet X) : Set X) = (s : Set X) ∩ t :=
  rfl

@[simp] theorem coe_compl : ((sᶜ : RegularOpenSet X) : Set X) = interior (s : Set X)ᶜ :=
  rfl

theorem disjoint_iff : Disjoint s t ↔ (s : Set X) ∩ t = ∅ := by
  simp [_root_.disjoint_iff, ← SetLike.coe_set_eq]

instance : CompleteBooleanAlgebra (RegularOpenSet X) where
  sSup S := ⟨interior (closure (⋃ s ∈ S, s)), isRegularOpen_interior_closure⟩
  le_sSup S s hs := by
    change (s : Set X) ⊆ interior (closure (⋃ s ∈ S, s))
    apply s.isOpen.subset_interior_closure.trans
    gcongr
    exact Set.subset_biUnion_of_mem hs
  sSup_le S s hs := by
    change interior (closure (⋃ s ∈ S, (s : Set X))) ⊆ s
    rw [← s.isRegularOpen.interior_closure_eq]
    gcongr
    exact Set.iUnion₂_subset hs
  sInf S := ⟨interior (closure (⋂ s ∈ S, s)), isRegularOpen_interior_closure⟩
  sInf_le S s hs := by
    change interior (closure (⋂ s ∈ S, (s : Set X))) ⊆ s
    rw [← s.isRegularOpen.interior_closure_eq]
    gcongr
    exact Set.biInter_subset_of_mem hs
  le_sInf S s hs := by
    change (s : Set X) ⊆ interior (closure (⋂ s ∈ S, s))
    apply s.isOpen.subset_interior_closure.trans
    gcongr
    exact Set.subset_iInter₂ hs

@[simp] theorem coe_sSup {S : Set (RegularOpenSet X)} :
    ((sSup S : RegularOpenSet X) : Set X) = interior (closure (⋃ s ∈ S, s)) :=
  rfl

@[simp] theorem coe_iSup {ι : Sort*} {s : ι → RegularOpenSet X} :
    ((⨆ i, s i : RegularOpenSet X) : Set X) = interior (closure (⋃ i, s i)) := by
  simp [← sSup_range]

@[simp] theorem coe_sInf {S : Set (RegularOpenSet X)} :
    ((sInf S : RegularOpenSet X) : Set X) = interior (closure (⋂ s ∈ S, s)) :=
  rfl

@[simp] theorem coe_iInf {ι : Sort*} {s : ι → RegularOpenSet X} :
    ((⨅ i, s i : RegularOpenSet X) : Set X) = interior (closure (⋂ i, s i)) := by
  simp [← sInf_range]

instance [Nonempty X] : Nontrivial (RegularOpenSet X) :=
  ⟨⊥, ⊤, SetLike.coe_ne_coe.1 Set.empty_ne_univ⟩

end RegularOpenSet

open TopologicalSpace

instance [TopologicalSpace X] [SeparableSpace X] :
    CountableChainCondition (RegularOpenSet X) where
  ccc S hS := by
    wlog h : ⊥ ∉ S generalizing S
    · rw [not_not] at h
      rw [← Set.union_diff_cancel (Set.singleton_subset_iff.2 h)]
      refine .union (Set.countable_singleton _) ?_
      exact this _ (hS.mono Set.diff_subset) (by simp)
    rcases exists_countable_dense X with ⟨s, hs, hs'⟩
    have : ∀ t : S, ∃ (a : s), a.1 ∈ t.1 := by
      intro ⟨t, ht⟩
      have ht' : t ≠ ⊥ := fun heq => h (by simpa [heq] using ht)
      rw [← SetLike.coe_ne_coe, RegularOpenSet.coe_bot, ← Set.nonempty_iff_ne_empty] at ht'
      rcases hs'.inter_open_nonempty t t.isOpen ht' with ⟨a, ha, ha'⟩
      exists ⟨a, ha'⟩
    choose f hf using this
    have hf' : f.Injective := by
      intro t₁ t₂ h
      by_contra h'
      have := hS t₁.2 t₂.2 (Subtype.coe_ne_coe.2 h')
      simp only [RegularOpenSet.disjoint_iff, Set.eq_empty_iff_forall_notMem,
        Set.mem_inter_iff, SetLike.mem_coe, not_and] at this
      apply this (f t₁) (hf t₁)
      rw [h]
      exact hf t₂
    rw [← Set.countable_coe_iff] at hs
    exact hf'.countable
