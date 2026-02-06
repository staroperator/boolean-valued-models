import BooleanValuedModels.DeltaSystemLemma
import BooleanValuedModels.BooleanAlgebra.CountableChainCondition
import Mathlib.Topology.Bases
import Mathlib.Topology.Clopen

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

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

theorem Homeomorph.isRegularOpen_image (f : X ≃ₜ Y) : IsRegularOpen (f '' s) ↔ IsRegularOpen s := by
  rw [isRegularOpen_iff, ← f.image_closure, ← f.image_interior, ← f.coe_toEquiv,
    Equiv.image_eq_iff_eq, isRegularOpen_iff]

theorem Homeomorph.isRegularOpen_preimage (f : X ≃ₜ Y) {s} :
    IsRegularOpen (f ⁻¹' s) ↔ IsRegularOpen s := by
  rw [← f.isRegularOpen_image, f.image_preimage]

structure RegularOpenSet (X : Type*) [TopologicalSpace X] where
  carrier : Set X
  isRegularOpen' : IsRegularOpen carrier

namespace RegularOpenSet

instance : SetLike (RegularOpenSet X) X :=
  ⟨carrier, fun s t _ => by cases s; cases t; congr⟩

@[simp] theorem coe_mk {s : Set X} {hs : IsRegularOpen s} : (⟨s, hs⟩ : RegularOpenSet X) = s := rfl

instance : PartialOrder (RegularOpenSet X) := .ofSetLike _ _

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

@[simps]
def Homeomorph.regularOpenSetCongr (f : X ≃ₜ Y) : RegularOpenSet X ≃o RegularOpenSet Y where
  toFun s := ⟨f '' s, f.isRegularOpen_image.2 s.2⟩
  invFun s := ⟨f ⁻¹' s, f.isRegularOpen_preimage.2 s.2⟩
  left_inv s := by simp [← SetLike.coe_set_eq]
  right_inv s := by simp [← SetLike.coe_set_eq]
  map_rel_iff' := by simp [← SetLike.coe_subset_coe]

open TopologicalSpace

instance [TopologicalSpace X] [SeparableSpace X] : CountableChainCondition (RegularOpenSet X) :=
  .mk' fun S h hS => by
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

namespace PiDiscrete

variable {α : Type*} {β : α → Type*}

@[grind]
def basicOpen (I : Finset α) (f : ∀ i, β i) : Set (∀ i, β i) :=
  Set.pi I fun i => {f i}

@[simp]
theorem mem_basicOpen {I} {f g : ∀ i, β i} : g ∈ basicOpen I f ↔ ∀ i ∈ I, f i = g i := by
  grind

theorem mem_basicOpen_self {I} {f : ∀ i, β i} : f ∈ basicOpen I f := by
  grind

variable [∀ i, TopologicalSpace (β i)] [∀ i, DiscreteTopology (β i)] {I : Finset α} {f g : ∀ i, β i}

theorem isOpen_basicOpen : IsOpen (basicOpen I f) := by
  rw [isOpen_pi_iff]
  exact fun g hg => ⟨_, _, by grind [isOpen_discrete], subset_rfl⟩

theorem isClosed_basicOpen : IsClosed (basicOpen I f) := by
  rw [← isOpen_compl_iff, isOpen_pi_iff]
  refine fun g hg => ?_
  simp only [Set.mem_compl_iff, mem_basicOpen, not_forall] at hg
  rcases hg with ⟨i, hi, hfi⟩
  exact ⟨I, fun i => {g i}, by simp, by grind⟩

theorem isClopen_basicOpen : IsClopen (basicOpen I f) :=
  ⟨isClosed_basicOpen, isOpen_basicOpen⟩

theorem isRegularOpen_basicOpen : IsRegularOpen (basicOpen I f) :=
  isRegularOpen_of_isClopen isClopen_basicOpen

theorem isTopologicalBasis_basicOpen :
    IsTopologicalBasis {basicOpen I f | (I : Finset α) (f : ∀ i, β i)} := by
  classical
  by_cases h : IsEmpty (∀ i, β i)
  · simpa using h
  simp only [isEmpty_pi, not_exists, not_isEmpty_iff] at h
  convert isTopologicalBasis_pi fun i => isTopologicalBasis_singletons (β i) with s
  constructor
  · intro ⟨I, f, h⟩
    exact ⟨fun i => {f i}, I, by grind⟩
  · intro ⟨s, I, h₁, h₂⟩
    choose! f hf using h₁
    exact ⟨I, f, by grind⟩

theorem exists_basicOpen_subset {s : Set (∀ i, β i)} (hs : s.Nonempty) (hs' : IsOpen s) :
    ∃ I f, basicOpen I f ⊆ s := by
  rcases isTopologicalBasis_basicOpen.exists_nonempty_subset hs hs' with ⟨_, ⟨I, f, rfl⟩, -, h⟩
  exact ⟨I, f, h⟩

instance [∀ a, Countable (β a)] : CountableChainCondition (RegularOpenSet (∀ a, β a)) :=
  .mk' fun S h hS => by
    classical
    by_contra hS'
    rw [← Set.countable_coe_iff, not_countable_iff] at hS'
    have : ∀ s : S, (s.1 : Set (∀ i, β i)).Nonempty := by
      intro ⟨s, hs⟩
      simp_rw [Set.nonempty_iff_ne_empty, ← RegularOpenSet.coe_bot, SetLike.coe_ne_coe]
      rintro rfl
      contradiction
    choose I f hI using fun s : S => exists_basicOpen_subset (this s) s.1.isOpen
    rcases Uncountable.exists_uncountable_pairwise_inter_eq I with ⟨T, J, hT, hT'⟩
    apply not_uncountable (α := ∀ j : J, β j.1)
    rw [← Set.uncountable_univ_iff]
    refine .mono (Set.subset_univ ((fun s (j : J) => f s j.1) '' T))
      (hT.image fun s₁ hs₁ s₂ hs₂ h => ?_)
    by_contra! h'
    refine Set.eq_empty_iff_forall_notMem.1
        (RegularOpenSet.disjoint_iff.1 <| hS s₁.2 s₂.2 (Subtype.coe_ne_coe.2 h'))
        (fun i => if i ∈ I s₁ then f s₁ i else f s₂ i) ⟨?_, ?_⟩
        <;> apply hI <;> simp only [mem_basicOpen, left_eq_ite_iff] <;> intro j hj
    · simp [hj]
    · by_cases hj' : j ∈ I s₁
      · simp only [hj', ↓reduceIte]
        refine (congr_fun h ⟨j, ?_⟩).symm
        rw [← hT' hs₁ hs₂ h']
        simp [*]
      · simp [hj']

end PiDiscrete
