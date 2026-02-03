import BooleanValuedModels.BooleanAlgebra.BooleanCompletion
import BooleanValuedModels.BooleanAlgebra.RegularOpen
import BooleanValuedModels.DeltaSystemLemma
import Mathlib.Data.Finmap

noncomputable def Nontrivial.fst (α) [Nontrivial α] : α :=
  Classical.choose exists_pair_ne

noncomputable def Nontrivial.snd (α) [Nontrivial α] : α :=
  Classical.choose (Classical.choose_spec exists_pair_ne)

theorem Nontrivial.fst_ne_snd {α} [Nontrivial α] : fst α ≠ snd α :=
  Classical.choose_spec (Classical.choose_spec exists_pair_ne)

variable {α : Type*} {β : α → Type*} {f g : Finmap β}

lemma Multiset.mem_keys {s : Multiset (Sigma β)} {a} : a ∈ s.keys ↔ ∃ b, ⟨a, b⟩ ∈ s := by
  simp [keys]

lemma Multiset.fst_mem_keys {s : Multiset (Sigma β)} {a} (ha : a ∈ s) : a.fst ∈ s.keys := by
  grind [mem_keys]

namespace Finmap

def extend [DecidableEq α] (f : Finmap β) (g : ∀ a, β a) : ∀ a, β a := fun a =>
  match f.lookup a with
  | some b => b
  | none => g a

theorem extend_apply_of_mem_entries [DecidableEq α] {g a b} (h : ⟨a, b⟩ ∈ f.entries) :
    extend f g a = b := by
  simp [extend, lookup_eq_some_iff.2 h]

theorem extend_apply_of_notMem [DecidableEq α] {g a} (h : a ∉ f) : extend f g a = g a := by
  simp [extend, lookup_eq_none.2 h]

def restrict (f : ∀ a, β a) (s : Finset α) : Finmap β where
  entries := (s.map ⟨fun a => ⟨a, f a⟩, fun _ _ _ => by grind⟩).val
  nodupKeys := by simp [← Multiset.nodup_keys, Multiset.keys, s.nodup]

theorem mem_restrict_entries {a : Sigma β} {f s} :
    a ∈ (restrict f s).entries ↔ a.fst ∈ s ∧ f a.fst = a.snd := by
  simp only [restrict, Finset.map_val, Function.Embedding.coeFn_mk, Multiset.mem_map]
  grind

theorem mem_restrict {f : ∀ a, β a} {a s} : a ∈ (restrict f s) ↔ a ∈ s := by
  simp [mem_def, Multiset.mem_keys, mem_restrict_entries]

instance : PartialOrder (Finmap β) where
  le f g := g.entries ⊆ f.entries
  le_refl _ := Multiset.Subset.refl _
  le_antisymm f g h₁ h₂ := by
    rw [Finmap.ext_iff, f.nodup_entries.ext g.nodup_entries]
    exact fun a => ⟨@h₂ a, @h₁ a⟩
  le_trans _ _ _ h₁ h₂ := Multiset.Subset.trans h₂ h₁

theorem le_def : f ≤ g ↔ g.entries ⊆ f.entries := Iff.rfl

theorem insert_le_of_notMem [DecidableEq α] {a b} (h : a ∉ f) : f.insert a b ≤ f := by
  rw [le_def, entries_insert_of_notMem h]
  apply Multiset.subset_cons

def embedPi (f : Finmap β) : Set (∀ a, β a) :=
  {g | ∀ a ∈ f.entries, g a.1 = a.2}

theorem extend_mem_embedPi [DecidableEq α] {g : ∀ a, β a} : extend f g ∈ embedPi f := by
  classical
  intro a ha
  simp [extend_apply_of_mem_entries ha]

theorem embedPi_subset_embedPi [∀ a, Nontrivial (β a)] :
    embedPi f ⊆ embedPi g ↔ f ≤ g := by
  classical
  constructor
  · intro h a ha
    by_cases hf : a.fst ∈ f
    · simp only [mem_iff, lookup_eq_some_iff] at hf
      rcases hf with ⟨b, hb⟩
      have := @h (f.extend fun _ => Nontrivial.fst _) extend_mem_embedPi _ ha
      rw [extend_apply_of_mem_entries hb] at this
      rwa [this] at hb
    · have h₁ := @h (f.extend fun _ => Nontrivial.fst _) extend_mem_embedPi _ ha
      rw [extend_apply_of_notMem hf] at h₁
      have h₂ := @h (f.extend fun _ => Nontrivial.snd _) extend_mem_embedPi _ ha
      rw [extend_apply_of_notMem hf] at h₂
      rw [← h₂] at h₁
      exfalso
      exact Nontrivial.fst_ne_snd h₁
  · exact fun hfg h hh a ha => hh _ (hfg ha)

theorem embedPi_injective [∀ a, Nontrivial (β a)] :
    Function.Injective (embedPi : Finmap β → _) := by
  intro _ _ h
  simpa [subset_antisymm_iff, embedPi_subset_embedPi, le_antisymm_iff] using h

end Finmap

variable [∀ a, TopologicalSpace (β a)] [∀ a, DiscreteTopology (β a)]

namespace Finmap

theorem isOpen_embedPi : IsOpen (embedPi f) := by
  rw [isOpen_pi_iff]
  intro g hg
  simp only [embedPi, Set.mem_setOf] at hg
  refine ⟨f.keys, fun a => {g a}, by simp, fun h hh a ha => ?_⟩
  simp only [Set.mem_pi, SetLike.mem_coe, Set.mem_singleton_iff] at hh
  rw [hh _ (Multiset.fst_mem_keys ha), hg _ ha]

theorem isClosed_embedPi : IsClosed (embedPi f) := by
  rw [← isOpen_compl_iff, isOpen_pi_iff]
  intro g hg
  simp only [Set.mem_compl_iff, embedPi, Set.mem_setOf, not_forall, exists_prop] at hg
  rcases hg with ⟨⟨a, b⟩, hab, hg⟩
  simp only at hg
  refine ⟨{a}, fun a => {g a}, by simp, fun h hh => ?_⟩
  simp only [Finset.coe_singleton, Set.singleton_pi, Set.mem_preimage, Function.eval,
    Set.mem_singleton_iff] at hh
  simp only [Set.mem_compl_iff, embedPi, Set.mem_setOf_eq, not_forall, exists_prop, Sigma.exists]
  refine ⟨a, b, hab, ?_⟩
  rwa [hh]

instance [∀ a, Nontrivial (β a)] : BooleanCompletion (Finmap β) (RegularOpenSet (∀ a, β a)) where
  embed.toFun f := ⟨embedPi f, isRegularOpen_of_isClopen ⟨isClosed_embedPi, isOpen_embedPi⟩⟩
  embed.inj' _ _ h := by
    simpa [embedPi_injective.eq_iff] using h
  embed.map_rel_iff' := by
    intro f g
    rw [← embedPi_subset_embedPi]
    rfl
  embed_ne_bot f := by
    classical
    rw [← SetLike.coe_ne_coe]
    change embedPi f ≠ _
    simp only [RegularOpenSet.coe_bot, ne_eq, Set.eq_empty_iff_forall_notMem, not_forall, not_not]
    exact ⟨f.extend fun _ => Nontrivial.fst _, extend_mem_embedPi⟩
  exists_embed_le s hs := by
    change ∃ f : Finmap β, embedPi f ⊆ s
    simp only [ne_eq, ← SetLike.coe_ne_coe, RegularOpenSet.coe_bot, Set.eq_empty_iff_forall_notMem,
      SetLike.mem_coe, not_forall, not_not] at hs
    rcases hs with ⟨f, hf⟩
    have hs := s.isOpen
    simp only [isOpen_pi_iff, SetLike.mem_coe, isOpen_discrete, true_and] at hs
    rcases hs f hf with ⟨I, t, ht, ht'⟩
    refine ⟨restrict f I, fun g hg => ht' fun a ha => ?_⟩
    rw [SetLike.mem_coe, ← mem_restrict (f := f), mem_def, Multiset.mem_keys] at ha
    rcases ha with ⟨b, hab⟩
    specialize hg _ hab
    simp only [mem_restrict_entries] at hab
    rw [hg, ← hab.2]
    exact ht _ hab.1

theorem forces_iff [∀ a, Nontrivial (β a)] (p : Finmap β) (s : RegularOpenSet (∀ a, β a)) :
    p ⊩ s ↔ ∀ f, (∀ a ∈ p.entries, f a.1 = a.2) → f ∈ s := Iff.rfl

end Finmap

abbrev Finmap' (α β : Type*) := Finmap fun _ : α => β

instance [∀ a, Countable (β a)] : CountableChainCondition (RegularOpenSet (∀ a, β a)) where
  ccc S hS := by
    classical
    wlog h : ⊥ ∉ S generalizing S
    · rw [not_not] at h
      rw [← Set.union_diff_cancel (Set.singleton_subset_iff.2 h)]
      refine .union (Set.countable_singleton _) ?_
      exact this _ (hS.mono Set.diff_subset) (by simp)
    by_contra hS'
    rw [← Set.countable_coe_iff, not_countable_iff] at hS'
    have : ∀ s : S, ∃ f, ∃ (I : Finset α),
        f ∈ s.1 ∧ Set.pi I (fun a => {f a}) ⊆ s.1 := by
      intro ⟨s, hs⟩
      have hs' : s ≠ ⊥ := fun heq => h (by simpa [heq] using hs)
      simp only [← SetLike.coe_ne_coe, RegularOpenSet.coe_bot, ne_eq,
        Set.eq_empty_iff_forall_notMem, not_forall, not_not] at hs'
      rcases hs' with ⟨f, hf⟩
      have := s.isOpen
      simp only [isOpen_pi_iff, SetLike.mem_coe, isOpen_discrete, true_and] at this
      rcases this f hf with ⟨I, u, hu, hs⟩
      refine ⟨f, I, hf, (Set.pi_mono ?_).trans hs⟩
      simpa
    choose f I hf hI using this
    rcases Uncountable.exists_uncountable_pairwise_inter_eq I with ⟨T, J, hT, hT'⟩
    apply not_uncountable (α := ∀ j : J, β j.1)
    rw [← Set.uncountable_univ_iff]
    refine .mono (Set.subset_univ ((fun s (j : J) => f s j.1) '' T))
      (hT.image fun s₁ hs₁ s₂ hs₂ h => ?_)
    by_contra! h'
    refine Set.eq_empty_iff_forall_notMem.1
        (RegularOpenSet.disjoint_iff.1 <| hS s₁.2 s₂.2 (Subtype.coe_ne_coe.2 h'))
        (fun i => if i ∈ I s₁ then f s₁ i else f s₂ i) ⟨?_, ?_⟩
        <;> apply hI <;> simp only [Set.mem_pi, SetLike.mem_coe, Set.mem_singleton_iff]
        <;> intro j hj
    · simp [hj]
    · by_cases hj' : j ∈ I s₁
      · simp only [hj', ↓reduceIte]
        refine congr_fun h ⟨j, ?_⟩
        rw [← hT' hs₁ hs₂ h']
        simp [*]
      · simp [hj']
