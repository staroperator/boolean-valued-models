import Mathlib.SetTheory.Cardinal.Pigeonhole

open Order Ordinal Cardinal Set Order

universe u v

namespace Set

variable {α : Type u} {β : Type v}

/-- A set is uncountable if it is not countable.
This is protected so that it does not conflict with global `Uncountable`. -/
protected def Uncountable (s : Set α) : Prop :=
  ¬s.Countable

theorem uncountable_coe_iff {s : Set α} : Uncountable s ↔ s.Uncountable :=
  not_countable_iff.symm.trans countable_coe_iff.not

alias ⟨_root_.Uncountable.to_set, Uncountable.to_subtype⟩ := uncountable_coe_iff

theorem uncountable_univ_iff : (@univ α).Uncountable ↔ Uncountable α := by
  rw [Set.Uncountable, countable_univ_iff, not_countable_iff]

protected lemma Uncountable.mono {s t : Set α} (h : s ⊆ t) : s.Uncountable → t.Uncountable :=
  mt (·.mono h)

theorem Uncountable.diff {s t : Set α} (hs : s.Uncountable) (ht : t.Countable) :
    (s \ t).Uncountable := fun h =>
  hs <| h.of_diff ht

theorem Uncountable.image {s : Set α} {f : α → β} (hs : s.Uncountable) (hi : InjOn f s) :
    (f '' s).Uncountable :=
  mt (countable_of_injective_of_countable_image hi) hs

theorem Uncountable.infinite {s : Set α} (hs : s.Uncountable) : s.Infinite :=
  mt Finite.countable hs

theorem Uncountable.nonempty {s : Set α} (hs : s.Uncountable) : s.Nonempty :=
  hs.infinite.nonempty

theorem Uncountable.nontrivial {s : Set α} (hs : s.Uncountable) : s.Nontrivial :=
  hs.infinite.nontrivial

end Set

theorem Cardinal.exists_uncountable_fiber {β α : Type u} (f : β → α) (h : #α < #β)
    (hβ : Uncountable β) : ∃ a : α, Uncountable (f ⁻¹' {a}) := by
  simp_rw [← Cardinal.aleph0_lt_mk_iff, ← Order.succ_le_iff, succ_aleph0] at hβ ⊢
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₁ hβ aleph0_lt_aleph_one.le
      (by rw [isRegular_aleph_one.cof_eq]; exact hα.trans aleph0_lt_aleph_one)
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_lt f h hα
    rw [← Order.succ_le_succ_iff, succ_aleph0] at hα
    exact ⟨a, hα.trans (succ_le_of_lt ha)⟩

theorem Uncountable.exists_uncountable_pairwise_inter_eq {α : Type u} {ι : Type v} [DecidableEq α]
    [Uncountable ι] (f : ι → Finset α) :
    ∃ (s : Set ι) (t : Finset α), s.Uncountable ∧ s.Pairwise (f · ∩ f · = t) := by
  suffices ∀ (s : Set ι) (n : ℕ), (∀ i ∈ s, (f i).card = n) → s.Uncountable →
      ∃ s' ⊆ s, ∃ (t : Finset α), s'.Uncountable ∧ s'.Pairwise (f · ∩ f · = t) by
    rcases exists_uncountable_fiber (fun i => ULift.up (f i).card) (by simp) (by infer_instance)
      with ⟨⟨n⟩, h⟩
    rcases this _ n (by grind) h.to_set with ⟨s', -, t, hs, ht⟩
    exact ⟨s', t, hs, ht⟩
  intro s n hn hs
  induction n generalizing f s with
  | zero =>
    exact ⟨s, subset_rfl, ∅, hs, fun i hi j hj hij => by grind⟩
  | succ n ih =>
    by_cases h : ∃ a, Uncountable {i ∈ s | a ∈ f i}
    · rcases h with ⟨a, ha⟩
      rcases ih (fun i => f i \ {a}) _ (by grind) ha.to_set with ⟨s', hs', t, hs'', ht⟩
      exact ⟨s', hs'.trans (sep_subset _ _), t ∪ {a}, hs'', fun i hi j hj hij => by
        grind [Set.Pairwise]⟩
    simp only [coe_setOf, not_exists, not_uncountable_iff] at h
    let g : Ordinal.{v} → ι := WellFoundedLT.fix fun j ih =>
      Classical.epsilon fun i => i ∈ s ∧ ∀ k (hk : k < j), f i ∩ f (ih k hk) = ∅
    have hg : ∀ j < ω₁, g j ∈ s ∧ ∀ k < j, f (g j) ∩ f (g k) = ∅ := by
      intro j hj
      suffices {i ∈ s | ∀ k (hk : k < j), f i ∩ f (g k) = ∅}.Nonempty by
        simp only [nonempty_def, mem_setOf_eq] at this
        apply Classical.epsilon_spec at this
        unfold g
        rwa [WellFoundedLT.fix_eq]
      rw [setOf_and, setOf_mem_eq, ← diff_compl, ← diff_self_inter]
      refine (hs.diff ?_).nonempty
      simp_rw [compl_setOf, not_forall, setOf_exists, ← mem_Iio, inter_iUnion₂]
      refine .biUnion ?_ fun a ha => ?_
      · rwa [← le_aleph0_iff_set_countable, mk_Iio_ordinal, lift_le_aleph0, ← lt_succ_iff,
          succ_aleph0, ← lt_ord, ord_aleph]
      · simp_rw [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, not_and', not_forall,
          ← SetLike.mem_coe, setOf_exists, not_not, inter_iUnion₂]
        refine .biUnion (Finset.finite_toSet _).countable fun i hi => ?_
        simp_rw [SetLike.mem_coe, inter_setOf_eq_sep]
        exact h i
    have hg' : InjOn g (Iio ω₁) := by
      intro j hj k hk hjk
      by_contra hjk'
      wlog hjk'' : k < j generalizing j k
      · exact this hk hj hjk.symm (ne_comm.1 hjk') (lt_of_le_of_ne (le_of_not_gt hjk'') hjk')
      have := (hg j hj).2 k hjk''
      simp only [← hjk, Finset.inter_self] at this
      simpa [this] using hn _ (hg j hj).1
    refine ⟨g '' Iio ω₁, by grind, ∅, .image ?_ hg', Pairwise.image ?_⟩
    · rw [← uncountable_coe_iff, ← aleph0_lt_mk_iff, mk_Iio_ordinal, aleph0_lt_lift, card_omega]
      exact aleph0_lt_aleph_one
    intro j hj k hk hjk
    simp only [Function.onFun_apply]
    wlog hjk' : k < j generalizing j k
    · rw [Finset.inter_comm]
      exact this hk hj hjk.symm (lt_of_le_of_ne (le_of_not_gt hjk') hjk)
    exact (hg j hj).2 k hjk'
