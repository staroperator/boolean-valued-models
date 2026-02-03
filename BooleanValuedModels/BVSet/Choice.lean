import BooleanValuedModels.BVSet.MaximumPrinciple
import BooleanValuedModels.BVSet.Relations

namespace BVSet

variable {B : Type u} [CompleteBooleanAlgebra B]

/-- `BVSet` satisfies the axiom of choice. Here we give a direct proof via maximum principle, using
the fact that every `BVSet` is equivalent to a `BVSet` where the boolean values of each element
form an antichain.

See <https://math.stackexchange.com/questions/5122668/can-vb-vdash-ac-be-proved-directly-instead-of-via-zorns-lemma-or-well-order> -/
theorem exists_choice_func [Small.{v} B] (u : BVSet.{u, v} B) :
    ∅ ∉ᴮ u ≤ ⨆ f, isFunc u (⋃ᴮ u) f ⊓ ⨅ x, x ∈ᴮ u ⇨ ⨆ y, y ∈ᴮ x ⊓ kpair x y ∈ᴮ f := by
  cases exists_wellOrder u.Index
  let b : u.Index → B := WellFoundedLT.fix fun i ih =>
    u i \ ⨆ j : Set.Iio i, ih j.1 j.2 ⊓ j.1 =ᴮ i
  have hb₁ : ∀ i, b i = u i \ ⨆ j : Set.Iio i, b j.1 ⊓ j.1 =ᴮ i := by
    intro i
    unfold b
    conv_lhs => rw [WellFoundedLT.fix_eq]
  have hb₂ : ∀ i j, i ≠ j → b i ⊓ b j ⊓ i =ᴮ j = ⊥ := by
    intro i j hij
    wlog hij' : j < i generalizing i j
    · rw [inf_comm (b i), eq_symm]
      exact this j i hij.symm (hij.lt_of_le (le_of_not_gt hij'))
    grw [hb₁, eq_bot_iff, sdiff_le_hnot, hnot_eq_compl, compl_iSup, iInf_le _ ⟨j, hij'⟩,
      eq_symm, inf_assoc, compl_inf_self]
  have hb₃ : ∀ i, b i ≤ u i := by
    intro i
    unfold b
    rw [WellFoundedLT.fix_eq]
    exact sdiff_le
  have hb₄ : ∀ x, x ∈ᴮ u = ⨆ i, b i ⊓ x =ᴮ i := by
    intro x
    rw [mem_def]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      apply IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) x i
      simp_rw [eq_symm (i : BVSet B)]
      nth_grw 1 [← sup_idem (iSup _), ← iSup₂_le_iSup fun j => j < i]
      nth_grw 2 [← le_iSup _ i]
      rw [sup_inf_left]
      apply le_inf
      · simp only [hb₁ i, iSup_subtype, Set.mem_Iio]
        rw [sup_sdiff_self]
        exact le_sup_right
      · simp
    · exact iSup_mono fun i => inf_le_inf_right _ (hb₃ i)
  let c : u.Index → BVSet B := fun i =>
    Classical.choose (IsExtentional.exists_eq_iSup (f := fun x => x ∈ᴮ (i : BVSet B)) (by fun_prop))
  have hc : ∀ i, c i ∈ᴮ i = i ≠ᴮ ∅ := fun i => by
    rw [ne_empty]
    exact Classical.choose_spec (IsExtentional.exists_eq_iSup (f := fun x => x ∈ᴮ (i : BVSet B)) (by fun_prop))
  let f : BVSet B := ⟨u.Index, fun i => kpair i (c i), b⟩
  refine le_iSup_of_le f (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_)
  · rw [isRel_eq_subset_prod, subset_def]
    simp only [Index_mk, val_mk, dom_mk, le_iInf_iff, le_himp_iff, f]
    intro i
    grw [hb₃, ← le_kpair_mem_prod, mem_sUnion]
    refine le_inf ?_ (le_iSup_of_le i (le_inf ?_ ?_))
    · grw [inf_le_right, val_le_dom_mem]
    · grw [inf_le_right, val_le_dom_mem]
    · grw [val_le_dom_mem, mem_def', compl_iSup, iInf_le _ (i : BVSet B), compl_inf,
        inf_sup_right, compl_inf_self, bot_sup_eq, inf_le_left, hc]
  · refine le_iInf fun x => ?_
    rw [le_himp_iff, hb₄ x, inf_iSup_eq]
    refine iSup_le fun i => ?_
    rw [← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) x i
    refine le_iSup_of_le (c i) (le_inf ?_ ?_)
    · rw [mem_sUnion]
      refine le_iSup_of_le i (le_inf ?_ ?_)
      · grw [inf_le_right, hb₃, val_le_dom_mem]
      · grw [hb₃, val_le_dom_mem, mem_def', compl_iSup, iInf_le _ (i : BVSet B), compl_inf,
          inf_sup_right, compl_inf_self, bot_sup_eq, inf_le_left, hc]
    · grw [inf_le_right, mem_def]
      simp only [Index_mk, val_mk, dom_mk, f]
      apply le_iSup_of_le i
      simp
  · refine le_iInf fun x => ?_
    rw [le_himp_iff, hb₄ x, inf_iSup_eq]
    refine iSup_le fun i => ?_
    rw [← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) x i
    refine le_iInf fun y₁ => ?_
    grw [← le_himp]
    refine le_iInf fun y₂ => ?_
    grw [← le_himp, mem_def (v := f), mem_def (v := f)]
    simp only [Index_mk, val_mk, dom_mk, f]
    rw [le_himp_iff, inf_iSup_eq]
    refine iSup_le fun j => ?_
    rw [kpair_eq_kpair, ← inf_assoc, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) y₁
    rw [le_himp_iff, inf_iSup_eq]
    refine iSup_le fun k => ?_
    rw [kpair_eq_kpair, ← inf_assoc, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) y₂
    grw [inf_right_comm _ ((i : BVSet B) =ᴮ j), eq_symm (i : BVSet B), inf_assoc, eq_trans]
    rcases eq_or_ne j k with rfl | hjk
    · simp
    · rw [inf_assoc, inf_assoc, ← inf_assoc (b j), hb₂ j k hjk]
      simp
  · refine le_iInf fun x => ?_
    rw [le_himp_iff, hb₄ x, inf_iSup_eq]
    refine iSup_le fun i => ?_
    rw [← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) x i
    refine le_iSup_of_le (c i) (le_inf ?_ ?_)
    · grw [hb₃, val_le_dom_mem, mem_def', compl_iSup, iInf_le _ (i : BVSet B), compl_inf,
        inf_sup_right, compl_inf_self, bot_sup_eq, inf_le_left, hc]
    · rw [mem_def (v := f)]
      simp only [Index_mk, val_mk, dom_mk, f]
      refine le_iSup_of_le i ?_
      simp

end BVSet
