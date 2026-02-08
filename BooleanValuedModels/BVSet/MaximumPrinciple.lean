module

public import BooleanValuedModels.BVSet.Basic

import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

variable {B : Type u} [CompleteBooleanAlgebra B]

namespace BVSet

noncomputable def mix (ι : Type v) (f : ι → BVSet B) (b : ι → B) : BVSet B :=
  mkI (Σ i, (f i).dom) (fun ⟨_, x⟩ => x) fun ⟨i, x⟩ => b i ⊓ x ∈ᴮ f i

variable {ι : Type v} {f : ι → BVSet B} {b : ι → B} {i : ι}

/-- Mixing lemma. -/
theorem le_mix_beq (ha : ∀ i j, i ≠ j → b i ⊓ b j ≤ f i =ᴮ f j) : b i ≤ mix ι f b =ᴮ f i := by
  simp only [mix, beq_def, mkI_bsubset, le_inf_iff, le_iInf_iff, le_himp_iff]
  constructor
  · intro ⟨j, x, hx⟩
    simp only [ge_iff_le]
    by_cases hij : i = j
    · subst hij
      simp
    · grw [← inf_assoc, ha i j hij, bmem_congr_right']
  · simp only [bsubset_def, bmem_mkI, le_iInf_iff, le_himp_iff, Subtype.forall, mem_dom_iff]
    intro x hx
    apply le_iSup_of_le ⟨i, x, hx⟩
    simp only [beq_refl, le_top, inf_of_le_left, le_inf_iff, inf_le_left, true_and]
    grw [inf_le_right, val_le_bmem]

theorem le_mix_beq_of_pairwise_disjoint (ha : ∀ i j, i ≠ j → Disjoint (b i) (b j)) {i} :
    b i ≤ mix ι f b =ᴮ f i :=
  le_mix_beq fun i j hij => le_of_eq_of_le (ha i j hij).eq_bot bot_le

/-- Maximum principle. -/
theorem IsExtentional.exists_eq_iSup [Small.{v} B] {f : BVSet.{u, v} B → B}
    (hf : IsExtentional f) : ∃ u, f u = ⨆ x, f x := by
  let ι : Type v := Shrink { a // ∃ u, f u = a }
  rcases exists_wellOrder ι with ⟨hlo, hwo⟩
  let g : ι → BVSet B := fun i => Classical.choose ((equivShrink _).symm i).2
  let b : ι → B := fun i => f (g i) \ ⨆ j < i, f (g j)
  have hb₁ : ∀ i, b i ≤ f (g i) := by simp [b]
  have hb₂ : ∀ i, ⨆ j ≤ i, b j = ⨆ j ≤ i, f (g j) := by
    intro i
    induction i using hwo.induction with | _ i ih
    rw [biSup_le_eq_sup, biSup_lt_eq_biSup_lt_biSup_le]
    conv_lhs => enter [1, 1, j, 1, hj]; rw [ih _ hj]
    rw [← biSup_lt_eq_biSup_lt_biSup_le, biSup_le_eq_sup]
    simp [b]
  have hb₃ : ∀ i, ∀ j < i, b i ⊓ b j = ⊥ := by
    intro i j hij
    grw [eq_bot_iff, hb₁ j]
    simp only [b, sdiff_eq, compl_iSup]
    nth_grw 2 [inf_le_right]
    grw [iInf₂_le j hij, compl_inf_self]
  exists mix ι g b
  apply le_antisymm
  · exact le_iSup f (mix ι g b)
  · trans ⨆ i, f (g i)
    · rw [iSup_le_iff]
      intro x
      let i : ι := equivShrink _ ⟨f x, x, rfl⟩
      refine le_iSup_of_le i (ge_of_eq ?_)
      simp only [g, i, Equiv.symm_apply_apply]
      exact Classical.choose_spec (p := fun y => f y = f x) _
    trans ⨆ i, b i
    · rw [iSup_le_iff]
      intro i
      trans ⨆ j ≤ i, b j
      · rw [hb₂ i]
        apply le_iSup₂_of_le i <;> rfl
      · exact iSup₂_le_iSup _ _
    · rw [iSup_le_iff]
      intro i
      rw [← inf_idem (b i)]
      trans mix ι g b =ᴮ g i ⊓ b i
      · gcongr
        refine le_mix_beq_of_pairwise_disjoint fun i j hij => ?_
        rw [disjoint_iff]
        rcases hij.lt_or_gt with hij | hij
        · rw [inf_comm]
          exact hb₃ j i hij
        · exact hb₃ i j hij
      · grw [hb₁ i, beq_symm, hf (g i) (mix ι g b)]

end BVSet
