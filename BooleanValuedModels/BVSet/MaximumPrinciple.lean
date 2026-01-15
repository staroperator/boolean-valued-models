import BooleanValuedModels.BVSet.Defs
import Mathlib.SetTheory.Cardinal.Order

variable {B : Type u} [CompleteBooleanAlgebra B]

namespace BVSet

def sum (ι : Type v) (a : ι → B) (u : ι → BVSet B) : BVSet B :=
  mk (Σ i, (u i).Index) (fun ⟨_, x⟩ => x) fun ⟨i, x⟩ => a i ⊓ x ∈ᴮ u i

variable {ι : Type v} {a : ι → B} {u : ι → BVSet B}

/-- Mixing lemma. -/
theorem le_sum_eq (ha : ∀ i j, i ≠ j → a i ⊓ a j ≤ u i =ᴮ u j) {i} : a i ≤ sum ι a u =ᴮ u i := by
  rw [eq_def, subset_def, subset_def]
  simp only [le_inf_iff, le_iInf_iff, le_himp_iff]
  constructor
  · intro ⟨j, x⟩
    simp only [sum, val_mk, dom_mk, ge_iff_le]
    by_cases hij : i = j
    · subst hij
      simp
    · grw [← inf_assoc, ha i j hij]
      apply mem_congr_right'
  · intro j
    simp only [mem_def]
    apply le_iSup_of_le ⟨i, j⟩
    simp only [sum, val_mk, dom_mk, BVSet.eq_refl, le_top, inf_of_le_left, le_inf_iff, inf_le_left,
      true_and]
    apply inf_le_of_right_le
    exact val_le_mem

theorem le_sum_eq_of_pairwise_disjoint (ha : ∀ i j, i ≠ j → Disjoint (a i) (a j)) {i} : a i ≤ sum ι a u =ᴮ u i :=
  le_sum_eq fun i j hij => le_of_eq_of_le (ha i j hij).eq_bot bot_le

end BVSet

open BVSet

/-- Maximum principle. -/
theorem SetTheory.Formula.exists_eq_iSup {f : BVSet.{u, max u v} B → B} (hf : IsExtentional f) :
    ∃ u, f u = ⨆ x, f x := by
  let ι : Type _ := Id { a // ∃ u, f u = a }
  rcases exists_wellOrder ι with ⟨hlo, hwo⟩
  let u : ι → BVSet B := fun ⟨_, h⟩ => Classical.choose h
  let a : ι → B := fun i => f (u i) \ ⨆ j < i, f (u j)
  have ha₁ : ∀ i, a i ≤ f (u i) := by simp [a]
  have ha₂ : ∀ i, ⨆ j ≤ i, a j = ⨆ j ≤ i, f (u j) := by
    intro i
    induction i using hwo.induction with | _ i ih
    rw [biSup_le_eq_sup, biSup_lt_eq_biSup_lt_biSup_le]
    conv_lhs => enter [1, 1, j, 1, hj]; rw [ih _ hj]
    rw [← biSup_lt_eq_biSup_lt_biSup_le, biSup_le_eq_sup]
    simp [a]
  have ha₃ : ∀ i, ∀ j < i, a i ⊓ a j = ⊥ := by
    intro i j hij
    grw [eq_bot_iff, ha₁ j]
    simp only [a, sdiff_eq, compl_iSup]
    nth_grw 2 [inf_le_right]
    grw [iInf₂_le j hij, compl_inf_self]
  exists sum ι a u
  apply le_antisymm
  · exact le_iSup f (sum ι a u)
  · trans ⨆ i, f (u i)
    · rw [iSup_le_iff]
      intro x
      let i : ι := ⟨f x, x, rfl⟩
      refine le_iSup_of_le i (ge_of_eq ?_)
      simp only [u, i]
      exact Classical.choose_spec (p := fun y => f y = f x) _
    trans ⨆ i, a i
    · rw [iSup_le_iff]
      intro i
      trans ⨆ j ≤ i, a j
      · rw [ha₂ i]
        apply le_iSup₂ (f := fun i _ => f (u i)) i
        exact le_refl i
      · exact iSup₂_le_iSup _ _
    · rw [iSup_le_iff]
      intro i
      rw [← inf_idem (a i)]
      trans sum ι a u =ᴮ u i ⊓ a i
      · gcongr
        refine le_sum_eq_of_pairwise_disjoint fun i j hij => ?_
        rw [disjoint_iff]
        rcases hij.lt_or_gt with hij | hij
        · rw [inf_comm]
          exact ha₃ j i hij
        · exact ha₃ i j hij
      · grw [ha₁ i, BVSet.eq_symm, hf (u i) (sum ι a u)]
