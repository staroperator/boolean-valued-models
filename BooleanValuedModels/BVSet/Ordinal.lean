import BooleanValuedModels.BVSet.ZFSet
import Mathlib.SetTheory.ZFC.Ordinal

universe u v

variable {B : Type u} [CompleteBooleanAlgebra B] {u v w : BVSet.{u, v} B}

namespace BVSet

def isTransitive (u : BVSet B) : B :=
  ⨅ x, x ∈ᴮ u ⇨ x ⊆ᴮ u

@[fun_prop] protected theorem IsExtentional.isTransitive : IsExtentional (B := B) isTransitive := by
  unfold isTransitive
  fun_prop

@[gcongr] theorem isTransitive_congr {u v : BVSet B} (h : u ≈ v) :
    isTransitive u = isTransitive v := by
  apply IsExtentional.congr _ h
  fun_prop

theorem isTransitive_inf_mem_le (u v : BVSet B) : isTransitive u ⊓ v ∈ᴮ u ≤ v ⊆ᴮ u := by
  simp only [isTransitive]
  grw [iInf_le _ v, himp_inf_le]

@[simp] theorem isTransitive_empty : isTransitive ∅ = (⊤ : B) := by
  simp [isTransitive]

theorem _root_.ZFSet.isTransitive_toBVSet_of_isTransitive {x : ZFSet.{v}} (hx : x.IsTransitive) :
    isTransitive x.toBVSet = (⊤ : B) := by
  simp only [isTransitive, eq_top_iff]
  rw [IsExtentional.iInf_mem_toBVSet_himp (by fun_prop), le_iInf_iff]
  intro ⟨y, hy⟩
  simp [ZFSet.toBVSet_subset_toBVSet_of_subset (hx _ hy)]

def isOrdinal (u : BVSet B) : B :=
  isTransitive u ⊓ ⨅ x, x ∈ᴮ u ⇨ ⨅ y, y ∈ᴮ u ⇨ x ∈ᴮ y ⊔ x =ᴮ y ⊔ y ∈ᴮ x

@[fun_prop] protected theorem IsExtentional.isOrdinal : IsExtentional (B := B) isOrdinal := by
  unfold isOrdinal
  fun_prop

@[gcongr] theorem isOrdinal_congr {u v : BVSet B} (h : u ≈ v) :
    isOrdinal u = isOrdinal v := by
  apply IsExtentional.congr _ h
  fun_prop

@[simp] theorem isOrdinal_empty : isOrdinal ∅ = (⊤ : B) := by
  simp [isOrdinal]

theorem isOrdinal_le_isTransitive : isOrdinal u ≤ isTransitive u :=
  inf_le_left

theorem isOrdinal_mem_trichotomous :
    isOrdinal u ⊓ v ∈ᴮ u ⊓ w ∈ᴮ u ≤ v ∈ᴮ w ⊔ v =ᴮ w ⊔ w ∈ᴮ v := by
  simp only [isOrdinal]
  grw [inf_le_right (a := isTransitive u), iInf_le _ v, himp_inf_le, iInf_le _ w, himp_inf_le]

theorem isOrdinal_inf_mem_inf_mem_inf_mem_le {x y z} :
    isOrdinal u ⊓ x ∈ᴮ u ⊓ y ∈ᴮ x ⊓ z ∈ᴮ y ≤ z ∈ᴮ x := by
  apply le_of_inf_le (x ∈ᴮ z ⊔ x =ᴮ z ⊔ z ∈ᴮ x)
  · grw [← isOrdinal_mem_trichotomous (u := u)]
    refine le_inf ?_ ?_
    · grw [inf_le_left, inf_le_left]
    · grw [← subset_inf_mem_le z y u]
      apply le_inf
      · grw [← isTransitive_inf_mem_le]
        apply le_inf
        · grw [inf_le_left, inf_le_left, inf_le_left, isOrdinal_le_isTransitive]
        · grw [← subset_inf_mem_le y x u]
          apply le_inf
          · grw [inf_le_left, inf_le_left, isOrdinal_le_isTransitive, isTransitive_inf_mem_le]
          · grw [inf_le_left, inf_le_right]
      · grw [inf_le_right]
  · rw [inf_sup_left, inf_sup_left]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [inf_assoc (isOrdinal u ⊓ x ∈ᴮ u), inf_assoc (isOrdinal u ⊓ x ∈ᴮ u)]
      grw [inf_le_right]
      rw [inf_right_comm (y ∈ᴮ x), mem_cycle₃]
      exact bot_le
    · rw [inf_assoc (isOrdinal u ⊓ x ∈ᴮ u), inf_assoc (isOrdinal u ⊓ x ∈ᴮ u), inf_assoc (y ∈ᴮ x), inf_comm (z ∈ᴮ y)]
      grw [inf_le_right, mem_congr_left', mem_cycle₂, bot_le]
    · grw [inf_le_right]

theorem isOrdinal_inf_mem_le_isOrdinal :
    isOrdinal u ⊓ v ∈ᴮ u ≤ isOrdinal v := by
  apply le_inf
  · apply le_iInf
    intro x
    rw [le_himp_iff, subset_def']
    apply le_iInf
    intro y
    rw [le_himp_iff]
    exact isOrdinal_inf_mem_inf_mem_inf_mem_le
  · apply le_iInf
    intro x
    rw [le_himp_iff]
    apply le_iInf
    intro y
    rw [le_himp_iff]
    grw [← isOrdinal_mem_trichotomous (u := u)]
    refine le_inf (le_inf ?_ ?_) ?_
    · grw [inf_le_left, inf_le_left, inf_le_left]
    · grw [isOrdinal_le_isTransitive, isTransitive_inf_mem_le, subset_inf_mem_le, inf_le_left]
    · grw [isOrdinal_le_isTransitive, isTransitive_inf_mem_le, inf_le_left (a := v ⊆ᴮ u),
        subset_inf_mem_le]

theorem isOrdinal_inf_subset_le_mem_sup_eq :
    isOrdinal u ⊓ isOrdinal v ⊓ v ⊆ᴮ u ≤ v ∈ᴮ u ⊔ v =ᴮ u := by
  rw [← compl_himp_eq', le_himp_iff]
  apply le_of_inf_le ((u \ v) ≠ᴮ ∅)
  · grw [inf_assoc, inf_le_right, subset_inf_ne_le]
  · grw [regularity, inf_iSup_eq]
    apply iSup_le
    intro x
    simp only [mem_sdiff, ← inf_assoc]
    apply le_of_inf_le (x =ᴮ v)
    · apply le_of_inf_le (x ⊆ᴮ v)
      · grw [← subset_inf_inter_eq_empty_le (u := x) (v := u)]
        apply le_inf
        · grw [← isTransitive_inf_mem_le (u := u) (v := x)]
          apply le_inf
          · repeat grw [inf_le_left]
            grw [isOrdinal_le_isTransitive]
          · grw [inf_le_left, inf_le_left, inf_le_right]
        · grw [inf_le_right]
      · rw [← inf_compl_le_bot, inf_assoc]
        grw [subset_inf_ne_le, regularity, inf_iSup_eq]
        apply iSup_le
        intro y
        simp only [mem_sdiff, ← inf_assoc]
        apply le_of_inf_le (x ∈ᴮ y ⊔ x =ᴮ y ⊔ y ∈ᴮ x)
        · grw [← isOrdinal_mem_trichotomous (u := u)]
          refine le_inf (le_inf ?_ ?_) ?_
          · repeat grw [inf_le_left]
          · iterate 5 grw [inf_le_left]
            grw [inf_le_right]
          · grw [← subset_inf_mem_le y v u]
            apply le_inf
            · iterate 7 grw [inf_le_left]
              grw [inf_le_right]
            · grw [inf_le_left, inf_le_left, inf_le_right]
        · rw [inf_sup_left, inf_sup_left]
          refine sup_le (sup_le ?_ ?_) ?_
          · apply le_of_inf_le (y ⊆ᴮ x)
            · grw [← subset_inf_inter_eq_empty_le (u := y) (v := v)]
              apply le_inf
              · grw [← isTransitive_inf_mem_le (u := v)]
                apply le_inf
                · iterate 9 grw [inf_le_left]
                  grw [inf_le_right, isOrdinal_le_isTransitive]
                · iterate 3 grw [inf_le_left]
                  grw [inf_le_right]
              · grw [inf_le_left, inf_le_right]
            · grw [inf_assoc, mem_inf_subset_le, mem_self]
              simp
          · grw [inf_le_left (b := _ =ᴮ ∅), inf_le_left (b := _ᶜ), inf_assoc,
              inf_comm (y ∈ᴮ v), mem_congr_left', inf_le_left (b := _ =ᴮ ∅),
              inf_assoc]
            simp
          · grw [inf_le_left (b := _ =ᴮ ∅), inf_assoc]
            simp
    · grw [inf_le_right (a := isOrdinal u), inf_le_right (a := isOrdinal v), inf_le_right (a := v ⊆ᴮ u),
        inf_le_right (a := v ≠ᴮ u), inf_le_left (b := _ᶜ), inf_le_left (b := _ =ᴮ ∅),
        inf_comm, mem_congr_left]

theorem isOrdinal_le_subset_sup_mem :
    isOrdinal u ⊓ isOrdinal v ≤ u ⊆ᴮ v ⊔ v ∈ᴮ u := by
  rw [← compl_himp_eq, le_himp_iff, compl_subset]
  grw [regularity, inf_iSup_eq]
  apply iSup_le
  intro x
  simp only [mem_sdiff, ← inf_assoc]
  apply le_of_inf_le (x ∈ᴮ v ⊔ x =ᴮ v)
  · grw [← isOrdinal_inf_subset_le_mem_sup_eq]
    refine le_inf (le_inf ?_ ?_) ?_
    · grw [inf_le_left, inf_le_left, inf_le_left, inf_le_right]
    · grw [← isOrdinal_inf_mem_le_isOrdinal (u := u) (v := x)]
      apply le_inf
      · repeat grw [inf_le_left]
      · grw [inf_le_left, inf_le_left, inf_le_right]
    · grw [← subset_inf_inter_eq_empty_le (v := u)]
      apply le_inf
      · grw [← isTransitive_inf_mem_le]
        apply le_inf
        · repeat grw [inf_le_left]
          grw [isOrdinal_le_isTransitive]
        · grw [inf_le_left, inf_le_left, inf_le_right]
      · grw [inf_le_right]
  · rw [inf_sup_left]
    apply sup_le
    · grw [inf_le_left (b := _ =ᴮ ∅), inf_assoc]
      simp
    · grw [inf_le_left (b := _ =ᴮ ∅), inf_le_left (b := _ᶜ), inf_assoc, inf_comm (x ∈ᴮ u),
        mem_congr_left, inf_le_right]

theorem isOrdinal_trichotomous :
    isOrdinal u ⊓ isOrdinal v ≤ u ∈ᴮ v ⊔ u =ᴮ v ⊔ v ∈ᴮ u := by
  apply le_of_inf_le _ isOrdinal_le_subset_sup_mem
  rw [inf_sup_left]
  apply sup_le
  · grw [inf_comm (isOrdinal u), isOrdinal_inf_subset_le_mem_sup_eq]
    exact le_sup_left
  · grw [inf_le_right]
    exact le_sup_right

theorem _root_.ZFSet.isOrdinal_toBVSet_of_isOrdinal {x : ZFSet.{v}} (hx : x.IsOrdinal) :
    isOrdinal x.toBVSet = (⊤ : B) := by
  simp only [isOrdinal, ZFSet.isTransitive_toBVSet_of_isTransitive hx.isTransitive, top_inf_eq, eq_top_iff]
  rw [IsExtentional.iInf_mem_toBVSet_himp (by fun_prop), le_iInf_iff]
  intro ⟨y, hy⟩
  simp only
  rw [IsExtentional.iInf_mem_toBVSet_himp (by fun_prop), le_iInf_iff]
  intro ⟨z, hz⟩
  simp only
  rcases (hx.mem hy).mem_trichotomous (hx.mem hz) with h | h | h
  · simp [ZFSet.toBVSet_mem_toBVSet_of_mem h]
  · simp [h, eq_refl]
  · simp [ZFSet.toBVSet_mem_toBVSet_of_mem h]

theorem _root_.ZFSet.isOrdinal_toBVSet {o : Ordinal} :
    isOrdinal o.toZFSet.toBVSet = (⊤ : B) :=
  ZFSet.isOrdinal_toBVSet_of_isOrdinal (ZFSet.isOrdinal_toZFSet o)

theorem isOrdinal_eq_iSup_eq {u : BVSet.{u, max u v} B} :
    isOrdinal u = ⨆ o : Ordinal.{max u v}, u =ᴮ o.toZFSet.toBVSet := by
  apply le_antisymm
  · let f : u.Index → Set Ordinal := fun i => {o : Ordinal | o.toZFSet.toBVSet =ᴮ (i : BVSet B) ≠ ⊥}
    haveI : ∀ i, Small.{max u v} (f i) := fun i =>
      small_of_injective (f := fun ⟨o, _⟩ => o.toZFSet.toBVSet =ᴮ (i : BVSet B)) fun ⟨o₁, ho₁⟩ ⟨o₂, ho₂⟩ h => by
        simp only [ne_eq, Set.mem_setOf_eq, f, ← bot_lt_iff_ne_bot] at ho₁ ho₂
        simp only at h
        simp only [Subtype.mk.injEq]
        by_contra h'
        apply ho₁.not_ge
        rw [← inf_idem (_ =ᴮ _)]
        conv_lhs => arg 2; rw [h, eq_symm]
        grw [eq_trans, ZFSet.toBVSet_eq_toBVSet_of_ne (B := B) (Ordinal.toZFSet_injective.ne h')]
    let o := Order.succ (⨆ i, sSup (f i))
    rw [← inf_top_eq (isOrdinal u), ← ZFSet.isOrdinal_toBVSet]
    refine isOrdinal_trichotomous.trans (sup_le (sup_le ?_ ?_) ?_)
    · rw [ZFSet.mem_toBVSet,
        ← (Equiv.subtypeEquivRight (p := (· ∈ o.toZFSet)) (Set.ext_iff.1 Ordinal.coe_toZFSet)).symm.iSup_comp]
      apply iSup_le
      simp only [Equiv.subtypeEquivRight_symm_apply_coe, Subtype.forall, Set.mem_image, Set.mem_Iio,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro i hi
      exact le_iSup (u =ᴮ ·.toZFSet.toBVSet) i
    · exact le_iSup (u =ᴮ ·.toZFSet.toBVSet) o
    · rw [mem_def, iSup_le_iff]
      intro i
      suffices o ∉ f i by
        simp only [ne_eq, Set.mem_setOf_eq, not_not, f] at this
        simp [this]
      intro ho
      apply (Order.lt_succ (⨆ i, sSup (f i))).not_ge
      apply le_ciSup_of_le (Ordinal.bddAbove_of_small _) i
      exact le_csSup (Ordinal.bddAbove_of_small _) ho
  · apply iSup_le
    intro o
    grw [← IsExtentional.eq_inf_le' isOrdinal (by fun_prop) o.toZFSet.toBVSet]
    simp [ZFSet.isOrdinal_toBVSet]

theorem IsExtentional.iInf_isOrdinal_himp {f} (hf : IsExtentional f) :
    ⨅ x : BVSet.{u, max u v} B, isOrdinal x ⇨ f x = ⨅ o : Ordinal.{max u v}, f o.toZFSet.toBVSet := by
  simp_rw [isOrdinal_eq_iSup_eq.{u, v}, iSup_himp_eq]
  rw [iInf_comm]
  congr! with o
  rw [hf.iInf_eq_himp]

theorem IsExtentional.iSup_isOrdinal_inf {f} (hf : IsExtentional f) :
    ⨆ x : BVSet.{u, max u v} B, isOrdinal x ⊓ f x = ⨆ o : Ordinal.{max u v}, f o.toZFSet.toBVSet := by
  simp_rw [isOrdinal_eq_iSup_eq.{u, v}, iSup_inf_eq]
  rw [iSup_comm]
  congr! with o
  rw [hf.iSup_eq_inf]

end BVSet
