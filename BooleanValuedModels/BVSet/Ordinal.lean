module

public import BooleanValuedModels.BVSet.ZFSet
public import Mathlib.SetTheory.ZFC.Ordinal

@[expose] public section

universe u v

variable {B : Type u} [CompleteBooleanAlgebra B] {u v w : BVSet.{u, v} B}

open BVSet ZFSet Ordinal

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

theorem isTransitive_inf_bmem_le (u v : BVSet B) : isTransitive u ⊓ v ∈ᴮ u ≤ v ⊆ᴮ u := by
  simp only [isTransitive]
  grw [iInf_le _ v, himp_inf_le]

@[simp] theorem isTransitive_empty : isTransitive ∅ = (⊤ : B) := by
  simp [isTransitive]

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

theorem isOrdinal_bmem_trichotomous :
    isOrdinal u ⊓ v ∈ᴮ u ⊓ w ∈ᴮ u ≤ v ∈ᴮ w ⊔ v =ᴮ w ⊔ w ∈ᴮ v := by
  simp only [isOrdinal]
  grw [inf_le_right (a := isTransitive u), iInf_le _ v, himp_inf_le, iInf_le _ w, himp_inf_le]

theorem isOrdinal_inf_bmem_inf_bmem_inf_bmem_le {x y z} :
    isOrdinal u ⊓ x ∈ᴮ u ⊓ y ∈ᴮ x ⊓ z ∈ᴮ y ≤ z ∈ᴮ x := by
  apply le_of_inf_le (x ∈ᴮ z ⊔ x =ᴮ z ⊔ z ∈ᴮ x)
  · grw [← isOrdinal_bmem_trichotomous (u := u)]
    refine le_inf ?_ ?_
    · grw [inf_le_left, inf_le_left]
    · grw [← bsubset_inf_bmem_le z y u]
      apply le_inf
      · grw [← isTransitive_inf_bmem_le]
        apply le_inf
        · grw [inf_le_left, inf_le_left, inf_le_left, isOrdinal_le_isTransitive]
        · grw [← bsubset_inf_bmem_le y x u]
          apply le_inf
          · grw [inf_le_left, inf_le_left, isOrdinal_le_isTransitive, isTransitive_inf_bmem_le]
          · grw [inf_le_left, inf_le_right]
      · grw [inf_le_right]
  · rw [inf_sup_left, inf_sup_left]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [inf_assoc (isOrdinal u ⊓ x ∈ᴮ u), inf_assoc (isOrdinal u ⊓ x ∈ᴮ u)]
      grw [inf_le_right]
      rw [inf_right_comm (y ∈ᴮ x), mem_cycle₃]
      exact bot_le
    · rw [inf_assoc (isOrdinal u ⊓ x ∈ᴮ u), inf_assoc (isOrdinal u ⊓ x ∈ᴮ u), inf_assoc (y ∈ᴮ x),
        inf_comm (z ∈ᴮ y)]
      grw [inf_le_right, bmem_congr_left', bmem_cycle₂, bot_le]
    · grw [inf_le_right]

theorem isOrdinal_inf_bmem_le_isOrdinal :
    isOrdinal u ⊓ v ∈ᴮ u ≤ isOrdinal v := by
  apply le_inf
  · apply le_iInf
    intro x
    rw [le_himp_iff, bsubset_def']
    apply le_iInf
    intro y
    rw [le_himp_iff]
    exact isOrdinal_inf_bmem_inf_bmem_inf_bmem_le
  · apply le_iInf
    intro x
    rw [le_himp_iff]
    apply le_iInf
    intro y
    rw [le_himp_iff]
    grw [← isOrdinal_bmem_trichotomous (u := u)]
    refine le_inf (le_inf ?_ ?_) ?_
    · grw [inf_le_left, inf_le_left, inf_le_left]
    · grw [isOrdinal_le_isTransitive, isTransitive_inf_bmem_le, bsubset_inf_bmem_le, inf_le_left]
    · grw [isOrdinal_le_isTransitive, isTransitive_inf_bmem_le, inf_le_left (a := v ⊆ᴮ u),
        bsubset_inf_bmem_le]

theorem isOrdinal_inf_bsubset_le_bmem_sup_eq :
    isOrdinal u ⊓ isOrdinal v ⊓ v ⊆ᴮ u ≤ v ∈ᴮ u ⊔ v =ᴮ u := by
  rw [← compl_himp_eq', le_himp_iff]
  apply le_of_inf_le ((u \ v) ≠ᴮ ∅)
  · grw [inf_assoc, inf_le_right, bsubset_inf_bne_le]
  · grw [regularity, inf_iSup_eq]
    apply iSup_le
    intro x
    simp only [bmem_sdiff, ← inf_assoc]
    apply le_of_inf_le (x =ᴮ v)
    · apply le_of_inf_le (x ⊆ᴮ v)
      · grw [← bsubset_inf_inter_beq_empty_le (u := x) (v := u)]
        apply le_inf
        · grw [← isTransitive_inf_bmem_le (u := u) (v := x)]
          apply le_inf
          · repeat grw [inf_le_left]
            grw [isOrdinal_le_isTransitive]
          · grw [inf_le_left, inf_le_left, inf_le_right]
        · grw [inf_le_right]
      · rw [← inf_compl_le_bot, inf_assoc]
        grw [bsubset_inf_bne_le, regularity, inf_iSup_eq]
        apply iSup_le
        intro y
        simp only [bmem_sdiff, ← inf_assoc]
        apply le_of_inf_le (x ∈ᴮ y ⊔ x =ᴮ y ⊔ y ∈ᴮ x)
        · grw [← isOrdinal_bmem_trichotomous (u := u)]
          refine le_inf (le_inf ?_ ?_) ?_
          · repeat grw [inf_le_left]
          · iterate 5 grw [inf_le_left]
            grw [inf_le_right]
          · grw [← bsubset_inf_bmem_le y v u]
            apply le_inf
            · iterate 7 grw [inf_le_left]
              grw [inf_le_right]
            · grw [inf_le_left, inf_le_left, inf_le_right]
        · rw [inf_sup_left, inf_sup_left]
          refine sup_le (sup_le ?_ ?_) ?_
          · apply le_of_inf_le (y ⊆ᴮ x)
            · grw [← bsubset_inf_inter_beq_empty_le (u := y) (v := v)]
              apply le_inf
              · grw [← isTransitive_inf_bmem_le (u := v)]
                apply le_inf
                · iterate 9 grw [inf_le_left]
                  grw [inf_le_right, isOrdinal_le_isTransitive]
                · iterate 3 grw [inf_le_left]
                  grw [inf_le_right]
              · grw [inf_le_left, inf_le_right]
            · grw [inf_assoc, bmem_inf_bsubset_le, bmem_self]
              simp
          · grw [inf_le_left (b := _ =ᴮ ∅), inf_le_left (b := _ᶜ), inf_assoc,
              inf_comm (y ∈ᴮ v), bmem_congr_left', inf_le_left (b := _ =ᴮ ∅),
              inf_assoc]
            simp
          · grw [inf_le_left (b := _ =ᴮ ∅), inf_assoc]
            simp
    · grw [inf_le_right (a := isOrdinal u), inf_le_right (a := isOrdinal v),
        inf_le_right (a := v ⊆ᴮ u), inf_le_right (a := v ≠ᴮ u), inf_le_left (b := _ᶜ),
        inf_le_left (b := _ =ᴮ ∅), inf_comm, bmem_congr_left]

theorem isOrdinal_le_bsubset_sup_bmem :
    isOrdinal u ⊓ isOrdinal v ≤ u ⊆ᴮ v ⊔ v ∈ᴮ u := by
  rw [← compl_himp_eq, le_himp_iff, compl_subset]
  grw [regularity, inf_iSup_eq]
  apply iSup_le
  intro x
  simp only [bmem_sdiff, ← inf_assoc]
  apply le_of_inf_le (x ∈ᴮ v ⊔ x =ᴮ v)
  · grw [← isOrdinal_inf_bsubset_le_bmem_sup_eq]
    refine le_inf (le_inf ?_ ?_) ?_
    · grw [inf_le_left, inf_le_left, inf_le_left, inf_le_right]
    · grw [← isOrdinal_inf_bmem_le_isOrdinal (u := u) (v := x)]
      apply le_inf
      · repeat grw [inf_le_left]
      · grw [inf_le_left, inf_le_left, inf_le_right]
    · grw [← bsubset_inf_inter_beq_empty_le (v := u)]
      apply le_inf
      · grw [← isTransitive_inf_bmem_le]
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
        bmem_congr_left, inf_le_right]

theorem isOrdinal_trichotomous :
    isOrdinal u ⊓ isOrdinal v ≤ u ∈ᴮ v ⊔ u =ᴮ v ⊔ v ∈ᴮ u := by
  apply le_of_inf_le _ isOrdinal_le_bsubset_sup_bmem
  rw [inf_sup_left]
  apply sup_le
  · grw [inf_comm (isOrdinal u), isOrdinal_inf_bsubset_le_bmem_sup_eq]
    exact le_sup_left
  · grw [inf_le_right]
    exact le_sup_right

end BVSet

namespace ZFSet

theorem isTransitive_toBVSet_of_isTransitive {x : ZFSet.{v}} (hx : x.IsTransitive) :
    isTransitive x.toBVSet = (⊤ : B) := by
  simp only [isTransitive, eq_top_iff]
  rw [IsExtentional.iInf_bmem_toBVSet_himp (by fun_prop), le_iInf_iff]
  intro ⟨y, hy⟩
  simp [toBVSet_bsubset_toBVSet_of_subset (hx _ hy)]

theorem isOrdinal_toBVSet_of_isOrdinal {x : ZFSet.{v}} (hx : x.IsOrdinal) :
    isOrdinal x.toBVSet = (⊤ : B) := by
  simp only [isOrdinal, isTransitive_toBVSet_of_isTransitive hx.isTransitive, top_inf_eq,
    eq_top_iff]
  rw [IsExtentional.iInf_bmem_toBVSet_himp (by fun_prop), le_iInf_iff]
  intro ⟨y, hy⟩
  simp only
  rw [IsExtentional.iInf_bmem_toBVSet_himp (by fun_prop), le_iInf_iff]
  intro ⟨z, hz⟩
  simp only
  rcases (hx.mem hy).mem_trichotomous (hx.mem hz) with h | h | h
  · simp [toBVSet_bmem_toBVSet_of_mem h]
  · simp [h, beq_refl]
  · simp [toBVSet_bmem_toBVSet_of_mem h]

@[simp] theorem isOrdinal_toBVSet (o : Ordinal) :
    isOrdinal o.toZFSet.toBVSet = (⊤ : B) :=
  isOrdinal_toBVSet_of_isOrdinal (isOrdinal_toZFSet o)

end ZFSet

open ZFSet

namespace BVSet

theorem isOrdinal_eq_iSup_beq [Small.{v} B] {u : BVSet.{u, v} B} :
    isOrdinal u = ⨆ o : Ordinal.{v}, u =ᴮ o.toZFSet.toBVSet := by
  apply le_antisymm
  · let f : u.dom → Set Ordinal := fun i => {o : Ordinal | o.toZFSet.toBVSet =ᴮ (i : BVSet B) ≠ ⊥}
    haveI : ∀ i, Small.{v} (f i) := fun i =>
      small_of_injective (f := fun ⟨o, _⟩ => o.toZFSet.toBVSet =ᴮ (i : BVSet B))
        fun ⟨o₁, ho₁⟩ ⟨o₂, ho₂⟩ h => by
          simp only [ne_eq, Set.mem_setOf_eq, f, ← bot_lt_iff_ne_bot] at ho₁ ho₂
          simp only at h
          simp only [Subtype.mk.injEq]
          by_contra h'
          apply ho₁.not_ge
          rw [← inf_idem (_ =ᴮ _)]
          conv_lhs => arg 2; rw [h, beq_symm]
          grw [beq_trans, toBVSet_beq_toBVSet_of_ne (toZFSet_injective.ne h')]
    let o := Order.succ (⨆ i, sSup (f i))
    rw [← inf_top_eq (isOrdinal u), ← isOrdinal_toBVSet]
    refine isOrdinal_trichotomous.trans (sup_le (sup_le ?_ ?_) ?_)
    · rw [bmem_toBVSet, ← (Equiv.subtypeEquivRight (p := (· ∈ o.toZFSet))
        (Set.ext_iff.1 coe_toZFSet)).symm.iSup_comp]
      apply iSup_le
      simp only [Equiv.subtypeEquivRight_symm_apply_coe, Subtype.forall, Set.mem_image, Set.mem_Iio,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro i hi
      exact le_iSup (u =ᴮ ·.toZFSet.toBVSet) i
    · exact le_iSup (u =ᴮ ·.toZFSet.toBVSet) o
    · rw [bmem_def, iSup_le_iff]
      intro i
      suffices o ∉ f i by
        simp only [ne_eq, Set.mem_setOf_eq, not_not, f] at this
        simp [this]
      intro ho
      apply (Order.lt_succ (⨆ i, sSup (f i))).not_ge
      apply le_ciSup_of_le (bddAbove_of_small _) i
      exact le_csSup (bddAbove_of_small _) ho
  · apply iSup_le
    intro o
    grw [← IsExtentional.beq_inf_le' isOrdinal (by fun_prop) o.toZFSet.toBVSet]
    simp [isOrdinal_toBVSet]

theorem IsExtentional.iInf_isOrdinal_himp [Small.{v} B] {f} (hf : IsExtentional f) :
    ⨅ x : BVSet.{u, v} B, isOrdinal x ⇨ f x = ⨅ o : Ordinal.{v}, f o.toZFSet.toBVSet := by
  simp_rw [isOrdinal_eq_iSup_beq, iSup_himp_eq]
  rw [iInf_comm]
  congr! with o
  rw [hf.iInf_beq_himp]

theorem IsExtentional.iSup_isOrdinal_inf [Small.{v} B] {f} (hf : IsExtentional f) :
    ⨆ x : BVSet.{u, v} B, isOrdinal x ⊓ f x = ⨆ o : Ordinal.{v}, f o.toZFSet.toBVSet := by
  simp_rw [isOrdinal_eq_iSup_beq, iSup_inf_eq]
  rw [iSup_comm]
  congr! with o
  rw [hf.iSup_beq_inf]



noncomputable instance : NatCast (BVSet B) := ⟨(ZFSet.toBVSet <| Ordinal.toZFSet ·)⟩

theorem natCast_def (n : ℕ) : (n : BVSet B) = (n : Ordinal).toZFSet.toBVSet := rfl

theorem natCast_beq_natCast {n m : ℕ} :
    (n : BVSet B) =ᴮ m = if n = m then ⊤ else ⊥ := by
  split_ifs with h
  · simp [h]
  · rw [natCast_def, natCast_def, toBVSet_beq_toBVSet_of_ne (by simpa [toZFSet_injective.eq_iff])]

noncomputable def omega : BVSet B := (ω).toZFSet.toBVSet

notation "ωᴮ" => omega

theorem omega_def : (ωᴮ : BVSet B) = (ω).toZFSet.toBVSet := rfl

theorem empty_bmem_omega : ∅ ∈ᴮ ωᴮ = (⊤ : B) := by
  grw [← toBVSet_empty, ← toZFSet_zero]
  exact toBVSet_bmem_toBVSet_of_mem (toZFSet_mem_toZFSet_iff.2 omega0_pos)

theorem le_succ_bmem_omega {u : BVSet B} : u ∈ᴮ ωᴮ ≤ insert u u ∈ᴮ ωᴮ := by
  rw [omega_def, bmem_toBVSet, bmem_toBVSet]
  apply iSup_le
  intro ⟨x, hx⟩
  simp only [mem_toZFSet_iff, lt_omega0, ↓existsAndEq, true_and] at hx
  rcases hx with ⟨n, rfl⟩
  refine le_iSup_of_le ⟨insert (n : Ordinal).toZFSet (n : Ordinal).toZFSet, ?_⟩ ?_
  · rw [← toZFSet_succ, toZFSet_mem_toZFSet_iff, ← add_one_eq_succ, ← Nat.cast_succ, lt_omega0]
    exact ⟨_, rfl⟩
  · simp only
    grw [← IsExtentional.beq_inf_le' (fun y => insert y y =ᴮ toBVSet _) (by fun_prop)
      (n : Ordinal).toZFSet.toBVSet, ← toBVSet_insert]
    simp

theorem omega_bsubset (u : BVSet B) : ∅ ∈ᴮ u ⊓ ⨅ x, x ∈ᴮ u ⇨ insert x x ∈ᴮ u ≤ ωᴮ ⊆ᴮ u := by
  rw [omega_def, toBVSet_bsubset]
  refine le_iInf fun ⟨i, hi⟩ => ?_
  simp only [mem_toZFSet_iff, lt_omega0, ↓existsAndEq, true_and] at hi
  rcases hi with ⟨n, rfl⟩
  simp only
  clear hi
  induction n with
  | zero =>
    simp only [Nat.cast_zero, toZFSet_zero]
    grw [toBVSet_empty, inf_le_left]
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, add_one_eq_succ, toZFSet_succ]
    grw [toBVSet_insert]
    apply le_of_inf_le
    · exact ih
    · grw [inf_le_right (a := ∅ ∈ᴮ u), iInf_le _ (n : Ordinal).toZFSet.toBVSet, himp_inf_le]

theorem natCast_bmem_omega {n : ℕ} : n ∈ᴮ ωᴮ = (⊤ : B) := by
  rw [natCast_def, omega_def, toBVSet_bmem_toBVSet_of_mem (by simp [lt_omega0])]

end BVSet
