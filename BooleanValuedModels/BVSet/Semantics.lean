import BooleanValuedModels.BVSet.Cardinal
import BooleanValuedModels.BVSet.Choice
import BooleanValuedModels.BVSet.Ordinal
import BooleanValuedModels.ModelTheory.BVSemantics
import BooleanValuedModels.ModelTheory.FinLemmas
import BooleanValuedModels.ZFC.Syntax

variable {B : Type u} [CompleteBooleanAlgebra B] [Small.{v} B]

open FirstOrder Language set

namespace BVSet

noncomputable instance : set.BVStructure (BVSet.{u, v} B) B where
  funMap
  | .empty, _ => ∅
  | .insert, v => insert (v 0) (v 1)
  | .sUnion, v => ⋃ᴮ (v 0)
  | .powerset, v => 𝒫ᴮ (v 0)
  | .omega, _ => ωᴮ
  relMap
  | .mem, v => v 0 ∈ᴮ v 1
  eq u v := u =ᴮ v
  eq_refl := eq_refl
  eq_symm := eq_symm 
  eq_trans := eq_trans
  eq_funMap
  | .empty, _, _ => by simp
  | .insert, _, _ => by
    have : IsExtentionalFun₂ (insert : BVSet B → BVSet B → BVSet B) := by
      apply IsExtentionalFun₂.of_isExtentionalFun <;> fun_prop
    exact (this _ _ _ _).trans' <| le_inf (iInf_le _ 0) (iInf_le _ 1)
  | .sUnion, _, _ => by
    have : IsExtentionalFun (⋃ᴮ · : BVSet B → BVSet B) := by fun_prop
    exact (this _ _).trans' <| iInf_le _ 0
  | .powerset, _, _ => by
    have : IsExtentionalFun (𝒫ᴮ · : BVSet B → BVSet B) := by fun_prop
    exact (this _ _).trans' <| iInf_le _ 0
  | .omega, _, _ => by simp
  eq_relMap
  | .mem, _, _ => by
    have : IsExtentional₂ (· ∈ᴮ · : BVSet B → BVSet B → B) := by
      apply IsExtentional₂.of_isExtentional <;> fun_prop
    exact (this _ _ _ _).trans' (inf_le_inf_right _ (le_inf (iInf_le _ 0) (iInf_le _ 1)))

variable {α : Type w} {t t₁ t₂ : set.Term α} {v : α → BVSet.{u, v} B}

@[simp]
theorem bvStructureEq_def (u v : BVSet B) : BVStructure.eq set u v = u =ᴮ v :=
  rfl

@[simp]
theorem bvrealize_empty : (∅ : set.Term α).bvrealize v = ∅ :=
  rfl

@[simp]
theorem bvrealize_insert : (insert t₁ t₂).bvrealize v = insert (t₁.bvrealize v) (t₂.bvrealize v) :=
  rfl

@[simp]
theorem bvrealize_singleton : ({t} : set.Term α).bvrealize v = {t.bvrealize v} :=
  rfl

@[simp]
theorem bvrealize_sUnion : (⋃₀ t).bvrealize v = ⋃ᴮ (t.bvrealize v) :=
  rfl

@[simp]
theorem bvrealize_powerset : (𝒫 t).bvrealize v = 𝒫ᴮ (t.bvrealize v) :=
  rfl

@[simp]
theorem bvrealize_omega : (ω : set.Term α).bvrealize v = ωᴮ :=
  rfl

@[simp]
theorem bvrealize_mem {n} {t₁ t₂ : set.Term (α ⊕ Fin n)} {xs : Fin n → BVSet B} :
    (t₁ ∈' t₂).bvrealize v xs = t₁.bvrealize (Sum.elim v xs) ∈ᴮ t₂.bvrealize (Sum.elim v xs) :=
  rfl

@[simp]
theorem bvrealize_subset {n} {t₁ t₂ : set.Term (α ⊕ Fin n)} {xs : Fin n → BVSet B} :
    (t₁ ⊆' t₂).bvrealize v xs = t₁.bvrealize (Sum.elim v xs) ⊆ᴮ t₂.bvrealize (Sum.elim v xs) := by
  simp [set.subset, Sum.elim_comp_map, ← subset_def']

@[simp]
theorem bvrealize_kpair {t₁ t₂ : set.Term α} :
    (set.kpair t₁ t₂).bvrealize v = kpair (t₁.bvrealize v) (t₂.bvrealize v) := by
  simp [set.kpair, kpair]

@[simp]
theorem bvrealize_isRel {n} {a b f : set.Term (α ⊕ Fin n)} {xs : Fin n → BVSet B} :
    (set.isRel a b f).bvrealize v xs = isRel (a.bvrealize (Sum.elim v xs))
      (b.bvrealize (Sum.elim v xs)) (f.bvrealize (Sum.elim v xs)) := by
  simp [set.isRel, isRel, Sum.elim_comp_map, Fin.snoc_comp_castAdd (m := 0),
    Fin.snoc_comp_castAdd (m := 2)]

@[simp]
theorem bvrealize_isUnique {n} {a b f : set.Term (α ⊕ Fin n)} {xs : Fin n → BVSet B} :
    (set.isUnique a b f).bvrealize v xs = isUnique (a.bvrealize (Sum.elim v xs))
      (b.bvrealize (Sum.elim v xs)) (f.bvrealize (Sum.elim v xs)) := by
  simp [set.isUnique, isUnique, Sum.elim_comp_map, Fin.snoc_comp_castAdd (m := 0),
    Fin.snoc_comp_castAdd (m := 2)]

@[simp]
theorem bvrealize_isTotal {n} {a b f : set.Term (α ⊕ Fin n)} {xs : Fin n → BVSet B} :
    (set.isTotal a b f).bvrealize v xs = isTotal (a.bvrealize (Sum.elim v xs))
      (b.bvrealize (Sum.elim v xs)) (f.bvrealize (Sum.elim v xs)) := by
  simp [set.isTotal, isTotal, Sum.elim_comp_map, Fin.snoc_comp_castAdd (m := 0)]

@[simp]
theorem bvrealize_isFunc {n} {a b f : set.Term (α ⊕ Fin n)} {xs : Fin n → BVSet B} :
    (set.isFunc a b f).bvrealize v xs = isFunc (a.bvrealize (Sum.elim v xs))
      (b.bvrealize (Sum.elim v xs)) (f.bvrealize (Sum.elim v xs)) := by
  simp [set.isFunc, isFunc]

@[simp]
theorem bvrealize_isInjective {n} {a b f : set.Term (α ⊕ Fin n)} {xs : Fin n → BVSet B} :
    (set.isInjective a b f).bvrealize v xs = isInjective (a.bvrealize (Sum.elim v xs))
      (b.bvrealize (Sum.elim v xs)) (f.bvrealize (Sum.elim v xs)) := by
  simp [set.isInjective, isInjective, Sum.elim_comp_map, Fin.snoc_comp_castSucc,
    Fin.snoc_comp_castAdd (m := 0), Fin.snoc_comp_castAdd (m := 2)]

@[simp]
theorem bvrealize_isSurjective {n} {a b f : set.Term (α ⊕ Fin n)} {xs : Fin n → BVSet B} :
    (set.isSurjective a b f).bvrealize v xs = isSurjective (a.bvrealize (Sum.elim v xs))
      (b.bvrealize (Sum.elim v xs)) (f.bvrealize (Sum.elim v xs)) := by
  simp [set.isSurjective, isSurjective, Sum.elim_comp_map, Fin.snoc_comp_castSucc,
    Fin.snoc_comp_castAdd (m := 0)]

@[simp]
theorem bvrealize_cardLE {n} {a b : set.Term (α ⊕ Fin n)} {xs : Fin n → BVSet B} :
    (set.cardLE a b).bvrealize v xs
      = (a.bvrealize (Sum.elim v xs)) ≲ᴮ (b.bvrealize (Sum.elim v xs)) := by
  simp [set.cardLE, cardLE, Sum.elim_comp_map, Fin.snoc_comp_castSucc]

@[simp]
theorem bvrealize_cardLT {n} {a b : set.Term (α ⊕ Fin n)} {xs : Fin n → BVSet B} :
    (set.cardLT a b).bvrealize v xs
      = (a.bvrealize (Sum.elim v xs)) <ᴮ (b.bvrealize (Sum.elim v xs)) := by
  simp [set.cardLT, cardLT]

instance : BVStructure.IsFull set (BVSet B) B where
  exists_eq_iSup φ v xs := by
    apply IsExtentional.exists_eq_iSup
    intro u v
    convert φ.eq_inf_bvrealize_le_bvrealize
    simp only [bvStructureEq_def, eq_refl, iInf_top, le_top, inf_of_le_right]
    refine le_antisymm (le_iInf fun i => ?_) (iInf_le_of_le (Fin.last _) ?_)
    · cases i using Fin.lastCases with simp
    · simp

instance : Theory.BVModel (BVSet B) ZF where
  bvrealize_of_mem
  | _, .extensionality => by
    simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfExtensionality, Nat.reduceAdd,
      Fin.isValue, Function.comp_apply, BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_imp,
      BoundedFormula.bvrealize_iff, bvrealize_mem, Term.bvrealize_var, Sum.elim_inr,
      Fin.snoc_apply_two', Fin.snoc_apply_zero, Fin.snoc_apply_zero', Fin.snoc_apply_one,
      Fin.snoc_apply_one', BoundedFormula.bvrealize_bdEqual, bvStructureEq_def, iInf_eq_top,
      himp_eq_top_iff]
    intro u v
    simp_rw [bihimp_def, iInf_inf_eq, ← subset_def', inf_comm, ← eq_def]
    rfl
  | _, .empty => by
    simp [axiomOfEmpty, Sentence.bvrealize, Formula.bvrealize]
  | _, .pairing => by
    simp [axiomOfPairing, Sentence.bvrealize, Formula.bvrealize]
  | _, .union => by
    simp [axiomOfUnion, Sentence.bvrealize, Formula.bvrealize]
  | _, .powerset => by
    simp [axiomOfPowerset, Sentence.bvrealize, Formula.bvrealize]
  | _, .infinity => by
    simp +contextual [axiomOfInfinity, Sentence.bvrealize, Formula.bvrealize, empty_mem_omega,
      le_succ_mem_omega, omega_subset]
  | _, .regularity => by
    simp [axiomOfRegularity, Sentence.bvrealize, Formula.bvrealize, ← ne_empty, ← mem_inter,
      regularity]
  | _, .replacement φ => by
    simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfReplacement, Nat.reduceAdd,
      Fin.isValue, Function.comp_apply, Nat.succ_eq_add_one, Matrix.empty_eq,
      BoundedFormula.bvrealize_iAlls, BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_imp,
      bvrealize_mem, Term.bvrealize_var, Sum.elim_inr, Fin.snoc_apply_one', Fin.snoc_apply_zero,
      Fin.snoc_apply_zero', BoundedFormula.bvrealize_inf, BoundedFormula.bvrealize_ex,
      BoundedFormula.bvrealize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
      Function.comp_id, Sum.elim_comp_map, Sum.elim_comp_inr, Matrix.comp_vecCons,
      Fin.snoc_apply_one, Fin.snoc_apply_two', Fin.snoc_apply_two, Fin.snoc_apply_three',
      BoundedFormula.bvrealize_bdEqual, bvStructureEq_def, BoundedFormula.bvrealize_iff,
      iInf_eq_top, himp_eq_top_iff]
    intro v a
    let f := fun x y => BoundedFormula.bvrealize φ (Sum.elim v ![x, y]) ![]
    convert_to ⨅ x, x ∈ᴮ a ⇨ (⨆ y, f x y) ⊓ (⨅ y₁, ⨅ y₂, f x y₁ ⇨ f x y₂ ⇨ y₁ =ᴮ y₂) ≤
      ⨆ b, ⨅ y, bihimp (y ∈ᴮ b) (⨆ x, x ∈ᴮ a ⊓ f x y)
    have hf : IsExtentional₂ f := by
      intro x₁ x₂ y₁ y₂
      convert BoundedFormula.eq_inf_bvrealize_le_bvrealize using 2
      simp [iInf_sum, iInf_fin_succ]
    -- this uses AC
    let g := fun x => Classical.choose (IsExtentional.exists_eq_iSup (hf.left x))
    have hg : ∀ x, f x (g x) = ⨆ y, f x y := fun x =>
      Classical.choose_spec (IsExtentional.exists_eq_iSup (hf.left x))
    apply le_iSup_of_le (a.replace g)
    refine le_iInf fun y => ?_
    rw [mem_replace', bihimp_def, IsExtentional.iSup_mem_inf (hf.right y)]
    apply le_inf
    · rw [le_himp_iff, inf_iSup_eq]
      refine iSup_le fun i => le_iSup_of_le i (le_inf ?_ ?_)
      · grw [inf_le_right, inf_le_left]
      · grw [iInf_le _ (i : BVSet B), ← inf_assoc, val_le_dom_mem, himp_inf_le, ← hg, iInf_le _ y,
          iInf_le _ (g i), inf_assoc, himp_inf_le, inf_himp_le]
    · rw [le_himp_iff, inf_iSup_eq]
      refine iSup_le fun i => le_iSup_of_le i (le_inf ?_ ?_)
      · grw [inf_le_right, inf_le_left]
      · rw [← inf_assoc]
        apply IsExtentional.inf_eq_le_of_le (by fun_prop) (hf.left _) y
        rw [hg]
        grw [iInf_le _ (i : BVSet B), val_le_dom_mem, himp_inf_le, inf_le_left]

instance : Theory.BVModel (BVSet B) ZFC where
  bvrealize_of_mem φ hφ := by
    simp only [Theory.zfc, Set.union_singleton, Set.mem_insert_iff] at hφ
    rcases hφ with rfl | hφ
    · simp [axiomOfChoice, Sentence.bvrealize, Formula.bvrealize, exists_choice_func]
    · exact Theory.BVModel.bvrealize_of_mem φ hφ
