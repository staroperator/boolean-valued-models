module

public import BooleanValuedModels.BVSet.Cardinal
public import BooleanValuedModels.BVSet.Choice
public import BooleanValuedModels.BVSet.Ordinal
public import BooleanValuedModels.ModelTheory.BVSemantics
public import BooleanValuedModels.ZFC.Syntax

import BooleanValuedModels.ModelTheory.FinLemmas

@[expose] public section

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
  beq u v := u =ᴮ v
  beq_refl := beq_refl
  beq_symm := beq_symm
  beq_trans := beq_trans
  beq_funMap
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
  beq_relMap
  | .mem, _, _ => by
    have : IsExtentional₂ (· ∈ᴮ · : BVSet B → BVSet B → B) := by
      apply IsExtentional₂.of_isExtentional <;> fun_prop
    exact (this _ _ _ _).trans' (inf_le_inf_right _ (le_inf (iInf_le _ 0) (iInf_le _ 1)))

variable {α : Type w} {t t₁ t₂ : set.Term α} {v : α → BVSet.{u, v} B}

@[simp]
theorem bvStructureEq_def (u v : BVSet B) : BVStructure.beq set u v = u =ᴮ v :=
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
  simp [set.subset, Sum.elim_comp_map, ← bsubset_def']

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
    convert φ.beq_inf_bvrealize_le_bvrealize
    simp only [bvStructureEq_def, beq_refl, iInf_top, le_top, inf_of_le_right]
    refine le_antisymm (le_iInf fun i => ?_) (iInf_le_of_le (Fin.last _) ?_)
    · cases i using Fin.lastCases with simp
    · simp

@[simp]
theorem bvrealize_axiomOfExtensionality : axiomOfExtensionality.bvrealize (BVSet B) = ⊤ := by
  simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfExtensionality, Nat.reduceAdd,
    Fin.isValue, Function.comp_apply, BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_imp,
    BoundedFormula.bvrealize_iff, bvrealize_mem, Term.bvrealize_var, Sum.elim_inr,
    Fin.snoc_apply_two', Fin.snoc_apply_zero, Fin.snoc_apply_zero', Fin.snoc_apply_one,
    Fin.snoc_apply_one', BoundedFormula.bvrealize_bdEqual, bvStructureEq_def, iInf_eq_top,
    himp_eq_top_iff]
  intro u v
  simp_rw [bihimp_def, iInf_inf_eq, ← bsubset_def', inf_comm, ← beq_def]
  rfl

@[simp]
theorem bvrealize_axiomOfEmpty : axiomOfEmpty.bvrealize (BVSet B) = ⊤ := by
  simp [axiomOfEmpty, Sentence.bvrealize, Formula.bvrealize]

@[simp]
theorem bvrealize_axiomOfPairing : axiomOfPairing.bvrealize (BVSet B) = ⊤ := by
  simp [axiomOfPairing, Sentence.bvrealize, Formula.bvrealize]

@[simp]
theorem bvrealize_axiomOfUnion : axiomOfUnion.bvrealize (BVSet B) = ⊤ := by
  simp [axiomOfUnion, Sentence.bvrealize, Formula.bvrealize]

@[simp]
theorem bvrealize_axiomOfPowerset : axiomOfPowerset.bvrealize (BVSet B) = ⊤ := by
  simp [axiomOfPowerset, Sentence.bvrealize, Formula.bvrealize]

@[simp]
theorem bvrealize_axiomOfInfinity : axiomOfInfinity.bvrealize (BVSet B) = ⊤ := by
  simp +contextual [axiomOfInfinity, Sentence.bvrealize, Formula.bvrealize, empty_bmem_omega,
    le_succ_bmem_omega, omega_bsubset]

@[simp]
theorem bvrealize_axiomOfRegularity : axiomOfRegularity.bvrealize (BVSet B) = ⊤ := by
  simp [axiomOfRegularity, Sentence.bvrealize, Formula.bvrealize, ← bne_empty, ← bmem_inter,
    regularity]

theorem IsExtentional.bvrealize {α : Type*} {n} {φ : set.BoundedFormula α n}
    {v : BVSet B → α → BVSet B} {xs : BVSet B → Fin n → BVSet B}
    (hv : ∀ i, IsExtentionalFun fun x => v x i) (hxs : ∀ i, IsExtentionalFun fun x => xs x i) :
    IsExtentional fun x => φ.bvrealize (v x) (xs x) := by
  intro x y
  simp only
  grw [← φ.beq_inf_bvrealize_le_bvrealize (v := v x) (xs := xs x) (ys := xs y)]
  gcongr
  simp only [bvStructureEq_def, le_inf_iff, le_iInf_iff]
  constructor
  · intro i
    apply hv i
  · intro i
    apply hxs i

@[simp]
theorem bvrealize_axiomOfSeparation {α : Type*} [Finite α] {φ : set.Formula (α ⊕ Fin 1)} :
    (axiomOfSeparation φ).bvrealize (BVSet B) = ⊤ := by
  simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfSeparation, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, Nat.succ_eq_add_one, Matrix.empty_eq, BoundedFormula.bvrealize_iAlls,
    BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_ex, BoundedFormula.bvrealize_iff,
    bvrealize_mem, Term.bvrealize_var, Sum.elim_inr, Fin.snoc_apply_two', Fin.snoc_apply_one,
    Fin.snoc_apply_one', BoundedFormula.bvrealize_inf, Fin.snoc_apply_zero, Fin.snoc_apply_zero',
    BoundedFormula.bvrealize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
    Function.comp_id, Sum.elim_comp_map, Sum.elim_comp_inr, Matrix.comp_vecCons, iInf_eq_top]
  intro a u
  rw [eq_top_iff]
  apply le_iSup_of_le (u.sep fun x => BoundedFormula.bvrealize φ (Sum.elim a ![x]) ![])
  rw [le_iInf_iff]
  intro x
  rw [bmem_sep']
  · simp
  · apply IsExtentional.bvrealize
    · rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_fin_one]
        <;> fun_prop
    · simp

@[simp]
theorem bvrealize_axiomOfCollection {α : Type*} [Finite α] {φ : set.Formula (α ⊕ Fin 2)} :
    (axiomOfCollection φ).bvrealize (BVSet B) = ⊤ := by
  simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfCollection, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, Nat.succ_eq_add_one, Matrix.empty_eq, BoundedFormula.bvrealize_iAlls,
    BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_imp, bvrealize_mem, Term.bvrealize_var,
    Sum.elim_inr, Fin.snoc_apply_one', Fin.snoc_apply_zero, Fin.snoc_apply_zero',
    BoundedFormula.bvrealize_ex, BoundedFormula.bvrealize_relabel, Nat.add_zero, Fin.castAdd_zero,
    Fin.cast_refl, Function.comp_id, Sum.elim_comp_map, Sum.elim_comp_inr, Matrix.comp_vecCons,
    Fin.snoc_apply_one, Fin.snoc_apply_two', BoundedFormula.bvrealize_inf, Fin.snoc_apply_three',
    Fin.snoc_apply_two, iInf_eq_top, himp_eq_top_iff]
  intro a u
  let s : u.dom → Set B := fun x => {b | ∃ y, φ.bvrealize (Sum.elim a ![x, y]) = b}
  have : ∀ x : u.dom, ∀ b : s x, ∃ y, φ.bvrealize (Sum.elim a ![x, y]) = b := by simp [s]
  choose f hf using this
  simp only [Formula.bvrealize, Matrix.empty_eq] at hf
  let v := mkI (Σ x : u.dom, s x) (Sigma.uncurry f) fun _ => ⊤
  apply le_iSup_of_le v
  nth_rw 2 [IsExtentional.iInf_bmem_himp]
  on_goal 2 =>
    refine .iSup fun _ => .inf (by fun_prop) ?_
    apply IsExtentional.bvrealize
    · simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, Fin.forall_fin_two, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      refine ⟨?_, ?_, ?_⟩ <;> fun_prop
    · simp
  refine le_iInf fun x => ?_
  grw [le_himp_iff, val_le_bmem, iInf_le _ x.1, himp_inf_le]
  refine iSup_le fun y => ?_
  let b := φ.bvrealize (Sum.elim a ![x, y])
  have hb : b ∈ s x := by simp [s, b]
  refine le_iSup_of_le (f x ⟨b, hb⟩) (le_inf ?_ ?_)
  · simp only [bmem_mkI, le_top, inf_of_le_right, v]
    apply le_iSup_of_le ⟨x, b, hb⟩
    simp [Sigma.uncurry]
  · rw [hf x ⟨b, hb⟩]
    rfl

instance : BVSet B ⊨ᵇᵛ ZF where
  bvrealize_of_mem φ hφ := by
    simp only [Theory.zf, Set.mem_setOf_eq] at hφ
    cases hφ <;> simp

@[simp]
theorem bvrealize_axiomOfChoice : axiomOfChoice.bvrealize (BVSet B) = ⊤ := by
  simp [axiomOfChoice, Sentence.bvrealize, Formula.bvrealize, exists_choice_func]

instance : Theory.BVModel (BVSet B) ZFC where
  bvrealize_of_mem φ hφ := by
    simp only [Theory.zfc, Set.union_singleton, Set.mem_insert_iff] at hφ
    rcases hφ with rfl | hφ
    · simp
    · exact Theory.BVModel.bvrealize_of_mem φ hφ

end BVSet
