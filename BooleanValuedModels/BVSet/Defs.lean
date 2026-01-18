import BooleanValuedModels.BooleanAlgebra.Lemmas
import Mathlib.Logic.Small.Defs
import Mathlib.Tactic.FunProp

universe u v

@[pp_with_univ]
inductive BVSet (B : Type u)
| mk (ι : Type v) (dom : ι → BVSet B) (val : ι → B)

namespace BVSet

variable {B : Type u} {u v w : BVSet B}

def Index : BVSet B → Type v
| mk ι _ _ => ι

@[simp] theorem Index_mk {ι : Type v} {dom : ι → BVSet B} {val} : (mk ι dom val).Index = ι := rfl

instance : CoeSort (BVSet B) (Type v) := ⟨Index⟩

def dom : (x : BVSet B) → x.Index → BVSet B
| mk _ dom _ => dom

@[simp] theorem dom_mk {ι : Type v} {dom : ι → BVSet B} {val} : (mk ι dom val).dom = dom := rfl

instance {x : BVSet B} : CoeOut x.Index (BVSet B) := ⟨x.dom⟩

def val : (x : BVSet B) → x.Index → B
| mk _ _ val => val

@[simp] theorem val_mk {ι : Type v} {dom : ι → BVSet B} {val} : (mk ι dom val).val = val := rfl

instance : CoeFun (BVSet B) (fun x => x → B) := ⟨val⟩

@[elab_as_elim] protected theorem induction {motive : BVSet B → Prop} (u : BVSet B)
    (h : ∀ u, (∀ x : u.Index, motive x) → motive u) : motive u := by
  induction u with | _ u udom uval ih
  exact h _ ih

variable [CompleteBooleanAlgebra B]

def eq : BVSet.{u, v} B → BVSet.{u, v} B → B
| ⟨u, udom, uval⟩, ⟨v, vdom, vval⟩ =>
  (⨅ x : u, uval x ⇨ ⨆ y : v, vval y ⊓ (udom x).eq (vdom y)) ⊓
    ⨅ y : v, vval y ⇨ ⨆ x : u, uval x ⊓ (udom x).eq (vdom y)

infix:70 " =ᴮ " => eq
notation:70 u " ≠ᴮ " v:70 => (u =ᴮ v)ᶜ

def mem : BVSet.{u, v} B → BVSet.{u, v} B → B
| u, v => ⨆ x : v, v x ⊓ u.eq x

infix:70 " ∈ᴮ " => mem
notation:70 u " ∉ᴮ " v:70 => (u ∈ᴮ v)ᶜ

def subset : BVSet.{u, v} B → BVSet.{u, v} B → B
| u, v => ⨅ x : u, u x ⇨ (x : BVSet B).mem v

infix:70 " ⊆ᴮ " => subset

@[simp] theorem eq_refl (u : BVSet B) : u =ᴮ u = ⊤ := by
  rcases u with ⟨u, udom, uval⟩
  rw [BVSet.eq]
  simp only [inf_eq_top_iff, iInf_eq_top, himp_eq_top_iff]
  constructor <;> intro x <;> apply le_iSup_of_le x <;> simp [eq_refl]

theorem eq_symm (u v : BVSet B) : u =ᴮ v = v =ᴮ u := by
  rcases u with ⟨u, udom, uval⟩
  rcases v with ⟨v, vdom, vval⟩
  rw [BVSet.eq, BVSet.eq]
  conv_lhs => rw [inf_comm]
  congr! 7 <;> apply eq_symm

theorem mem_def : u ∈ᴮ v = ⨆ x : v, v x ⊓ u =ᴮ x := rfl

theorem subset_def : u ⊆ᴮ v = ⨅ x : u, u x ⇨ x ∈ᴮ v := rfl

theorem eq_def : u =ᴮ v = u ⊆ᴮ v ⊓ v ⊆ᴮ u := by
  rcases u with ⟨u, udom, uval⟩
  rcases v with ⟨v, vdom, vval⟩
  rw [BVSet.eq, BVSet.subset, BVSet.subset]
  simp only [val_mk, dom_mk, mem_def]
  conv_rhs => enter [2, 1, x, 2, 1, y]; rw [eq_symm]
  rfl

theorem eq_le_subset : u =ᴮ v ≤ u ⊆ᴮ v := by
  grw [eq_def, inf_le_left]

theorem eq_le_subset' : u =ᴮ v ≤ v ⊆ᴮ u := by
  grw [eq_def, inf_le_right]

lemma eq_inf_val_le_mem {x : u} : u =ᴮ v ⊓ u x ≤ x ∈ᴮ v := by
  rw [eq_def, subset_def]
  apply (inf_le_inf_right _ (inf_le_of_left_le (iInf_le _ x))).trans
  simp

lemma eq_inf_val_le_mem' {x : v} : u =ᴮ v ⊓ v x ≤ x ∈ᴮ u := by
  rw [eq_symm]
  exact eq_inf_val_le_mem

theorem eq_trans (u v w : BVSet B) : u =ᴮ v ⊓ v =ᴮ w ≤ u =ᴮ w := by
  rcases u with ⟨u, udom, uval⟩
  rcases v with ⟨v, vdom, vval⟩
  rcases w with ⟨w, wdom, wval⟩
  conv_rhs => rw [eq_def]
  simp only [subset_def, le_inf_iff, le_iInf_iff, le_himp_iff, Index_mk, dom_mk, val_mk]
  constructor
  · intro x
    rw [inf_right_comm]
    apply (inf_le_inf_right _ eq_inf_val_le_mem).trans
    rw [mem_def, iSup_inf_eq]
    simp only [Index_mk, val_mk, dom_mk, iSup_le_iff]
    intro y
    rw [inf_right_comm, inf_comm (vval y)]
    apply (inf_le_inf_right _ eq_inf_val_le_mem).trans
    simp only [dom_mk, mem_def, Index_mk, val_mk]
    rw [iSup_inf_eq]
    refine iSup_mono fun z => ?_
    rw [inf_assoc, inf_comm (vdom y =ᴮ wdom z)]
    apply inf_le_inf_left
    apply eq_trans
  · intro z
    rw [inf_assoc]
    apply (inf_le_inf_left _ eq_inf_val_le_mem').trans
    rw [mem_def, inf_iSup_eq]
    simp only [Index_mk, val_mk, dom_mk, iSup_le_iff]
    intro y
    rw [← inf_assoc]
    apply (inf_le_inf_right _ eq_inf_val_le_mem').trans
    simp only [dom_mk, mem_def, Index_mk, val_mk]
    rw [iSup_inf_eq]
    refine iSup_mono fun x => ?_
    rw [inf_assoc, inf_comm (vdom y =ᴮ udom x)]
    apply inf_le_inf_left
    apply eq_trans

theorem eq_trans' (u v w : BVSet B) : v =ᴮ w ⊓ u =ᴮ v ≤ u =ᴮ w := by
  rw [inf_comm]
  apply eq_trans

theorem val_le_dom_mem {x : u} : u x ≤ x ∈ᴮ u := by
  rw [mem_def]
  apply le_iSup_of_le x
  simp

theorem mem_congr_left (u v w : BVSet B) : u =ᴮ v ⊓ u ∈ᴮ w ≤ v ∈ᴮ w := by
  rw [mem_def, inf_iSup_eq, mem_def]
  refine iSup_mono fun z => ?_
  rw [inf_left_comm, eq_symm u]
  exact inf_le_inf_left _ <| eq_trans _ _ _

theorem mem_congr_left' (u v w : BVSet B) : u =ᴮ v ⊓ v ∈ᴮ w ≤ u ∈ᴮ w := by
  rw [eq_symm]
  apply mem_congr_left

theorem mem_congr_right (u v w : BVSet B) : v =ᴮ w ⊓ u ∈ᴮ v ≤ u ∈ᴮ w := by
  rw [mem_def, inf_iSup_eq, iSup_le_iff]
  intro y
  rw [← inf_assoc]
  apply (inf_le_inf_right _ eq_inf_val_le_mem).trans
  rw [inf_comm, eq_symm]
  apply mem_congr_left

theorem mem_congr_right' (u v w : BVSet B) : v =ᴮ w ⊓ u ∈ᴮ w ≤ u ∈ᴮ v := by
  rw [eq_symm]
  apply mem_congr_right



@[fun_prop] def IsExtentionalFun (f : BVSet.{u, v} B → BVSet.{u, v} B) :=
  ∀ x y, x =ᴮ y ≤ f x =ᴮ f y

theorem IsExtentionalFun.eq_le_eq (f) (hf : IsExtentionalFun f) (u v : BVSet B) :
    u =ᴮ v ≤ f u =ᴮ f v := hf u v

@[fun_prop] theorem IsExtentionalFun.id : IsExtentionalFun fun x : BVSet B => x :=
  fun x y => by simp

@[fun_prop] theorem IsExtentionalFun.const {a : BVSet B} : IsExtentionalFun fun _ => a :=
  fun x y => by simp

@[fun_prop] theorem IsExtentionalFun.comp {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentionalFun (f ∘ g) :=
  fun x y => (hg x y).trans (hf _ _)

@[fun_prop] def IsExtentional (f : BVSet B → B) :=
  ∀ x y, x =ᴮ y ⊓ f x ≤ f y

theorem IsExtentional.eq_inf_le (f) (hf : IsExtentional f) (u v : BVSet B) :
    u =ᴮ v ⊓ f u ≤ f v := hf u v

theorem IsExtentional.eq_inf_le' (f) (hf : IsExtentional f) (u v : BVSet B) :
    v =ᴮ u ⊓ f u ≤ f v := by
  grw [eq_symm, hf.eq_inf_le]

theorem IsExtentional.inf_eq_le (f) (hf : IsExtentional f) (u v : BVSet B) :
    f u ⊓ u =ᴮ v ≤ f v := by
  grw [inf_comm, hf.eq_inf_le]

theorem IsExtentional.inf_eq_le' (f) (hf : IsExtentional f) (u v : BVSet B) :
    f u ⊓ v =ᴮ u ≤ f v := by
  grw [inf_comm, hf.eq_inf_le']

@[fun_prop] theorem IsExtentional.const {a : B} : IsExtentional fun _ => a :=
  fun x y => by simp

@[fun_prop] theorem IsExtentional.comp {f : BVSet B → B} {g : BVSet B → BVSet B}
    (hf : IsExtentional f) (hg : IsExtentionalFun g) : IsExtentional (f ∘ g) :=
  fun x y => by grw [hg x y]; apply hf

@[fun_prop] theorem IsExtentional.eq {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentional fun x => f x =ᴮ g x := by
  intro x y
  simp only
  rw [← inf_idem (x =ᴮ y), inf_assoc]
  nth_grw 1 [hg x y, hf x y]
  grw [eq_symm (f x) (g x), eq_trans', eq_symm (g x) (f y), eq_trans']

@[fun_prop] theorem IsExtentional.mem {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentional fun x => f x ∈ᴮ g x := by
  intro x y
  simp only
  rw [← inf_idem (x =ᴮ y), inf_assoc]
  nth_grw 1 [hg x y, hf x y]
  grw [mem_congr_left, mem_congr_right]

@[fun_prop] theorem IsExtentional.sup {f g : BVSet B → B}
    (hf : IsExtentional f) (hg : IsExtentional g) : IsExtentional fun x => f x ⊔ g x := by
  intro x y
  simp only [inf_sup_left, sup_le_iff]
  constructor
  · exact (hf x y).trans le_sup_left
  · exact (hg x y).trans le_sup_right

@[fun_prop] theorem IsExtentional.inf {f g : BVSet B → B}
    (hf : IsExtentional f) (hg : IsExtentional g) : IsExtentional fun x => f x ⊓ g x := by
  intro x y
  simp only [le_inf_iff]
  constructor
  · nth_grw 2 [inf_le_left]
    apply hf
  · nth_grw 2 [inf_le_right]
    apply hg

@[fun_prop] theorem IsExtentional.compl {f : BVSet B → B} (hf : IsExtentional f) :
    IsExtentional fun x => (f x)ᶜ := by
  intro x y
  simp only
  rw [← le_himp_iff, compl_himp_compl, le_himp_iff, eq_symm]
  apply hf

@[fun_prop] theorem IsExtentional.himp {f g : BVSet B → B}
    (hf : IsExtentional f) (hg : IsExtentional g) : IsExtentional fun x => f x ⇨ g x := by
  simp_rw [himp_eq]
  fun_prop

@[fun_prop] protected theorem IsExtentional.iInf {α : Sort*} {f : α → BVSet B → B}
    (hf : ∀ x, IsExtentional (f x)) : IsExtentional fun x => ⨅ y, f y x := by
  intro x y
  simp only [le_iInf_iff]
  intro z
  grw [iInf_le _ z]
  apply hf

theorem IsExtentional.inf_eq_le_of_le {f g} (hf : IsExtentional f) (hg : IsExtentional g)
    (u v : BVSet B) (h : f v ≤ g v) : f u ⊓ u =ᴮ v ≤ g u := by
  rw [← himp_eq_top_iff] at h
  grw [← le_himp_iff', ← inf_top_eq (u =ᴮ v), ← h]
  apply eq_inf_le'
  fun_prop

theorem IsExtentional.inf_eq_le_of_le' {f g} (hf : IsExtentional f) (hg : IsExtentional g)
    (u v : BVSet B) (h : f u ≤ g u) : f v ⊓ u =ᴮ v ≤ g v := by
  rw [eq_symm]
  exact hf.inf_eq_le_of_le hg v u h

@[fun_prop] protected theorem IsExtentional.iSup {α : Sort*} {f : α → BVSet B → B}
    (hf : ∀ x, IsExtentional (f x)) : IsExtentional fun x => ⨆ y, f y x := by
  intro x y
  simp only [inf_iSup_eq, iSup_le_iff]
  intro z
  exact (hf _ _ _).trans <| le_iSup (fun z => f z y) z

theorem IsExtentional.iSup_eq_inf {f : BVSet B → B} (hf : IsExtentional f) :
    ⨆ x : BVSet B, x =ᴮ u ⊓ f x = f u := by
  apply le_antisymm
  · rw [iSup_le_iff]
    intro x
    apply hf
  · apply le_iSup_of_le u
    simp

theorem IsExtentional.iInf_eq_himp {f : BVSet B → B} (hf : IsExtentional f) :
    ⨅ x : BVSet B, x =ᴮ u ⇨ f x = f u := by
  apply le_antisymm
  · apply iInf_le_of_le u
    simp
  · rw [le_iInf_iff]
    intro v
    rw [le_himp_iff', BVSet.eq_symm]
    apply hf

theorem IsExtentional.iSup_mem_inf {f : BVSet B → B} (hf : IsExtentional f) :
    ⨆ x : BVSet B, x ∈ᴮ u ⊓ f x = ⨆ x : u, u x ⊓ f x := by
  simp_rw [BVSet.mem_def, iSup_inf_eq]
  rw [iSup_comm]
  simp_rw [inf_assoc, ← fun j => inf_iSup_eq (u j) fun i => i =ᴮ j ⊓ f i, hf.iSup_eq_inf]

theorem IsExtentional.iInf_mem_himp {f : BVSet B → B} (hf : IsExtentional f) :
    ⨅ x : BVSet B, x ∈ᴮ u ⇨ f x = ⨅ x : u, u x ⇨ f x := by
  simp_rw [BVSet.mem_def, iSup_himp_eq]
  rw [iInf_comm]
  simp_rw [← himp_himp, ← himp_iInf_eq, hf.iInf_eq_himp]

theorem mem_def' : u ∈ᴮ v = ⨆ x, x ∈ᴮ v ⊓ x =ᴮ u := by
  rw [mem_def, IsExtentional.iSup_mem_inf (by fun_prop)]
  simp_rw [eq_symm]

theorem subset_def' : u ⊆ᴮ v = ⨅ x : BVSet B, x ∈ᴮ u ⇨ x ∈ᴮ v := by
  rw [subset_def, IsExtentional.iInf_mem_himp (by fun_prop)]

@[fun_prop] theorem IsExtentional.subset {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentional fun x => f x ⊆ᴮ g x := by
  simp only [subset_def']
  refine .iInf fun x => ?_
  fun_prop

theorem subset_congr_left : u =ᴮ v ⊓ u ⊆ᴮ w ≤ v ⊆ᴮ w := by
  have : IsExtentional fun x => x ⊆ᴮ w := by fun_prop
  apply this

theorem subset_congr_right : v =ᴮ w ⊓ u ⊆ᴮ v ≤ u ⊆ᴮ w := by
  have : IsExtentional fun x => u ⊆ᴮ x := by fun_prop
  apply this

theorem IsExtentionalFun.of_isExtentional {f : BVSet B → BVSet B}
    (h : ∀ y, IsExtentional fun x => y ∈ᴮ f x) : IsExtentionalFun f := by
  intro x y
  conv_rhs => rw [BVSet.eq_def]
  simp only [subset_def', le_inf_iff, le_iInf_iff, le_himp_iff]
  constructor
  · intro z
    apply h
  · intro z
    rw [eq_symm]
    apply h

theorem mem_inf_subset_le (u v w : BVSet B) : u ∈ᴮ v ⊓ v ⊆ᴮ w ≤ u ∈ᴮ w := by
  grw [subset_def', iInf_le _ u, inf_himp_le]

theorem subset_inf_mem_le (u v w : BVSet B) : v ⊆ᴮ w ⊓ u ∈ᴮ v ≤ u ∈ᴮ w := by
  rw [inf_comm]
  apply mem_inf_subset_le

theorem subset_refl (u) : u ⊆ᴮ u = (⊤ : B) := by
  simp [subset_def']

theorem subset_antisymm (u v : BVSet B) : u ⊆ᴮ v ⊓ v ⊆ᴮ u ≤ u =ᴮ v := by
  rw [eq_def]

theorem subset_trans (u v w : BVSet B) : u ⊆ᴮ v ⊓ v ⊆ᴮ w ≤ u ⊆ᴮ w := by
  simp only [subset_def', le_iInf_iff, le_himp_iff]
  intro x
  grw [iInf_le _ x, iInf_le _ x, inf_right_comm, himp_inf_le, inf_himp_le]

theorem subset_trans' (u v w : BVSet B) : v ⊆ᴮ w ⊓ u ⊆ᴮ v ≤ u ⊆ᴮ w := by
  rw [inf_comm]
  apply subset_trans

@[fun_prop] def IsExtentional₂ (f : BVSet B → BVSet B → B) :=
  ∀ x₁ x₂ y₁ y₂, x₁ =ᴮ x₂ ⊓ y₁ =ᴮ y₂ ⊓ f x₁ y₁ ≤ f x₂ y₂

theorem isExtentional₂_iff {f : BVSet B → BVSet B → B} :
    IsExtentional₂ f ↔ (∀ x, IsExtentional (f x)) ∧ ∀ y, IsExtentional fun x => f x y := by
  refine ⟨fun hf => ⟨fun x y₁ y₂ => ?_, fun y x₁ x₂ => ?_⟩, fun ⟨hf₁, hf₂⟩ x₁ x₂ y₁ y₂ => ?_⟩
  · simpa using hf x x y₁ y₂
  · simpa using hf x₁ x₂ y y
  · grw [inf_assoc, hf₁ x₁ y₁ y₂]
    apply hf₂

@[fun_prop] theorem IsExtentional₂.of_isExtentional {f : BVSet B → BVSet B → B}
    (hf₁ : ∀ x, IsExtentional (f x)) (hf₂ : ∀ y, IsExtentional fun x => f x y) :
    IsExtentional₂ f :=
  isExtentional₂_iff.2 ⟨hf₁, hf₂⟩

theorem IsExtentional₂.left {f : BVSet B → BVSet B → B} (x)
    (hf : IsExtentional₂ f) : IsExtentional (f x) :=
  (isExtentional₂_iff.1 hf).1 x

theorem IsExtentional₂.right {f : BVSet B → BVSet B → B} (y)
    (hf : IsExtentional₂ f) : IsExtentional fun x => f x y :=
  (isExtentional₂_iff.1 hf).2 y

@[fun_prop] def IsExtentionalFun₂ (f : BVSet.{u, v} B → BVSet.{u, v} B → BVSet.{u, v} B) :=
  ∀ x₁ x₂ y₁ y₂, x₁ =ᴮ x₂ ⊓ y₁ =ᴮ y₂ ≤ f x₁ y₁ =ᴮ f x₂ y₂

theorem isExtentionalFun₂_iff {f : BVSet B → BVSet B → BVSet B} :
    IsExtentionalFun₂ f ↔ (∀ x, IsExtentionalFun (f x)) ∧ ∀ y, IsExtentionalFun fun x => f x y := by
  refine ⟨fun hf => ⟨fun x y₁ y₂ => ?_, fun y x₁ x₂ => ?_⟩, fun ⟨hf₁, hf₂⟩ x₁ x₂ y₁ y₂ => ?_⟩
  · simpa using hf x x y₁ y₂
  · simpa using hf x₁ x₂ y y
  · grw [hf₁ x₁ y₁ y₂, hf₂ y₂ x₁ x₂]
    simp only
    grw [eq_trans']

@[fun_prop] theorem IsExtentionalFun₂.of_isExtentionalFun {f : BVSet B → BVSet B → BVSet B}
    (hf₁ : ∀ x, IsExtentionalFun (f x)) (hf₂ : ∀ y, IsExtentionalFun fun x => f x y) :
    IsExtentionalFun₂ f :=
  isExtentionalFun₂_iff.2 ⟨hf₁, hf₂⟩

theorem IsExtentionalFun₂.left {f : BVSet B → BVSet B → BVSet B} (x)
    (hf : IsExtentionalFun₂ f) : IsExtentionalFun (f x) :=
  (isExtentionalFun₂_iff.1 hf).1 x

theorem IsExtentionalFun₂.right {f : BVSet B → BVSet B → BVSet B} (y)
    (hf : IsExtentionalFun₂ f) : IsExtentionalFun fun x => f x y :=
  (isExtentionalFun₂_iff.1 hf).2 y



instance : Setoid (BVSet B) where
  r u v := u =ᴮ v = ⊤
  iseqv.refl u := by simp
  iseqv.symm h := by simpa [eq_symm]
  iseqv.trans h₁ h₂ := by
    grw [eq_top_iff, ← eq_trans, h₁, h₂, top_inf_eq]

theorem equiv_def : u ≈ v ↔ u =ᴮ v = ⊤ := Iff.rfl

@[refl] theorem equiv_refl (u : BVSet B) : u ≈ u := IsEquiv.toIsPreorder.refl _

@[symm] theorem equiv_symm : u ≈ v → v ≈ u := IsEquiv.toIsSymm.symm _ _

@[trans] theorem equiv_trans : u ≈ v → v ≈ w → u ≈ w := IsEquiv.toIsPreorder.trans _ _ _

theorem ext (h : ∀ x, x ∈ᴮ u = x ∈ᴮ v) : u ≈ v := by
  rw [equiv_def]
  simp [eq_def, subset_def', h]

theorem IsExtentionalFun.congr {f} (hf : IsExtentionalFun f) (h : u ≈ v) : f u ≈ f v := by
  grw [equiv_def, eq_top_iff, ← hf u v, ← eq_top_iff]
  exact h

theorem IsExtentional.congr {f} (hf : IsExtentional f) (h : u ≈ v) : f u = f v := by
  apply le_antisymm
  · grw [← hf u v]
    simp [equiv_def.1 h]
  · grw [← hf v u]
    simp [equiv_def.1 (equiv_symm h)]

@[gcongr] theorem mem_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ∈ᴮ v₁ = u₂ ∈ᴮ v₂ := by
  trans u₂ ∈ᴮ v₁
  · exact IsExtentional.congr (f := (· ∈ᴮ v₁)) (by fun_prop) h₁
  · exact IsExtentional.congr (by fun_prop) h₂

@[gcongr] theorem mem_congr_le {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ∈ᴮ v₁ ≤ u₂ ∈ᴮ v₂ :=
  (mem_congr h₁ h₂).le

@[gcongr] theorem eq_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ =ᴮ v₁ = u₂ =ᴮ v₂ := by
  trans u₂ =ᴮ v₁
  · exact IsExtentional.congr (f := (· =ᴮ v₁)) (by fun_prop) h₁
  · exact IsExtentional.congr (by fun_prop) h₂

@[gcongr] theorem eq_congr_le {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ =ᴮ v₁ ≤ u₂ =ᴮ v₂ :=
  (eq_congr h₁ h₂).le

@[gcongr] theorem subset_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ⊆ᴮ v₁ = u₂ ⊆ᴮ v₂ := by
  trans u₂ ⊆ᴮ v₁
  · exact IsExtentional.congr (f := (· ⊆ᴮ v₁)) (by fun_prop) h₁
  · exact IsExtentional.congr (by fun_prop) h₂

@[gcongr] theorem subset_congr_le {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ⊆ᴮ v₁ ≤ u₂ ⊆ᴮ v₂ :=
  (subset_congr h₁ h₂).le



def empty : BVSet B :=
  ⟨PEmpty, nofun, nofun⟩

instance : EmptyCollection (BVSet B) := ⟨empty⟩
instance : Nonempty (BVSet B) := ⟨∅⟩

@[simp] theorem mem_empty : u ∈ᴮ ∅ = ⊥ := by
  simp [EmptyCollection.emptyCollection, empty, mem_def]

@[simp] theorem empty_subset : ∅ ⊆ᴮ u = ⊤ := by
  simp [subset_def']

theorem eq_empty : u =ᴮ ∅ = ⨅ x, (x ∈ᴮ u)ᶜ := by
  simp [eq_def, subset_def']

theorem ne_empty : u ≠ᴮ ∅ = ⨆ x, x ∈ᴮ u := by
  simp [eq_empty, compl_iInf]

protected def insert (u v : BVSet.{u, v} B) : BVSet B :=
  ⟨Option v.Index, (·.elim u v.dom), (·.elim ⊤ v.val)⟩

instance : Insert (BVSet B) (BVSet B) := ⟨BVSet.insert⟩

@[simp] theorem mem_insert : u ∈ᴮ insert v w = u =ᴮ v ⊔ u ∈ᴮ w := by
  simp [insert, BVSet.insert, mem_def, iSup_option]

theorem mem_insert_self : u ∈ᴮ insert u v = ⊤ := by
  simp

theorem le_subset_insert : u ⊆ᴮ w ≤ u ⊆ᴮ insert v w := by
  simp only [subset_def', mem_insert, le_iInf_iff, le_himp_iff]
  intro x
  grw [iInf_le _ x, himp_inf_le, ← le_sup_right]

@[fun_prop] theorem IsExtentionalFun.insert {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentionalFun fun x => insert (f x) (g x) := by
  apply of_isExtentional
  intro x
  simp only [mem_insert]
  fun_prop

@[gcongr] theorem insert_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    insert u₁ v₁ ≈ insert u₂ v₂ := by
  trans insert u₂ v₁
  · apply IsExtentionalFun.congr _ h₁
    fun_prop
  · apply IsExtentionalFun.congr _ h₂
    fun_prop

@[simp] theorem insert_eq_empty : insert u v =ᴮ ∅ = ⊥ := by
  rw [eq_empty, eq_bot_iff]
  apply iInf_le_of_le u
  simp

instance : Singleton (BVSet B) (BVSet B) := ⟨(insert · ∅)⟩

@[simp] theorem mem_singleton : u ∈ᴮ {v} = u =ᴮ v := by
  simp [Singleton.singleton]

@[fun_prop] theorem IsExtentionalFun.singleton {f : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) : IsExtentionalFun fun x => {f x} := by
  apply of_isExtentional
  intro x
  simp only [mem_singleton]
  fun_prop

@[gcongr] theorem singleton_congr (h : u ≈ v) : ({u} : BVSet B) ≈ {v} := by
  apply IsExtentionalFun.congr _ h
  fun_prop

@[simp] theorem singleton_eq_empty : ({u} : BVSet B) =ᴮ ∅ = ⊥ := by
  simp [Singleton.singleton]

@[simp] theorem singleton_eq_singleton : {u} =ᴮ {v} = u =ᴮ v := by
  apply le_antisymm
  · grw [eq_le_subset, subset_def', iInf_le _ u]
    simp
  · apply IsExtentionalFun.eq_le_eq
    fun_prop

def sUnion (u : BVSet.{u, v} B) : BVSet B :=
  ⟨Σ x : u, (x : BVSet B).Index, fun ⟨_, y⟩ => y, fun ⟨x, y⟩ => u x ⊓ (x : BVSet B) y⟩

prefix:110 "⋃ᴮ " => sUnion

theorem mem_sUnion' : u ∈ᴮ ⋃ᴮ v = ⨆ x : v, v x ⊓ u ∈ᴮ x := by
  conv_lhs => simp only [sUnion, mem_def, Index_mk, val_mk, dom_mk]
  simp only [iSup_sigma]
  simp_rw [inf_assoc, ← inf_iSup_eq, ← mem_def]

@[simp] theorem mem_sUnion : u ∈ᴮ ⋃ᴮ v = ⨆ x, x ∈ᴮ v ⊓ u ∈ᴮ x := by
  rw [mem_sUnion', IsExtentional.iSup_mem_inf (by fun_prop)]

@[fun_prop] theorem IsExtentionalFun.sUnion {f : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) : IsExtentionalFun fun x => ⋃ᴮ (f x) := by
  apply of_isExtentional
  intro x
  simp only [mem_sUnion]
  fun_prop

@[gcongr] theorem sUnion_congr (h : u ≈ v) : ⋃ᴮ u ≈ ⋃ᴮ v := by
  apply IsExtentionalFun.congr _ h
  fun_prop

noncomputable def powerset [Small.{v} B] (u : BVSet.{u, v} B) : BVSet.{u, v} B :=
  ⟨u.Index → Shrink B, fun f => ⟨u.Index, u.dom, (equivShrink B).symm ∘ f⟩,
    fun f => ⟨u.Index, u.dom, (equivShrink B).symm ∘ f⟩ ⊆ᴮ u⟩

prefix:110 "𝒫ᴮ " => powerset

@[simp] theorem mem_powerset [Small.{v} B] : u ∈ᴮ 𝒫ᴮ v = u ⊆ᴮ v := by
  simp only [powerset, mem_def, Index_mk, val_mk, dom_mk]
  apply le_antisymm
  · rw [iSup_le_iff]
    intro f
    rw [inf_comm, BVSet.eq_symm]
    simpa using subset_congr_left
  · apply le_iSup_of_le fun x : v => equivShrink B ((x : BVSet B) ∈ᴮ u)
    rw [le_inf_iff]
    constructor
    · conv_rhs =>
        simp only [subset_def, Index_mk, val_mk, Function.comp_apply, Equiv.symm_apply_apply, dom_mk]
      rw [le_iInf_iff]
      intro x
      rw [subset_def']
      exact iInf_le _ (x : BVSet B)
    · rw [eq_def, le_inf_iff]
      constructor
      · simp only [subset_def']
        refine iInf_mono fun x => ?_
        simp only [le_himp_iff, himp_inf_self]
        conv_lhs => arg 1; rw [mem_def]
        conv_rhs =>
          rw [mem_def]
          simp only [Index_mk, val_mk, Function.comp_apply, Equiv.symm_apply_apply, dom_mk]
        rw [iSup_inf_eq]
        refine iSup_mono fun y => ?_
        rw [inf_right_comm, le_inf_iff]
        constructor
        · rw [inf_assoc]
          apply inf_le_of_right_le
          rw [inf_comm]
          apply mem_congr_left
        · simp
      · simp [subset_def]

@[fun_prop] theorem IsExtentionalFun.powerset [Small.{v} B] {f : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) : IsExtentionalFun fun x => 𝒫ᴮ (f x) := by
  apply of_isExtentional
  intro x
  simp only [mem_powerset]
  fun_prop

@[gcongr] theorem powerset_congr [Small.{v} B] (h : u ≈ v) : 𝒫ᴮ u ≈ 𝒫ᴮ v := by
  apply IsExtentionalFun.congr _ h
  fun_prop

def sep (u : BVSet B) (f : BVSet B → B) : BVSet B :=
  ⟨u.Index, fun i => i, fun i => u i ⊓ f i⟩

theorem mem_sep' {f} : u ∈ᴮ sep v f = ⨆ x : v, v x ⊓ u =ᴮ x ⊓ f x := by
  simp only [sep, mem_def, Index_mk, val_mk, dom_mk]
  ac_rfl

theorem mem_sep {f} (hf : IsExtentional f) : u ∈ᴮ sep v f = u ∈ᴮ v ⊓ f u := by
  simp only [sep, mem_def, Index_mk, val_mk, dom_mk, iSup_inf_eq]
  congr! 2 with i
  rw [inf_assoc, inf_assoc]
  congr 1
  apply le_antisymm
  · simp only [le_inf_iff, inf_le_right, true_and]
    rw [inf_comm, eq_symm]
    apply hf
  · simp only [le_inf_iff, inf_le_left, and_true]
    apply hf

@[fun_prop] theorem IsExtentionalFun.sep {f} {g : BVSet B → BVSet B → B}
    (hf : IsExtentionalFun f) (hg : IsExtentional₂ g) :
    IsExtentionalFun fun x => sep (f x) (g x) := by
  intro x y
  conv_rhs => simp only [BVSet.eq_def, subset_def', mem_sep (hg.left x), mem_sep (hg.left y)]
  apply le_inf
  · apply le_iInf
    intro z
    rw [le_himp_iff]
    apply le_inf
    · nth_grw 2 [inf_le_left]
      apply IsExtentional.eq_inf_le
      fun_prop
    · nth_grw 2 [inf_le_right]
      apply IsExtentional.eq_inf_le
      exact hg.right z
  · apply le_iInf
    intro z
    rw [le_himp_iff]
    apply le_inf
    · nth_grw 2 [inf_le_left]
      apply IsExtentional.eq_inf_le'
      fun_prop
    · nth_grw 2 [inf_le_right]
      apply IsExtentional.eq_inf_le'
      exact hg.right z

@[gcongr] theorem sep_congr {f} (h : u ≈ v) (hf : IsExtentional f) : sep u f ≈ sep v f := by
  apply ext
  intro x
  grw [mem_sep hf, mem_sep hf, h]

def replace (u : BVSet B) (f : BVSet B → BVSet B) : BVSet B :=
  ⟨u.Index, fun i => f i, fun i => u i⟩

theorem mem_replace' {f} : u ∈ᴮ replace v f = ⨆ x : v, v x ⊓ u =ᴮ f x := by
  simp [replace, mem_def]
  
theorem mem_replace {f} (hf : IsExtentionalFun f) :
    u ∈ᴮ replace v f = ⨆ x : BVSet B, x ∈ᴮ v ⊓ u =ᴮ f x := by
  rw [mem_replace', IsExtentional.iSup_mem_inf (by fun_prop)]

@[fun_prop] theorem IsExtentionalFun.replace {f} {g : BVSet B → BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun₂ g) :
    IsExtentionalFun fun x => replace (f x) (g x) := by
  intro x y
  conv_rhs =>
    rw [BVSet.eq_def]
    simp only [subset_def', mem_replace (hg.left x), mem_replace (hg.left y)]
  apply le_inf
  · apply le_iInf
    intro z
    rw [le_himp_iff, inf_iSup_eq]
    apply iSup_le
    intro a
    apply le_iSup_of_le a
    apply le_inf
    · nth_grw 2 [inf_le_left]
      apply IsExtentional.eq_inf_le
      fun_prop
    · nth_grw 2 [inf_le_right]
      apply IsExtentional.eq_inf_le
      have := hg.right a
      fun_prop
  · apply le_iInf
    intro z
    rw [le_himp_iff, inf_iSup_eq]
    apply iSup_le
    intro a
    apply le_iSup_of_le a
    apply le_inf
    · nth_grw 2 [inf_le_left]
      apply IsExtentional.eq_inf_le'
      fun_prop
    · nth_grw 2 [inf_le_right]
      apply IsExtentional.eq_inf_le'
      have := hg.right a
      fun_prop

@[gcongr] theorem sep_replace {f} (h : u ≈ v) (hf : IsExtentionalFun f) :
    replace u f ≈ replace v f := by
  apply ext
  intro x
  rw [mem_replace hf, mem_replace hf]
  congr! 2 with y
  grw [h]

def union (u v : BVSet B) : BVSet B := ⋃ᴮ {u, v}

instance : Union (BVSet B) := ⟨union⟩

@[simp] theorem mem_union : u ∈ᴮ (v ∪ w) = u ∈ᴮ v ⊔ u ∈ᴮ w := by
  simp only [Union.union, union, mem_sUnion, mem_insert, mem_singleton]
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [inf_sup_right]
    apply sup_le_sup <;> apply mem_congr_right
  · apply sup_le
    · apply le_iSup_of_le v
      simp
    · apply le_iSup_of_le w
      simp

@[fun_prop] protected theorem IsExtentionalFun.union {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentionalFun fun x => f x ∪ g x := by
  simp only [Union.union, union]
  fun_prop

@[gcongr] theorem union_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ∪ v₁ ≈ u₂ ∪ v₂ := by
  trans u₂ ∪ v₁
  · apply IsExtentionalFun.congr _ h₁
    fun_prop
  · apply IsExtentionalFun.congr _ h₂
    fun_prop

def inter (u v : BVSet B) : BVSet B := sep u (· ∈ᴮ v)

instance : Inter (BVSet B) := ⟨inter⟩

@[simp] theorem mem_inter : u ∈ᴮ (v ∩ w) = u ∈ᴮ v ⊓ u ∈ᴮ w := by
  simp only [Inter.inter, inter]
  rw [mem_sep (by fun_prop)]

@[fun_prop] protected theorem IsExtentionalFun.inter {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentionalFun fun x => f x ∩ g x := by
  simp only [Inter.inter, inter]
  fun_prop

@[gcongr] theorem inter_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ∪ v₁ ≈ u₂ ∪ v₂ := by
  trans u₂ ∪ v₁
  · apply IsExtentionalFun.congr _ h₁
    fun_prop
  · apply IsExtentionalFun.congr _ h₂
    fun_prop

theorem empty_inter : ∅ ∩ u ≈ ∅ := by
  simp [equiv_def, eq_def, subset_def']

theorem inter_empty : u ∩ ∅ ≈ ∅ := by
  simp [equiv_def, eq_def, subset_def']

theorem inter_subset_left : (u ∩ v) ⊆ᴮ u = ⊤ := by
  simp [subset_def']

theorem inter_subset_right : (u ∩ v) ⊆ᴮ v = ⊤ := by
  simp [subset_def']

theorem le_subset_inter : u ⊆ᴮ v ⊓ u ⊆ᴮ w ≤ u ⊆ᴮ (v ∩ w) := by
  simp only [subset_def', ← iInf_inf_eq]
  apply iInf_mono
  intro x
  rw [mem_inter, himp_inf_distrib]

theorem inter_comm : u ∩ v ≈ v ∩ u := by
  rw [equiv_def, eq_def, eq_top_iff]
  apply le_inf <;> grw [← le_subset_inter] <;> simp [inter_subset_left, inter_subset_right]

def sdiff (u v : BVSet B) : BVSet B := sep u fun x => (x ∈ᴮ v)ᶜ

instance : SDiff (BVSet B) := ⟨sdiff⟩

@[simp] theorem mem_sdiff : u ∈ᴮ (v \ w) = u ∈ᴮ v ⊓ (u ∈ᴮ w)ᶜ := by
  simp only [SDiff.sdiff, sdiff]
  rw [mem_sep (by fun_prop)]

@[fun_prop] protected theorem IsExtentionalFun.sdiff {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentionalFun fun x => f x \ g x := by
  simp only [SDiff.sdiff, sdiff]
  fun_prop

@[gcongr] theorem sdiff_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ \ v₁ ≈ u₂ \ v₂ := by
  trans u₂ \ v₁
  · apply IsExtentionalFun.congr _ h₁
    fun_prop
  · apply IsExtentionalFun.congr _ h₂
    fun_prop

theorem compl_subset : (u ⊆ᴮ v)ᶜ = (u \ v) ≠ᴮ ∅ := by
  simp [subset_def', ne_empty, compl_iInf, sdiff_eq]

theorem subset_le : u ⊆ᴮ v ≤ u =ᴮ v ⊔ (v \ u) ≠ᴮ ∅ := by
  rw [← compl_himp_eq', compl_compl, le_himp_iff]
  conv_rhs => rw [eq_def]
  apply le_inf
  · exact inf_le_left
  · grw [inf_le_right, eq_empty, subset_def']
    apply iInf_mono
    intro x
    simp [inf_sup_right]

theorem subset_inf_ne_le : u ⊆ᴮ v ⊓ u ≠ᴮ v ≤ (v \ u) ≠ᴮ ∅ := by
  grw [subset_le, inf_sup_right]
  apply sup_le
  · simp
  · exact inf_le_left

theorem subset_inf_inter_eq_empty_le : u ⊆ᴮ v ⊓ (u ∩ (v \ w)) =ᴮ ∅ ≤ u ⊆ᴮ w := by
  conv_rhs => rw [subset_def']
  apply le_iInf
  intro x
  rw [le_himp_iff, subset_def', eq_empty]
  grw [iInf_le _ x, iInf_le _ x]
  simp only [mem_inter, mem_sdiff, compl_inf, inf_sup_left, inf_sup_right, compl_compl]
  refine sup_le ?_ (sup_le ?_ ?_)
  · grw [inf_assoc, compl_inf_self, inf_bot_eq, bot_le]
  · grw [inf_right_comm, himp_inf_le, inf_compl_self, bot_le]
  · grw [inf_le_left, inf_le_right]

theorem IsExtentional.mem_wf {f : BVSet B → B} (hf : IsExtentional f) :
    ⨅ x, (⨅ y, y ∈ᴮ x ⇨ f y) ⇨ f x ≤ ⨅ x, f x := by
  apply le_iInf
  intro u
  induction u using BVSet.induction with | _ u ih
  rw [← inf_idem (iInf _)]
  nth_grw 2 [iInf_le _ u]
  grw [hf.iInf_mem_himp, ← le_himp_iff, ← le_himp_himp]
  apply le_iInf
  intro x
  grw [le_himp_iff, inf_le_left, ih x]

theorem regularity : u ≠ᴮ ∅ ≤ ⨆ x, x ∈ᴮ u ⊓ (x ∩ u) =ᴮ ∅ := by
  rw [← compl_le_compl_iff_le, compl_iSup, compl_compl, eq_empty]
  simp_rw [fun i => inf_comm (i ∈ᴮ u), compl_inf', eq_empty, mem_inter, compl_inf']
  apply IsExtentional.mem_wf
  fun_prop

theorem mem_self : u ∈ᴮ u = ⊥ := by
  have : ({u} : BVSet B) ≠ᴮ ∅ = ⊤ := by simp
  grw [eq_bot_iff, ← inf_top_eq (u ∈ᴮ u), ← this, regularity, inf_iSup_eq]
  apply iSup_le
  intro x
  grw [eq_empty, iInf_le _ u, ← inf_assoc, inf_compl_le_bot]
  simp only [mem_singleton, mem_inter, eq_refl, le_top, inf_of_le_left]
  grw [inf_comm, mem_congr_right']

theorem mem_cycle₂ : u ∈ᴮ v ⊓ v ∈ᴮ u = ⊥ := by
  have : ({u, v} : BVSet B) ≠ᴮ ∅ = ⊤ := by simp
  grw [eq_bot_iff, ← inf_top_eq (_ ⊓ _), ← this, regularity, inf_iSup_eq]
  apply iSup_le
  intro x
  simp only [mem_insert, mem_singleton, inf_sup_right, inf_sup_left, ← inf_assoc]
  apply sup_le
  · grw [eq_empty, iInf_le _ v, inf_compl_le_bot]
    simp only [mem_inter, mem_insert, mem_singleton, eq_refl, le_top, sup_of_le_right,
      inf_of_le_left]
    grw [inf_le_right (a := u ∈ᴮ v), inf_comm, mem_congr_right']
  · grw [eq_empty, iInf_le _ u, inf_compl_le_bot]
    simp only [mem_inter, mem_insert, eq_refl, mem_singleton, le_top, sup_of_le_left,
      inf_of_le_left]
    grw [inf_le_left (a := u ∈ᴮ v), inf_comm, mem_congr_right']

theorem mem_cycle₃ : u ∈ᴮ v ⊓ v ∈ᴮ w ⊓ w ∈ᴮ u = ⊥ := by
  have : ({u, v, w} : BVSet B) ≠ᴮ ∅ = ⊤ := by simp
  grw [eq_bot_iff, ← inf_top_eq (_ ⊓ _), ← this, regularity, inf_iSup_eq]
  apply iSup_le
  intro x
  simp only [mem_insert, mem_singleton, inf_sup_right, inf_sup_left, ← inf_assoc]
  refine sup_le ?_ (sup_le ?_ ?_)
  · grw [eq_empty, iInf_le _ w, inf_compl_le_bot]
    simp only [mem_inter, mem_insert, mem_singleton, eq_refl, le_top, sup_of_le_right,
      inf_of_le_left]
    grw [inf_le_right (a := u ∈ᴮ v), inf_le_right (a := v ∈ᴮ w), inf_comm, mem_congr_right']
  · grw [eq_empty, iInf_le _ u, inf_compl_le_bot]
    simp only [mem_inter, mem_insert, eq_refl, mem_singleton, le_top, sup_of_le_left,
      inf_of_le_left]
    grw [inf_le_left (a := u ∈ᴮ v), inf_le_left (a := u ∈ᴮ v), inf_comm, mem_congr_right']
  · grw [eq_empty, iInf_le _ v, inf_compl_le_bot]
    simp only [mem_inter, mem_insert, eq_refl, mem_singleton, le_top, sup_of_le_left,
      sup_of_le_right, inf_of_le_left]
    grw [inf_le_right (a := u ∈ᴮ v), inf_le_left (a := v ∈ᴮ w), inf_comm, mem_congr_right']

end BVSet
