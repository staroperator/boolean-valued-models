import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Tactic.FunProp

theorem iSup_himp_eq {α ι : Type*} [CompleteBooleanAlgebra α] {f : ι → α} {a} :
    (⨆ x, f x) ⇨ a = ⨅ x, f x ⇨ a := by
  refine eq_of_forall_le_iff fun b => ?_
  simp [inf_iSup_eq]

theorem himp_iInf_eq {α ι : Type*} [CompleteBooleanAlgebra α] {f : ι → α} {a} :
    a ⇨ (⨅ x, f x) = ⨅ x, a ⇨ f x := by
  simp [himp_eq, iInf_sup_eq]

@[gcongr] theorem sup_congr {α : Type*} [Max α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⊔ b = c ⊔ d :=
  congr_arg₂ Max.max h₁ h₂

@[gcongr] theorem inf_congr {α : Type*} [Min α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⊓ b = c ⊓ d :=
  congr_arg₂ Min.min h₁ h₂

@[gcongr] theorem himp_congr {α : Type*} [HImp α] {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ⇨ b = c ⇨ d :=
  congr_arg₂ HImp.himp h₁ h₂



universe u v

@[pp_with_univ]
inductive BVSet (B : Type u)
| mk (ι : Type v) (dom : ι → BVSet B) (val : ι → B)

namespace BVSet

variable {B : Type u}

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

instance : CoeFun (BVSet B) (λ x => x → B) := ⟨val⟩

variable [CompleteBooleanAlgebra B]

def eq : BVSet.{u, v} B → BVSet.{u, v} B → B
| ⟨u, udom, uval⟩, ⟨v, vdom, vval⟩ =>
  (⨅ x : u, uval x ⇨ ⨆ y : v, vval y ⊓ (udom x).eq (vdom y)) ⊓
    ⨅ y : v, vval y ⇨ ⨆ x : u, uval x ⊓ (udom x).eq (vdom y)

infix:70 " =ᴮ " => eq

def mem : BVSet.{u, v} B → BVSet.{u, v} B → B
| u, v => ⨆ x : v, v x ⊓ u.eq x

infix:70 " ∈ᴮ " => mem

def subset : BVSet.{u, v} B → BVSet.{u, v} B → B
| u, v => ⨅ x : u, u x ⇨ (x : BVSet B).mem v

infix:70 " ⊆ᴮ " => subset

theorem eq_refl (u : BVSet B) : u =ᴮ u = ⊤ := by
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

theorem mem_def {u v : BVSet B} : u ∈ᴮ v = ⨆ x : v, v x ⊓ u =ᴮ x := rfl

theorem subset_def {u v : BVSet B} : u ⊆ᴮ v = ⨅ x : u, u x ⇨ x ∈ᴮ v := rfl

theorem eq_def {u v : BVSet B} : u =ᴮ v = u ⊆ᴮ v ⊓ v ⊆ᴮ u := by
  rcases u with ⟨u, udom, uval⟩
  rcases v with ⟨v, vdom, vval⟩
  rw [BVSet.eq, BVSet.subset, BVSet.subset]
  simp only [val_mk, dom_mk, mem_def]
  conv_rhs => enter [2, 1, x, 2, 1, y]; rw [eq_symm]
  rfl

lemma eq_inf_val_le_mem {u v : BVSet B} {x : u} : u =ᴮ v ⊓ u x ≤ x ∈ᴮ v := by
  rw [eq_def, subset_def]
  apply (inf_le_inf_right _ (inf_le_of_left_le (iInf_le _ x))).trans
  simp

lemma eq_inf_val_le_mem' {u v : BVSet B} {x : v} : u =ᴮ v ⊓ v x ≤ x ∈ᴮ u := by
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

variable {u v w : BVSet B}

theorem eq_trans' (u v w : BVSet B) : v =ᴮ w ⊓ u =ᴮ v ≤ u =ᴮ w := by
  rw [inf_comm]
  apply eq_trans

theorem val_le_mem {x : u} : u x ≤ x ∈ᴮ u := by
  rw [mem_def]
  apply le_iSup_of_le x
  simp [eq_refl]

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

@[fun_prop] theorem IsExtentionalFun.id : IsExtentionalFun λ x : BVSet B => x := λ x y => by simp

@[fun_prop] theorem IsExtentionalFun.const {a : BVSet B} : IsExtentionalFun λ _ => a := λ x y => by simp [eq_refl]

@[fun_prop] theorem IsExtentionalFun.comp {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentionalFun (f ∘ g) :=
  λ x y => (hg x y).trans (hf _ _)

@[fun_prop] def IsExtentional (f : BVSet B → B) :=
  ∀ x y, x =ᴮ y ⊓ f x ≤ f y

@[fun_prop] theorem IsExtentional.const {a : B} : IsExtentional λ _ => a := λ x y => by simp

@[fun_prop] theorem IsExtentional.comp {f : BVSet B → B} {g : BVSet B → BVSet B}
    (hf : IsExtentional f) (hg : IsExtentionalFun g) : IsExtentional (f ∘ g) :=
  λ x y => by grw [hg x y]; apply hf

@[fun_prop] theorem IsExtentional.eq {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentional λ x => f x =ᴮ g x := λ x y => by
  simp only
  rw [← inf_idem (x =ᴮ y), inf_assoc]
  nth_grw 1 [hg x y, hf x y]
  grw [eq_symm (f x) (g x), eq_trans', eq_symm (g x) (f y), eq_trans']

@[fun_prop] theorem IsExtentional.mem {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentional λ x => f x ∈ᴮ g x := λ x y => by
  simp only
  rw [← inf_idem (x =ᴮ y), inf_assoc]
  nth_grw 1 [hg x y, hf x y]
  grw [mem_congr_left, mem_congr_right]

@[fun_prop] theorem IsExtentional.sup {f g : BVSet B → B}
    (hf : IsExtentional f) (hg : IsExtentional g) : IsExtentional λ x => f x ⊔ g x := λ x y => by
  simp only [inf_sup_left, sup_le_iff]
  constructor
  · exact (hf x y).trans le_sup_left
  · exact (hg x y).trans le_sup_right

@[fun_prop] theorem IsExtentional.inf {f g : BVSet B → B}
    (hf : IsExtentional f) (hg : IsExtentional g) : IsExtentional λ x => f x ⊓ g x := λ x y => by
  simp only [le_inf_iff]
  constructor
  · nth_grw 2 [inf_le_left]
    apply hf
  · nth_grw 2 [inf_le_right]
    apply hg

@[fun_prop] theorem IsExtentional.compl {f : BVSet B → B} (hf : IsExtentional f) :
    IsExtentional λ x => (f x)ᶜ := λ x y => by
  simp only
  rw [← le_himp_iff, compl_himp_compl, le_himp_iff, eq_symm]
  apply hf

@[fun_prop] theorem IsExtentional.himp {f g : BVSet B → B}
    (hf : IsExtentional f) (hg : IsExtentional g) : IsExtentional λ x => f x ⇨ g x := by
  simp_rw [himp_eq]
  fun_prop

@[fun_prop] theorem IsExtentional.iInf {α : Sort*} {f : α → BVSet B → B}
    (hf : ∀ x, IsExtentional (f x)) : IsExtentional λ x => ⨅ y, f y x := λ x y => by
  simp only [le_iInf_iff]
  intro z
  grw [iInf_le _ z]
  apply hf

@[fun_prop] theorem IsExtentional.iSup {α : Sort*} {f : α → BVSet B → B}
    (hf : ∀ x, IsExtentional (f x)) : IsExtentional λ x => ⨆ y, f y x := λ x y => by
  simp only [inf_iSup_eq, iSup_le_iff]
  intro z
  exact (hf _ _ _).trans <| le_iSup (λ z => f z y) z

theorem IsExtentional.iSup_eq_inf {f : BVSet B → B} (hf : IsExtentional f) :
    ⨆ x : BVSet B, x =ᴮ u ⊓ f x = f u := by
  apply le_antisymm
  · rw [iSup_le_iff]
    intro x
    apply hf
  · apply le_iSup_of_le u
    simp [BVSet.eq_refl]

theorem IsExtentional.iInf_eq_himp {f : BVSet B → B} (hf : IsExtentional f) :
    ⨅ x : BVSet B, x =ᴮ u ⇨ f x = f u := by
  apply le_antisymm
  · apply iInf_le_of_le u
    simp [BVSet.eq_refl]
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

theorem subset_def' : u ⊆ᴮ v = ⨅ x : BVSet B, x ∈ᴮ u ⇨ x ∈ᴮ v := by
  rw [subset_def, IsExtentional.iInf_mem_himp (by fun_prop)]

@[fun_prop] theorem IsExtentional.subset {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentional λ x => f x ⊆ᴮ g x := by
  simp only [subset_def']
  refine .iInf λ x => ?_
  fun_prop

theorem subset_congr_left : u =ᴮ v ⊓ u ⊆ᴮ w ≤ v ⊆ᴮ w := by
  have : IsExtentional λ x => x ⊆ᴮ w := by fun_prop
  apply this

theorem subset_congr_right : v =ᴮ w ⊓ u ⊆ᴮ v ≤ u ⊆ᴮ w := by
  have : IsExtentional λ x => u ⊆ᴮ x := by fun_prop
  apply this

theorem IsExtentionalFun.of_isExtentional {f : BVSet B → BVSet B}
    (h : ∀ y, IsExtentional λ x => y ∈ᴮ f x) : IsExtentionalFun f := by
  intro x y
  conv_rhs => rw [BVSet.eq_def]
  simp only [subset_def', le_inf_iff, le_iInf_iff, le_himp_iff]
  constructor
  · intro z
    apply h
  · intro z
    rw [eq_symm]
    apply h



instance : Setoid (BVSet B) where
  r u v := u =ᴮ v = ⊤
  iseqv.refl u := by simp [eq_refl]
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

@[gcongr] theorem eq_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ =ᴮ v₁ = u₂ =ᴮ v₂ := by
  trans u₂ =ᴮ v₁
  · exact IsExtentional.congr (f := (· =ᴮ v₁)) (by fun_prop) h₁
  · exact IsExtentional.congr (by fun_prop) h₂

@[gcongr] theorem subset_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ⊆ᴮ v₁ = u₂ ⊆ᴮ v₂ := by
  trans u₂ ⊆ᴮ v₁
  · exact IsExtentional.congr (f := (· ⊆ᴮ v₁)) (by fun_prop) h₁
  · exact IsExtentional.congr (by fun_prop) h₂

def empty : BVSet B :=
  ⟨PEmpty, nofun, nofun⟩

instance : EmptyCollection (BVSet B) := ⟨empty⟩
instance : Nonempty (BVSet B) := ⟨∅⟩

@[simp] theorem mem_empty : u ∈ᴮ ∅ = ⊥ := by
  simp [EmptyCollection.emptyCollection, empty, mem_def]

protected def insert (u v : BVSet.{u, v} B) : BVSet B :=
  ⟨Option v.Index, (·.elim u v.dom), (·.elim ⊤ v.val)⟩

instance : Insert (BVSet B) (BVSet B) := ⟨BVSet.insert⟩

@[simp] theorem mem_insert : u ∈ᴮ insert v w = u =ᴮ v ⊔ u ∈ᴮ w := by
  simp [insert, BVSet.insert, mem_def, iSup_option]

@[fun_prop] theorem IsExtentionalFun.insert {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentionalFun λ x => insert (f x) (g x) := by
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

instance : Singleton (BVSet B) (BVSet B) := ⟨(insert · ∅)⟩

@[simp] theorem mem_singleton : u ∈ᴮ {v} = u =ᴮ v := by
  simp [Singleton.singleton]

@[fun_prop] theorem IsExtentionalFun.singleton {f : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) : IsExtentionalFun λ x => {f x} := by
  apply of_isExtentional
  intro x
  simp only [mem_singleton]
  fun_prop

@[gcongr] theorem singleton_congr {u v : BVSet B} (h : u ≈ v) : ({u} : BVSet B) ≈ {v} := by
  apply IsExtentionalFun.congr _ h
  fun_prop

def union (u : BVSet.{u, v} B) : BVSet B :=
  ⟨Σ x : u, (x : BVSet B).Index, fun ⟨_, y⟩ => y, fun ⟨x, y⟩ => u x ⊓ (x : BVSet B) y⟩

prefix:110 "⋃ᴮ " => union

theorem mem_union : u ∈ᴮ ⋃ᴮ v = ⨆ x : v, v x ⊓ u ∈ᴮ x := by
  conv_lhs => simp only [union, mem_def, Index_mk, val_mk, dom_mk]
  simp only [iSup_sigma]
  simp_rw [inf_assoc, ← inf_iSup_eq, ← mem_def]

theorem mem_union' : u ∈ᴮ ⋃ᴮ v = ⨆ x, x ∈ᴮ v ⊓ u ∈ᴮ x := by
  rw [mem_union, IsExtentional.iSup_mem_inf (by fun_prop)]

@[fun_prop] theorem IsExtentionalFun.union {f : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) : IsExtentionalFun λ x => ⋃ᴮ (f x) := by
  apply of_isExtentional
  intro x
  simp only [mem_union']
  fun_prop

@[gcongr] theorem union_congr {u v : BVSet B} (h : u ≈ v) : ⋃ᴮ u ≈ ⋃ᴮ v := by
  apply IsExtentionalFun.congr _ h
  fun_prop

def powerset (u : BVSet.{u, max u v} B) : BVSet.{u, max u v} B :=
  ⟨u.Index → B, fun f => ⟨u.Index, u.dom, f⟩, fun f => ⟨u.Index, u.dom, f⟩ ⊆ᴮ u⟩

prefix:110 "𝒫ᴮ " => powerset

@[simp] theorem mem_powerset : u ∈ᴮ 𝒫ᴮ v = u ⊆ᴮ v := by
  simp only [powerset, mem_def, Index_mk, val_mk, dom_mk]
  apply le_antisymm
  · rw [iSup_le_iff]
    intro f
    rw [inf_comm, BVSet.eq_symm]
    simpa using subset_congr_left
  · apply le_iSup_of_le fun x : v => (x : BVSet B) ∈ᴮ u
    rw [le_inf_iff]
    constructor
    · conv_rhs => simp only [subset_def, Index_mk, val_mk, dom_mk]
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
        conv_rhs => rw [mem_def]; simp only [Index_mk, val_mk, dom_mk]
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

@[fun_prop] theorem IsExtentionalFun.powerset {f : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) : IsExtentionalFun λ x => 𝒫ᴮ (f x) := by
  apply of_isExtentional
  intro x
  simp only [mem_powerset]
  fun_prop

@[gcongr] theorem powerset_congr {u v : BVSet B} (h : u ≈ v) : 𝒫ᴮ u ≈ 𝒫ᴮ v := by
  apply IsExtentionalFun.congr _ h
  fun_prop

def sep (u : BVSet B) (f : BVSet B → B) : BVSet B :=
  ⟨u.Index, fun i => i, fun i => u i ⊓ f i⟩

theorem mem_sep {f} : u ∈ᴮ sep v f = ⨆ x : v, v x ⊓ u =ᴮ x ⊓ f x := by
  simp only [sep, mem_def, Index_mk, val_mk, dom_mk]
  ac_rfl

theorem mem_sep' {f} (hf : IsExtentional f) : u ∈ᴮ sep v f = u ∈ᴮ v ⊓ f u := by
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

def replace (u : BVSet B) (f : BVSet B → BVSet B) : BVSet B :=
  ⟨u.Index, fun i => f i, fun i => u i⟩

theorem mem_replace {f} : u ∈ᴮ replace v f = ⨆ x : v, v x ⊓ u =ᴮ f x := by
  simp [replace, mem_def]
  
theorem mem_replace' {f} (hf : IsExtentionalFun f) : u ∈ᴮ replace v f = ⨆ x : BVSet B, x ∈ᴮ v ⊓ u =ᴮ f x := by
  rw [mem_replace, IsExtentional.iSup_mem_inf (by fun_prop)]

end BVSet
