module

public import BooleanValuedModels.BVSet.Defs
public import BooleanValuedModels.BooleanAlgebra.Lemmas
public import Mathlib.Data.Sym.Sym2

@[expose] public noncomputable section

instance {α : Type u} [Small.{v} α] : Small.{v} (Option α) :=
  small_map (Equiv.optionEquivSumPUnit α)

namespace BVSet

variable {B : Type u} [CompleteBooleanAlgebra B] {u v w : BVSet.{u, v} B}

def beq (u : BVSet.{u, v} B) (v : BVSet.{u, v} B) : B :=
  (⨅ x : u, u.val x ⇨ ⨆ y : v, v.val y ⊓ beq x y)
  ⊓ (⨅ y : v, v.val y ⇨ ⨆ x : u, u.val x ⊓ beq x y)
termination_by u

infix:70 " =ᴮ " => beq
notation:70 u " ≠ᴮ " v:70 => (u =ᴮ v)ᶜ

@[simp]
theorem beq_refl (u : BVSet B) : u =ᴮ u = ⊤ := by
  rw [beq]
  simp only [inf_eq_top_iff, iInf_eq_top, himp_eq_top_iff]
  constructor <;> intro x <;> apply le_iSup_of_le x <;> simp [beq_refl x.1]
termination_by u

theorem beq_symm (u v : BVSet B) : u =ᴮ v = v =ᴮ u := by
  rw [beq, beq]
  conv_lhs => rw [inf_comm]
  congr! 7 <;> apply beq_symm
termination_by u

def bmem (u : BVSet.{u, v} B) (v : BVSet.{u, v} B) : B :=
  ⨆ x : v, v.val x ⊓ u =ᴮ x

infix:70 " ∈ᴮ " => bmem
notation:70 u " ∉ᴮ " v:70 => (u ∈ᴮ v)ᶜ

def bsubset (u : BVSet.{u, v} B) (v : BVSet.{u, v} B) : B :=
  ⨅ x : u.dom, u.val x ⇨ x.1 ∈ᴮ v
infix:70 " ⊆ᴮ " => bsubset

theorem bmem_def : u ∈ᴮ v = ⨆ x : v, v.val x ⊓ u =ᴮ x := rfl

theorem bsubset_def : u ⊆ᴮ v = ⨅ x : u.dom, u.val x ⇨ x ∈ᴮ v := rfl

theorem beq_def : u =ᴮ v = u ⊆ᴮ v ⊓ v ⊆ᴮ u := by
  rw [beq]
  simp only [bsubset_def, bmem_def]
  conv_rhs => enter [2, 1, x, 2, 1, y]; rw [beq_symm]

theorem beq_le_bsubset : u =ᴮ v ≤ u ⊆ᴮ v := by
  grw [beq_def, inf_le_left]

theorem beq_le_bsubset' : u =ᴮ v ≤ v ⊆ᴮ u := by
  grw [beq_def, inf_le_right]

lemma beq_inf_val_le_bmem {x : u} : u =ᴮ v ⊓ u x ≤ x ∈ᴮ v := by
  rw [beq_def, bsubset_def]
  apply (inf_le_inf_right _ (inf_le_of_left_le (iInf_le _ x))).trans
  simp

lemma beq_inf_val_le_bmem' {x : v} : u =ᴮ v ⊓ v x ≤ x ∈ᴮ u := by
  rw [beq_symm]
  exact beq_inf_val_le_bmem

theorem beq_trans (u v w : BVSet B) : u =ᴮ v ⊓ v =ᴮ w ≤ u =ᴮ w := by
  conv_rhs => rw [beq_def]
  simp only [bsubset_def, le_inf_iff, le_iInf_iff, le_himp_iff]
  constructor
  · intro x
    grw [inf_right_comm, beq_inf_val_le_bmem, bmem_def, iSup_inf_eq]
    refine iSup_le fun y => ?_
    grw [inf_right_comm, inf_comm (v.val y), beq_inf_val_le_bmem, bmem_def, iSup_inf_eq]
    refine iSup_mono fun z => ?_
    rw [inf_assoc, inf_comm (y.1 =ᴮ z)]
    apply inf_le_inf_left
    apply beq_trans
  · intro z
    grw [inf_assoc, beq_inf_val_le_bmem', bmem_def, inf_iSup_eq]
    refine iSup_le fun y => ?_
    grw [← inf_assoc, beq_inf_val_le_bmem', bmem_def, iSup_inf_eq]
    refine iSup_mono fun x => ?_
    rw [inf_assoc, inf_comm (y.1 =ᴮ x)]
    apply inf_le_inf_left
    apply beq_trans
termination_by v

theorem beq_trans' (u v w : BVSet B) : v =ᴮ w ⊓ u =ᴮ v ≤ u =ᴮ w := by
  rw [inf_comm]
  apply beq_trans

theorem val_le_bmem {x : u} : u x ≤ x ∈ᴮ u := by
  rw [bmem_def]
  apply le_iSup_of_le x
  simp

theorem bmem_congr_left (u v w : BVSet B) : u =ᴮ v ⊓ u ∈ᴮ w ≤ v ∈ᴮ w := by
  rw [bmem_def, inf_iSup_eq, bmem_def]
  refine iSup_mono fun z => ?_
  rw [inf_left_comm, beq_symm u]
  exact inf_le_inf_left _ <| beq_trans _ _ _

theorem bmem_congr_left' (u v w : BVSet B) : u =ᴮ v ⊓ v ∈ᴮ w ≤ u ∈ᴮ w := by
  rw [beq_symm]
  apply bmem_congr_left

theorem bmem_congr_right (u v w : BVSet B) : v =ᴮ w ⊓ u ∈ᴮ v ≤ u ∈ᴮ w := by
  rw [bmem_def, inf_iSup_eq, iSup_le_iff]
  intro y
  rw [← inf_assoc]
  apply (inf_le_inf_right _ beq_inf_val_le_bmem).trans
  rw [inf_comm, beq_symm]
  apply bmem_congr_left

theorem bmem_congr_right' (u v w : BVSet B) : v =ᴮ w ⊓ u ∈ᴮ w ≤ u ∈ᴮ v := by
  rw [beq_symm]
  apply bmem_congr_right



@[fun_prop]
def IsExtentionalFun (f : BVSet.{u, v} B → BVSet.{u, v} B) :=
  ∀ x y, x =ᴮ y ≤ f x =ᴮ f y

theorem IsExtentionalFun.eq_le_eq (f) (hf : IsExtentionalFun f) (u v : BVSet B) :
    u =ᴮ v ≤ f u =ᴮ f v := hf u v

@[fun_prop]
theorem IsExtentionalFun.id : IsExtentionalFun fun x : BVSet B => x :=
  fun x y => by simp

@[fun_prop]
theorem IsExtentionalFun.const {a : BVSet B} : IsExtentionalFun fun _ => a :=
  fun x y => by simp

@[fun_prop]
theorem IsExtentionalFun.comp {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentionalFun (f ∘ g) :=
  fun x y => (hg x y).trans (hf _ _)

@[fun_prop]
def IsExtentional (f : BVSet B → B) :=
  ∀ x y, x =ᴮ y ⊓ f x ≤ f y

theorem IsExtentional.beq_inf_le (f) (hf : IsExtentional f) (u v : BVSet B) :
    u =ᴮ v ⊓ f u ≤ f v := hf u v

theorem IsExtentional.beq_inf_le' (f) (hf : IsExtentional f) (u v : BVSet B) :
    v =ᴮ u ⊓ f u ≤ f v := by
  grw [beq_symm, hf.beq_inf_le]

theorem IsExtentional.inf_beq_le (f) (hf : IsExtentional f) (u v : BVSet B) :
    f u ⊓ u =ᴮ v ≤ f v := by
  grw [inf_comm, hf.beq_inf_le]

theorem IsExtentional.inf_eq_le' (f) (hf : IsExtentional f) (u v : BVSet B) :
    f u ⊓ v =ᴮ u ≤ f v := by
  grw [inf_comm, hf.beq_inf_le']

@[fun_prop]
theorem IsExtentional.const {a : B} : IsExtentional fun _ => a :=
  fun x y => by simp

@[fun_prop]
theorem IsExtentional.comp {f : BVSet B → B} {g : BVSet B → BVSet B}
    (hf : IsExtentional f) (hg : IsExtentionalFun g) : IsExtentional (f ∘ g) :=
  fun x y => by grw [hg x y]; apply hf

@[fun_prop]
theorem IsExtentional.eq {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentional fun x => f x =ᴮ g x := by
  intro x y
  simp only
  rw [← inf_idem (x =ᴮ y), inf_assoc]
  nth_grw 1 [hg x y, hf x y]
  grw [beq_symm (f x) (g x), beq_trans', beq_symm (g x) (f y), beq_trans']

@[fun_prop]
theorem IsExtentional.mem {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentional fun x => f x ∈ᴮ g x := by
  intro x y
  simp only
  rw [← inf_idem (x =ᴮ y), inf_assoc]
  nth_grw 1 [hg x y, hf x y]
  grw [bmem_congr_left, bmem_congr_right]

@[fun_prop]
theorem IsExtentional.sup {f g : BVSet B → B}
    (hf : IsExtentional f) (hg : IsExtentional g) : IsExtentional fun x => f x ⊔ g x := by
  intro x y
  simp only [inf_sup_left, sup_le_iff]
  constructor
  · exact (hf x y).trans le_sup_left
  · exact (hg x y).trans le_sup_right

@[fun_prop]
theorem IsExtentional.inf {f g : BVSet B → B}
    (hf : IsExtentional f) (hg : IsExtentional g) : IsExtentional fun x => f x ⊓ g x := by
  intro x y
  simp only [le_inf_iff]
  constructor
  · nth_grw 2 [inf_le_left]
    apply hf
  · nth_grw 2 [inf_le_right]
    apply hg

@[fun_prop]
theorem IsExtentional.compl {f : BVSet B → B} (hf : IsExtentional f) :
    IsExtentional fun x => (f x)ᶜ := by
  intro x y
  simp only
  rw [← le_himp_iff, compl_himp_compl, le_himp_iff, beq_symm]
  apply hf

@[fun_prop]
theorem IsExtentional.himp {f g : BVSet B → B}
    (hf : IsExtentional f) (hg : IsExtentional g) : IsExtentional fun x => f x ⇨ g x := by
  simp_rw [himp_eq]
  fun_prop

@[fun_prop]
protected theorem IsExtentional.iInf {α : Sort*} {f : α → BVSet B → B}
    (hf : ∀ x, IsExtentional (f x)) : IsExtentional fun x => ⨅ y, f y x := by
  intro x y
  simp only [le_iInf_iff]
  intro z
  grw [iInf_le _ z]
  apply hf

theorem IsExtentional.inf_beq_le_of_le {f g} (hf : IsExtentional f) (hg : IsExtentional g)
    (u v : BVSet B) (h : f v ≤ g v) : f u ⊓ u =ᴮ v ≤ g u := by
  rw [← himp_eq_top_iff] at h
  grw [← le_himp_iff', ← inf_top_eq (u =ᴮ v), ← h]
  apply beq_inf_le'
  fun_prop

theorem IsExtentional.inf_beq_le_of_le' {f g} (hf : IsExtentional f) (hg : IsExtentional g)
    (u v : BVSet B) (h : f u ≤ g u) : f v ⊓ u =ᴮ v ≤ g v := by
  rw [beq_symm]
  exact hf.inf_beq_le_of_le hg v u h

@[fun_prop]
protected theorem IsExtentional.iSup {α : Sort*} {f : α → BVSet B → B}
    (hf : ∀ x, IsExtentional (f x)) : IsExtentional fun x => ⨆ y, f y x := by
  intro x y
  simp only [inf_iSup_eq, iSup_le_iff]
  intro z
  exact (hf _ _ _).trans <| le_iSup (fun z => f z y) z

theorem IsExtentional.iSup_beq_inf {f : BVSet B → B} (hf : IsExtentional f) :
    ⨆ x, x =ᴮ u ⊓ f x = f u := by
  apply le_antisymm
  · rw [iSup_le_iff]
    intro x
    apply hf
  · apply le_iSup_of_le u
    simp

theorem IsExtentional.iInf_beq_himp {f : BVSet B → B} (hf : IsExtentional f) :
    ⨅ x, x =ᴮ u ⇨ f x = f u := by
  apply le_antisymm
  · apply iInf_le_of_le u
    simp
  · rw [le_iInf_iff]
    intro v
    rw [le_himp_iff', beq_symm]
    apply hf

theorem IsExtentional.iSup_bmem_inf {f : BVSet B → B} (hf : IsExtentional f) :
    ⨆ x, x ∈ᴮ u ⊓ f x = ⨆ x : u, u x ⊓ f x := by
  simp_rw [bmem_def, iSup_inf_eq]
  rw [iSup_comm]
  simp_rw [inf_assoc, ← fun j => inf_iSup_eq (u j) fun i => i =ᴮ j ⊓ f i, hf.iSup_beq_inf]

theorem IsExtentional.iInf_bmem_himp {f : BVSet B → B} (hf : IsExtentional f) :
    ⨅ x, x ∈ᴮ u ⇨ f x = ⨅ x : u, u x ⇨ f x := by
  simp_rw [bmem_def, iSup_himp_eq]
  rw [iInf_comm]
  simp_rw [← himp_himp, ← himp_iInf_eq, hf.iInf_beq_himp]

theorem bmem_def' : u ∈ᴮ v = ⨆ x, x ∈ᴮ v ⊓ x =ᴮ u := by
  rw [bmem_def, IsExtentional.iSup_bmem_inf (by fun_prop)]
  simp_rw [beq_symm]

theorem bsubset_def' : u ⊆ᴮ v = ⨅ x, x ∈ᴮ u ⇨ x ∈ᴮ v := by
  rw [bsubset_def, IsExtentional.iInf_bmem_himp (by fun_prop)]

@[fun_prop]
theorem IsExtentional.subset {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) : IsExtentional fun x => f x ⊆ᴮ g x := by
  simp only [bsubset_def']
  fun_prop

theorem bsubset_congr_left : u =ᴮ v ⊓ u ⊆ᴮ w ≤ v ⊆ᴮ w := by
  have : IsExtentional fun x => x ⊆ᴮ w := by fun_prop
  apply this

theorem bsubset_congr_right : v =ᴮ w ⊓ u ⊆ᴮ v ≤ u ⊆ᴮ w := by
  have : IsExtentional fun x => u ⊆ᴮ x := by fun_prop
  apply this

theorem IsExtentionalFun.of_isExtentional {f : BVSet B → BVSet B}
    (h : ∀ y, IsExtentional fun x => y ∈ᴮ f x) : IsExtentionalFun f := by
  intro x y
  conv_rhs => rw [beq_def]
  simp only [bsubset_def', le_inf_iff, le_iInf_iff, le_himp_iff]
  constructor
  · intro z
    apply h
  · intro z
    rw [beq_symm]
    apply h

theorem bmem_inf_bsubset_le (u v w : BVSet B) : u ∈ᴮ v ⊓ v ⊆ᴮ w ≤ u ∈ᴮ w := by
  grw [bsubset_def', iInf_le _ u, inf_himp_le]

theorem bsubset_inf_bmem_le (u v w : BVSet B) : v ⊆ᴮ w ⊓ u ∈ᴮ v ≤ u ∈ᴮ w := by
  rw [inf_comm]
  apply bmem_inf_bsubset_le

@[simp]
theorem bsubset_refl (u : BVSet B) : u ⊆ᴮ u = ⊤ := by
  simp [bsubset_def']

theorem bsubset_antisymm (u v : BVSet B) : u ⊆ᴮ v ⊓ v ⊆ᴮ u ≤ u =ᴮ v := by
  rw [beq_def]

theorem bsubset_trans (u v w : BVSet B) : u ⊆ᴮ v ⊓ v ⊆ᴮ w ≤ u ⊆ᴮ w := by
  simp only [bsubset_def', le_iInf_iff, le_himp_iff]
  intro x
  grw [iInf_le _ x, iInf_le _ x, inf_right_comm, himp_inf_le, inf_himp_le]

theorem bsubset_trans' (u v w : BVSet B) : v ⊆ᴮ w ⊓ u ⊆ᴮ v ≤ u ⊆ᴮ w := by
  rw [inf_comm]
  apply bsubset_trans

@[fun_prop]
def IsExtentional₂ (f : BVSet B → BVSet B → B) :=
  ∀ x₁ x₂ y₁ y₂, x₁ =ᴮ x₂ ⊓ y₁ =ᴮ y₂ ⊓ f x₁ y₁ ≤ f x₂ y₂

theorem isExtentional₂_iff {f : BVSet B → BVSet B → B} :
    IsExtentional₂ f ↔ (∀ x, IsExtentional (f x)) ∧ ∀ y, IsExtentional fun x => f x y := by
  refine ⟨fun hf => ⟨fun x y₁ y₂ => ?_, fun y x₁ x₂ => ?_⟩, fun ⟨hf₁, hf₂⟩ x₁ x₂ y₁ y₂ => ?_⟩
  · simpa using hf x x y₁ y₂
  · simpa using hf x₁ x₂ y y
  · grw [inf_assoc, hf₁ x₁ y₁ y₂]
    apply hf₂

@[fun_prop]
theorem IsExtentional₂.of_isExtentional {f : BVSet B → BVSet B → B}
    (hf₁ : ∀ x, IsExtentional (f x)) (hf₂ : ∀ y, IsExtentional fun x => f x y) :
    IsExtentional₂ f :=
  isExtentional₂_iff.2 ⟨hf₁, hf₂⟩

theorem IsExtentional₂.left {f : BVSet B → BVSet B → B} (x)
    (hf : IsExtentional₂ f) : IsExtentional (f x) :=
  (isExtentional₂_iff.1 hf).1 x

theorem IsExtentional₂.right {f : BVSet B → BVSet B → B} (y)
    (hf : IsExtentional₂ f) : IsExtentional fun x => f x y :=
  (isExtentional₂_iff.1 hf).2 y

@[fun_prop]
def IsExtentionalFun₂ (f : BVSet.{u, v} B → BVSet.{u, v} B → BVSet.{u, v} B) :=
  ∀ x₁ x₂ y₁ y₂, x₁ =ᴮ x₂ ⊓ y₁ =ᴮ y₂ ≤ f x₁ y₁ =ᴮ f x₂ y₂

theorem isExtentionalFun₂_iff {f : BVSet B → BVSet B → BVSet B} :
    IsExtentionalFun₂ f ↔ (∀ x, IsExtentionalFun (f x)) ∧ ∀ y, IsExtentionalFun fun x => f x y := by
  refine ⟨fun hf => ⟨fun x y₁ y₂ => ?_, fun y x₁ x₂ => ?_⟩, fun ⟨hf₁, hf₂⟩ x₁ x₂ y₁ y₂ => ?_⟩
  · simpa using hf x x y₁ y₂
  · simpa using hf x₁ x₂ y y
  · grw [hf₁ x₁ y₁ y₂, hf₂ y₂ x₁ x₂]
    simp only
    grw [beq_trans']

@[fun_prop]
theorem IsExtentionalFun₂.of_isExtentionalFun {f : BVSet B → BVSet B → BVSet B}
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
  iseqv.symm h := by simpa [beq_symm]
  iseqv.trans h₁ h₂ := by
    grw [eq_top_iff, ← beq_trans, h₁, h₂, top_inf_eq]

theorem equiv_def : u ≈ v ↔ u =ᴮ v = ⊤ := Iff.rfl

@[refl]
theorem equiv_refl (u : BVSet B) : u ≈ u := IsEquiv.toIsPreorder.refl _

@[symm]
theorem equiv_symm : u ≈ v → v ≈ u := IsEquiv.toSymm.symm _ _

@[trans]
theorem equiv_trans : u ≈ v → v ≈ w → u ≈ w := IsEquiv.toIsPreorder.trans _ _ _

theorem ext' (h : ∀ x, x ∈ᴮ u = x ∈ᴮ v) : u ≈ v := by
  rw [equiv_def]
  simp [beq_def, bsubset_def', h]

theorem IsExtentionalFun.congr {f} (hf : IsExtentionalFun f) (h : u ≈ v) : f u ≈ f v := by
  grw [equiv_def, eq_top_iff, ← hf u v, ← eq_top_iff]
  exact h

theorem IsExtentional.congr {f} (hf : IsExtentional f) (h : u ≈ v) : f u = f v := by
  apply le_antisymm
  · grw [← hf u v]
    simp [equiv_def.1 h]
  · grw [← hf v u]
    simp [equiv_def.1 (equiv_symm h)]

@[gcongr]
theorem bmem_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ∈ᴮ v₁ = u₂ ∈ᴮ v₂ := by
  trans u₂ ∈ᴮ v₁
  · exact IsExtentional.congr (f := (· ∈ᴮ v₁)) (by fun_prop) h₁
  · exact IsExtentional.congr (by fun_prop) h₂

@[gcongr]
theorem bmem_congr_le {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ∈ᴮ v₁ ≤ u₂ ∈ᴮ v₂ :=
  (bmem_congr h₁ h₂).le

@[gcongr]
theorem beq_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ =ᴮ v₁ = u₂ =ᴮ v₂ := by
  trans u₂ =ᴮ v₁
  · exact IsExtentional.congr (f := (· =ᴮ v₁)) (by fun_prop) h₁
  · exact IsExtentional.congr (by fun_prop) h₂

@[gcongr]
theorem beq_congr_le {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ =ᴮ v₁ ≤ u₂ =ᴮ v₂ :=
  (beq_congr h₁ h₂).le

@[gcongr]
theorem bsubset_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ⊆ᴮ v₁ = u₂ ⊆ᴮ v₂ := by
  trans u₂ ⊆ᴮ v₁
  · exact IsExtentional.congr (f := (· ⊆ᴮ v₁)) (by fun_prop) h₁
  · exact IsExtentional.congr (by fun_prop) h₂

@[gcongr]
theorem bsubset_congr_le {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ⊆ᴮ v₁ ≤ u₂ ⊆ᴮ v₂ :=
  (bsubset_congr h₁ h₂).le



def mkI (ι : Type w) [Small.{v} ι] (f : ι → BVSet.{u, v} B) (b : ι → B) : BVSet B :=
  mk (Set.range f) fun ⟨x, _⟩ => ⨆ i ∈ f ⁻¹' {x}, b i

@[simp]
theorem mem_mkI_iff {ι} [Small.{v} ι] {f : ι → BVSet B} {b u} :
    u ∈ mkI ι f b ↔ ∃ i, f i = u := by
  simp [mkI]

theorem mem_mkI {ι} [Small.{v} ι] {f : ι → BVSet B} {b i} :
    f i ∈ mkI ι f b := by
  simp [mem_mkI_iff]

theorem dom_mkI {ι} [Small.{v} ι] {f : ι → BVSet B} {b} :
    (mkI ι f b).dom = Set.range f := by
  simp [mkI, dom_mk]

theorem val_mkI_apply {ι} [Small.{v} ι] {f : ι → BVSet B} {b} {i : (mkI ι f b).dom} :
    (mkI ι f b).val i = ⨆ j ∈ f ⁻¹' {i.1}, b j := by
  simp [mkI, val_mk_apply]

theorem bmem_mkI {ι} [Small.{v} ι] {f : ι → BVSet B} {b u} :
    u ∈ᴮ mkI ι f b = ⨆ i, b i ⊓ u =ᴮ f i := by
  simp only [bmem_def, val_mkI_apply, iSup_inf_eq]
  refine le_antisymm  (iSup_le fun ⟨x, hx⟩ => iSup₂_le fun i hi => ?_) (iSup_le fun i => ?_)
  · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi
    apply le_iSup_of_le i
    simp [← hi]
  · exact le_iSup_of_le ⟨f i, mem_mkI⟩ (le_iSup₂_of_le i (by simp) le_rfl)

theorem mkI_bsubset {ι} [Small.{v} ι] {f : ι → BVSet B} {b u} :
    mkI ι f b ⊆ᴮ u = ⨅ i, b i ⇨ f i ∈ᴮ u := by
  simp only [bsubset_def', bmem_mkI, iSup_himp_eq, ← himp_himp]
  rw [iInf_comm]
  congr! with i
  rw [← himp_iInf_eq, IsExtentional.iInf_beq_himp (by fun_prop)]

protected def empty : BVSet.{u, v} B :=
  mkI Empty nofun nofun

instance : EmptyCollection (BVSet B) := ⟨.empty⟩
instance : Nonempty (BVSet B) := ⟨∅⟩

@[simp]
theorem bmem_empty : u ∈ᴮ ∅ = ⊥ := by
  simp [EmptyCollection.emptyCollection, BVSet.empty, bmem_mkI]

@[simp]
theorem bempty_subset : ∅ ⊆ᴮ u = ⊤ := by
  simp [bsubset_def']

theorem beq_empty : u =ᴮ ∅ = ⨅ x, (x ∈ᴮ u)ᶜ := by
  simp [beq_def, bsubset_def']

theorem bne_empty : u ≠ᴮ ∅ = ⨆ x, x ∈ᴮ u := by
  simp [beq_empty, compl_iInf]

protected def insert (u v : BVSet.{u, v} B) : BVSet B :=
  mkI (Option v.dom) (Option.elim' u Subtype.val) (Option.elim' ⊤ v.val)

instance : Insert (BVSet B) (BVSet B) := ⟨BVSet.insert⟩

@[simp]
theorem bmem_insert : u ∈ᴮ insert v w = u =ᴮ v ⊔ u ∈ᴮ w := by
  simp [insert, BVSet.insert, bmem_mkI, iSup_option, ← bmem_def]

theorem bmem_insert_self : u ∈ᴮ insert u v = ⊤ := by
  simp

theorem le_bsubset_insert : u ⊆ᴮ w ≤ u ⊆ᴮ insert v w := by
  simp only [bsubset_def', bmem_insert, le_iInf_iff, le_himp_iff]
  intro x
  grw [iInf_le _ x, himp_inf_le, ← le_sup_right]

@[fun_prop]
theorem IsExtentionalFun.insert {f g : BVSet B → BVSet B} (hf : IsExtentionalFun f)
    (hg : IsExtentionalFun g) : IsExtentionalFun fun x => insert (f x) (g x) := by
  apply of_isExtentional
  intro x
  simp only [bmem_insert]
  fun_prop

@[gcongr]
theorem insert_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    insert u₁ v₁ ≈ insert u₂ v₂ := by
  trans insert u₂ v₁
  · apply IsExtentionalFun.congr _ h₁
    fun_prop
  · apply IsExtentionalFun.congr _ h₂
    fun_prop

@[simp]
theorem insert_beq_empty : insert u v =ᴮ ∅ = ⊥ := by
  rw [beq_empty, eq_bot_iff]
  apply iInf_le_of_le u
  simp

theorem insert_idem : insert u (insert u v) ≈ insert u v :=
  ext' fun x => by simp

theorem insert_comm : insert u (insert v w) ≈ insert v (insert u w) :=
  ext' fun x => by simpa using sup_left_comm _ _ _

instance : Singleton (BVSet B) (BVSet B) := ⟨(insert · ∅)⟩

@[simp]
theorem bmem_singleton : u ∈ᴮ {v} = u =ᴮ v := by
  simp [Singleton.singleton]

@[fun_prop]
theorem IsExtentionalFun.singleton {f : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) : IsExtentionalFun fun x => {f x} := by
  apply of_isExtentional
  intro x
  simp only [bmem_singleton]
  fun_prop

@[gcongr]
theorem singleton_congr (h : u ≈ v) : ({u} : BVSet B) ≈ {v} := by
  apply IsExtentionalFun.congr _ h
  fun_prop

@[simp]
theorem singleton_beq_empty : ({u} : BVSet B) =ᴮ ∅ = ⊥ := by
  simp [Singleton.singleton]

theorem pair_self : {u, u} ≈ ({u} : BVSet B) :=
  ext' fun x => by simp

theorem pair_comm (u v) : {u, v} ≈ ({v, u} : BVSet B) :=
  ext' fun x => by simpa using sup_comm _ _

@[simp]
theorem singleton_beq_singleton : {u} =ᴮ {v} = u =ᴮ v := by
  apply le_antisymm
  · grw [beq_le_bsubset, bsubset_def', iInf_le _ u]
    simp
  · apply IsExtentionalFun.eq_le_eq
    fun_prop

@[simp]
theorem singleton_beq_pair : {u} =ᴮ {v, w} = u =ᴮ v ⊓ u =ᴮ w := by
  apply le_antisymm
  · apply le_inf
    · grw [beq_le_bsubset', bsubset_def', iInf_le _ v, beq_symm]
      simp
    · grw [beq_le_bsubset', bsubset_def', iInf_le _ w, beq_symm]
      simp
  · grw [← pair_self, ← beq_trans {u, u} {v, u}]
    apply inf_le_inf
    · apply IsExtentionalFun.eq_le_eq ({·, u})
      fun_prop
    · apply IsExtentionalFun.eq_le_eq
      fun_prop

@[simp]
theorem pair_beq_singleton : {u, v} =ᴮ {w} = u =ᴮ w ⊓ v =ᴮ w := by
  rw [beq_symm, singleton_beq_pair, beq_symm w u, beq_symm w v]

@[simp]
theorem pair_beq_pair {u₁ u₂ v₁ v₂ : BVSet B} :
    {u₁, v₁} =ᴮ {u₂, v₂} = u₁ =ᴮ u₂ ⊓ v₁ =ᴮ v₂ ⊔ u₁ =ᴮ v₂ ⊓ u₂ =ᴮ v₁ := by
  apply le_antisymm
  · suffices ∀ u₁ u₂ v₁ v₂, {u₁, v₁} =ᴮ {u₂, v₂} ⊓ u₁ =ᴮ u₂ ≤ v₁ =ᴮ v₂ by
      rw [← inf_idem ({_, _} =ᴮ _)]
      nth_grw 2 [beq_le_bsubset]
      grw [bsubset_def', iInf_le _ u₁]
      simp only [bmem_insert, beq_refl, bmem_singleton, le_top, sup_of_le_left, top_himp,
        inf_sup_left]
      apply sup_le
      · grw [← le_sup_left]
        apply le_inf
        · grw [inf_le_right]
        · apply this
      · grw [← le_sup_right]
        apply le_inf
        · grw [inf_le_right]
        · grw [pair_comm u₂ v₂, beq_symm u₂ v₁]
          apply this
    intro u₁ u₂ v₁ v₂
    apply IsExtentional.inf_beq_le_of_le' (by fun_prop) (by fun_prop) u₁ u₂
    rw [← inf_idem ({_, _} =ᴮ _)]
    nth_grw 2 [beq_le_bsubset]
    grw [bsubset_def', iInf_le _ v₁]
    simp only [bmem_insert, bmem_singleton, beq_refl, le_top, sup_of_le_right, top_himp,
      inf_sup_left, sup_le_iff, inf_le_right, and_true]
    apply IsExtentional.inf_beq_le_of_le (by fun_prop) (by fun_prop) v₁ u₁
    grw [pair_self]
    simp
  · have : IsExtentionalFun₂ (B := B) ({·, ·}) := .of_isExtentionalFun (by fun_prop) (by fun_prop)
    apply sup_le
    · apply this
    · grw [pair_comm u₂ v₂, beq_symm u₂ v₁]
      apply this

@[simp]
theorem singleton_bsubset : {u} ⊆ᴮ v = u ∈ᴮ v := by
  simp only [bsubset_def', bmem_singleton]
  rw [IsExtentional.iInf_beq_himp (by fun_prop)]

@[simp]
theorem pair_bsubset : {u, v} ⊆ᴮ w = u ∈ᴮ w ⊓ v ∈ᴮ w := by
  simp only [bsubset_def', bmem_insert, bmem_singleton, sup_himp_distrib, iInf_inf_eq]
  rw [IsExtentional.iInf_beq_himp (by fun_prop), IsExtentional.iInf_beq_himp (by fun_prop)]

def sUnion (u : BVSet.{u, v} B) : BVSet B :=
  mkI (Σ x : u, x.1.dom) (fun ⟨_, y⟩ => y) fun ⟨x, y⟩ => u.val x ⊓ x.1.val y

prefix:110 "⋃ᴮ " => sUnion

theorem bmem_sUnion : u ∈ᴮ ⋃ᴮ v = ⨆ x : v, v x ⊓ u ∈ᴮ x := by
  simp only [BVSet.sUnion, bmem_mkI, iSup_sigma]
  simp_rw [inf_assoc, ← inf_iSup_eq, ← bmem_def]

@[simp]
theorem bmem_sUnion' : u ∈ᴮ ⋃ᴮ v = ⨆ x, x ∈ᴮ v ⊓ u ∈ᴮ x := by
  rw [bmem_sUnion, IsExtentional.iSup_bmem_inf (by fun_prop)]

@[fun_prop]
theorem IsExtentionalFun.sUnion {f : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) : IsExtentionalFun fun x => ⋃ᴮ (f x) := by
  apply of_isExtentional
  intro x
  simp only [bmem_sUnion']
  fun_prop

@[gcongr]
theorem sUnion_congr (h : u ≈ v) : ⋃ᴮ u ≈ ⋃ᴮ v := by
  apply IsExtentionalFun.congr _ h
  fun_prop

theorem sUnion_empty : ⋃ᴮ (∅ : BVSet B) ≈ ∅ :=
  ext' fun x => by simp

theorem sUnion_singleton : ⋃ᴮ {u} ≈ u :=
  ext' fun x => by
    simp only [bmem_sUnion', bmem_singleton]
    rw [IsExtentional.iSup_beq_inf (by fun_prop)]

protected def indexSep (u : BVSet.{u, v} B) (f : u.dom → B) : BVSet.{u, v} B :=
  mk u.dom f

theorem indexSep_bmem_bsubset : v.indexSep (· ∈ᴮ u) ⊆ᴮ u = ⊤ := by
  simp [bsubset_def, BVSet.indexSep, val_mk_apply]

theorem bsubset_le_indexSep_bmem_beq : u ⊆ᴮ v ≤ v.indexSep (fun i => i ∈ᴮ u) =ᴮ u := by
  rw [beq_def, indexSep_bmem_bsubset, top_inf_eq]
  rw [bsubset_def, bsubset_def]
  simp only [BVSet.indexSep]
  refine le_iInf fun i => iInf_le_of_le i ?_
  simp only [le_himp_iff, himp_inf_self, bmem_def, iSup_inf_eq]
  refine iSup_le fun j => le_iSup_of_le ⟨j, by simp⟩ (le_inf ?_ ?_)
  · rw [inf_right_comm, val_mk_apply]
    apply IsExtentional.inf_beq_le_of_le' (f := fun _ => _) (g := (· ∈ᴮ u)) (by fun_prop)
      (by fun_prop) i.1 j.1
    grw [inf_le_right, val_le_bmem]
  · grw [inf_le_left, inf_le_right]

theorem bsubset_le_indexSep_bmem_bsubset : u ⊆ᴮ v ≤ v.indexSep (· ∈ᴮ u) ⊆ᴮ v := by
  conv_rhs => simp only [BVSet.indexSep, bsubset_def, val_mk_apply]
  rw [bsubset_def']
  refine le_iInf fun i => iInf_le_of_le i ?_
  simp

def powerset [Small.{v} B] (u : BVSet.{u, v} B) : BVSet.{u, v} B :=
  mkI (u.dom → B) (fun f => u.indexSep f) fun f => u.indexSep f ⊆ᴮ u

prefix:110 "𝒫ᴮ " => powerset

@[simp]
theorem bmem_powerset [Small.{v} B] : u ∈ᴮ 𝒫ᴮ v = u ⊆ᴮ v := by
  simp only [powerset, bmem_mkI]
  apply le_antisymm
  · rw [iSup_le_iff]
    intro f
    rw [inf_comm, beq_symm]
    exact bsubset_congr_left
  · refine le_iSup_of_le (fun i : v => i ∈ᴮ u) (le_inf ?_ ?_)
    · exact bsubset_le_indexSep_bmem_bsubset
    · rw [beq_symm]
      exact bsubset_le_indexSep_bmem_beq

@[fun_prop]
theorem IsExtentionalFun.powerset [Small.{v} B] {f : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) : IsExtentionalFun fun x => 𝒫ᴮ (f x) := by
  apply of_isExtentional
  intro x
  simp only [bmem_powerset]
  fun_prop

@[gcongr]
theorem powerset_congr [Small.{v} B] (h : u ≈ v) : 𝒫ᴮ u ≈ 𝒫ᴮ v := by
  apply IsExtentionalFun.congr _ h
  fun_prop

def sep (u : BVSet B) (f : BVSet B → B) : BVSet B :=
  mkI u.dom Subtype.val fun i => u.val i ⊓ f i

theorem bmem_sep {f} : u ∈ᴮ v.sep f = ⨆ x : v, v x ⊓ u =ᴮ x ⊓ f x := by
  simp only [sep, bmem_mkI]
  ac_rfl

theorem bmem_sep' {f} (hf : IsExtentional f) : u ∈ᴮ v.sep f = u ∈ᴮ v ⊓ f u := by
  simp_rw [bmem_sep, inf_assoc,
    ← IsExtentional.iSup_bmem_inf (f := fun x => u =ᴮ x ⊓ f x) (by fun_prop), inf_left_comm,
    beq_symm u, IsExtentional.iSup_beq_inf (f := fun x => x ∈ᴮ v ⊓ f x) (by fun_prop)]

theorem bmem_sep_le_bmem {f} (hf : IsExtentional f) : u ∈ᴮ v.sep f ≤ u ∈ᴮ v := by
  grw [bmem_sep' hf, inf_le_left]

theorem bmem_sep_le_apply {f} (hf : IsExtentional f) : u ∈ᴮ v.sep f ≤ f u := by
  grw [bmem_sep' hf, inf_le_right]

@[fun_prop]
theorem IsExtentionalFun.sep {f} {g : BVSet B → BVSet B → B}
    (hf : IsExtentionalFun f) (hg : IsExtentional₂ g) :
    IsExtentionalFun fun x => (f x).sep (g x) := by
  intro x y
  conv_rhs => simp only [beq_def, bsubset_def', bmem_sep' (hg.left x), bmem_sep' (hg.left y)]
  apply le_inf
  · apply le_iInf
    intro z
    rw [le_himp_iff]
    apply le_inf
    · nth_grw 2 [inf_le_left]
      apply IsExtentional.beq_inf_le
      fun_prop
    · nth_grw 2 [inf_le_right]
      apply IsExtentional.beq_inf_le
      exact hg.right z
  · apply le_iInf
    intro z
    rw [le_himp_iff]
    apply le_inf
    · nth_grw 2 [inf_le_left]
      apply IsExtentional.beq_inf_le'
      fun_prop
    · nth_grw 2 [inf_le_right]
      apply IsExtentional.beq_inf_le'
      exact hg.right z

@[gcongr]
theorem sep_congr {f} (h : u ≈ v) (hf : IsExtentional f) : u.sep f ≈ v.sep f := by
  apply ext'
  intro x
  grw [bmem_sep' hf, bmem_sep' hf, h]

theorem sep_bsubset {f} (hf : IsExtentional f) : u.sep f ⊆ᴮ u = ⊤ := by
  simp [bsubset_def', bmem_sep' hf]

def replace (u : BVSet B) (f : BVSet B → BVSet B) : BVSet B :=
  mkI u.dom (f ∘ Subtype.val) u.val

theorem bmem_replace {f} : u ∈ᴮ v.replace f = ⨆ x : v, v x ⊓ u =ᴮ f x := by
  simp [BVSet.replace, bmem_mkI]
  
theorem bmem_replace' {f} (hf : IsExtentionalFun f) :
    u ∈ᴮ v.replace f = ⨆ x : BVSet B, x ∈ᴮ v ⊓ u =ᴮ f x := by
  rw [bmem_replace, IsExtentional.iSup_bmem_inf (by fun_prop)]

@[fun_prop]
theorem IsExtentionalFun.replace {f} {g : BVSet B → BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun₂ g) :
    IsExtentionalFun fun x => replace (f x) (g x) := by
  intro x y
  conv_rhs =>
    rw [beq_def]
    simp only [bsubset_def', bmem_replace' (hg.left x), bmem_replace' (hg.left y)]
  apply le_inf
  · apply le_iInf
    intro z
    rw [le_himp_iff, inf_iSup_eq]
    apply iSup_le
    intro a
    apply le_iSup_of_le a
    apply le_inf
    · nth_grw 2 [inf_le_left]
      apply IsExtentional.beq_inf_le
      fun_prop
    · nth_grw 2 [inf_le_right]
      apply IsExtentional.beq_inf_le
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
      apply IsExtentional.beq_inf_le'
      fun_prop
    · nth_grw 2 [inf_le_right]
      apply IsExtentional.beq_inf_le'
      have := hg.right a
      fun_prop

@[gcongr]
theorem sep_replace {f} (h : u ≈ v) (hf : IsExtentionalFun f) :
    replace u f ≈ replace v f := by
  apply ext'
  intro x
  rw [bmem_replace' hf, bmem_replace' hf]
  congr! 2 with y
  grw [h]

theorem replace_empty {f} (hf : IsExtentionalFun f) : replace (∅ : BVSet B) f ≈ ∅ :=
  ext' fun x => by simp [bmem_replace' hf]

theorem replace_singleton {f} (hf : IsExtentionalFun f) : replace {u} f ≈ {f u} :=
  ext' fun x => by
    simp only [bmem_replace' hf, bmem_singleton]
    rw [IsExtentional.iSup_beq_inf (by fun_prop)]

theorem replace_insert {f} (hf : IsExtentionalFun f) :
    replace (insert u v) f ≈ insert (f u) (replace v f) :=
  ext' fun x => by
    simp only [bmem_replace' hf, bmem_insert, inf_sup_right, iSup_sup_eq]
    rw [IsExtentional.iSup_beq_inf (by fun_prop)]

protected def union (u v : BVSet B) : BVSet B := ⋃ᴮ {u, v}

instance : Union (BVSet B) := ⟨.union⟩

theorem sUnion_pair : ⋃ᴮ {u, v} = u ∪ v := rfl

@[simp]
theorem bmem_union : u ∈ᴮ (v ∪ w) = u ∈ᴮ v ⊔ u ∈ᴮ w := by
  simp only [Union.union, BVSet.union, bmem_sUnion', bmem_insert, bmem_singleton]
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [inf_sup_right]
    apply sup_le_sup <;> apply bmem_congr_right
  · apply sup_le
    · apply le_iSup_of_le v
      simp
    · apply le_iSup_of_le w
      simp

@[fun_prop]
protected theorem IsExtentionalFun.union {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentionalFun fun x => f x ∪ g x := by
  simp only [Union.union, BVSet.union]
  fun_prop

@[gcongr]
theorem union_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ∪ v₁ ≈ u₂ ∪ v₂ := by
  trans u₂ ∪ v₁
  · apply IsExtentionalFun.congr _ h₁
    fun_prop
  · apply IsExtentionalFun.congr _ h₂
    fun_prop

@[simp]
theorem bsubset_union_left : u ⊆ᴮ (u ∪ v) = ⊤ := by
  simp [bsubset_def']

@[simp]
theorem bsubset_union_right : v ⊆ᴮ (u ∪ v) = ⊤ := by
  simp [bsubset_def']

theorem empty_union : ∅ ∪ u ≈ u :=
  ext' fun x => by simp

theorem union_empty : u ∪ ∅ ≈ u :=
  ext' fun x => by simp

theorem union_comm : u ∪ v ≈ v ∪ u :=
  ext' fun x => by simpa using sup_comm _ _

theorem union_singleton : u ∪ {v} ≈ insert v u :=
  ext' fun x => by simpa using sup_comm _ _

theorem union_insert : u ∪ insert v w ≈ insert v (u ∪ w) :=
  ext' fun x => by simpa using sup_left_comm _ _ _

protected def inter (u v : BVSet B) : BVSet B := sep u (· ∈ᴮ v)

instance : Inter (BVSet B) := ⟨.inter⟩

@[simp]
theorem bmem_inter : u ∈ᴮ (v ∩ w) = u ∈ᴮ v ⊓ u ∈ᴮ w := by
  simp only [Inter.inter, BVSet.inter]
  rw [bmem_sep' (by fun_prop)]

@[fun_prop]
protected theorem IsExtentionalFun.inter {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentionalFun fun x => f x ∩ g x := by
  simp only [Inter.inter, BVSet.inter]
  fun_prop

@[gcongr]
theorem inter_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ∪ v₁ ≈ u₂ ∪ v₂ := by
  trans u₂ ∪ v₁
  · apply IsExtentionalFun.congr _ h₁
    fun_prop
  · apply IsExtentionalFun.congr _ h₂
    fun_prop

theorem empty_inter : ∅ ∩ u ≈ ∅ :=
  ext' fun x => by simp

theorem inter_empty : u ∩ ∅ ≈ ∅ :=
  ext' fun x => by simp

theorem inter_bsubset_left : (u ∩ v) ⊆ᴮ u = ⊤ := by
  simp [bsubset_def']

theorem inter_bsubset_right : (u ∩ v) ⊆ᴮ v = ⊤ := by
  simp [bsubset_def']

theorem le_bsubset_inter : u ⊆ᴮ v ⊓ u ⊆ᴮ w ≤ u ⊆ᴮ (v ∩ w) := by
  simp only [bsubset_def', ← iInf_inf_eq]
  apply iInf_mono
  intro x
  rw [bmem_inter, himp_inf_distrib]

theorem inter_comm : u ∩ v ≈ v ∩ u :=
  ext' fun x => by simpa using inf_comm _ _

protected def sdiff (u v : BVSet B) : BVSet B := sep u fun x => (x ∈ᴮ v)ᶜ

instance : SDiff (BVSet B) := ⟨.sdiff⟩

@[simp]
theorem bmem_sdiff : u ∈ᴮ (v \ w) = u ∈ᴮ v ⊓ (u ∈ᴮ w)ᶜ := by
  simp only [SDiff.sdiff, BVSet.sdiff]
  rw [bmem_sep' (by fun_prop)]

@[fun_prop]
protected theorem IsExtentionalFun.sdiff {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentionalFun fun x => f x \ g x := by
  simp only [SDiff.sdiff, BVSet.sdiff]
  fun_prop

@[gcongr]
theorem sdiff_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ \ v₁ ≈ u₂ \ v₂ := by
  trans u₂ \ v₁
  · apply IsExtentionalFun.congr _ h₁
    fun_prop
  · apply IsExtentionalFun.congr _ h₂
    fun_prop

theorem compl_subset : (u ⊆ᴮ v)ᶜ = (u \ v) ≠ᴮ ∅ := by
  simp [bsubset_def', bne_empty, compl_iInf, sdiff_eq]

theorem bsubset_le : u ⊆ᴮ v ≤ u =ᴮ v ⊔ (v \ u) ≠ᴮ ∅ := by
  rw [← compl_himp_eq', compl_compl, le_himp_iff]
  conv_rhs => rw [beq_def]
  apply le_inf
  · exact inf_le_left
  · grw [inf_le_right, beq_empty, bsubset_def']
    apply iInf_mono
    intro x
    simp [inf_sup_right]

theorem bsubset_inf_bne_le : u ⊆ᴮ v ⊓ u ≠ᴮ v ≤ (v \ u) ≠ᴮ ∅ := by
  grw [bsubset_le, inf_sup_right]
  apply sup_le
  · simp
  · exact inf_le_left

theorem bsubset_inf_inter_beq_empty_le : u ⊆ᴮ v ⊓ (u ∩ (v \ w)) =ᴮ ∅ ≤ u ⊆ᴮ w := by
  conv_rhs => rw [bsubset_def']
  apply le_iInf
  intro x
  rw [le_himp_iff, bsubset_def', beq_empty]
  grw [iInf_le _ x, iInf_le _ x]
  simp only [bmem_inter, bmem_sdiff, compl_inf, inf_sup_left, inf_sup_right, compl_compl]
  refine sup_le ?_ (sup_le ?_ ?_)
  · grw [inf_assoc, compl_inf_self, inf_bot_eq, bot_le]
  · grw [inf_right_comm, himp_inf_le, inf_compl_self, bot_le]
  · grw [inf_le_left, inf_le_right]

theorem IsExtentional.bmem_wf {f : BVSet B → B} (hf : IsExtentional f) :
    ⨅ x, (⨅ y, y ∈ᴮ x ⇨ f y) ⇨ f x ≤ ⨅ x, f x := by
  apply le_iInf
  intro u
  induction u using BVSet.induction with | _ u ih
  rw [← inf_idem (iInf _)]
  nth_grw 2 [iInf_le _ u]
  grw [hf.iInf_bmem_himp, ← le_himp_iff, ← le_himp_himp]
  apply le_iInf
  intro x
  grw [le_himp_iff, inf_le_left, ih x x.2]

theorem regularity : u ≠ᴮ ∅ ≤ ⨆ x, x ∈ᴮ u ⊓ (x ∩ u) =ᴮ ∅ := by
  rw [← compl_le_compl_iff_le, compl_iSup, compl_compl, beq_empty]
  simp_rw [fun i => inf_comm (i ∈ᴮ u), compl_inf', beq_empty, bmem_inter, compl_inf']
  apply IsExtentional.bmem_wf
  fun_prop

theorem bmem_self : u ∈ᴮ u = ⊥ := by
  have : ({u} : BVSet B) ≠ᴮ ∅ = ⊤ := by simp
  grw [eq_bot_iff, ← inf_top_eq (u ∈ᴮ u), ← this, regularity, inf_iSup_eq]
  apply iSup_le
  intro x
  grw [beq_empty, iInf_le _ u, ← inf_assoc, inf_compl_le_bot]
  simp only [bmem_singleton, bmem_inter, beq_refl, le_top, inf_of_le_left]
  grw [inf_comm, bmem_congr_right']

theorem bmem_cycle₂ : u ∈ᴮ v ⊓ v ∈ᴮ u = ⊥ := by
  have : ({u, v} : BVSet B) ≠ᴮ ∅ = ⊤ := by simp
  grw [eq_bot_iff, ← inf_top_eq (_ ⊓ _), ← this, regularity, inf_iSup_eq]
  apply iSup_le
  intro x
  simp only [bmem_insert, bmem_singleton, inf_sup_right, inf_sup_left, ← inf_assoc]
  apply sup_le
  · grw [beq_empty, iInf_le _ v, inf_compl_le_bot]
    simp only [bmem_inter, bmem_insert, bmem_singleton, beq_refl, le_top, sup_of_le_right,
      inf_of_le_left]
    grw [inf_le_right (a := u ∈ᴮ v), inf_comm, bmem_congr_right']
  · grw [beq_empty, iInf_le _ u, inf_compl_le_bot]
    simp only [bmem_inter, bmem_insert, beq_refl, bmem_singleton, le_top, sup_of_le_left,
      inf_of_le_left]
    grw [inf_le_left (a := u ∈ᴮ v), inf_comm, bmem_congr_right']

theorem mem_cycle₃ : u ∈ᴮ v ⊓ v ∈ᴮ w ⊓ w ∈ᴮ u = ⊥ := by
  have : ({u, v, w} : BVSet B) ≠ᴮ ∅ = ⊤ := by simp
  grw [eq_bot_iff, ← inf_top_eq (_ ⊓ _), ← this, regularity, inf_iSup_eq]
  apply iSup_le
  intro x
  simp only [bmem_insert, bmem_singleton, inf_sup_right, inf_sup_left, ← inf_assoc]
  refine sup_le ?_ (sup_le ?_ ?_)
  · grw [beq_empty, iInf_le _ w, inf_compl_le_bot]
    simp only [bmem_inter, bmem_insert, bmem_singleton, beq_refl, le_top, sup_of_le_right,
      inf_of_le_left]
    grw [inf_le_right (a := u ∈ᴮ v), inf_le_right (a := v ∈ᴮ w), inf_comm, bmem_congr_right']
  · grw [beq_empty, iInf_le _ u, inf_compl_le_bot]
    simp only [bmem_inter, bmem_insert, beq_refl, bmem_singleton, le_top, sup_of_le_left,
      inf_of_le_left]
    grw [inf_le_left (a := u ∈ᴮ v), inf_le_left (a := u ∈ᴮ v), inf_comm, bmem_congr_right']
  · grw [beq_empty, iInf_le _ v, inf_compl_le_bot]
    simp only [bmem_inter, bmem_insert, beq_refl, bmem_singleton, le_top, sup_of_le_left,
      sup_of_le_right, inf_of_le_left]
    grw [inf_le_right (a := u ∈ᴮ v), inf_le_left (a := v ∈ᴮ w), inf_comm, bmem_congr_right']

end BVSet
