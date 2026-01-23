import BooleanValuedModels.BVSet.Ordinal
import BooleanValuedModels.BooleanAlgebra.CountableChainCondition
import BooleanValuedModels.DeltaSystemLemma
import Mathlib.SetTheory.ZFC.Cardinal

@[simp]
theorem Ordinal.card_toZFSet (o : Ordinal) : o.toZFSet.card = o.card := by
  simpa [← coe_toZFSet, ZFSet.cardinalMk_coe_sort, mk_Iio_ordinal, ← lift_card] using
    Cardinal.mk_image_eq (s := Set.Iio o) toZFSet_injective

universe u v

variable {B : Type u} [CompleteBooleanAlgebra B] {u v w f x y : BVSet.{u, v} B}

namespace BVSet

def kpair (u v : BVSet B) : BVSet B :=
  {{u}, {u, v}}

@[fun_prop] protected theorem IsExtentionalFun.kpair {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentionalFun fun x => kpair (f x) (g x) := by
  unfold kpair
  fun_prop

@[gcongr] theorem kpair_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    kpair u₁ v₁ ≈ kpair u₂ v₂ := by
  trans kpair u₂ v₁
  · apply IsExtentionalFun.congr _ h₁
    fun_prop
  · apply IsExtentionalFun.congr _ h₂
    fun_prop

theorem kpair_eq_kpair {u₁ u₂ v₁ v₂ : BVSet B} :
    kpair u₁ v₁ =ᴮ kpair u₂ v₂ = u₁ =ᴮ u₂ ⊓ v₁ =ᴮ v₂ := by
  apply le_antisymm
  · apply le_of_inf_le (u₁ =ᴮ u₂)
    · grw [eq_le_subset, subset_def', iInf_le _ {u₁}]
      simp [kpair]
    · apply le_inf
      · grw [inf_le_right]
      · grw [IsExtentional.inf_eq_le' (kpair u₁ v₁ =ᴮ kpair · v₂) (by fun_prop)]
        apply le_of_inf_le (u₁ =ᴮ v₁ ⇨ v₁ =ᴮ v₂)
        · rw [le_himp_iff]
          grw [IsExtentional.inf_eq_le (fun u => kpair u v₁ =ᴮ kpair u v₂) (by fun_prop)]
          simp [kpair]
        · simp only [kpair, pair_eq_pair, eq_refl, le_top, inf_of_le_right, singleton_eq_pair,
            le_sup_right, sup_of_le_left, inf_sup_right, le_himp_iff, inf_le_left, inf_of_le_left,
            sup_le_iff, le_refl, true_and]
          grw [inf_assoc, inf_himp_le, inf_le_right]
  · have : IsExtentionalFun₂ (B := B) kpair := by
      apply IsExtentionalFun₂.of_isExtentionalFun <;> fun_prop
    apply this

lemma le_kpair_mem [Small.{v} B] :
    u ∈ᴮ w ⊓ v ∈ᴮ w ≤ kpair u v ∈ᴮ 𝒫ᴮ 𝒫ᴮ w := by
  simp [kpair]

noncomputable def prod [Small.{v} B] (u v : BVSet.{u, v} B) : BVSet B :=
  (𝒫ᴮ 𝒫ᴮ (u ∪ v)).sep fun x => ⨆ y, y ∈ᴮ u ⊓ ⨆ z, z ∈ᴮ v ⊓ x =ᴮ kpair y z

@[fun_prop] protected theorem IsExtentionalFun.prod [Small.{v} B] {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentionalFun fun x => prod (f x) (g x) := by
  unfold prod
  fun_prop

@[gcongr] theorem prod_congr [Small.{v} B] {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    prod u₁ v₁ ≈ prod u₂ v₂ := by
  trans prod u₂ v₁
  · apply IsExtentionalFun.congr _ h₁
    fun_prop
  · apply IsExtentionalFun.congr _ h₂
    fun_prop

theorem mem_prod [Small.{v} B] :
    u ∈ᴮ prod v w = ⨆ x, x ∈ᴮ v ⊓ ⨆ y, y ∈ᴮ w ⊓ u =ᴮ kpair x y := by
  rw [prod, mem_sep (by fun_prop), inf_eq_right]
  apply iSup_le
  intro x
  rw [inf_iSup_eq]
  apply iSup_le
  intro y
  grw [← inf_assoc, ← IsExtentional.eq_inf_le' (· ∈ᴮ _) (by fun_prop) (kpair x y) u]
  apply le_inf
  · grw [inf_le_right]
  · grw [inf_le_left, ← le_kpair_mem]
    apply inf_le_inf
    · grw [← subset_inf_mem_le x v (v ∪ w)]
      simp
    · grw [← subset_inf_mem_le y w (v ∪ w)]
      simp

theorem le_kpair_mem_prod [Small.{v} B] {x y} :
    x ∈ᴮ u ⊓ y ∈ᴮ v ≤ kpair x y ∈ᴮ prod u v := by
  rw [mem_prod]
  refine le_iSup_of_le x (le_inf ?_ (le_iSup_of_le y (le_inf ?_ ?_)))
  · grw [inf_le_left]
  · grw [inf_le_right]
  · simp

def isFunc [Small.{v} B] (u v f : BVSet B) :=
  f ⊆ᴮ prod u v ⊓ (⨅ x, x ∈ᴮ u ⇨ ⨆ y, y ∈ᴮ v ⊓ kpair x y ∈ᴮ f)
    ⊓ ⨅ x, x ∈ᴮ u ⇨ ⨅ y₁, y₁ ∈ᴮ v ⇨ ⨅ y₂, y₂ ∈ᴮ v ⇨ kpair x y₁ ∈ᴮ f ⇨ kpair x y₂ ∈ᴮ f ⇨ y₁ =ᴮ y₂

@[fun_prop] protected theorem IsExtentional.isFunc [Small.{v} B] {f g h : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) (hh : IsExtentionalFun h) :
    IsExtentional fun x => isFunc (f x) (g x) (h x) := by
  unfold isFunc
  fun_prop

@[gcongr] theorem isFunc_congr [Small.{v} B] {u₁ u₂ v₁ v₂ f₁ f₂ : BVSet B}
    (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) (h₃ : f₁ ≈ f₂) :
    isFunc u₁ v₁ f₁ = isFunc u₂ v₂ f₂ := by
  trans isFunc u₂ v₁ f₁
  · apply IsExtentional.congr _ h₁
    fun_prop
  trans isFunc u₂ v₂ f₁
  · apply IsExtentional.congr _ h₂
    fun_prop
  · apply IsExtentional.congr _ h₃
    fun_prop

theorem isFunc_total [Small.{v} B] :
    isFunc u v f ≤ ⨅ x, x ∈ᴮ u ⇨ ⨆ y, y ∈ᴮ v ⊓ kpair x y ∈ᴮ f :=
  inf_le_of_left_le inf_le_right

theorem isFunc_total' [Small.{v} B] {x} :
    isFunc u v f ⊓ x ∈ᴮ u ≤ ⨆ y, y ∈ᴮ v ⊓ kpair x y ∈ᴮ f := by
  grw [isFunc_total, iInf_le _ x, himp_inf_le]

theorem isFunc_unique [Small.{v} B] :
    isFunc u v f ≤ ⨅ x, x ∈ᴮ u ⇨ ⨅ y₁, y₁ ∈ᴮ v ⇨ ⨅ y₂, y₂ ∈ᴮ v ⇨ kpair x y₁ ∈ᴮ f ⇨ kpair x y₂ ∈ᴮ f ⇨ y₁ =ᴮ y₂ :=
  inf_le_right

theorem isFunc_unique' [Small.{v} B] {x y₁ y₂ : BVSet B} :
    isFunc u v f ⊓ x ∈ᴮ u ⊓ y₁ ∈ᴮ v ⊓ y₂ ∈ᴮ v ⊓ kpair x y₁ ∈ᴮ f ⊓ kpair x y₂ ∈ᴮ f ≤ y₁ =ᴮ y₂ := by
  grw [isFunc_unique, iInf_le _ x, himp_inf_le, iInf_le _ y₁, himp_inf_le, iInf_le _ y₂, himp_inf_le, himp_inf_le, himp_inf_le]

def isInjective (u v f : BVSet B) :=
  ⨅ x₁, x₁ ∈ᴮ u ⇨ ⨅ x₂, x₂ ∈ᴮ u ⇨ ⨅ y, y ∈ᴮ v ⇨ kpair x₁ y ∈ᴮ f ⇨ kpair x₂ y ∈ᴮ f ⇨ x₁ =ᴮ x₂

@[fun_prop] protected theorem IsExtentional.isInjective {f g h : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) (hh : IsExtentionalFun h) :
    IsExtentional fun x => isInjective (f x) (g x) (h x) := by
  unfold isInjective
  fun_prop

@[gcongr] theorem isInjective_congr {u₁ u₂ v₁ v₂ f₁ f₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) (h₃ : f₁ ≈ f₂) :
    isInjective u₁ v₁ f₁ = isInjective u₂ v₂ f₂ := by
  trans isInjective u₂ v₁ f₁
  · apply IsExtentional.congr _ h₁
    fun_prop
  trans isInjective u₂ v₂ f₁
  · apply IsExtentional.congr _ h₂
    fun_prop
  · apply IsExtentional.congr _ h₃
    fun_prop

theorem isInjective_injective {x₁ x₂ y : BVSet B} :
    isInjective u v f ⊓ x₁ ∈ᴮ u ⊓ x₂ ∈ᴮ u ⊓ y ∈ᴮ v ⊓ kpair x₁ y ∈ᴮ f ⊓ kpair x₂ y ∈ᴮ f ≤ x₁ =ᴮ x₂ := by
  grw [isInjective, iInf_le _ x₁, himp_inf_le, iInf_le _ x₂, himp_inf_le, iInf_le _ y, himp_inf_le,
    himp_inf_le, himp_inf_le]

def isSurjective (u v f : BVSet B) :=
  ⨅ y, y ∈ᴮ v ⇨ ⨆ x, x ∈ᴮ u ⊓ kpair x y ∈ᴮ f

@[fun_prop] protected theorem IsExtentional.isSurjective {f g h : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) (hh : IsExtentionalFun h) :
    IsExtentional fun x => isSurjective (f x) (g x) (h x) := by
  unfold isSurjective
  fun_prop

@[gcongr] theorem isSurjective_congr {u₁ u₂ v₁ v₂ f₁ f₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) (h₃ : f₁ ≈ f₂) :
    isSurjective u₁ v₁ f₁ = isSurjective u₂ v₂ f₂ := by
  trans isSurjective u₂ v₁ f₁
  · apply IsExtentional.congr _ h₁
    fun_prop
  trans isSurjective u₂ v₂ f₁
  · apply IsExtentional.congr _ h₂
    fun_prop
  · apply IsExtentional.congr _ h₃
    fun_prop

variable [Small.{v} B]

def cardLE (u v : BVSet B) :=
  ⨆ f, isFunc u v f ⊓ isInjective u v f

infix:70 " ≲ᴮ " => cardLE

@[fun_prop] protected theorem IsExtentional.cardLE {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentional fun x => f x ≲ᴮ g x := by
  unfold cardLE
  fun_prop

@[gcongr] theorem cardLE_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ≲ᴮ v₁ = u₂ ≲ᴮ v₂ := by
  trans u₂ ≲ᴮ v₁
  · apply IsExtentional.congr _ h₁
    fun_prop
  · apply IsExtentional.congr _ h₂
    fun_prop

theorem cardLE_inf_ne_empty_le_isSurjective :
    u ≲ᴮ v ⊓ u ≠ᴮ ∅ ≤ ⨆ f, isFunc v u f ⊓ isSurjective v u f := by
  simp_rw [cardLE, iSup_inf_eq, ne_empty, inf_iSup_eq]
  refine iSup_le fun f => iSup_le fun x₀ => ?_
  let g := sep (prod v u) fun z =>
    ⨆ x, x ∈ᴮ u ⊓ ⨆ y, y ∈ᴮ v ⊓ z =ᴮ kpair y x ⊓ (kpair x y ∈ᴮ f ⊔ (x =ᴮ x₀ ⊓ (⨆ x', x' ∈ᴮ u ⊓ kpair x' y ∈ᴮ f)ᶜ))
  refine le_iSup_of_le g (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_)
  · grw [sep_subset (by fun_prop), ← le_top]
  · refine le_iInf fun y => ?_
    rw [le_himp_iff]
    apply le_of_inf_le_of_compl_le (⨆ x', x' ∈ᴮ u ⊓ kpair x' y ∈ᴮ f)
    · rw [inf_iSup_eq]
      refine iSup_le fun x => le_iSup_of_le x (le_inf ?_ ?_)
      · grw [inf_le_right, inf_le_left]
      · rw [mem_sep (by fun_prop)]
        refine le_inf ?_ (le_iSup_of_le x (le_inf ?_ (le_iSup_of_le y (le_inf (le_inf ?_ ?_) ?_))))
        · grw [← le_kpair_mem_prod]
          apply le_inf
          · grw [inf_le_left, inf_le_right]
          · grw [inf_le_right, inf_le_left]
        · grw [inf_le_right, inf_le_left]
        · grw [inf_le_left, inf_le_right]
        · simp
        · apply le_sup_of_le_left
          grw [inf_le_right, inf_le_right]
    · refine le_iSup_of_le x₀ (le_inf ?_ ?_)
      · grw [inf_le_left, inf_le_left, inf_le_right]
      · rw [mem_sep (by fun_prop)]
        refine le_inf ?_ (le_iSup_of_le x₀ (le_inf ?_ (le_iSup_of_le y (le_inf (le_inf ?_ ?_) ?_))))
        · grw [← le_kpair_mem_prod]
          apply le_inf
          · grw [inf_le_left, inf_le_right]
          · grw [inf_le_left, inf_le_left, inf_le_right]
        · grw [inf_le_left, inf_le_left, inf_le_right]
        · grw [inf_le_left, inf_le_right]
        · simp
        · refine le_sup_of_le_right (le_inf ?_ ?_)
          · simp
          · grw [inf_le_right]
  · refine le_iInf fun y => le_himp_iff.2 (le_iInf fun x₁ => le_himp_iff.2 (le_iInf fun x₂ => ?_))
    grw [le_himp_iff, le_himp_iff, mem_sep_le_apply (by fun_prop), inf_iSup_eq]
    refine iSup_le fun x₁' => ?_
    grw [inf_le_right (a := _ ∈ᴮ u), inf_iSup_eq]
    refine iSup_le fun y' => ?_
    grw [inf_le_right (a := _ ∈ᴮ v), ← inf_assoc, inf_right_comm, kpair_eq_kpair, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) x₁ x₁'
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) y y'
    grw [le_himp_iff, mem_sep_le_apply (by fun_prop), inf_iSup_eq]
    refine iSup_le fun x₂' => ?_
    grw [inf_le_right (a := _ ∈ᴮ u), inf_iSup_eq]
    refine iSup_le fun y'' => ?_
    grw [inf_le_right (a := _ ∈ᴮ v), ← inf_assoc, inf_right_comm, kpair_eq_kpair, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) x₂ x₂'
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) y y''
    rw [inf_sup_left, inf_sup_left, inf_sup_right, inf_sup_right]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · grw [inf_le_left (b := x₀ ∈ᴮ u), inf_right_comm _ (y ∈ᴮ v), inf_right_comm _ (y ∈ᴮ v),
        isInjective, iInf_le _ x₁, inf_assoc _ _ (x₁ ∈ᴮ u), himp_inf_le, iInf_le _ x₂, inf_assoc _ _ (x₂ ∈ᴮ u),
        himp_inf_le, iInf_le _ y, inf_assoc _ _ (y ∈ᴮ v), himp_inf_le, inf_assoc _ _ (kpair x₁ _ ∈ᴮ _),
        himp_inf_le, inf_assoc, himp_inf_le, inf_le_right]
    · grw [inf_right_comm, ← inf_assoc, ← bot_le (a := x₁ =ᴮ x₂), inf_compl_le_bot]
      refine le_iSup_of_le x₂ (le_inf ?_ ?_)
      · grw [inf_le_left, inf_le_left, inf_le_right]
      · grw [inf_le_left, inf_le_right]
    · grw [← inf_assoc, ← bot_le (a := x₁ =ᴮ x₂), inf_compl_le_bot]
      refine le_iSup_of_le x₁ (le_inf ?_ ?_)
      · grw [inf_le_left, inf_le_left, inf_le_left, inf_le_right]
      · grw [inf_le_left, inf_le_right]
    · grw [inf_le_left (a := x₁ =ᴮ x₀), inf_le_left (a := x₂ =ᴮ x₀), inf_assoc, eq_symm x₂ x₀, eq_trans, inf_le_right]
  · refine le_iInf fun x => le_himp_iff.2 ?_
    grw [inf_le_left (a := isFunc _ _ _), inf_le_left (a := isFunc _ _ _), ← inf_idem (x ∈ᴮ u), ← inf_assoc,
      isFunc_total', iSup_inf_eq]
    refine iSup_mono fun y => le_inf ?_ ?_
    · grw [inf_le_left, inf_le_left]
    · rw [mem_sep (by fun_prop)]
      refine le_inf ?_ (le_iSup_of_le x (le_inf ?_ (le_iSup_of_le y (le_inf (le_inf ?_ ?_) (le_sup_of_le_left ?_)))))
      · grw [← le_kpair_mem_prod, inf_le_left (a := y ∈ᴮ v)]
      · grw [inf_le_right]
      · grw [inf_le_left, inf_le_left]
      · simp
      · grw [inf_le_left, inf_le_right]

@[simp]
theorem cardLE_refl : u ≲ᴮ u = ⊤ := by
  rw [eq_top_iff]
  apply le_iSup_of_le <| (u.prod u).sep fun y => ⨆ x, x ∈ᴮ u ⊓ y =ᴮ kpair x x
  refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
  · rw [sep_subset (by fun_prop)]
  · refine le_iInf fun x => le_himp_iff.2 (le_iSup_of_le x (le_inf ?_ ?_))
    · grw [inf_le_right]
    · rw [top_inf_eq, mem_sep (by fun_prop)]
      refine le_inf ?_ (le_iSup_of_le x ?_)
      · grw [← le_kpair_mem_prod]
        simp
      · simp
  · refine le_iInf fun x => le_himp_iff.2 (le_iInf fun y₁ => le_himp_iff.2 (le_iInf fun y₂ => le_himp_iff.2 ?_))
    grw [top_inf_eq, le_himp_iff, mem_sep_le_apply (by fun_prop), inf_iSup_eq]
    refine iSup_le fun y => ?_
    rw [← inf_assoc, kpair_eq_kpair, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) y₁ y
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) x y
    grw [le_himp_iff, mem_sep_le_apply (by fun_prop), inf_iSup_eq]
    refine iSup_le fun y => ?_
    rw [← inf_assoc, kpair_eq_kpair, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) y₂ y
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) x y
    simp
  · refine le_iInf fun x₁ => le_himp_iff.2 (le_iInf fun x₂ => le_himp_iff.2 (le_iInf fun y => le_himp_iff.2 ?_))
    grw [top_inf_eq, le_himp_iff, mem_sep_le_apply (by fun_prop), inf_iSup_eq]
    refine iSup_le fun y₁ => ?_
    rw [← inf_assoc, kpair_eq_kpair, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) y y₁
    apply IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) x₁ y
    grw [le_himp_iff, mem_sep_le_apply (by fun_prop), inf_iSup_eq]
    refine iSup_le fun y₂ => ?_
    rw [← inf_assoc, kpair_eq_kpair, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le (by fun_prop) (by fun_prop) y y₂
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) x₂ y₂
    simp

theorem cardLE_trans : u ≲ᴮ v ⊓ v ≲ᴮ w ≤ u ≲ᴮ w := by
  rw [cardLE, iSup_inf_eq]
  refine iSup_le fun f => ?_
  rw [cardLE, inf_iSup_eq]
  refine iSup_le fun g => le_iSup_of_le ((u.prod w).sep fun p =>
    ⨆ x, x ∈ᴮ u ⊓ ⨆ y, y ∈ᴮ v ⊓ ⨆ z, z ∈ᴮ w ⊓ kpair x y ∈ᴮ f ⊓ kpair y z ∈ᴮ g ⊓ p =ᴮ kpair x z) ?_
  refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
  · grw [sep_subset (by fun_prop), ← le_top]
  · grw [inf_le_left (b := isInjective u v f), inf_le_left (b := isInjective v w g)]
    refine le_iInf fun x => ?_
    grw [le_himp_iff, inf_inf_distrib_right, isFunc_total', iSup_inf_eq]
    refine iSup_le fun y => ?_
    grw [inf_comm (y ∈ᴮ v), inf_assoc, inf_inf_distrib_left (y ∈ᴮ v), inf_comm (y ∈ᴮ v), isFunc_total', iSup_inf_eq, inf_iSup_eq]
    refine iSup_le fun z => ?_
    rw [inf_comm (z ∈ᴮ w), ← inf_assoc, ← inf_assoc, ← inf_assoc]
    refine le_iSup_of_le z (le_inf ?_ ?_)
    · grw [inf_le_left, inf_le_left, inf_le_right]
    · grw [mem_sep (by fun_prop), ← le_kpair_mem_prod]
      refine le_inf (le_inf ?_ ?_) (le_iSup_of_le x (le_inf ?_ (le_iSup_of_le y (le_inf ?_
        (le_iSup_of_le z (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_))))))
      · grw [inf_le_right]
      · grw [inf_le_left, inf_le_left, inf_le_right]
      · grw [inf_le_right]
      · grw [inf_le_left, inf_le_right]
      · grw [inf_le_left, inf_le_left, inf_le_right]
      · grw [inf_le_left, inf_le_left, inf_le_left, inf_le_left]
      · grw [inf_le_left, inf_le_left, inf_le_left, inf_le_right]
      · simp
  · grw [inf_le_left (b := isInjective u v f), inf_le_left (b := isInjective v w g)]
    refine le_iInf fun x => le_himp_iff.2 (le_iInf fun z₁ => le_himp_iff.2 (le_iInf fun z₂ => le_himp_iff.2 ?_))
    grw [le_himp_iff, mem_sep_le_apply (by fun_prop), inf_iSup_eq]
    refine iSup_le fun x₁ => ?_
    rw [← inf_assoc, inf_iSup_eq]
    refine iSup_le fun y₁ => ?_
    rw [← inf_assoc, inf_iSup_eq]
    refine iSup_le fun z₁' => ?_
    rw [← inf_assoc, ← inf_assoc, ← inf_assoc, kpair_eq_kpair, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) z₁ z₁'
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) x x₁
    grw [le_himp_iff, mem_sep_le_apply (by fun_prop), inf_iSup_eq]
    refine iSup_le fun x₂ => ?_
    rw [← inf_assoc, inf_iSup_eq]
    refine iSup_le fun y₂ => ?_
    rw [← inf_assoc, inf_iSup_eq]
    refine iSup_le fun z₂' => ?_
    rw [← inf_assoc, ← inf_assoc, ← inf_assoc, kpair_eq_kpair, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) z₂ z₂'
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) x x₂
    apply le_of_inf_le (y₁ =ᴮ y₂)
    · grw [← isFunc_unique' (u := u) (v := v) (f := f) (x := x)]
      refine le_inf (le_inf (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_) ?_) ?_
      · repeat grw [inf_le_left]
      · iterate 4 grw [inf_le_left]
        grw [inf_le_right]
      · iterate 8 grw [inf_le_left]
        grw [inf_le_right]
      · grw [inf_le_left, inf_le_left, inf_le_left, inf_le_right]
      · iterate 6 grw [inf_le_left]
        grw [inf_le_right]
      · grw [inf_le_left, inf_le_right]
    · apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) y₁ y₂
      grw [← isFunc_unique' (u := v) (v := w) (f := g) (x := y₁)]
      refine le_inf (le_inf (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_) ?_) ?_
      · iterate 13 grw [inf_le_left]
        grw [inf_le_right]
      · grw [inf_le_left, inf_le_left, inf_le_left, inf_le_right]
      · iterate 7 grw [inf_le_left]
        grw [inf_le_right]
      · grw [inf_le_left, inf_le_left, inf_le_right]
      · iterate 5 grw [inf_le_left]
        grw [inf_le_right]
      · grw [inf_le_right]
  · grw [inf_le_right (b := isInjective u v f), inf_le_right (b := isInjective v w g)]
    refine le_iInf fun x₁ => le_himp_iff.2 (le_iInf fun x₂ => le_himp_iff.2 (le_iInf fun z => le_himp_iff.2 ?_))
    grw [le_himp_iff, mem_sep_le_apply (by fun_prop), inf_iSup_eq]
    refine iSup_le fun x₁' => ?_
    rw [← inf_assoc, inf_iSup_eq]
    refine iSup_le fun y₁ => ?_
    rw [← inf_assoc, inf_iSup_eq]
    refine iSup_le fun z₁ => ?_
    rw [← inf_assoc, ← inf_assoc, ← inf_assoc, kpair_eq_kpair, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) z z₁
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) x₁ x₁'
    grw [le_himp_iff, mem_sep_le_apply (by fun_prop), inf_iSup_eq]
    refine iSup_le fun x₂' => ?_
    rw [← inf_assoc, inf_iSup_eq]
    refine iSup_le fun y₂ => ?_
    rw [← inf_assoc, inf_iSup_eq]
    refine iSup_le fun z₂ => ?_
    rw [← inf_assoc, ← inf_assoc, ← inf_assoc, kpair_eq_kpair, ← inf_assoc]
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) z z₂
    apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) x₂ x₂'
    apply le_of_inf_le (y₁ =ᴮ y₂)
    · grw [← isInjective_injective (u := v) (v := w) (f := g) (y := z)]
      refine le_inf (le_inf (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_) ?_) ?_
      · iterate 13 grw [inf_le_left]
        grw [inf_le_right]
      · iterate 8 grw [inf_le_left]
        grw [inf_le_right]
      · iterate 3 grw [inf_le_left]
        grw [inf_le_right]
      · iterate 2 grw [inf_le_left]
        grw [inf_le_right]
      · iterate 5 grw [inf_le_left]
        grw [inf_le_right]
      · grw [inf_le_right]
    · apply IsExtentional.inf_eq_le_of_le' (by fun_prop) (by fun_prop) y₁ y₂
      grw [← isInjective_injective (u := u) (v := v) (f := f) (y := y₁)]
      refine le_inf (le_inf (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_) ?_) ?_
      · repeat grw [inf_le_left]
      · iterate 9 grw [inf_le_left]
        grw [inf_le_right]
      · iterate 4 grw [inf_le_left]
        grw [inf_le_right]
      · iterate 3 grw [inf_le_left]
        grw [inf_le_right]
      · iterate 6 grw [inf_le_left]
        grw [inf_le_right]
      · grw [inf_le_left, inf_le_right]

theorem cardLE_trans' : v ≲ᴮ w ⊓ u ≲ᴮ v ≤ u ≲ᴮ w := by
  grw [inf_comm, cardLE_trans]

def cardLT (u v : BVSet B) :=
  u ≲ᴮ v ⊓ (v ≲ᴮ u)ᶜ

infix:70 " <ᴮ " => cardLT

@[fun_prop] protected theorem IsExtentional.cardLT {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentional fun x => f x <ᴮ g x := by
  unfold cardLT
  fun_prop

@[gcongr] theorem cardLT_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ <ᴮ v₁ = u₂ <ᴮ v₂ := by
  trans u₂ <ᴮ v₁
  · apply IsExtentional.congr _ h₁
    fun_prop
  · apply IsExtentional.congr _ h₂
    fun_prop

theorem cardLT_le_cardLE : u <ᴮ v ≤ u ≲ᴮ v :=
  inf_le_left

theorem cardLT_le_compl_cardLE : u <ᴮ v ≤ (v ≲ᴮ u)ᶜ :=
  inf_le_right

theorem cardLT_irrefl : u <ᴮ u = ⊥ := by
  simp [cardLT]

theorem cardLT_trans_cardLE : u <ᴮ v ⊓ v ≲ᴮ w ≤ u <ᴮ w := by
  apply le_inf
  · grw [cardLT_le_cardLE, cardLE_trans]
  · grw [← inf_compl_le_bot, compl_compl, inf_assoc, cardLE_trans, cardLT_le_compl_cardLE, compl_inf_self]

theorem cardLT_trans_cardLE' : u ≲ᴮ v ⊓ v <ᴮ w ≤ u <ᴮ w := by
  apply le_inf
  · grw [cardLT_le_cardLE, cardLE_trans]
  · grw [← inf_compl_le_bot, compl_compl, inf_right_comm, cardLE_trans', cardLT_le_compl_cardLE, inf_compl_self]

def cardEQ (u v : BVSet B) :=
  u ≲ᴮ v ⊓ v ≲ᴮ u

infix:70 " ≈ᴮ " => cardEQ

@[fun_prop] protected theorem IsExtentional.cardEQ {f g : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) :
    IsExtentional fun x => f x ≈ᴮ g x := by
  unfold cardEQ
  fun_prop

@[gcongr] theorem cardEQ_congr {u₁ u₂ v₁ v₂ : BVSet B} (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) :
    u₁ ≈ᴮ v₁ = u₂ ≈ᴮ v₂ := by
  trans u₂ ≈ᴮ v₁
  · apply IsExtentional.congr _ h₁
    fun_prop
  · apply IsExtentional.congr _ h₂
    fun_prop

end BVSet

namespace ZFSet

open BVSet

variable {x y : ZFSet.{v}}

theorem toBVSet_pair :
    (x.pair y).toBVSet ≈ kpair (x.toBVSet : BVSet B) y.toBVSet := by
  simp only [ZFSet.pair, kpair]
  grw [ZFSet.toBVSet_insert, ZFSet.toBVSet_singleton, ZFSet.toBVSet_singleton, ZFSet.toBVSet_insert,
    ZFSet.toBVSet_singleton]

theorem toBVSet_prod [Small.{v} B] :
    (x.prod y).toBVSet ≈ x.toBVSet.prod (y.toBVSet : BVSet B) := by
  apply BVSet.ext
  intro u
  apply le_antisymm
  · rw [ZFSet.mem_toBVSet]
    apply iSup_le
    intro ⟨z, hz⟩
    simp only [mem_prod] at hz
    rcases hz with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    rw [BVSet.mem_prod, IsExtentional.iSup_mem_toBVSet_inf (by fun_prop)]
    apply le_iSup_of_le ⟨z₁, hz₁⟩
    rw [IsExtentional.iSup_mem_toBVSet_inf (by fun_prop)]
    apply le_iSup_of_le ⟨z₂, hz₂⟩
    simp only
    grw [ZFSet.toBVSet_pair]
  · rw [BVSet.mem_prod, IsExtentional.iSup_mem_toBVSet_inf (by fun_prop)]
    apply iSup_le
    intro ⟨z₁, hz₁⟩
    rw [IsExtentional.iSup_mem_toBVSet_inf (by fun_prop)]
    apply iSup_le
    intro ⟨z₂, hz₂⟩
    rw [ZFSet.mem_toBVSet]
    apply le_iSup_of_le ⟨z₁.pair z₂, by simp [hz₁, hz₂]⟩
    simp only
    grw [ZFSet.toBVSet_pair]

theorem isFunc_toBVSet_of_isFunc [Small.{v} B] {f : ZFSet} (h : ZFSet.IsFunc x y f) :
    isFunc x.toBVSet y.toBVSet f.toBVSet = (⊤ : B) := by
  unfold isFunc
  rw [inf_eq_top_iff, inf_eq_top_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · grw [← ZFSet.toBVSet_prod]
    rw [ZFSet.toBVSet_subset_toBVSet_of_subset h.1]
  · rw [IsExtentional.iInf_mem_toBVSet_himp (by fun_prop), iInf_eq_top]
    intro ⟨a, ha⟩
    rw [IsExtentional.iSup_mem_toBVSet_inf (by fun_prop), eq_top_iff]
    rcases h.2 a ha with ⟨b, hb, -⟩
    have hb' := h.1 hb
    simp only [ZFSet.mem_prod, ZFSet.pair_inj, exists_eq_right_right'] at hb'
    apply le_iSup_of_le ⟨b, hb'.2⟩
    simp only [top_le_iff]
    grw [← ZFSet.toBVSet_pair, ZFSet.toBVSet_mem_toBVSet_of_mem hb]
  · rw [IsExtentional.iInf_mem_toBVSet_himp (by fun_prop), iInf_eq_top]
    intro ⟨a, ha⟩
    rw [IsExtentional.iInf_mem_toBVSet_himp (by fun_prop), iInf_eq_top]
    intro ⟨b₁, hb₁⟩
    rw [IsExtentional.iInf_mem_toBVSet_himp (by fun_prop), iInf_eq_top]
    intro ⟨b₂, hb₂⟩
    simp only [himp_eq_top_iff, le_himp_iff, ge_iff_le]
    grw [← ZFSet.toBVSet_pair, ← ZFSet.toBVSet_pair]
    by_cases h₁ : a.pair b₁ ∈ f
    · by_cases h₂ : a.pair b₂ ∈ f
      · simp [(h.2 a ha).unique h₁ h₂]
      · simp [ZFSet.toBVSet_mem_toBVSet_of_notMem h₂]
    · simp [ZFSet.toBVSet_mem_toBVSet_of_notMem h₁]

theorem isInjective_toBVSet_of_injOn {f : ZFSet → ZFSet} [ZFSet.Definable₁ f] (hf : Set.InjOn f x) :
    isInjective x.toBVSet y.toBVSet (ZFSet.map f x).toBVSet = (⊤ : B) := by
  rw [eq_top_iff, isInjective, IsExtentional.iInf_mem_toBVSet_himp (by fun_prop)]
  refine le_iInf fun z₁ => ?_
  rw [IsExtentional.iInf_mem_toBVSet_himp (by fun_prop)]
  refine le_iInf fun z₂ => ?_
  rw [IsExtentional.iInf_mem_toBVSet_himp (by fun_prop)]
  refine le_iInf fun z => ?_
  grw [← ZFSet.toBVSet_pair, ← ZFSet.toBVSet_pair]
  by_cases hz₁ : z₁.1.pair z ∈ ZFSet.map f x
  · grw [ZFSet.toBVSet_mem_toBVSet_of_mem hz₁, top_himp]
    by_cases hz₂ : z₂.1.pair z ∈ ZFSet.map f x
    · grw [ZFSet.toBVSet_mem_toBVSet_of_mem hz₂, top_himp]
      simp only [ZFSet.mem_map, ZFSet.pair_inj, ↓existsAndEq, SetLike.coe_mem, true_and] at hz₁ hz₂
      simp [Subtype.val_inj.1 (hf z₁.2 z₂.2 (hz₁.trans hz₂.symm))]
    · simp [ZFSet.toBVSet_mem_toBVSet_of_notMem hz₂]
  · simp [ZFSet.toBVSet_mem_toBVSet_of_notMem hz₁]

theorem isSurjective_toBVSet_of_surjOn {f : ZFSet → ZFSet} [ZFSet.Definable₁ f] (hf : Set.SurjOn f x y) :
    isSurjective x.toBVSet y.toBVSet (ZFSet.map f x).toBVSet = (⊤ : B) := by
  rw [eq_top_iff, isSurjective, IsExtentional.iInf_mem_toBVSet_himp (by fun_prop)]
  refine le_iInf fun z => ?_
  rcases hf z.2 with ⟨z', hz', hz⟩
  simp only [SetLike.mem_coe] at hz'
  rw [IsExtentional.iSup_mem_toBVSet_inf (by fun_prop)]
  apply le_iSup_of_le ⟨z', hz'⟩
  grw [← ZFSet.toBVSet_pair, ZFSet.toBVSet_mem_toBVSet_of_mem]
  simp [hz', hz]

open Cardinal

theorem cardLE_toBVSet_of_card_le_card [Small.{v} B] (h : x.card ≤ y.card) :
    x.toBVSet ≲ᴮ y.toBVSet = (⊤ : B) := by
  classical
  haveI := @Classical.allZFSetDefinable
  rw [← lift_le, ← ZFSet.cardinalMk_coe_sort, ← ZFSet.cardinalMk_coe_sort, Cardinal.le_def] at h
  rcases h with ⟨f⟩
  let g : ZFSet := ZFSet.map (fun z => if hz : z ∈ x then f ⟨z, hz⟩ else ∅) x
  rw [eq_top_iff]
  apply le_iSup_of_le g.toBVSet
  rw [ZFSet.isFunc_toBVSet_of_isFunc, ZFSet.isInjective_toBVSet_of_injOn, top_inf_eq]
  · intro z₁ hz₁ z₂ hz₂ h
    simp only [SetLike.mem_coe] at hz₁ hz₂
    simpa [hz₁, hz₂] using h
  · rw [ZFSet.map_isFunc]
    intro z hz
    simp [hz]

theorem cardLE_toBVSet_of_card_gt_card [Small.{v} B] [CountableChainCondition B]
    (h : y.card < x.card) : x.toBVSet ≲ᴮ y.toBVSet = (⊥ : B) := by
  have hxne : x.toBVSet ≠ᴮ ∅ = (⊤ : B) := by
    grw [← ZFSet.toBVSet_empty, ZFSet.toBVSet_eq_toBVSet_of_ne, compl_bot]
    rintro rfl
    simp at h
  rw [← lift_lt, ← ZFSet.cardinalMk_coe_sort, ← ZFSet.cardinalMk_coe_sort] at h
  rcases le_or_gt x.card ℵ₀ with hx | hx
  · rw [← lift_le, ← ZFSet.cardinalMk_coe_sort, lift_aleph0] at hx
    haveI : Finite y := by rw [← lt_aleph0_iff_finite]; exact h.trans_le hx
    grw [eq_bot_iff, ← inf_top_eq (_ ≲ᴮ _), ← hxne, cardLE_inf_ne_empty_le_isSurjective]
    apply iSup_le
    intro f
    rw [← inf_idem (isFunc _ _ _)]
    nth_grw 2 [isFunc_total]
    rw [IsExtentional.iInf_mem_toBVSet_himp (by fun_prop)]
    conv_lhs => enter [1, 2, 1, z]; rw [IsExtentional.iSup_mem_toBVSet_inf (by fun_prop)]
    rw [iInf_iSup_eq_of_finite, inf_iSup_eq, iSup_inf_eq]
    apply iSup_le
    intro g
    have : ¬ g.Surjective := fun hg => (Cardinal.mk_le_of_surjective hg).not_gt h
    simp only [Function.Surjective, not_forall, not_exists] at this
    rcases this with ⟨z, hz⟩
    grw [isSurjective, IsExtentional.iInf_mem_toBVSet_himp (by fun_prop), iInf_le _ z,
      IsExtentional.iSup_mem_toBVSet_inf (by fun_prop), inf_iSup_eq]
    apply iSup_le
    intro z'
    grw [iInf_le _ z', ← inf_top_eq (isFunc _ _ _), ← ZFSet.toBVSet_mem_toBVSet_of_mem z.2,
      ← inf_top_eq (isFunc _ _ _), ← ZFSet.toBVSet_mem_toBVSet_of_mem (g z').2,
      ← inf_top_eq (isFunc _ _ _), ← ZFSet.toBVSet_mem_toBVSet_of_mem z'.2, isFunc_unique']
    simp [ZFSet.toBVSet_eq_toBVSet_of_ne (Subtype.val_injective.ne (hz z'))]
  · rw [← lift_lt, ← ZFSet.cardinalMk_coe_sort, lift_aleph0, aleph0_lt_mk_iff] at hx
    by_contra
    grw [← ne_eq, ← bot_lt_iff_ne_bot, ← inf_top_eq (_ ≲ᴮ _), ← hxne,
      cardLE_inf_ne_empty_le_isSurjective, bot_lt_iSup] at this
    rcases this with ⟨f, hf⟩
    generalize ha : isFunc (y.toBVSet : BVSet B) x.toBVSet f ⊓ isSurjective y.toBVSet x.toBVSet f = a at hf
    rw [← inf_idem a] at hf
    nth_grw 2 [← ha, inf_le_right] at hf
    rw [isSurjective, IsExtentional.iInf_mem_toBVSet_himp (by fun_prop), inf_iInf] at hf
    apply forall_lt_of_lt_iInf at hf
    conv at hf =>
      intro z
      rw [IsExtentional.iSup_mem_toBVSet_inf (by fun_prop), inf_iSup_eq, bot_lt_iSup]
    choose g hg using hf
    rcases exists_uncountable_fiber g h hx with ⟨z, hz⟩
    apply hz.not_countable
    rw [Set.countable_coe_iff]
    apply Set.countable_of_injective_of_countable_image
      (f := fun z' => a ⊓ kpair z.1.toBVSet z'.1.toBVSet ∈ᴮ f)
    · rintro z₁ hz₁ z₂ hz₂ h
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz₁ hz₂ h
      have := hg z₁
      rw [← inf_idem (a ⊓ _)] at this
      nth_rw 2 [hz₁] at this
      rw [h, hz₁, ← inf_inf_distrib_left, ← inf_assoc, ← ha] at this
      nth_grw 3 [inf_le_left] at this
      rw [← inf_top_eq (isFunc _ _ _), ← ZFSet.toBVSet_mem_toBVSet_of_mem z₂.2,
        ← inf_top_eq (isFunc _ _ _), ← ZFSet.toBVSet_mem_toBVSet_of_mem z₁.2,
        ← inf_top_eq (isFunc _ _ _), ← ZFSet.toBVSet_mem_toBVSet_of_mem z.2] at this
      grw [isFunc_unique'] at this
      by_contra! hne
      simp [ZFSet.toBVSet_eq_toBVSet_of_ne (Subtype.val_injective.ne hne)] at this
    · apply CountableChainCondition.ccc
      apply Set.Pairwise.image
      simp only [Set.Pairwise, Set.mem_preimage, Set.mem_singleton_iff, ne_eq, Function.onFun]
      rintro z₁ hz₁ z₂ hz₂ hne
      by_contra
      rw [disjoint_iff, ← ne_eq, ← bot_lt_iff_ne_bot, ← inf_inf_distrib_left, ← inf_assoc, ← ha] at this
      nth_grw 3 [inf_le_left] at this
      rw [← inf_top_eq (isFunc _ _ _), ← ZFSet.toBVSet_mem_toBVSet_of_mem z₂.2,
        ← inf_top_eq (isFunc _ _ _), ← ZFSet.toBVSet_mem_toBVSet_of_mem z₁.2,
        ← inf_top_eq (isFunc _ _ _), ← ZFSet.toBVSet_mem_toBVSet_of_mem z.2] at this
      grw [isFunc_unique'] at this
      simp [ZFSet.toBVSet_eq_toBVSet_of_ne (Subtype.val_injective.ne hne)] at this

theorem cardLT_toBVSet_of_card_lt_card [Small.{v} B] [CountableChainCondition B]
    (h : x.card < y.card) : x.toBVSet <ᴮ y.toBVSet = (⊤ : B) := by
  simp [cardLT, cardLE_toBVSet_of_card_le_card h.le, cardLE_toBVSet_of_card_gt_card h]

theorem cardLT_toBVSet_of_card_ge_card [Small.{v} B]
    (h : y.card ≤ x.card) : x.toBVSet <ᴮ y.toBVSet = (⊥ : B) := by
  simp [cardLT, cardLE_toBVSet_of_card_le_card h]

theorem cardEQ_toBVSet_of_card_eq_card [Small.{v} B] [CountableChainCondition B]
    (h : x.card = y.card) : x.toBVSet ≈ᴮ y.toBVSet = (⊤ : B) := by
  simp [cardEQ, cardLE_toBVSet_of_card_le_card h.le, cardLE_toBVSet_of_card_le_card h.ge]

theorem cardEQ_toBVSet_of_card_ne_card [Small.{v} B] [CountableChainCondition B]
    (h : x.card ≠ y.card) : x.toBVSet ≈ᴮ y.toBVSet = (⊥ : B) := by
  rcases h.lt_or_gt with h | h <;> simp [cardEQ, cardLE_toBVSet_of_card_gt_card h]

end ZFSet
