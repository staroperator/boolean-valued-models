import BooleanValuedModels.BVSet.Defs

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

def isRel (u v f : BVSet B) :=
  ⨅ z, z ∈ᴮ f ⇨ ⨆ x, x ∈ᴮ u ⊓ ⨆ y, y ∈ᴮ v ⊓ z =ᴮ kpair x y

@[fun_prop] protected theorem IsExtentional.isRel {f g h : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) (hh : IsExtentionalFun h) :
    IsExtentional fun x => isRel (f x) (g x) (h x) := by
  unfold isRel
  fun_prop

@[gcongr] theorem isRel_congr {u₁ u₂ v₁ v₂ f₁ f₂ : BVSet B}
    (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) (h₃ : f₁ ≈ f₂) :
    isRel u₁ v₁ f₁ = isRel u₂ v₂ f₂ := by
  trans isRel u₂ v₁ f₁
  · apply IsExtentional.congr _ h₁
    fun_prop
  trans isRel u₂ v₂ f₁
  · apply IsExtentional.congr _ h₂
    fun_prop
  · apply IsExtentional.congr _ h₃
    fun_prop

theorem isRel_eq_subset_prod [Small.{v} B] :
    isRel u v f = f ⊆ᴮ prod u v := by
  simp [isRel, subset_def', mem_prod]

def isUnique (u v f : BVSet B) :=
  ⨅ x, x ∈ᴮ u ⇨ ⨅ y₁, y₁ ∈ᴮ v ⇨ ⨅ y₂, y₂ ∈ᴮ v ⇨ kpair x y₁ ∈ᴮ f ⇨ kpair x y₂ ∈ᴮ f ⇨ y₁ =ᴮ y₂

@[fun_prop] protected theorem IsExtentional.isUnique {f g h : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) (hh : IsExtentionalFun h) :
    IsExtentional fun x => isUnique (f x) (g x) (h x) := by
  unfold isUnique
  fun_prop

@[gcongr] theorem isUnique_congr {u₁ u₂ v₁ v₂ f₁ f₂ : BVSet B}
    (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) (h₃ : f₁ ≈ f₂) :
    isUnique u₁ v₁ f₁ = isUnique u₂ v₂ f₂ := by
  trans isUnique u₂ v₁ f₁
  · apply IsExtentional.congr _ h₁
    fun_prop
  trans isUnique u₂ v₂ f₁
  · apply IsExtentional.congr _ h₂
    fun_prop
  · apply IsExtentional.congr _ h₃
    fun_prop

def isTotal (u v f : BVSet B) :=
  ⨅ x, x ∈ᴮ u ⇨ ⨆ y, y ∈ᴮ v ⊓ kpair x y ∈ᴮ f

@[fun_prop] protected theorem IsExtentional.isTotal {f g h : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) (hh : IsExtentionalFun h) :
    IsExtentional fun x => isTotal (f x) (g x) (h x) := by
  unfold isTotal
  fun_prop

@[gcongr] theorem isTotal_congr {u₁ u₂ v₁ v₂ f₁ f₂ : BVSet B}
    (h₁ : u₁ ≈ u₂) (h₂ : v₁ ≈ v₂) (h₃ : f₁ ≈ f₂) :
    isTotal u₁ v₁ f₁ = isTotal u₂ v₂ f₂ := by
  trans isTotal u₂ v₁ f₁
  · apply IsExtentional.congr _ h₁
    fun_prop
  trans isTotal u₂ v₂ f₁
  · apply IsExtentional.congr _ h₂
    fun_prop
  · apply IsExtentional.congr _ h₃
    fun_prop

def isFunc (u v f : BVSet B) :=
  isRel u v f ⊓ isTotal u v f ⊓ isUnique u v f

@[fun_prop] protected theorem IsExtentional.isFunc {f g h : BVSet B → BVSet B}
    (hf : IsExtentionalFun f) (hg : IsExtentionalFun g) (hh : IsExtentionalFun h) :
    IsExtentional fun x => isFunc (f x) (g x) (h x) := by
  unfold isFunc
  fun_prop

@[gcongr] theorem isFunc_congr {u₁ u₂ v₁ v₂ f₁ f₂ : BVSet B}
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

theorem isFunc_total :
    isFunc u v f ≤ ⨅ x, x ∈ᴮ u ⇨ ⨆ y, y ∈ᴮ v ⊓ kpair x y ∈ᴮ f :=
  inf_le_of_left_le inf_le_right

theorem isFunc_total' {x} :
    isFunc u v f ⊓ x ∈ᴮ u ≤ ⨆ y, y ∈ᴮ v ⊓ kpair x y ∈ᴮ f := by
  grw [isFunc_total, iInf_le _ x, himp_inf_le]

theorem isFunc_unique :
    isFunc u v f ≤ ⨅ x, x ∈ᴮ u ⇨ ⨅ y₁, y₁ ∈ᴮ v ⇨ ⨅ y₂, y₂ ∈ᴮ v ⇨ kpair x y₁ ∈ᴮ f ⇨ kpair x y₂ ∈ᴮ f ⇨ y₁ =ᴮ y₂ :=
  inf_le_right

theorem isFunc_unique' {x y₁ y₂ : BVSet B} :
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

end BVSet
