import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.PrimeIdeal
import Mathlib.Order.ZornAtoms

namespace Order

variable {P : Type*}

open CompleteLattice

namespace Ideal

section OrderTop

theorem eq_top_iff_top_mem [LE P] [OrderTop P] {I : Ideal P} :
    I = ⊤ ↔ ⊤ ∈ I :=
  ⟨fun h => h ▸ Set.mem_univ _, top_of_top_mem⟩

theorem isProper_iff_top_notMem [LE P] [OrderTop P] {I : Ideal P} :
    I.IsProper ↔ ⊤ ∉ I := by
  rw [isProper_iff_ne_top, ne_eq, eq_top_iff_top_mem]

theorem isProper_principal_iff [PartialOrder P] [OrderTop P] {a : P} :
    (principal a).IsProper ↔ a ≠ ⊤ := by
  rw [isProper_iff_top_notMem, mem_principal, top_le_iff]

end OrderTop

section CompleteLattice

variable [CompleteLattice P] {I : Ideal P}

theorem biSup_mem_iff {α} {s : Set α} {f : α → P} (hs : s.Finite) :
    ⨆ i ∈ s, f i ∈ I ↔ ∀ i ∈ s, f i ∈ I := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    rw [iSup_insert, sup_mem_iff, ih]
    simp

theorem iSup_mem_iff {α} [Finite α] {f : α → P} : ⨆ i, f i ∈ I ↔ ∀ i, f i ∈ I := by
  simpa [← Equiv.plift.symm.iSup_comp, Equiv.plift.forall_congr_left]
    using biSup_mem_iff (f := f ∘ PLift.down) Set.finite_univ

theorem iSup_mem {α} [Finite α] {f : α → P} (hf : ∀ i, f i ∈ I) : ⨆ i, f i ∈ I :=
  iSup_mem_iff.2 hf

end CompleteLattice

section SemilatticeSup

variable [SemilatticeSup P] [OrderTop P] [OrderBot P]

instance : IsCoatomic (Ideal P) := by
  apply IsCoatomic.of_isChain_bounded
  intro S hS₁ hS₂ hS₃
  let I : Ideal P := {
    carrier := ⋃ s ∈ S, ↑s
    lower' a b h ha := by
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ha ⊢
      rcases ha with ⟨I, hI, ha⟩
      exact ⟨I, hI, I.lower h ha⟩
    nonempty' := by
      rcases hS₂ with ⟨I, hI⟩
      exact Set.nonempty_biUnion.2 ⟨I, hI, I.nonempty⟩
    directed' a ha b hb := by
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ha hb ⊢
      rcases ha with ⟨I, hI, ha⟩
      rcases hb with ⟨J, hJ, hb⟩
      wlog h : I ≤ J generalizing I J a b
      · specialize this _ _ _ hJ hb _ hI ha (hS₁.lt_of_not_ge hI hJ h).le
        grind
      exact ⟨a ⊔ b, ⟨J, hJ, J.sup_mem (h ha) hb⟩, le_sup_left, le_sup_right⟩
  }
  refine ⟨I, ?_, ?_⟩
  · by_contra! hI
    rw [eq_top_iff_top_mem] at hI
    rcases Set.mem_iUnion₂.1 hI with ⟨I, hI, hI'⟩
    rw [SetLike.mem_coe, ← eq_top_iff_top_mem] at hI'
    subst hI'
    contradiction
  · intro J hJ
    rw [← SetLike.coe_subset_coe]
    apply Set.subset_iUnion₂ J hJ

theorem IsProper.exists_le_maximal {I : Ideal P} (hI : I.IsProper) : ∃ J ≥ I, J.IsMaximal := by
  rcases IsCoatomic.eq_top_or_exists_le_coatom I with rfl | ⟨J, hJ, hJ'⟩
  · simp [isProper_iff_ne_top] at hI
  · exact ⟨J, hJ', isMaximal_iff_isCoatom.2 hJ⟩

theorem exists_maximal [Nontrivial P] : ∃ (I : Ideal P), I.IsMaximal := by
  have : (⊥ : Ideal P).IsProper := by
    rw [isProper_iff_ne_top, ← principal_bot, ← SetLike.coe_ne_coe, coe_top,
      Set.ne_univ_iff_exists_notMem]
    simp_rw [SetLike.mem_coe, mem_principal, le_bot_iff]
    exact exists_ne _
  rcases IsProper.exists_le_maximal this with ⟨I, -, hI⟩
  exact ⟨I, hI⟩

end SemilatticeSup

theorem isPrime_iff_isMaximal [BooleanAlgebra P] {I : Ideal P} : IsPrime I ↔ IsMaximal I :=
  ⟨fun _ => IsPrime.isMaximal, fun _ => IsMaximal.isPrime⟩

end Ideal

namespace PFilter

section Preorder

variable [Preorder P]

def dualIso : PFilter P ≃o Ideal Pᵒᵈ where
  toFun := dual
  invFun := mk
  map_rel_iff' := Iff.rfl

abbrev IsProper (F : PFilter P) :=
  F.dual.IsProper

abbrev IsUltra (F : PFilter P) :=
  F.dual.IsMaximal

theorem IsUltra.isProper {F : PFilter P} (hF : F.IsUltra) : F.IsProper := hF.1

theorem IsUltra.maximal_proper {F G : PFilter P} (hF : F.IsUltra) (hG : F < G) :
    (G : Set P) = Set.univ := hF.2 hG

end Preorder

section Directed

variable [Preorder P] [IsDirected P (· ≥ ·)] [Nonempty P] {F : PFilter P}

instance : OrderTop (PFilter P) where
  top := ⟨⊤⟩
  le_top _ _ _ := LowerSet.mem_top

theorem isProper_iff_ne_top : IsProper F ↔ F ≠ ⊤ :=
  Ideal.isProper_iff_ne_top.trans dualIso.injective.ne_iff

theorem isMaximal_iff_isCoatom {F : PFilter P} : IsUltra F ↔ IsCoatom F :=
  Ideal.isMaximal_iff_isCoatom.trans (dualIso.isCoatom_iff _)

end Directed

section OrderBot

theorem eq_top_iff_bot_mem [Preorder P] [OrderBot P] {F : PFilter P} : F = ⊤ ↔ ⊥ ∈ F :=
  Iff.trans (by rw [← dualIso.map_top]; exact dualIso.apply_eq_iff_eq.symm)
    F.dual.eq_top_iff_top_mem

theorem isProper_iff_bot_notMem [Preorder P] [OrderBot P] {F : PFilter P} :
    F.IsProper ↔ ⊥ ∉ F := by
  rw [isProper_iff_ne_top, ne_eq, eq_top_iff_bot_mem]

alias ⟨IsProper.bot_notMem, _⟩ := isProper_iff_bot_notMem

theorem isProper_principal_iff [PartialOrder P] [OrderBot P] {a : P} :
    (principal a).IsProper ↔ a ≠ ⊥ := by
  rw [isProper_iff_bot_notMem, mem_principal, le_bot_iff]

end OrderBot

section SemilatticeInf

variable [SemilatticeInf P] [OrderBot P] [OrderTop P]

theorem IsProper.exists_le_ultra {F : PFilter P} (hF : F.IsProper) : ∃ G ≥ F, G.IsUltra := by
  rcases Ideal.IsProper.exists_le_maximal hF with ⟨I, hI, hI'⟩
  exact ⟨mk I, hI, hI'⟩

theorem exists_ultrafilter [Nontrivial P] : ∃ (F : PFilter P), F.IsUltra := by
  rcases Ideal.exists_maximal (P := Pᵒᵈ) with ⟨I, hI⟩
  exact ⟨mk I, hI⟩

end SemilatticeInf

section CompleteLattice

variable [CompleteLattice P] {F : PFilter P}

theorem biInf_mem_iff {α} {s : Set α} {f : α → P} (hs : s.Finite) :
    ⨅ i ∈ s, f i ∈ F ↔ ∀ i ∈ s, f i ∈ F := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    rw [iInf_insert, inf_mem_iff, ih]
    simp

theorem iInf_mem_iff {α} [Finite α] {f : α → P} : ⨅ i, f i ∈ F ↔ ∀ i, f i ∈ F := by
  simpa [← Equiv.plift.symm.iInf_comp, Equiv.plift.forall_congr_left]
    using biInf_mem_iff (f := f ∘ PLift.down) Set.finite_univ

theorem iInf_mem {α} [Finite α] {f : α → P} (hf : ∀ i, f i ∈ F) : ⨅ i, f i ∈ F :=
  iInf_mem_iff.2 hf

end CompleteLattice

section BooleanAlgebra

variable [BooleanAlgebra P] {F : PFilter P} {x y : P}

theorem IsProper.notMem_of_compl_mem (hF : IsProper F) (hx : xᶜ ∈ F) : x ∉ F :=
  Ideal.IsProper.notMem_of_compl_mem hF hx

theorem IsProper.compl_notMem_of_mem (hF : IsProper F) (hx : x ∈ F) : xᶜ ∉ F :=
  hF.notMem_of_compl_mem (by simpa)

theorem IsProper.notMem_or_compl_notMem (hF : IsProper F) : x ∉ F ∨ xᶜ ∉ F :=
  Ideal.IsProper.notMem_or_compl_notMem hF

theorem IsUltra.mem_or_compl_mem (hF : IsUltra F) (x : P) : x ∈ F ∨ xᶜ ∈ F :=
  hF.isPrime.mem_or_compl_mem

theorem IsUltra.compl_mem_iff_notMem (hF : IsUltra F) : xᶜ ∈ F ↔ x ∉ F :=
  ⟨hF.isProper.notMem_of_compl_mem, (hF.mem_or_compl_mem x).resolve_left⟩

theorem IsUltra.mem_iff_compl_notMem (hF : IsUltra F) : x ∈ F ↔ xᶜ ∉ F :=
  ⟨hF.isProper.compl_notMem_of_mem, (hF.mem_or_compl_mem x).resolve_right⟩

theorem IsUltra.sup_mem_iff (hF : IsUltra F) : x ⊔ y ∈ F ↔ x ∈ F ∨ y ∈ F := by
  rw [hF.mem_iff_compl_notMem, compl_sup, F.inf_mem_iff, not_and_or, ← hF.mem_iff_compl_notMem,
    ← hF.mem_iff_compl_notMem]

theorem IsUltra.himp_mem_iff (hF : IsUltra F) : x ⇨ y ∈ F ↔ x ∈ F → y ∈ F := by
  rw [himp_eq, hF.sup_mem_iff, hF.compl_mem_iff_notMem]
  tauto

end BooleanAlgebra

section CompleteBooleanAlgebra

theorem IsUltra.iSup_mem_iff [CompleteBooleanAlgebra P] {F : PFilter P} (hF : IsUltra F) {α}
    [Finite α] {f : α → P} : ⨆ i, f i ∈ F ↔ ∃ i, f i ∈ F := by
  rw [hF.mem_iff_compl_notMem, compl_iSup, F.iInf_mem_iff, not_forall]
  simp_rw [hF.compl_mem_iff_notMem, not_not]

end CompleteBooleanAlgebra

end PFilter

end Order
