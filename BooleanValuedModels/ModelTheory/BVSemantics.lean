module

public import BooleanValuedModels.BooleanAlgebra.Ultrafilter
public import Mathlib.ModelTheory.Satisfiability

import BooleanValuedModels.BooleanAlgebra.Lemmas

@[expose] public section

namespace FirstOrder.Language

class BVStructure (L : Language.{u, v}) (M : Type*) (B : outParam Type*) [CompleteBooleanAlgebra B]
    where
  funMap : ∀ {n}, L.Functions n → (Fin n → M) → M
  relMap : ∀ {n}, L.Relations n → (Fin n → M) → B
  beq : M → M → B
  beq_refl : ∀ x, beq x x = ⊤
  beq_symm : ∀ x y, beq x y = beq y x
  beq_trans : ∀ x y z, beq x y ⊓ beq y z ≤ beq x z
  beq_funMap : ∀ {n} (f : L.Functions n) (v w : Fin n → M),
    ⨅ i, beq (v i) (w i) ≤ beq (funMap f v) (funMap f w)
  beq_relMap : ∀ {n} (r : L.Relations n) (v w : Fin n → M),
    (⨅ i, beq (v i) (w i)) ⊓ relMap r v ≤ relMap r w

variable {L : Language.{u, v}} {M B : Type*} [CompleteBooleanAlgebra B] [L.BVStructure M B]
  {α : Type w} {n}

open BVStructure

namespace Term

def bvrealize (v : α → M) : L.Term α → M
  | var k => v k
  | func f ts => funMap f fun i => (ts i).bvrealize v

@[simp]
theorem bvrealize_var (v : α → M) (k) : bvrealize v (var k : L.Term α) = v k := rfl

@[simp]
theorem bvrealize_func (v : α → M) {n} (f : L.Functions n) (ts) :
    bvrealize v (func f ts : L.Term α) = funMap f fun i => (ts i).bvrealize v := rfl

@[simp]
theorem bvrealize_function_term {n} (v : Fin n → M) (f : L.Functions n) :
    f.term.bvrealize v = funMap f v := by
  rfl

@[simp]
theorem bvrealize_relabel {β} {t : L.Term α} {g : α → β} {v : β → M} :
    (t.relabel g).bvrealize v = t.bvrealize (v ∘ g) := by
  induction t with
  | var => rfl
  | func f ts ih => simp [ih]

theorem beq_le_beq_bvrealize {t : L.Term α} {v w : α → M} :
    ⨅ i, beq L (v i) (w i) ≤ beq L (t.bvrealize v) (t.bvrealize w) := by
  induction t with
  | var i =>
    exact iInf_le _ i
  | func f ts ih =>
    exact (le_iInf fun i => ih i).trans (beq_funMap f _ _)

end Term

namespace BoundedFormula

def bvrealize : ∀ {n}, L.BoundedFormula α n → (α → M) → (Fin n → M) → B
  | _, falsum, _v, _xs => ⊥
  | _, equal t₁ t₂, v, xs => beq L (t₁.bvrealize (Sum.elim v xs)) (t₂.bvrealize (Sum.elim v xs))
  | _, rel R ts, v, xs => relMap R fun i => (ts i).bvrealize (Sum.elim v xs)
  | _, imp f₁ f₂, v, xs => bvrealize f₁ v xs ⇨ bvrealize f₂ v xs
  | _, all f, v, xs => ⨅ x : M, bvrealize f v (Fin.snoc xs x)

variable {n : ℕ} {φ ψ : L.BoundedFormula α n} {θ : L.BoundedFormula α (n + 1)}
variable {v : α → M} {xs : Fin n → M}

@[simp]
theorem bvrealize_bot : (⊥ : L.BoundedFormula α n).bvrealize v xs = ⊥ :=
  rfl

@[simp]
theorem bvrealize_imp : (φ.imp ψ).bvrealize v xs = φ.bvrealize v xs ⇨ ψ.bvrealize v xs :=
  rfl

@[simp]
theorem bvrealize_not : φ.not.bvrealize v xs = (φ.bvrealize v xs)ᶜ := by
  simp [BoundedFormula.not]

@[simp]
theorem bvrealize_bdEqual (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (t₁.bdEqual t₂).bvrealize v xs
      = beq L (t₁.bvrealize (Sum.elim v xs)) (t₂.bvrealize (Sum.elim v xs)) :=
  rfl

@[simp]
theorem bvrealize_top : (⊤ : L.BoundedFormula α n).bvrealize v xs = ⊤ := by simp [Top.top]

@[simp]
theorem bvrealize_inf : (φ ⊓ ψ).bvrealize v xs = φ.bvrealize v xs ⊓ ψ.bvrealize v xs := by
  simp [bvrealize]

@[simp]
theorem bvrealize_sup : (φ ⊔ ψ).bvrealize v xs = φ.bvrealize v xs ⊔ ψ.bvrealize v xs := by
  simp [max, compl_himp_eq]

@[simp]
theorem bvrealize_all : (all θ).bvrealize v xs = ⨅ a : M, θ.bvrealize v (Fin.snoc xs a) :=
  rfl

@[simp]
theorem bvrealize_ex : θ.ex.bvrealize v xs = ⨆ a : M, θ.bvrealize v (Fin.snoc xs a) := by
  simp [BoundedFormula.ex, compl_iInf]

@[simp]
theorem bvrealize_iff :
    (φ.iff ψ).bvrealize v xs = bihimp (φ.bvrealize v xs) (ψ.bvrealize v xs) := by
  simpa [BoundedFormula.iff, bihimp_def] using inf_comm _ _

theorem bvrealize_mapTermRel_add_castLe {β} {L' : Language} [L'.BVStructure M B] {k : ℕ}
    {ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin (k + n)))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n}
    (v : ∀ {n}, (Fin (k + n) → M) → α → M) {v' : β → M} (xs : Fin (k + n) → M)
    (h1 :
      ∀ (n) (t : L.Term (α ⊕ (Fin n))) (xs' : Fin (k + n) → M),
        (ft n t).bvrealize (Sum.elim v' xs') = t.bvrealize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _)))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), relMap (fr n R) x = relMap R x)
    (h3 : ∀ (x y : M), beq L' x y = beq L x y)
    (hv : ∀ (n) (xs : Fin (k + n) → M) (x : M), @v (n + 1) (Fin.snoc xs x : Fin _ → M) = v xs) :
    (φ.mapTermRel ft fr fun _ => castLE (add_assoc _ _ _).symm.le).bvrealize v' xs =
      φ.bvrealize (v xs) (xs ∘ Fin.natAdd _) := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, bvrealize, h1, h3]
  | rel => simp [mapTermRel, bvrealize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, bvrealize, ih1, ih2]
  | all _ ih => simp [mapTermRel, bvrealize, ih, hv]

@[simp]
theorem bvrealize_relabel {β} {m n : ℕ} {φ : L.BoundedFormula α n} {g : α → β ⊕ (Fin m)} {v : β → M}
    {xs : Fin (m + n) → M} :
    (φ.relabel g).bvrealize v xs =
      φ.bvrealize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
  apply bvrealize_mapTermRel_add_castLe <;> simp

theorem beq_inf_bvrealize_le_bvrealize {φ : L.BoundedFormula α n} {v w : α → M} {xs ys : Fin n → M} :
    (⨅ i, beq L (v i) (w i)) ⊓ (⨅ i, beq L (xs i) (ys i)) ⊓ φ.bvrealize v xs ≤ φ.bvrealize w ys := by
  induction φ generalizing v w with
  | falsum => simp [bvrealize]
  | equal t₁ t₂ =>
    simp only [bvrealize]
    apply (beq_trans _ (t₁.bvrealize (Sum.elim v xs)) _).trans'
    apply le_inf
    · refine Term.beq_le_beq_bvrealize.trans' (le_iInf fun i => ?_)
      cases i with
      | inl i => grw [inf_le_left, inf_le_left, iInf_le _ i, beq_symm]; rfl
      | inr i => grw [inf_le_left, inf_le_right, iInf_le _ i, beq_symm]; rfl
    apply (beq_trans _ (t₂.bvrealize (Sum.elim v xs)) _).trans'
    apply le_inf
    · exact inf_le_right
    · refine Term.beq_le_beq_bvrealize.trans' (le_iInf fun i => ?_)
      cases i with
      | inl i => grw [inf_le_left, inf_le_left, iInf_le _ i]; rfl
      | inr i => grw [inf_le_left, inf_le_right, iInf_le _ i]; rfl
  | rel r ts =>
    simp only [bvrealize]
    refine (beq_relMap r _ _).trans' (inf_le_inf_right _ (le_iInf fun i => ?_))
    grw [← Term.beq_le_beq_bvrealize]
    refine le_iInf fun j => ?_
    cases j with
    | inl j => grw [inf_le_left, iInf_le _ j]; rfl
    | inr j => grw [inf_le_right, iInf_le _ j]; rfl
  | imp φ ψ ih₁ ih₂ =>
    simp only [bvrealize]
    grw [le_himp_iff, ← ih₂ (v := v) (w := w)]
    refine le_inf (inf_le_of_left_le inf_le_left) ?_
    simp_rw [fun i => beq_symm (L := L) (v i) (w i), fun i => beq_symm (L := L) (xs i) (ys i)]
    grw [inf_right_comm, ih₁, inf_himp_le]
  | all φ ih =>
    simp only [bvrealize]
    refine le_iInf fun a => ?_
    grw [← ih]
    refine le_inf (inf_le_of_left_le (inf_le_inf_left _ ?_)) (inf_le_of_right_le (iInf_le _ a))
    refine le_iInf fun i => ?_
    cases i using Fin.lastCases with
    | last => simp [beq_refl]
    | cast i => grw [iInf_le _ i]; simp

end BoundedFormula

nonrec def Formula.bvrealize (φ : L.Formula α) (v : α → M) : B :=
  φ.bvrealize v default

namespace BoundedFormula

variable {φ : L.BoundedFormula α n}

@[simp]
theorem bvrealize_alls {v : α → M} :
    φ.alls.bvrealize v = ⨅ xs : Fin n → M, φ.bvrealize v xs := by
  induction n with
  | zero => simp [alls, Formula.bvrealize]
  | succ n ih =>
    simp only [alls, ih, bvrealize]
    refine le_antisymm
      (le_iInf fun v => iInf_le_of_le (Fin.init v) <| iInf_le_of_le (v (Fin.last _)) ?_)
      (le_iInf fun v => le_iInf fun a => iInf_le_of_le (Fin.snoc v a) ?_) <;> simp

@[simp]
theorem bvrealize_exs {φ : L.BoundedFormula α n} {v : α → M} :
    φ.exs.bvrealize v = ⨆ xs : Fin n → M, φ.bvrealize v xs := by
  induction n with
  | zero => simp [exs, Formula.bvrealize]
  | succ n ih =>
    simp only [BoundedFormula.exs, ih, bvrealize_ex]
    refine le_antisymm (iSup_le fun v => iSup_le fun a => le_iSup_of_le (Fin.snoc v a) ?_)
      (iSup_le fun v => le_iSup_of_le (Fin.init v) <| le_iSup_of_le (v (Fin.last _)) ?_) <;> simp

@[simp]
theorem _root_.FirstOrder.Language.Formula.bvrealize_iAlls {β}
    [Finite β] {φ : L.Formula (α ⊕ β)} {v : α → M} : (φ.iAlls β).bvrealize v =
      ⨅ (i : β → M), φ.bvrealize (fun a => Sum.elim v i a) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  rw [Formula.iAlls]
  simp only [Nat.add_zero, bvrealize_alls, bvrealize_relabel, Function.comp_def,
    Fin.castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.iInf_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp_def],
      fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.bvrealize]
    congr
    funext i
    exact i.elim0

@[simp]
theorem bvrealize_iAlls {β} [Finite β] {φ : L.Formula (α ⊕ β)} {v : α → M} {v' : Fin 0 → M} :
    BoundedFormula.bvrealize (φ.iAlls β) v v' =
      ⨅ (i : β → M), φ.bvrealize (fun a => Sum.elim v i a) := by
  rw [← Formula.bvrealize_iAlls]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
theorem _root_.FirstOrder.Language.Formula.bvrealize_iExs {γ} [Finite γ]
    {φ : L.Formula (α ⊕ γ)} {v : α → M} : (φ.iExs γ).bvrealize v =
      ⨆ (i : γ → M), φ.bvrealize (Sum.elim v i) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iExs]
  simp only [Nat.add_zero, bvrealize_exs, bvrealize_relabel, Function.comp_def,
    Fin.castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.iSup_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp_def],
      fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.bvrealize]
    congr
    funext i
    exact i.elim0

@[simp]
theorem bvrealize_iExs {γ} [Finite γ] {φ : L.Formula (α ⊕ γ)} {v : α → M} {v' : Fin 0 → M} :
    BoundedFormula.bvrealize (φ.iExs γ) v v' =
      ⨆ (i : γ → M), φ.bvrealize (Sum.elim v i) := by
  rw [← Formula.bvrealize_iExs]; congr; simp [eq_iff_true_of_subsingleton]

end BoundedFormula

variable (M) in
nonrec def Sentence.bvrealize (φ : L.Sentence) : B :=
  φ.bvrealize (default : _ → M)

class Theory.BVModel (M : Type*) [L.BVStructure M B] (T : L.Theory) where
  bvrealize_of_mem : ∀ φ ∈ T, φ.bvrealize M = ⊤

infixl:51 " ⊨ᵇᵛ " => Theory.BVModel

namespace BVStructure

open Order

variable (L : Language) (M : Type*) [L.BVStructure M B] (F : PFilter B)

def ultraFilterSetoid : Setoid M where
  r x y := beq L x y ∈ F
  iseqv.refl x := by simp [beq_refl]
  iseqv.symm h := by simpa [beq_symm]
  iseqv.trans h₁ h₂ := F.mem_of_le (beq_trans _ _ _) (F.inf_mem h₁ h₂)

variable {L M F} in
@[simp]
theorem equiv_def {x y : M} :
    @HasEquiv.Equiv M (@instHasEquivOfSetoid _ (ultraFilterSetoid L M F)) x y ↔
      beq L x y ∈ F := Iff.rfl

abbrev QuotientStructure :=
  Quotient (ultraFilterSetoid L M F)

variable {L M F}

instance quotientStructure : L.Structure (QuotientStructure L M F) where
  funMap f v := Quotient.finLiftOn v (Quotient.mk _ ∘ BVStructure.funMap f) fun v w h => by
    apply Quotient.sound
    simp only [equiv_def] at h ⊢
    apply F.mem_of_le (beq_funMap f v w)
    exact F.iInf_mem h
  RelMap r v := Quotient.finLiftOn v (BVStructure.relMap r · ∈ F) fun v w h => by
    simp only [eq_iff_iff]
    refine ⟨fun h' => F.mem_of_le (beq_relMap r v w) <| F.inf_mem (F.iInf_mem h) h',
      fun h' => F.mem_of_le (beq_relMap r w v) <| F.inf_mem (F.iInf_mem fun i => ?_) h'⟩
    rw [beq_symm]
    exact h i

@[simp]
theorem QuotientStructure.funMap_mk {n} {f : L.Functions n} {v : Fin n → M} :
    Structure.funMap f (fun i => Quotient.mk (ultraFilterSetoid L M F) (v i))
      = ⟦BVStructure.funMap f v⟧ := by
  simp [quotientStructure]

@[simp]
theorem QuotientStructure.relMap_mk {n} {r : L.Relations n} {v : Fin n → M} :
    Structure.RelMap r (fun i => Quotient.mk (ultraFilterSetoid L M F) (v i))
      ↔ BVStructure.relMap r v ∈ F := by
  simp [quotientStructure]

@[simp]
theorem QuotientStructure.term_realize {t : L.Term α} {v : α → M} :
    t.realize (fun i => Quotient.mk (ultraFilterSetoid L M F) (v i)) = ⟦t.bvrealize v⟧ := by
  induction t with simp [*]

class IsFull (L : Language) (M : Type*) (B : outParam Type*) [CompleteBooleanAlgebra B]
    [L.BVStructure M B] where
  exists_eq_iSup : ∀ {α : Type w} {n} (φ : L.BoundedFormula α (n + 1)) (v : α → M) (xs : Fin n → M),
    ∃ (a : M), φ.bvrealize v (Fin.snoc xs a) = ⨆ x, φ.bvrealize v (Fin.snoc xs x)

@[simp]
theorem QuotientStructure.boundedFormula_realize [hM : IsFull.{w} L M B] [hF : F.IsUltra]
    {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin n → M} :
    φ.Realize (fun i => Quotient.mk (ultraFilterSetoid L M F) (v i))
      (fun i => Quotient.mk (ultraFilterSetoid L M F) (xs i)) ↔ φ.bvrealize v xs ∈ F := by
  induction φ with
  | falsum =>
    simp [BoundedFormula.Realize, BoundedFormula.bvrealize, hF.isProper.bot_notMem]
  | equal =>
    simp only [BoundedFormula.Realize, BoundedFormula.bvrealize]
    rw [← Function.comp_def, ← Function.comp_def, ← Sum.comp_elim, Function.comp_def, term_realize,
      term_realize, Quotient.eq_iff_equiv, equiv_def]
  | rel =>
    simp only [BoundedFormula.Realize, BoundedFormula.bvrealize]
    conv_lhs =>
      enter [2, i]
      rw [← Function.comp_def, ← Function.comp_def, ← Sum.comp_elim, Function.comp_def,
        term_realize]
    rw [relMap_mk]
  | imp _ _ ih₁ ih₂ =>
    simp [hF.himp_mem_iff, ih₁, ih₂]
  | all φ ih =>
    simp only [BoundedFormula.Realize, BoundedFormula.bvrealize]
    refine ⟨fun h => ?_, fun h x => ?_⟩
    · by_contra
      rw [← hF.compl_mem_iff_notMem, compl_iInf] at this
      rcases hM.exists_eq_iSup (∼ φ) v xs with ⟨a, ha⟩
      simp only [BoundedFormula.bvrealize_not] at ha
      rw [← ha, hF.compl_mem_iff_notMem, ← ih] at this
      apply this
      convert h ⟦a⟧ with i
      cases i using Fin.lastCases with simp
    · induction x using Quotient.inductionOn with | _ x
      have := F.mem_of_le (iInf_le _ x) h
      rw [← ih] at this
      convert this with i
      cases i using Fin.lastCases with simp

@[simp]
theorem QuotientStructure.formula_realize [hM : IsFull.{w} L M B] [hF : F.IsUltra] {φ : L.Formula α}
    {v : α → M} :
    φ.Realize (fun i => Quotient.mk (ultraFilterSetoid L M F) (v i)) ↔ φ.bvrealize v ∈ F := by
  rw [Formula.Realize, Formula.bvrealize]
  convert boundedFormula_realize (hF := hF) (φ := φ) (v := v) (xs := default)

@[simp]
theorem QuotientStructure.sentence_realize [hM : IsFull.{0} L M B] [hF : F.IsUltra]
    {φ : L.Sentence} :
    QuotientStructure L M F ⊨ φ ↔ φ.bvrealize M ∈ F := by
  rw [Sentence.Realize, Sentence.bvrealize]
  convert formula_realize (F := F) (M := M) (φ := φ)

variable {T : L.Theory} [M ⊨ᵇᵛ T] {φ : L.Sentence}

instance [IsFull.{0} L M B] [F.IsUltra] : QuotientStructure L M F ⊨ T where
  realize_of_mem φ hφ := by
    rw [QuotientStructure.sentence_realize, Theory.BVModel.bvrealize_of_mem _ hφ]
    exact F.top_mem

theorem bvrealize_eq_top_of_entails [Nonempty M] [IsFull.{0} L M B] [Nontrivial B] :
    T ⊨ᵇ φ → φ.bvrealize M = (⊤ : B) := by
  intro h
  by_contra hne
  have : (PFilter.principal (φ.bvrealize M)ᶜ).IsProper := by
    rwa [PFilter.isProper_principal_iff, ne_eq, compl_eq_bot]
  rcases this.exists_le_ultra with ⟨F, hF, hF'⟩
  rw [ge_iff_le, PFilter.principal_le_iff] at hF
  haveI : Nonempty (QuotientStructure L M F) := by rw [nonempty_quotient_iff]; infer_instance
  have := h.realize_sentence (QuotientStructure L M F)
  rw [QuotientStructure.sentence_realize] at this
  exact hF'.notMem_of_compl_mem hF this

theorem not_entails_of_bvrealize_ne_top [Nonempty M] [IsFull.{0} L M B] [Nontrivial B] :
    φ.bvrealize M ≠ (⊤ : B) → ¬ T ⊨ᵇ φ :=
  mt bvrealize_eq_top_of_entails

end FirstOrder.Language.BVStructure
