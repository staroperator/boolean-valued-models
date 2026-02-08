module

public import Mathlib.Logic.Small.Set
public import Mathlib.Tactic.ApplyAt

/-!
# Definition of `BVSet`

`BVSet B` is characterized as `BVSet B ≃ (s : {s : Set (BVSet.{u, v} B) // Small.{v} s}) × (s.1 → B)`.
The current definition first defines `BVMultiset B` characterized as
`BVMultiset.{u, v} B ≃ {s : Set (BVMultiset B × B) // Small.{v} s}` (via quotient of `BVTree`) and
define `BVSet B` as those whose `s` is a function.

## TODO

`BVSet B` may be definable directly via `QPF.Fix`.
-/

universe u v

inductive BVTree (B : Type u)
| mk (Index : Type v) (dom : Index → BVTree B) (val : Index → B)

variable {B : Type u}

namespace BVTree

def Equiv : BVTree.{u, v} B → BVTree.{u, v} B → Prop
| ⟨uIndex, udom, uval⟩, ⟨vIndex, vdom, vval⟩ =>
  (∀ i : uIndex, ∃ j : vIndex, (udom i).Equiv (vdom j) ∧ uval i = vval j)
  ∧ (∀ j : vIndex, ∃ i : uIndex, (udom i).Equiv (vdom j) ∧ vval j = uval i)

theorem Equiv.refl : ∀ (u : BVTree B), Equiv u u
| ⟨_, _, _⟩ => ⟨fun i => ⟨i, refl _, rfl⟩, fun i => ⟨i, refl _, rfl⟩⟩

theorem Equiv.symm : ∀ {u v : BVTree B}, Equiv u v → Equiv v u
| ⟨_, _, _⟩, ⟨_, _, _⟩, ⟨h₁, h₂⟩ =>
  ⟨fun j => (h₂ j).elim fun i ⟨hi, hi'⟩ => ⟨i, hi.symm, hi'⟩,
   fun i => (h₁ i).elim fun j ⟨hj, hj'⟩ => ⟨j, hj.symm, hj'⟩⟩

theorem Equiv.trans : ∀ {u v w : BVTree B}, Equiv u v → Equiv v w → Equiv u w
| ⟨_, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, ⟨h₁, h₁'⟩, ⟨h₂, h₂'⟩ =>
  ⟨fun i => (h₁ i).elim fun j ⟨hj, hj'⟩ => (h₂ j).elim fun k ⟨hk, hk'⟩ =>
    ⟨k, hj.trans hk, hj'.trans hk'⟩,
   fun k => (h₂' k).elim fun j ⟨hj, hj'⟩ => (h₁' j).elim fun i ⟨hi, hi'⟩ =>
     ⟨i, hi.trans hj, hj'.trans hi'⟩⟩

instance setoid : Setoid (BVTree B) where
  r u v := Equiv u v
  iseqv.refl := Equiv.refl
  iseqv.symm := Equiv.symm
  iseqv.trans := Equiv.trans

def Mem : BVTree.{u, v} B → B → BVTree.{u, v} B → Prop
| u, b, ⟨_, vdom, vval⟩ => ∃ i, (vdom i).Equiv u ∧ vval i = b

theorem Mem.congr_left : ∀ {u v : BVTree B}, u ≈ v → ∀ {w b}, Mem u b w ↔ Mem v b w
| _, _, h, ⟨_, _, _⟩, _ =>
  ⟨fun ⟨i, hi⟩ => ⟨i, hi.1.trans h, hi.2⟩,
   fun ⟨i, hi⟩ => ⟨i, hi.1.trans h.symm, hi.2⟩⟩

theorem Mem.ext : ∀ {u v : BVTree B}, (∀ w b, Mem w b u ↔ Mem w b v) → u ≈ v
| ⟨_, udom, uval⟩, ⟨_, vdom, vval⟩, h =>
  ⟨fun i => ((h (udom i) (uval i)).1 ⟨i, Equiv.refl _, rfl⟩).elim fun j hj =>
    ⟨j, hj.1.symm, hj.2.symm⟩,
   fun i => ((h (vdom i) (vval i)).2 ⟨i, Equiv.refl _, rfl⟩).elim fun j hj =>
    ⟨j, hj.1, hj.2.symm⟩⟩

theorem Mem.congr_right : ∀ {u v : BVTree B}, u ≈ v → ∀ {w b}, Mem w b u ↔ Mem w b v
| ⟨_, _, _⟩, ⟨_, _, _⟩, h, _, _ =>
  ⟨fun ⟨i, hi⟩ => (h.1 i).elim fun j hj => ⟨j, hj.1.symm.trans hi.1, hj.2.symm.trans hi.2⟩,
   fun ⟨i, hi⟩ => (h.2 i).elim fun j hj => ⟨j, hj.1.trans hi.1, hj.2.symm.trans hi.2⟩⟩

instance : Membership (BVTree B) (BVTree B) where
  mem v u := ∃ b, Mem u b v

theorem mem_acc_aux : ∀ {u v : BVTree.{u, v} B}, u ≈ v → Acc (· ∈ ·) v
| ⟨_, _, _⟩, ⟨_, _, _⟩, h =>
  ⟨_, fun _ ⟨_, ⟨i, hi⟩⟩ => (h.right i).elim fun _ hj => mem_acc_aux (hj.1.trans hi.1)⟩

theorem mem_acc (u : BVTree.{u, v} B) : Acc (· ∈ ·) u :=
  mem_acc_aux (Equiv.refl u)

theorem mem_wf : WellFounded (· ∈ · : BVTree B → BVTree B → Prop) :=
  ⟨mem_acc⟩

end BVTree

def BVMultiset (B : Type u) :=
  Quotient (@BVTree.setoid.{u, v} B)

namespace BVMultiset

def Mem (u : BVMultiset B) (b : B) (v : BVMultiset B) : Prop :=
  Quotient.liftOn₂ u v (fun u v => BVTree.Mem u b v) fun _ _ _ _ h₁ h₂ =>
    propext <| (BVTree.Mem.congr_left h₁).trans <| BVTree.Mem.congr_right h₂

theorem Mem.ext {u v : BVMultiset B} : (∀ w b, Mem w b u ↔ Mem w b v) → u = v :=
  Quotient.inductionOn₂ u v fun _ _ h => Quotient.sound (BVTree.Mem.ext fun w => h ⟦w⟧)

instance : Membership (BVMultiset B) (BVMultiset B) where
  mem v u := Quotient.liftOn₂ u v (· ∈ ·) fun _ _ _ _ h₁ h₂ =>
    propext <| exists_congr fun _ => (BVTree.Mem.congr_left h₁).trans <| BVTree.Mem.congr_right h₂

theorem mem_def {u v : BVMultiset B} : u ∈ v ↔ ∃ b, Mem u b v :=
  Quotient.inductionOn₂ u v fun _ _ => Iff.rfl

theorem mem_wf : WellFounded (· ∈ · : BVMultiset B → BVMultiset B → Prop) :=
  (@wellFounded_lift₂_iff _ _ (· ∈ ·) fun _ _ _ _ h₁ h₂ =>
    propext <| exists_congr fun _ => (BVTree.Mem.congr_left h₁).trans <|
      BVTree.Mem.congr_right h₂).2 BVTree.mem_wf

instance : WellFoundedRelation (BVMultiset B) where
  rel u v := u ∈ v
  wf := mem_wf

def dom (u : BVMultiset B) : Set (BVMultiset B × B) :=
  {(v, b) | Mem v b u}

instance small_dom (u : BVMultiset.{u, v} B) : Small.{v} u.dom :=
  Quotient.inductionOn u fun ⟨uIndex, udom, uval⟩ =>
    small_of_surjective (α := uIndex) (f := fun i => ⟨⟨⟦udom i⟧, uval i⟩, ⟨i, .refl _, rfl⟩⟩) (by
      intro ⟨⟨v, b⟩, hv⟩
      induction v using Quotient.inductionOn with | _ v
      rcases hv with ⟨i, hi⟩
      refine ⟨i, Subtype.mk_eq_mk.2 <| Prod.mk_inj.2 ⟨Quotient.sound hi.1, hi.2⟩⟩)

noncomputable def mk (s : Set (BVMultiset.{u, v} B × B)) [Small.{v} s] : BVMultiset B :=
  ⟦⟨Shrink s, fun x => ((equivShrink s).symm x).1.1.out, fun x => ((equivShrink s).symm x).1.2⟩⟧

theorem mem_mk_iff {s : Set (BVMultiset.{u, v} B × B)} [Small.{v} s] {u : BVMultiset B} {b} :
    Mem u b (mk s) ↔ (u, b) ∈ s := by
  induction u using Quotient.inductionOn with | _ u
  refine (equivShrink s).exists_congr_right.symm.trans ?_
  simp only [Equiv.symm_apply_apply, Subtype.exists, exists_and_left, exists_prop, Prod.exists,
    ↓existsAndEq, and_true]
  constructor
  · intro ⟨v, hv, hv'⟩
    rwa [Quotient.mk_eq_iff_out.2 hv.symm]
  · intro h
    exact ⟨⟦u⟧, Quotient.mk_out u, h⟩

theorem dom_mk {s : Set (BVMultiset.{u, v} B × B)} [Small.{v} s] : (mk s).dom = s := by
  ext ⟨u, b⟩
  simp [dom, mem_mk_iff]

theorem mk_dom {u : BVMultiset B} : mk u.dom = u := by
  apply Mem.ext
  simp [mem_mk_iff, dom]

noncomputable def domEquiv : BVMultiset.{u, v} B ≃ {s : Set (BVMultiset B × B) // Small.{v} s} where
  toFun u := ⟨u.dom, small_dom u⟩
  invFun s := have := s.2; mk s.1
  left_inv u := by simp [mk_dom]
  right_inv s := by simp [dom_mk]

def WellFormed (u : BVMultiset B) : Prop :=
  (∀ v ∈ u, WellFormed v) ∧ (∀ v b₁ b₂, Mem v b₁ u → Mem v b₂ u → b₁ = b₂)
termination_by u

end BVMultiset

@[pp_with_univ]
public def BVSet (B : Type u) :=
  {u : BVMultiset.{u, v} B // u.WellFormed}

namespace BVSet

@[no_expose]
public noncomputable instance : Membership (BVSet B) (BVSet B) where
  mem v u := u.1 ∈ v.1

theorem mem_def {u v : BVSet B} : u ∈ v ↔ u.1 ∈ v.1 := Iff.rfl

public theorem mem_wf : WellFounded (· ∈ · : BVSet B → BVSet B → Prop) :=
  (Subtype.relEmbedding (· ∈ ·) BVMultiset.WellFormed).wellFounded BVMultiset.mem_wf

public noncomputable instance : WellFoundedRelation (BVSet B) where
  rel u v := u ∈ v
  wf := mem_wf

@[expose, coe]
public noncomputable def dom (u : BVSet B) : Set (BVSet B) :=
  {v | v ∈ u}

public noncomputable instance : CoeSort (BVSet.{u, v} B) (Type (max (v + 1) u)) := ⟨(·.dom)⟩

@[simp]
public theorem mem_dom_iff {u v : BVSet B} : u ∈ v.dom ↔ u ∈ v := Iff.rfl

@[simp]
public theorem dom_mem {u : BVSet B} {i : u.dom} : i.1 ∈ u := i.2

public noncomputable def val (u : BVSet B) (x : u.dom) : B :=
  Classical.choose (BVMultiset.mem_def.1 x.2)

public noncomputable instance : CoeFun (BVSet B) (fun u => u.dom → B) := ⟨(·.val)⟩

theorem dom_val_mem {u : BVSet B} {x : u.dom} : x.1.1.Mem (u.val x) u.1 :=
  Classical.choose_spec (BVMultiset.mem_def.1 x.2)

theorem val_eq_of_mem {u : BVSet B} {x : u.dom} {b} : x.1.1.Mem b u.1 → u.val x = b := by
  intro h
  have := u.2
  rw [BVMultiset.WellFormed] at this
  exact this.2 _ _ _ dom_val_mem h

theorem mem_iff_val_eq {u x : BVSet B} {b} : x.1.Mem b u.1 ↔ ∃ h, u.val ⟨x, h⟩ = b := by
  constructor
  · intro h
    exists (BVMultiset.mem_def.2 ⟨b, h⟩)
    exact val_eq_of_mem h
  · rintro ⟨_, rfl⟩
    exact dom_val_mem

public instance small_dom (u : BVSet.{u, v} B) : Small.{v} u.dom :=
  @small_of_injective (u.dom) _ (BVMultiset.small_dom u.1)
    (fun x => ⟨⟨x.1.1, u.val x⟩, dom_val_mem⟩)
    fun _ _ => by simp +contextual [Subtype.val_inj]

@[ext]
public protected theorem ext {u v : BVSet.{u, v} B} (h₁ : u.dom = v.dom)
    (h₂ : ∀ i hi hi', u.val ⟨i, hi⟩ = v.val ⟨i, hi'⟩) : u = v := by
  apply Subtype.val_injective
  apply BVMultiset.Mem.ext
  intro w b
  constructor
  · intro hw
    have hw' : w ∈ u.1 := BVMultiset.mem_def.2 ⟨b, hw⟩
    have hw'' : w.WellFormed := by
      have := u.2
      rw [BVMultiset.WellFormed] at this
      exact this.1 w hw'
    rw [mem_iff_val_eq (x := ⟨w, hw''⟩)]
    exists h₁ ▸ hw'
    rw [← h₂ _ hw']
    exact val_eq_of_mem hw
  · intro hw
    have hw' : w ∈ v.1 := BVMultiset.mem_def.2 ⟨b, hw⟩
    have hw'' : w.WellFormed := by
      have := v.2
      rw [BVMultiset.WellFormed] at this
      exact this.1 w hw'
    rw [mem_iff_val_eq (x := ⟨w, hw''⟩)]
    exists h₁ ▸ hw'
    rw [h₂ _ _ hw']
    exact val_eq_of_mem hw

public noncomputable def mk (s : Set (BVSet.{u, v} B)) [Small.{v} s] (b : s → B) : BVSet B :=
  ⟨BVMultiset.mk (Set.range fun u : s => (u.1.1, b u)), by
    rw [BVMultiset.WellFormed]
    constructor
    · intro _ h
      simp_rw [BVMultiset.mem_def, BVMultiset.mem_mk_iff, Set.mem_range, Prod.mk_inj] at h
      rcases h with ⟨_, u, rfl, rfl⟩
      exact u.1.2
    · intro u b₁ b₂ h₁ h₂
      simp_rw [BVMultiset.mem_mk_iff, Set.mem_range, Prod.mk_inj] at h₁ h₂
      rcases h₁ with ⟨_, rfl, rfl⟩
      simp only [Subtype.val_inj] at h₂
      rcases h₂ with ⟨_, rfl, rfl⟩
      rfl⟩

@[simp]
public theorem mem_mk_iff {s : Set (BVSet.{u, v} B)} [Small.{v} s] {b : s → B} {u : BVSet B} :
    u ∈ mk s b ↔ u ∈ s := by
  simp [mk, mem_def, BVMultiset.mem_def, BVMultiset.mem_mk_iff, Subtype.val_inj]

public theorem dom_mk {s : Set (BVSet.{u, v} B)} [Small.{v} s] {b : s → B} : (mk s b).dom = s := by
  ext u
  simp

public theorem val_mk_apply {s : Set (BVSet.{u, v} B)} [Small.{v} s] {b : s → B} {i : (mk s b).dom} :
    (mk s b).val i = b ⟨i.1, (Set.ext_iff.1 dom_mk _).1 i.2⟩ := by
  apply val_eq_of_mem
  have : i.1 ∈ s := by simp [← dom_mk (s := s) (b := b)]
  simp [mk, BVMultiset.mem_mk_iff, Subtype.val_inj, this]

public theorem val_mk_heq {s : Set (BVSet.{u, v} B)} [Small.{v} s] {b : s → B} :
    (mk s b).val ≍ b := by
  apply Function.hfunext
  · simp [dom_mk]
  · rintro ⟨i, _⟩ ⟨j, _⟩ h
    apply Subtype.mk.hinj rfl (by simp) at h
    rcases h with ⟨_, _, h⟩
    rw [heq_eq_eq] at h
    simp [h, val_mk_apply]

public theorem mk_dom_val {u : BVSet.{u, v} B} : mk u.dom u.val = u := by
  apply BVSet.ext <;> simp [dom_mk, val_mk_apply]

@[expose]
public noncomputable def domValEquiv :
    BVSet.{u, v} B ≃ (s : {s : Set (BVSet.{u, v} B) // Small.{v} s}) × (s.1 → B) where
  toFun u := ⟨⟨u.dom, small_dom u⟩, u.val⟩
  invFun s := have := s.1.2; mk s.1.1 s.2
  left_inv u := by simp [mk_dom_val]
  right_inv s := by ext <;> simp [val_mk_heq]

@[elab_as_elim]
public protected theorem induction {motive : BVSet B → Prop} (u : BVSet B)
    (h : ∀ u, (∀ x ∈ u, motive x) → motive u) : motive u :=
  mem_wf.induction u h

end BVSet
