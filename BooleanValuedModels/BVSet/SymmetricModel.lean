module

public import BooleanValuedModels.BVSet.Ordinal
public import BooleanValuedModels.BVSet.Relations
public import BooleanValuedModels.BooleanAlgebra.GroupAction
public import BooleanValuedModels.ModelTheory.BVSemantics
public import BooleanValuedModels.ZFC.Syntax
public import Mathlib.Algebra.Group.Subgroup.Pointwise

import BooleanValuedModels.ModelTheory.FinLemmas
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.DepRewrite
import Mathlib.Tactic.FinCases

@[expose] public section

universe u v w

theorem MulAction.smul_mem_orbit_iff {α M} [Group M] [MulAction M α] {a₁ a₂ : α} (m : M) :
    m • a₂ ∈ orbit M a₁ ↔ a₂ ∈ orbit M a₁ :=
  ⟨fun h => inv_smul_smul m a₂ ▸ mem_orbit_of_mem_orbit m⁻¹ h, mem_orbit_of_mem_orbit _⟩

theorem OrderIso.trans_assoc {α β γ δ : Type*} [LE α] [LE β] [LE γ] [LE δ] (ab : α ≃o β) (bc : β ≃o γ) (cd : γ ≃o δ) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) := rfl

variable {B : Type u} [CompleteBooleanAlgebra B]

namespace BVSet

noncomputable def map (f : B ≃o B) (u : BVSet.{u, v} B) : BVSet.{u, v} B :=
  mkI u.dom (fun ⟨x, _⟩ => map f x) fun x => f (u.val x)
termination_by u

variable {f : B ≃o B} {u v : BVSet.{u, v} B}

private lemma map_symm_map : map f.symm (map f u) = u := by
  induction u using BVSet.induction generalizing f with | _ u ih
  rw [map, map]
  refine BVSet.ext ?_ fun i _ hi => ?_
  · ext
    simp only [mem_dom_iff, mem_mkI_iff, Subtype.exists, exists_prop, exists_exists_and_eq_and]
    grind
  · simp only [val_mkI_apply, Set.mem_preimage, Set.mem_singleton_iff]
    apply le_antisymm
    · apply iSup₂_le
      rintro _ rfl
      rw [← f.le_iff_le, f.apply_symm_apply]
      apply iSup₂_le
      rintro ⟨j, hj⟩ h
      simp
      apply congr_arg (map f.symm) at h
      rw [ih] at h
      simp only at h
      subst h
      rfl
      exact hj
    · apply le_iSup₂_of_le ⟨map f i, by simpa using ⟨_, hi, rfl⟩⟩ (by rw [ih _ hi])
      rw [f.le_symm_apply]
      apply le_iSup₂_of_le ⟨i, hi⟩ (by simp)
      rfl

theorem mem_map_iff {u} : u ∈ map f v ↔ ∃ w ∈ v, map f w = u := by
  rw [map]
  simp

lemma map_mem_map (h : u ∈ v) : map f u ∈ map f v := by
  simpa [mem_map_iff] using ⟨u, h, rfl⟩

@[simp]
theorem map_mem_map_iff : map f u ∈ map f v ↔ u ∈ v :=
  ⟨fun h => by simpa [map_symm_map] using map_mem_map (f := f.symm) h, map_mem_map⟩

@[simp]
theorem map_inj : map f u = map f v ↔ u = v :=
  ⟨fun h => by simpa [map_symm_map] using congr_arg (map f.symm) h, congr_arg _⟩

theorem dom_map : (map f u).dom = (map f) '' u.dom := by
  ext
  simp [mem_map_iff]

theorem val_map_apply (h) : (map f u).val ⟨map f v, map_mem_map h⟩ = f (u.val ⟨v, h⟩) := by
  rw! [map, val_mkI_apply]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun ⟨i, hi⟩ hi' => ?_
    rw [map_inj] at hi'
    subst hi'
    rfl
  · refine le_iSup₂_of_le ⟨_, h⟩ rfl ?_
    rfl

theorem map_refl (u : BVSet.{u, v} B) : map (OrderIso.refl _) u = u := by
  induction u using BVSet.induction with | _ u ih
  rw [map]
  ext _ _ hi
  · simp [ih]
  · simp only [OrderIso.coe_refl, val_mkI_apply, dom_mem, ih, Set.mem_preimage,
      Set.mem_singleton_iff]
    refine le_antisymm (iSup₂_le ?_) (le_iSup₂_of_le ⟨_, hi⟩ rfl ?_)
    · rintro i rfl
      rfl
    · rfl

theorem map_trans {g : B ≃o B} (u : BVSet.{u, v} B) : map (f.trans g) u = map g (map f u) := by
  induction u using BVSet.induction generalizing f g with | _ u ih
  rw [map]
  ext _ _ hi
  · simp [ih, mem_map_iff]
  · simp only [OrderIso.coe_trans, val_mkI_apply, dom_mem, ih, Set.mem_preimage,
      Set.mem_singleton_iff, Function.comp_apply]
    refine le_antisymm (iSup₂_le ?_) ?_
    · rintro i rfl
      rw [val_map_apply (map_mem_map i.2), val_map_apply i.2]
    · simp only [mem_dom_iff, mem_map_iff, exists_exists_and_eq_and] at hi
      rcases hi with ⟨i, hi', rfl⟩
      rw [val_map_apply (map_mem_map hi'), val_map_apply hi']
      refine le_iSup₂_of_le ⟨i, hi'⟩ rfl ?_
      rfl

theorem map_mkI {ι} [Small.{v} ι] {g b} : map f (mkI ι g b) = mkI ι (map f ∘ g) (f ∘ b) := by
  ext _ hi
  · simp [mem_map_iff]
  · simp only [mem_dom_iff, mem_map_iff, mem_mkI_iff, exists_exists_eq_and] at hi
    rcases hi with ⟨i, rfl⟩
    rw [val_map_apply mem_mkI, val_mkI_apply, val_mkI_apply]
    simp [f.map_iSup]

@[simps]
noncomputable def domMapEquiv : u.dom ≃ (map f u).dom where
  toFun x := ⟨map f x, map_mem_map x.2⟩
  invFun x := ⟨map f.symm x, by simpa [map_symm_map] using map_mem_map (f := f.symm) x.2⟩
  left_inv x := by simp [map_symm_map]
  right_inv x := by simp [← map_trans, map_refl]

@[simp]
theorem map_empty : map f (∅ : BVSet.{u, v} B) = ∅ := by
  simp only [EmptyCollection.emptyCollection, BVSet.empty, map_mkI]
  congr!

@[simp]
theorem map_insert : map f (insert u v) = insert (map f u) (map f v) := by
  simp only [insert, BVSet.insert, map_mkI]
  ext
  · simp only [mem_dom_iff, mem_mkI_iff, Function.comp_apply]
    rw [domMapEquiv.optionCongr.exists_congr_left]
    congr! with _ x
    cases x <;> simp [← Equiv.optionCongr_symm, ← map_trans, map_refl]
  · rw [val_mkI_apply, val_mkI_apply]
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff]
    rw [← domMapEquiv.optionCongr.iSup_comp]
    congr! with x <;> cases x <;> simp [domMapEquiv, val_map_apply]

@[simp]
theorem map_singleton : map f {u} = {map f u} := by
  simp [Singleton.singleton]

@[simp]
theorem map_sUnion : map f (⋃ᴮ u) = ⋃ᴮ (map f u) := by
  simp only [sUnion, map_mkI]
  ext _ hi
  · simp [mem_map_iff]
  · rw [val_mkI_apply, val_mkI_apply]
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, map_inf, iSup_sigma]
    rw [← domMapEquiv.iSup_comp]
    congr! 2 with x
    refine le_antisymm (iSup₂_le ?_) (iSup₂_le ?_)
    · rintro y rfl
      apply le_iSup₂_of_le ⟨map f y, map_mem_map y.2⟩ (by simp)
      simp [domMapEquiv, val_map_apply]
    · rintro ⟨_, hy⟩ rfl
      simp only [domMapEquiv, Equiv.coe_fn_mk, mem_dom_iff, mem_map_iff] at hy
      rcases hy with ⟨y, hy', rfl⟩
      apply le_iSup₂_of_le ⟨y, hy'⟩ (by simp)
      simp [domMapEquiv, val_map_apply, val_map_apply, hy']

@[simp]
theorem map_union : map f (u ∪ v) = map f u ∪ map f v := by
  simp [Union.union, BVSet.union]

theorem map_domSep {g} :
    map f (u.domSep g) = (map f u).domSep fun i => f (g ⟨map f.symm i, by
      simpa [map_symm_map] using map_mem_map (f := f.symm) i.2⟩) := by
  simp only [BVSet.domSep]
  rw [map]
  refine BVSet.ext ?_ fun i _ hi => ?_
  · ext
    simp [mem_map_iff]
  · rw [val_mkI_apply, val_mk_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine le_antisymm (iSup₂_le ?_) ?_
    · rintro _ rfl
      simp [map_symm_map, val_mk_apply]
    · simp only [mem_dom_iff, mem_mk_iff, mem_map_iff] at hi
      rcases hi with ⟨i, hi', rfl⟩
      apply le_iSup₂_of_le ⟨i, by simpa⟩ (by simp)
      simp [map_symm_map, val_mk_apply]

theorem map_sep {g : BVSet.{u, v} B → B} :
    map f (sep u g) = sep (map f u) fun x => f (g (map f.symm x)) := by
  simp only [sep, map_mkI]
  ext
  · simp [mem_map_iff]
  · rw [val_mkI_apply, val_mkI_apply]
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, map_inf]
    rw [← domMapEquiv.iSup_comp]
    congr! with x <;> simp [domMapEquiv, val_map_apply, map_symm_map]

theorem map_replace {g : BVSet.{u, v} B → BVSet.{u, v} B} :
    map f (replace u g) = replace (map f u) fun x => map f (g (map f.symm x)) := by
  simp only [replace, map_mkI]
  ext
  · simp [mem_map_iff, map_symm_map]
  · rw [val_mkI_apply, val_mkI_apply]
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff]
    rw [← domMapEquiv.iSup_comp]
    congr! with x <;> simp [domMapEquiv, val_map_apply, map_symm_map]

@[simp]
theorem map_beq_map {u v} : map f u =ᴮ map f v = f (u =ᴮ v) := by
  rw [map, map]
  conv_lhs =>
    simp only [beq_def, mkI_bsubset, bmem_mkI]
    simp only [← beq_def]
  conv_rhs =>
    simp only [beq_def, bsubset_def, map_inf, f.map_iInf, map_himp]
    simp [bmem_def, f.map_iSup]
  congr! with x y x y
  · exact map_beq_map
  · rw [beq_symm, beq_symm x.1]
    exact map_beq_map
termination_by u

@[gcongr]
theorem map_equiv : u ≈ v → map f u ≈ map f v := by
  simp [equiv_def]

theorem bmem_map : u ∈ᴮ map f v = ⨆ (i : v.dom), f (v i) ⊓ u =ᴮ map f i := by
  rw [map]
  simp [bmem_mkI]

@[simp]
theorem map_bmem_map : map f u ∈ᴮ map f v = f (u ∈ᴮ v) := by
  rw [bmem_map]
  simp [bmem_def, f.map_iSup]

@[simp]
theorem map_bsubset_map : map f u ⊆ᴮ map f v = f (u ⊆ᴮ v) := by
  rw [bsubset_def']
  simp_rw [bmem_map, fun x (i : u.dom) => inf_comm (f (u i)) (x =ᴮ map f i), iSup_himp_eq,
    iInf_comm (ι' := u.dom), ← himp_himp]
  conv_lhs =>
    enter [1, i]
    rw [IsExtentional.iInf_beq_himp (by fun_prop), ← bmem_map, map_bmem_map]
  simp [bsubset_def, f.map_iInf]

theorem map_inter : map f (u ∩ v) = map f u ∩ map f v := by
  simp [Inter.inter, BVSet.inter, map_sep, ← map_bmem_map, ← map_trans, map_refl]

theorem map_sdiff : map f (u \ v) = map f u \ map f v := by
  simp [SDiff.sdiff, BVSet.sdiff, map_sep, ← map_bmem_map, ← map_trans, map_refl]

@[simp]
theorem _root_.ZFSet.map_toBVSet {u : ZFSet.{v}} : map f u.toBVSet = u.toBVSet := by
  induction u using ZFSet.inductionOn with | _ u ih
  rw [ZFSet.toBVSet, map_mkI]
  congr! <;> simp [ih]

end BVSet

variable {G : Type w} [Group G] [MulAction G B] [SMulOrderIso G B] {g : G} {u v : BVSet.{u, v} B}

namespace BVSet

noncomputable instance : MulAction G (BVSet.{u, v} B) where
  smul a u := map (SMulOrderIso.toOrderIso a) u
  one_smul u := by
    simp [HSMul.hSMul, SMulOrderIso.toOrderIso_one, map_refl]
  mul_smul a b u := by
    simp [HSMul.hSMul, SMulOrderIso.toOrderIso_mul, map_trans]

theorem mem_smul_iff : u ∈ g • v ↔ ∃ w ∈ v, g • w = u :=
  mem_map_iff

@[simp]
theorem smul_mem_smul_iff : g • u ∈ g • v ↔ u ∈ v :=
  map_mem_map_iff

alias ⟨_, smul_mem_smul⟩ := smul_mem_smul_iff

@[simp]
theorem smul_inj : g • u = g • v ↔ u = v :=
  map_inj

theorem dom_smul : (g • u).dom = (g • ·) '' u.dom :=
  dom_map

theorem val_smul_apply (h) : (g • u).val ⟨g • v, smul_mem_smul h⟩ = g • u.val ⟨v, h⟩ :=
  val_map_apply h

theorem smul_mkI {ι} [Small.{v} ι] {f : ι → BVSet B} {b} :
    g • mkI ι f b = mkI ι (fun i => g • f i) (fun i => g • b i) :=
  map_mkI

@[simp]
theorem smul_empty : g • (∅ : BVSet.{u, v} B) = ∅ :=
  map_empty

@[simp]
theorem smul_insert : g • insert u v = insert (g • u) (g • v) :=
  map_insert

@[simp]
theorem smul_singleton : g • ({u} : BVSet B) = {g • u} :=
  map_singleton

@[simp]
theorem smul_sUnion : g • ⋃ᴮ u = ⋃ᴮ (g • u) :=
  map_sUnion

@[simp]
theorem smul_union : g • (u ∪ v) = g • u ∪ g • v :=
  map_union

theorem smul_domSep {f} :
    g • u.domSep f = (g • u).domSep fun i => g • f ⟨g⁻¹ • i, by
      simpa using smul_mem_smul (g := g⁻¹) i.2⟩ := by
  convert map_domSep
  simp [HSMul.hSMul, SMul.smul, SMulOrderIso.toOrderIso_inv]

@[simp]
theorem smul_sep {f : BVSet.{u, v} B → B} :
    g • sep u f = sep (g • u) fun x => g • f (g⁻¹ • x) := by
  convert map_sep
  simp [HSMul.hSMul, SMul.smul, SMulOrderIso.toOrderIso_inv]

@[simp]
theorem smul_inter : g • (u ∩ v) = g • u ∩ g • v :=
  map_inter

@[simp]
theorem smul_sdiff : g • (u \ v) = g • u \ g • v :=
  map_sdiff

@[simp]
theorem smul_replace {f : BVSet.{u, v} B → BVSet B} :
    g • replace u f = replace (g • u) fun x => g • f (g⁻¹ • x) := by
  convert map_replace
  simp [HSMul.hSMul, SMul.smul, SMulOrderIso.toOrderIso_inv]

@[simp]
theorem _root_.ZFSet.smul_toBVSet {u : ZFSet.{v}} : g • (u.toBVSet : BVSet.{u, v} B) = u.toBVSet :=
  ZFSet.map_toBVSet

@[simp]
theorem smul_beq_smul : g • u =ᴮ g • v = g • (u =ᴮ v) :=
  map_beq_map

@[simp]
theorem smul_bmem_smul : g • u ∈ᴮ g • v = g • (u ∈ᴮ v) :=
  map_bmem_map

@[simp]
theorem smul_bsubset_smul : g • u ⊆ᴮ g • v = g • (u ⊆ᴮ v) :=
  map_bsubset_map

@[gcongr]
theorem smul_equiv : u ≈ v → g • u ≈ g • v :=
  map_equiv

end BVSet

abbrev SubgroupFilter (G : Type*) [Group G] := Order.PFilter (Subgroup G)

open Pointwise MulAction

class SubgroupFilter.Normal (Γ : SubgroupFilter G) where
  conj_smul_mem : ∀ (g : G), ∀ H ∈ Γ, MulAut.conj g • H ∈ Γ

variable {Γ : SubgroupFilter G}

namespace BVSet

def HereditarilySymmetric (Γ : SubgroupFilter G) (u : BVSet.{u, v} B) : Prop :=
  stabilizer G u ∈ Γ ∧ ∀ x ∈ u, HereditarilySymmetric Γ x
termination_by u

theorem HereditarilySymmetric.stabilizer_mem (h : HereditarilySymmetric Γ u) :
    stabilizer G u ∈ Γ := by
  rw [HereditarilySymmetric] at h
  exact h.1

theorem HereditarilySymmetric.mem (h : HereditarilySymmetric Γ u) {x} (hx : x ∈ u) :
    HereditarilySymmetric Γ x := by
  rw [HereditarilySymmetric] at h
  exact h.2 _ hx

theorem HereditarilySymmetric.smul [Γ.Normal] (h : HereditarilySymmetric Γ u) (g : G) :
    HereditarilySymmetric Γ (g • u) := by
  induction u using BVSet.induction with | _ u ih
  rw [HereditarilySymmetric]
  constructor
  · rw [stabilizer_smul_eq_stabilizer_map_conj]
    apply SubgroupFilter.Normal.conj_smul_mem
    exact h.stabilizer_mem
  · simpa [mem_smul_iff] using fun x hx => ih _ hx (h.mem hx)

protected theorem HereditarilySymmetric.empty : HereditarilySymmetric Γ (∅ : BVSet.{u, v} B) := by
  rw [HereditarilySymmetric]
  constructor
  · convert Γ.top_mem
    ext
    simp
  · simp [EmptyCollection.emptyCollection, BVSet.empty]

protected theorem HereditarilySymmetric.insert (hu : HereditarilySymmetric Γ u)
    (hv : HereditarilySymmetric Γ v) : HereditarilySymmetric Γ (insert u v) := by
  rw [HereditarilySymmetric]
  constructor
  · refine Γ.mem_of_le ?_ (Γ.inf_mem hu.stabilizer_mem hv.stabilizer_mem)
    intro g
    simp +contextual
  · simp only [insert, BVSet.insert, mem_mkI_iff, forall_exists_index, forall_apply_eq_imp_iff]
    rintro (_ | ⟨x, hx⟩)
    · simpa
    · simpa using hv.mem hx

protected theorem HereditarilySymmetric.singleton (hu : HereditarilySymmetric Γ u) :
    HereditarilySymmetric Γ ({u} : BVSet B) :=
  hu.insert .empty

protected theorem HereditarilySymmetric.sUnion (hu : HereditarilySymmetric Γ u) :
    HereditarilySymmetric Γ (⋃ᴮ u) := by
  rw [HereditarilySymmetric]
  constructor
  · refine Γ.mem_of_le ?_ hu.stabilizer_mem
    intro g
    simp +contextual
  · simp only [sUnion, mem_mkI_iff, Sigma.exists, Subtype.exists, mem_dom_iff, exists_prop,
      exists_eq_right, forall_exists_index, and_imp]
    intro y x hx hy
    exact (hu.mem hx).mem hy

protected theorem HereditarilySymmetric.union (hu : HereditarilySymmetric Γ u)
    (hv : HereditarilySymmetric Γ v) : HereditarilySymmetric Γ (u ∪ v) :=
  (hu.insert hv.singleton).sUnion

variable (Γ) in
noncomputable def symmPowerset [Small.{v} B] (u : BVSet.{u, v} B) : BVSet.{u, v} B :=
  mkI {f : u.dom → B // HereditarilySymmetric Γ (u.domSep f)} (fun ⟨f, _⟩ => u.domSep f)
    fun ⟨f, _⟩ => u.domSep f ⊆ᴮ u

theorem bmem_symmPowerset [Small.{v} B] (hu : HereditarilySymmetric Γ u)
    (hv : HereditarilySymmetric Γ v) : u ∈ᴮ symmPowerset Γ v = u ⊆ᴮ v := by
  simp only [symmPowerset, bmem_mkI]
  refine le_antisymm (iSup_le fun f => ?_) ?_
  · grw [inf_comm, beq_symm, bsubset_congr_left]
  · refine le_iSup_of_le ⟨fun i : v => i ∈ᴮ u, ?_⟩ ?_
    · rw [HereditarilySymmetric]
      constructor
      · refine Γ.mem_of_le ?_ (Γ.inf_mem hu.stabilizer_mem hv.stabilizer_mem)
        intro g
        simp only [Subgroup.mem_inf, mem_stabilizer_iff, and_imp]
        intro hgu hgv
        rw [smul_domSep]
        ext
        · simp [BVSet.domSep, hgv]
        · simp [BVSet.domSep, val_mk_apply, ← smul_bmem_smul, hgu]
      · simpa [BVSet.domSep] using fun x hx => hv.mem hx
    · apply le_inf
      · exact bsubset_le_domSep_bmem_bsubset
      · rw [beq_symm]
        exact bsubset_le_domSep_bmem_beq

theorem smul_symmPowerset [Small.{v} B] [Γ.Normal] :
    g • symmPowerset Γ u = symmPowerset Γ (g • u) := by
  simp only [symmPowerset, smul_mkI]
  ext
  · simp only [mem_dom_iff, mem_mkI_iff, Subtype.exists, exists_prop]
    constructor
    · rintro ⟨f, hf, rfl⟩
      have hf' := hf.smul g
      rw [smul_domSep] at hf' ⊢
      exact ⟨_, hf', rfl⟩
    · rintro ⟨f, hf, rfl⟩
      have hf' := hf.smul g⁻¹
      simp_rw [← eq_inv_smul_iff]
      rw! (castMode := .all) [smul_domSep, inv_smul_smul] at hf' ⊢
      exact ⟨_, hf', rfl⟩
  · simp only [val_mkI_apply, Set.mem_preimage, Set.mem_singleton_iff, ← smul_bsubset_smul]
    apply le_antisymm (iSup₂_le ?_) (iSup₂_le ?_)
    · rintro ⟨f, hf⟩ rfl
      have hf' := hf.smul g
      rw [smul_domSep] at hf' ⊢
      apply le_iSup₂_of_le ⟨_, hf'⟩ <;> rfl
    · rintro ⟨f, hf⟩ rfl
      have hf' := hf.smul g⁻¹
      simp_rw [← eq_inv_smul_iff]
      rw! (castMode := .all) [smul_domSep, inv_smul_smul] at hf' ⊢
      apply le_iSup₂_of_le ⟨_, hf'⟩
      · simp [smul_domSep]
      · rfl

protected theorem HereditarilySymmetric.symmPowerset [Small.{v} B] [Γ.Normal]
    (hu : HereditarilySymmetric Γ u) : HereditarilySymmetric Γ (u.symmPowerset Γ) := by
  rw [HereditarilySymmetric]
  constructor
  · refine Γ.mem_of_le ?_ hu.stabilizer_mem
    intro g
    simp +contextual [smul_symmPowerset]
  · simp [symmPowerset]

protected theorem HereditarilySymmetric.toBVSet {u : ZFSet.{v}} :
    HereditarilySymmetric Γ (u.toBVSet : BVSet B) := by
  induction u using ZFSet.inductionOn with | _ u ih
  rw [HereditarilySymmetric]
  constructor
  · convert Γ.top_mem
    ext
    simp
  · rw [ZFSet.toBVSet]
    simpa

theorem HereditarilySymmetric.bmem_def (hv : HereditarilySymmetric Γ v) :
    u ∈ᴮ v = ⨆ x, ⨆ (_ : HereditarilySymmetric Γ x), x ∈ᴮ v ⊓ x =ᴮ u := by
  apply le_antisymm
  · rw [BVSet.bmem_def]
    refine iSup_le fun ⟨x, hx⟩ => ?_
    apply le_iSup₂_of_le x (hv.mem hx)
    gcongr 1
    · exact val_le_bmem
    · simp [beq_symm]
  · refine iSup₂_le fun x hx => ?_
    rw [inf_comm]
    apply bmem_congr_left

theorem HereditarilySymmetric.bsubset_def (hu : HereditarilySymmetric Γ u) :
    u ⊆ᴮ v = ⨅ x, ⨅ (_ : HereditarilySymmetric Γ x), x ∈ᴮ u ⇨ x ∈ᴮ v := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    rw [bsubset_def']
    exact iInf_le _ x
  · rw [BVSet.bsubset_def]
    refine le_iInf fun ⟨x, hx⟩ => ?_
    apply iInf₂_le_of_le x (hu.mem hx)
    gcongr
    exact val_le_bmem

end BVSet

variable (B Γ) in
def HSSet : Type max u (v + 1) :=
  {u : BVSet.{u, v} B // u.HereditarilySymmetric Γ}

namespace HSSet

open BVSet FirstOrder Language set

instance : Nonempty (HSSet B Γ) := ⟨⟨∅, .empty⟩⟩

theorem bmem_def {v : HSSet B Γ} : u ∈ᴮ v.1 = ⨆ (x : HSSet B Γ), x.1 ∈ᴮ v.1 ⊓ x.1 =ᴮ u := by
  simp only [HSSet]
  rw [v.2.bmem_def, iSup_subtype]

theorem bsubset_def {u : HSSet B Γ} : u.1 ⊆ᴮ v = ⨅ (x : HSSet B Γ), x.1 ∈ᴮ u.1 ⇨ x.1 ∈ᴮ v := by
  simp only [HSSet]
  rw [u.2.bsubset_def, iInf_subtype]

theorem iSup_bmem_inf {f : BVSet B → B} {u : HSSet B Γ} (hf : IsExtentional f) :
    ⨆ x : HSSet B Γ, x.1 ∈ᴮ u.1 ⊓ f x.1 = ⨆ x : u.1, u.1 x ⊓ f x := by
  conv_rhs =>
    rw [← hf.iSup_bmem_inf]
    enter [1, x]
    rw [bmem_def, iSup_inf_eq]
    enter [1, i]
    rw [beq_symm]
  rw [iSup_comm]
  simp_rw [inf_assoc, ← inf_iSup_eq, hf.iSup_beq_inf]

theorem iInf_bmem_himp {f : BVSet B → B} {u : HSSet B Γ} (hf : IsExtentional f) :
    ⨅ x : HSSet B Γ, x.1 ∈ᴮ u.1 ⇨ f x.1 = ⨅ x : u.1, u.1 x ⇨ f x := by
  conv_rhs =>
    rw [← hf.iInf_bmem_himp]
    enter [1, x]
    rw [bmem_def, iSup_himp_eq]
    enter [1, i]
    rw [beq_symm]
  rw [iInf_comm]
  simp_rw [← himp_himp, ← himp_iInf_eq, hf.iInf_beq_himp]

nonrec theorem bne_empty {u : HSSet B Γ} : u.1 ≠ᴮ ∅ = ⨆ x : HSSet B Γ, x.1 ∈ᴮ u.1 := by
  rw [bne_empty]
  conv_rhs =>
    enter [1, x]
    rw [← inf_top_eq (x.1 ∈ᴮ u.1)]
  rw [iSup_bmem_inf (f := fun _ => ⊤) (by fun_prop),
    ← IsExtentional.iSup_bmem_inf (f := fun _ => ⊤) (by fun_prop)]
  simp

variable [Γ.Normal]

noncomputable instance : MulAction G (HSSet B Γ) where
  smul g u := ⟨g • u.1, .smul u.2 g⟩
  one_smul u := Subtype.val_inj.1 (one_smul _ u.1)
  mul_smul _ _ u := Subtype.val_inj.1 (mul_smul _ _ u.1)

@[simp]
theorem val_smul {u : HSSet B Γ} : (g • u).1 = g • u.1 := rfl

variable [Small.{v} B]

noncomputable instance : set.BVStructure (HSSet B Γ) B where
  funMap
  | .empty, _ => ⟨∅, .empty⟩
  | .insert, v => ⟨insert (v 0).1 (v 1).1, .insert (v 0).2 (v 1).2⟩
  | .sUnion, v => ⟨⋃ᴮ (v 0).1, .sUnion (v 0).2⟩
  | .powerset, v => ⟨symmPowerset Γ (v 0).1, .symmPowerset (v 0).2⟩
  | .omega, _ => ⟨ωᴮ, .toBVSet⟩
  relMap
  | .mem, v => (v 0).1 ∈ᴮ (v 1).1
  beq u v := u.1 =ᴮ v.1
  beq_refl _ := beq_refl _
  beq_symm _ _ := beq_symm _ _
  beq_trans _ _ _ := beq_trans _ _ _
  beq_funMap
  | .empty, _, _ => by simp
  | .insert, _, _ => by
    have : IsExtentionalFun₂ (insert : BVSet B → BVSet B → BVSet B) := by
      apply IsExtentionalFun₂.of_isExtentionalFun <;> fun_prop
    exact (this _ _ _ _).trans' <| le_inf (iInf_le _ 0) (iInf_le _ 1)
  | .sUnion, _, _ => by
    have : IsExtentionalFun (⋃ᴮ · : BVSet B → BVSet B) := by fun_prop
    exact (this _ _).trans' <| iInf_le _ 0
  | .powerset, u, v => by
    simp only [ciInf_unique, Fin.default_eq_zero, Fin.isValue]
    conv_rhs => rw [beq_def, (u 0).2.symmPowerset.bsubset_def, (v 0).2.symmPowerset.bsubset_def]
    simp only [Fin.isValue, le_inf_iff, le_iInf_iff, le_himp_iff]
    constructor
    · intro x hx
      rw [bmem_symmPowerset hx (u 0).2, bmem_symmPowerset hx (v 0).2]
      apply IsExtentional.bsubset .const .id
    · intro x hx
      rw [bmem_symmPowerset hx (u 0).2, bmem_symmPowerset hx (v 0).2, beq_symm]
      apply IsExtentional.bsubset .const .id
  | .omega, _, _ => by simp
  beq_relMap
  | .mem, _, _ => by
    have : IsExtentional₂ (· ∈ᴮ · : BVSet B → BVSet B → B) := by
      apply IsExtentional₂.of_isExtentional <;> fun_prop
    exact (this _ _ _ _).trans' (inf_le_inf_right _ (le_inf (iInf_le _ 0) (iInf_le _ 1)))

variable {α : Type*} {t t₁ t₂ : set.Term α} {v : α → HSSet.{u, v} B Γ}

@[simp]
theorem bvStructureEq_def (u v : HSSet B Γ) : BVStructure.beq set u v = u.1 =ᴮ v.1 :=
  rfl

@[simp]
theorem bvrealize_empty : ((∅ : set.Term α).bvrealize v).1 = ∅ :=
  rfl

@[simp]
theorem bvrealize_insert :
    ((insert t₁ t₂).bvrealize v).1 = insert (t₁.bvrealize v).1 (t₂.bvrealize v).1 :=
  rfl

@[simp]
theorem bvrealize_singleton : (({t} : set.Term α).bvrealize v).1 = {(t.bvrealize v).1} :=
  rfl

@[simp]
theorem bvrealize_sUnion : ((⋃₀ t).bvrealize v).1 = ⋃ᴮ (t.bvrealize v).1 :=
  rfl

@[simp]
theorem bvrealize_powerset : ((𝒫 t).bvrealize v).1 = symmPowerset Γ (t.bvrealize v).1 :=
  rfl

@[simp]
theorem bvrealize_omega : ((ω : set.Term α).bvrealize v).1 = ωᴮ :=
  rfl

@[simp]
theorem bvrealize_mem {n} {t₁ t₂ : set.Term (α ⊕ Fin n)} {xs : Fin n → HSSet B Γ} :
    (t₁ ∈' t₂).bvrealize v xs =
      (t₁.bvrealize (Sum.elim v xs)).1 ∈ᴮ (t₂.bvrealize (Sum.elim v xs)).1 :=
  rfl

@[simp]
theorem bvrealize_subset {n} {t₁ t₂ : set.Term (α ⊕ Fin n)} {xs : Fin n → HSSet B Γ} :
    (t₁ ⊆' t₂).bvrealize v xs =
      (t₁.bvrealize (Sum.elim v xs)).1 ⊆ᴮ (t₂.bvrealize (Sum.elim v xs)).1 := by
  simp [set.subset, Sum.elim_comp_map, bsubset_def]

@[simp]
theorem bvrealize_kpair {t₁ t₂ : set.Term α} :
    ((set.kpair t₁ t₂).bvrealize v).1 = kpair (t₁.bvrealize v).1 (t₂.bvrealize v).1 := by
  simp [set.kpair, BVSet.kpair]

theorem smul_term_bvrealize {t : set.Term α} :
    g • t.bvrealize v = t.bvrealize fun i => g • v i := by
  induction t with
  | var => rfl
  | func f _ ih =>
    rw [← Subtype.val_inj]
    cases f with
    | empty =>
      exact smul_empty
    | insert =>
      exact smul_insert.trans (congr_arg₂ _ (Subtype.val_inj.2 (ih 0)) (Subtype.val_inj.2 (ih 1)))
    | sUnion =>
      exact smul_sUnion.trans (congr_arg _ (Subtype.val_inj.2 (ih 0)))
    | powerset =>
      exact smul_symmPowerset.trans (congr_arg _ (Subtype.val_inj.2 (ih 0)))
    | omega =>
      exact ZFSet.smul_toBVSet

theorem smul_boundedFormula_bvrealize {n} {φ : set.BoundedFormula α n} {xs} :
    g • φ.bvrealize v xs = φ.bvrealize (fun i => g • v i) fun i => g • xs i := by
  induction φ with
  | rel r =>
    cases r
    refine smul_bmem_smul.symm.trans (congr_arg₂ _ ?_ ?_) <;> rw [← val_smul, Subtype.val_inj]
      <;> convert smul_term_bvrealize <;> grind
  | equal =>
    refine smul_beq_smul.symm.trans (congr_arg₂ _ ?_ ?_) <;> rw [← val_smul, Subtype.val_inj]
      <;> convert smul_term_bvrealize <;> grind
  | falsum =>
    simp [BoundedFormula.bvrealize, smul_bot]
  | imp _ _ ih₁ ih₂ =>
    simp [BoundedFormula.bvrealize, smul_himp, ih₁, ih₂]
  | all _ ih =>
    simp only [BoundedFormula.bvrealize, smul_iInf, ih]
    refine le_antisymm (le_iInf fun u => iInf_le_of_le (g⁻¹ • u) ?_)
      (le_iInf fun u => iInf_le_of_le (g • u) ?_)
     <;> congr! with x <;> cases x using Fin.lastCases <;> simp

@[simp]
theorem bvrealize_axiomOfExtensionality : axiomOfExtensionality.bvrealize (HSSet B Γ) = ⊤ := by
  simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfExtensionality, Nat.reduceAdd,
    Fin.isValue, Function.comp_apply, BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_imp,
    BoundedFormula.bvrealize_iff, bvrealize_mem, Term.bvrealize_var, Sum.elim_inr,
    Fin.snoc_apply_two', Fin.snoc_apply_zero, Fin.snoc_apply_zero', Fin.snoc_apply_one,
    Fin.snoc_apply_one', BoundedFormula.bvrealize_bdEqual, bvStructureEq_def, iInf_eq_top,
    himp_eq_top_iff]
  intro u v
  simp_rw [bihimp_def, iInf_inf_eq, ← bsubset_def, inf_comm, ← beq_def]
  rfl

@[simp]
theorem bvrealize_axiomOfEmpty : axiomOfEmpty.bvrealize (HSSet B Γ) = ⊤ := by
  simp [axiomOfEmpty, Sentence.bvrealize, Formula.bvrealize]

@[simp]
theorem bvrealize_axiomOfPairing : axiomOfPairing.bvrealize (HSSet B Γ) = ⊤ := by
  simp [axiomOfPairing, Sentence.bvrealize, Formula.bvrealize]

@[simp]
theorem bvrealize_axiomOfUnion : axiomOfUnion.bvrealize (HSSet B Γ) = ⊤ := by
  simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfUnion, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_iff,
    bvrealize_mem, Term.bvrealize_var, Sum.elim_inr, Fin.snoc_apply_one', bvrealize_sUnion,
    Fin.snoc_apply_zero, Fin.snoc_apply_zero', bmem_sUnion', BoundedFormula.bvrealize_ex,
    BoundedFormula.bvrealize_inf, Fin.snoc_apply_two', Fin.snoc_apply_one, iInf_eq_top,
    bihimp_eq_top]
  intro u v
  rw [iSup_bmem_inf (by fun_prop), IsExtentional.iSup_bmem_inf (by fun_prop)]

@[simp]
theorem bvrealize_axiomOfPowerset : axiomOfPowerset.bvrealize (HSSet B Γ) = ⊤ := by
  simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfPowerset, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_iff, bvrealize_mem,
    Term.bvrealize_var, Sum.elim_inr, Fin.snoc_apply_one', bvrealize_powerset, Fin.snoc_apply_zero,
    Fin.snoc_apply_zero', bvrealize_subset, iInf_eq_top, bihimp_eq_top]
  intro u v
  rw [bmem_symmPowerset v.2 u.2]

@[simp]
theorem bvrealize_axiomOfInfinity : axiomOfInfinity.bvrealize (HSSet B Γ) = ⊤ := by
  simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfInfinity, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, BoundedFormula.bvrealize_inf, bvrealize_mem, bvrealize_empty,
    bvrealize_omega, empty_bmem_omega, BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_imp,
    Term.bvrealize_var, Sum.elim_inr, Fin.snoc_apply_zero', bvrealize_insert, 
    le_himp_iff, le_top, inf_of_le_right, le_succ_bmem_omega, implies_true,
    Fin.snoc_apply_one', Fin.snoc_apply_zero, bvrealize_subset, iInf_eq_top, himp_eq_top_iff,
    inf_eq_top_iff, iInf_eq_top, himp_eq_top_iff, le_himp_iff, true_and]
  intro x
  grw [← omega_bsubset]
  gcongr
  rw [iInf_bmem_himp (f := fun y => insert y y ∈ᴮ _) (by fun_prop),
    IsExtentional.iInf_bmem_himp (by fun_prop)]

@[simp]
theorem bvrealize_axiomOfRegularity : axiomOfRegularity.bvrealize (HSSet B Γ) = ⊤ := by
  simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfRegularity, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_imp,
    BoundedFormula.bvrealize_ex, bvrealize_mem, Term.bvrealize_var, Sum.elim_inr,
    Fin.snoc_apply_one', Fin.snoc_apply_zero, Fin.snoc_apply_zero', BoundedFormula.bvrealize_inf,
    BoundedFormula.bvrealize_not, Fin.snoc_apply_two', Fin.snoc_apply_one, iInf_eq_top,
    himp_eq_top_iff]
  intro u
  rw [← bne_empty]
  conv_rhs =>
    enter [1, x, 2]
    simp only [compl_iSup, compl_inf, ← compl_himp_eq, compl_compl]
    rw [iInf_bmem_himp (f := fun y => (y ∈ᴮ u.1)ᶜ) (by fun_prop),
      ← IsExtentional.iInf_bmem_himp (f := fun y => (y ∈ᴮ u.1)ᶜ) (by fun_prop)]
    simp only [← himp_bot, himp_himp]
    simp only [himp_bot, ← bmem_inter]
    rw [← compl_iSup, ← BVSet.bne_empty, compl_compl]
  rw [iSup_bmem_inf (f := fun x => (x ∩ u.1) =ᴮ ∅) (by fun_prop),
    ← IsExtentional.iSup_bmem_inf (f := fun x => (x ∩ u.1) =ᴮ ∅) (by fun_prop)]
  exact regularity

@[simp]
theorem bvrealize_axiomOfSeparation {α : Type*} [Finite α] {φ : set.Formula (α ⊕ Fin 1)} :
    (axiomOfSeparation φ).bvrealize (HSSet B Γ) = ⊤ := by
  simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfSeparation, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, Nat.succ_eq_add_one, Matrix.empty_eq, BoundedFormula.bvrealize_iAlls,
    BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_ex, BoundedFormula.bvrealize_iff,
    bvrealize_mem, Term.bvrealize_var, Sum.elim_inr, Fin.snoc_apply_two', Fin.snoc_apply_one,
    Fin.snoc_apply_one', BoundedFormula.bvrealize_inf, Fin.snoc_apply_zero, Fin.snoc_apply_zero',
    BoundedFormula.bvrealize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
    Function.comp_id, Sum.elim_comp_map, Sum.elim_comp_inr, Matrix.comp_vecCons, iInf_eq_top]
  intro a u
  rw [eq_top_iff]
  refine le_iSup_of_le ⟨u.1.domSep fun x =>
    u.1.val x ⊓ BoundedFormula.bvrealize φ (Sum.elim a ![⟨x.1, u.2.mem x.2⟩]) ![], ?_⟩ ?_
  · rw [HereditarilySymmetric]
    constructor
    · refine Γ.mem_of_le ?_
        (Γ.inf_mem u.2.stabilizer_mem (Γ.iInf_mem fun i => (a i).2.stabilizer_mem))
      intro g
      simp only [Subgroup.mem_inf, mem_stabilizer_iff, Subgroup.mem_iInf, and_imp]
      intro hgu hga
      rw! (castMode := .all) [smul_domSep, hgu]
      ext _ _ hi
      · simp [BVSet.domSep]
      · simp only [BVSet.domSep, mem_dom_iff, mem_mk_iff] at hi
        simp only [BVSet.domSep, val_mk_apply, smul_inf]
        congr
        · rw! (castMode := .all) [← val_smul_apply, hgu, smul_inv_smul]
          rfl
        · rw [smul_boundedFormula_bvrealize]
          congr! with i
          cases i with
          | inl i =>
            simpa [← val_smul, Subtype.val_inj] using hga i
          | inr i =>
            simp only [Sum.elim_inr, Matrix.cons_val_fin_one]
            rw [← Subtype.val_inj, val_smul, smul_inv_smul]
    · simpa [BVSet.domSep] using fun x hx => u.2.mem hx
  · refine le_iInf fun x => ?_
    simp only [bihimp_def, le_inf_iff, BVSet.bmem_domSep, le_himp_iff, top_inf_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [BVSet.bmem_def, iSup_inf_eq]
      refine iSup_le fun y => le_iSup_of_le y ?_
      refine le_inf (le_inf ?_ ?_) ?_
      · grw [inf_le_left, inf_le_left]
      · grw [← BoundedFormula.beq_inf_bvrealize_le_bvrealize (v := Sum.elim a ![x])
          (w := Sum.elim a ![⟨y, _⟩]) (xs := ![])]
        refine le_inf (le_inf (le_iInf fun i => ?_) ?_) ?_
        · cases i with
          | inl => simp
          | inr => grw [inf_le_left, inf_le_right]; simp
        · simp
        · grw [inf_le_right]
      · grw [inf_le_left, inf_le_right]
    · refine iSup_le fun y => ?_
      grw [inf_le_left (a := val _ _), val_le_bmem, inf_comm, bmem_congr_left']
    · refine iSup_le fun y => ?_
      grw [← BoundedFormula.beq_inf_bvrealize_le_bvrealize (v := Sum.elim a ![⟨y, _⟩])
        (w := Sum.elim a ![x]) (xs := ![])]
      refine le_inf (le_inf (le_iInf fun i => ?_) ?_) ?_
      · cases i with
        | inl => simp
        | inr => grw [inf_le_right, beq_symm]; simp
      · simp
      · grw [inf_le_left, inf_le_right]

@[simp]
theorem bvrealize_axiomOfCollection {α : Type*} [Finite α] {φ : set.Formula (α ⊕ Fin 2)} :
    (axiomOfCollection φ).bvrealize (HSSet B Γ) = ⊤ := by
  simp only [Sentence.bvrealize, Formula.bvrealize, axiomOfCollection, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, Nat.succ_eq_add_one, Matrix.empty_eq, BoundedFormula.bvrealize_iAlls,
    BoundedFormula.bvrealize_all, BoundedFormula.bvrealize_imp, bvrealize_mem, Term.bvrealize_var,
    Sum.elim_inr, Fin.snoc_apply_one', Fin.snoc_apply_zero, Fin.snoc_apply_zero',
    BoundedFormula.bvrealize_ex, BoundedFormula.bvrealize_relabel, Nat.add_zero, Fin.castAdd_zero,
    Fin.cast_refl, Function.comp_id, Sum.elim_comp_map, Sum.elim_comp_inr, Matrix.comp_vecCons,
    Fin.snoc_apply_one, Fin.snoc_apply_two', BoundedFormula.bvrealize_inf, Fin.snoc_apply_three',
    Fin.snoc_apply_two, iInf_eq_top, himp_eq_top_iff]
  intro a u
  let s : u.1 → Set B := fun x => {b | ∃ y, φ.bvrealize (Sum.elim a ![⟨x, u.2.mem x.2⟩, y]) = b}
  have : ∀ x : u.1, ∀ b : s x, ∃ y, φ.bvrealize (Sum.elim a ![⟨x, u.2.mem x.2⟩, y]) = b := by
    simp [s]
  choose f hf using this
  let s' : Set (BVSet B) := ⋃ x : u.1, ⋃ b : s x, orbit G (f x b).1
  have : Small.{v} s' := by
    refine @small_iUnion _ _ _ _ fun x => @small_iUnion _ _ _ _ fun b => ?_
    refine @small_subset _ (⋃ (g : B ≃o B), {map g (f x b).1}) _ ?_ ?_
    · intro y hy
      simp only [mem_orbit_iff] at hy
      rcases hy with ⟨g, rfl⟩
      simp only [Set.iUnion_singleton_eq_range, Set.mem_range]
      exists (SMulOrderIso.toOrderIso g)
    exact @small_iUnion _ _ (small_of_injective DFunLike.coe_injective) _ _
  let v := mk s' fun _ => ⊤
  refine le_iSup_of_le ⟨v, ?_⟩ ?_
  · rw [HereditarilySymmetric]
    constructor
    · convert Γ.top_mem
      ext g
      simp only [mem_stabilizer_iff, Subgroup.mem_top, iff_true]
      ext _ hi
      · simp only [mem_dom_iff, mem_smul_iff, mem_mk_iff, Set.iUnion_coe_set, Set.mem_iUnion,
          smul_eq_iff_eq_inv_smul, exists_eq_right, v, s']
        congr! 8
        exact smul_mem_orbit_iff _
      · simp only [mem_dom_iff, mem_smul_iff] at hi
        rcases hi with ⟨i, hi', rfl⟩
        rw [val_smul_apply hi']
        simp [v, val_mk_apply, smul_top]
    · intro x hx
      simp only [mem_mk_iff, Set.iUnion_coe_set, mem_dom_iff, Set.mem_iUnion, mem_orbit_iff, v,
        s'] at hx
      rcases hx with ⟨i, hi, b, hb, g, rfl⟩
      exact .smul (f _ _).2 g
  · refine le_iInf fun x => ?_
    rw [BVSet.bmem_def, iSup_himp_eq]
    refine le_iInf fun y => ?_
    grw [le_himp_iff, ← inf_assoc, iInf_le _ ⟨y.1, u.2.mem y.2⟩, val_le_bmem, himp_inf_le,
      iSup_inf_eq]
    refine iSup_le fun z => ?_
    let b := φ.bvrealize (Sum.elim a ![⟨y.1, u.2.mem y.2⟩, z])
    have hb : b ∈ s y := by simp [b, s]
    refine le_iSup_of_le (f y ⟨b, hb⟩) (le_inf ?_ ?_)
    · rw [BVSet.bmem_def]
      refine le_iSup_of_le ⟨(f y ⟨b, hb⟩).1, ?_⟩ ?_
      · simp only [mem_dom_iff, mem_mk_iff, Set.iUnion_coe_set, Set.mem_iUnion, v, s']
        exists y, y.2, b, hb
        apply mem_orbit_self
      · simp [v, val_mk_apply]
    · grw [← BoundedFormula.beq_inf_bvrealize_le_bvrealize
        (v := Sum.elim a ![⟨y.1, u.2.mem y.2⟩, f y ⟨b, hb⟩]) (w := Sum.elim a ![x, f y ⟨b, hb⟩])
        (xs := ![])]
      refine le_inf (le_inf (le_iInf fun i => ?_) ?_) ?_
      · cases i with
        | inl => simp
        | inr i =>
          fin_cases i
          · grw [inf_le_right, beq_symm]; simp
          · simp
      · simp
      · simp only [Formula.bvrealize, Matrix.empty_eq] at hf
        grw [hf y ⟨b, hb⟩, inf_le_left]
        rfl

instance : HSSet B Γ ⊨ᵇᵛ ZF where
  bvrealize_of_mem φ hφ := by
    simp only [Theory.zf, Set.mem_setOf_eq] at hφ
    cases hφ with simp

end HSSet
