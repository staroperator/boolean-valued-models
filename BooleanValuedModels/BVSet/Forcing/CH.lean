module

public import BooleanValuedModels.BooleanAlgebra.FinMap
public import BooleanValuedModels.BVSet.Semantics

@[expose] public section

namespace BVSet.Cohen

open Ordinal

variable {α : Ordinal.{u}} {n : ℕ} {o : (ω_ α).ToType}

local notation "ℙ" => Finmap' (ℕ × Ordinal.ToType (ω_ α)) Bool
local notation "𝔹" => RegularOpenSet (ℕ × Ordinal.ToType (ω_ α) → Bool)

def cohenRealVal (o : (ω_ α).ToType) (n : ℕ) : 𝔹 :=
  ⟨PiDiscrete.basicOpen {(n, o)} fun _ => true, PiDiscrete.isRegularOpen_basicOpen⟩

@[simp]
theorem coe_cohenRealVal :
    (cohenRealVal o n : Set _) = PiDiscrete.basicOpen {(n, o)} fun _ => true := rfl

@[simp]
theorem mem_cohenRealVal {f} : f ∈ cohenRealVal o n ↔ f (n, o) = true := by
  rw [← SetLike.mem_coe, coe_cohenRealVal]
  grind

@[simp]
theorem mem_compl_cohenRealVal {f} : f ∈ (cohenRealVal o n)ᶜ ↔ f (n, o) = false := by
  rw [← SetLike.mem_coe, RegularOpenSet.coe_compl, coe_cohenRealVal,
    PiDiscrete.isClopen_basicOpen.compl.isOpen.interior_eq]
  grind

noncomputable def cohenReal (o : Ordinal.ToType (ω_ α)) : BVSet.{u, u} 𝔹 :=
  mkI ℕ (fun n => n) fun n => cohenRealVal o n

theorem forces_mem_cohenReal {p : ℙ} :
    p ⊩ n ∈ᴮ cohenReal o ↔ p.lookup (n, o) = true := by
  simp only [cohenReal, bmem_mkI, natCast_beq_natCast, apply_ite, le_top, inf_of_le_left, bot_le,
    inf_of_le_right, iSup_ite, iSup_iSup_eq_right, iSup_bot, sup_of_le_left, Finmap.forces_iff,
    mem_cohenRealVal]
  constructor
  · intro h
    specialize h (p.extend fun _ => false) fun a ha => by rw [Finmap.extend_apply_of_mem_entries ha]
    match h' : p.lookup (n, o) with
    | some true => rfl
    | some false =>
      rw [Finmap.lookup_eq_some_iff] at h'
      simp [Finmap.extend_apply_of_mem_entries h'] at h
    | none =>
      rw [Finmap.lookup_eq_none] at h'
      simp [Finmap.extend_apply_of_notMem h'] at h
  · intro h f hf
    rw [Finmap.lookup_eq_some_iff] at h
    exact hf _ h

theorem forces_notMem_cohenReal {p : ℙ} :
    p ⊩ n ∉ᴮ cohenReal o ↔ p.lookup (n, o) = false := by
  simp only [cohenReal, bmem_mkI, natCast_beq_natCast, apply_ite, le_top, inf_of_le_left, bot_le,
    inf_of_le_right, iSup_ite, iSup_iSup_eq_right, iSup_bot, sup_of_le_left, Finmap.forces_iff,
    mem_compl_cohenRealVal]
  constructor
  · intro h
    specialize h (p.extend fun _ => true) fun a ha => by rw [Finmap.extend_apply_of_mem_entries ha]
    match h' : p.lookup (n, o) with
    | some true =>
      rw [Finmap.lookup_eq_some_iff] at h'
      simp [Finmap.extend_apply_of_mem_entries h'] at h
    | some false => rfl
    | none =>
      rw [Finmap.lookup_eq_none] at h'
      simp [Finmap.extend_apply_of_notMem h'] at h
  · intro h f hf
    rw [Finmap.lookup_eq_some_iff] at h
    exact hf _ h

theorem cohenReal_ne_cohenReal {o₁ o₂ : Ordinal.ToType (ω_ α)} (h : o₁ ≠ o₂) :
    cohenReal o₁ =ᴮ cohenReal o₂ = ⊥ := by
  rw [eq_bot_iff_forall_not_forces (α := ℙ)]
  intro p hp
  rcases Infinite.exists_notMem_finset (p.keys.image Prod.fst) with ⟨n, hn⟩
  simp only [Finset.mem_image, Finmap.mem_keys, Prod.exists, exists_and_right, exists_eq_right,
    not_exists] at hn
  let q : ℙ := (p.insert (n, o₁) true).insert (n, o₂) false
  apply forces_bot (p := q) (β := 𝔹)
  rw [← inf_compl_self (cohenReal o₁ =ᴮ cohenReal o₂), forces_inf]
  refine ⟨hp.weaken ?_, ?_⟩
  · apply (Finmap.insert_le_of_notMem (by simp [ne_comm.1 h, hn o₂])).trans
    exact Finmap.insert_le_of_notMem (by simp [hn o₁])
  · grw [beq_def, compl_inf, ← le_sup_left, bsubset_def', compl_iInf,
      ← le_iSup _ (n : BVSet 𝔹), compl_himp, sdiff_eq, forces_inf]
    constructor
    · rw [forces_mem_cohenReal, Finmap.lookup_insert_of_ne _ (by simpa), Finmap.lookup_insert]
    · rw [forces_notMem_cohenReal, Finmap.lookup_insert]

theorem cohenReal_mem_powerset_omega :
    cohenReal o ∈ᴮ 𝒫ᴮ ωᴮ = (⊤ : 𝔹) := by
  simp [cohenReal, mkI_bsubset, natCast_bmem_omega]

theorem cardLE_powerset_omega :
    (ω_ α).toZFSet.toBVSet ≲ᴮ 𝒫ᴮ ωᴮ = (⊤ : 𝔹) := by
  classical
  haveI := @Classical.allZFSetDefinable
  rw [eq_top_iff]
  let f : BVSet 𝔹 :=
    (prod (ω_ α).toZFSet.toBVSet (𝒫ᴮ ωᴮ)).sep fun x =>
      ⨆ (o : (ω_ α).ToType), x =ᴮ kpair o.toOrd.1.toZFSet.toBVSet (cohenReal o)
  refine le_iSup_of_le f (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_)
  · rw [isRel_eq_bsubset_prod, sep_bsubset (by fun_prop)]
  · rw [isTotal, IsExtentional.iInf_bmem_toBVSet_himp (by fun_prop)]
    refine le_iInf fun ⟨x, hx⟩ => ?_
    simp only [mem_toZFSet_iff] at hx
    rcases hx with ⟨o, ho, rfl⟩
    refine le_iSup_of_le (cohenReal (Ordinal.ToType.mk ⟨o, ho⟩)) (le_inf ?_ ?_)
    · rw [cohenReal_mem_powerset_omega]
    · rw [bmem_sep' (by fun_prop)]
      refine le_inf ?_ (le_iSup_of_le (Ordinal.ToType.mk ⟨o, ho⟩) ?_)
      · grw [← le_kpair_bmem_prod, ZFSet.toBVSet_bmem_toBVSet_of_mem (by simpa),
          cohenReal_mem_powerset_omega, top_inf_eq]
      · simp
  · rw [isUnique, IsExtentional.iInf_bmem_toBVSet_himp (by fun_prop)]
    refine le_iInf fun ⟨x, hx⟩ => ?_
    simp only [mem_toZFSet_iff] at hx
    rcases hx with ⟨o, ho, rfl⟩
    refine le_iInf fun y₁ => ?_
    grw [← le_himp]
    refine le_iInf fun y₂ => ?_
    grw [← le_himp, le_himp_iff, top_inf_eq, bmem_sep' (by fun_prop),
      inf_le_right (a := _ ∈ᴮ prod _ _)]
    refine iSup_le fun o₁ => ?_
    rw [kpair_beq_kpair]
    by_cases ho₁ : o₁ = Ordinal.ToType.mk ⟨o, ho⟩
    · subst ho₁
      simp only [OrderIso.symm_apply_apply, beq_refl, le_top, inf_of_le_right, le_himp_iff]
      grw [bmem_sep' (by fun_prop), inf_le_right (a := _ ∈ᴮ prod _ _), inf_iSup_eq]
      refine iSup_le fun o₂ => ?_
      rw [kpair_beq_kpair]
      by_cases ho₂ : o₂ = Ordinal.ToType.mk ⟨o, ho⟩
      · subst ho₂
        simp only [OrderIso.symm_apply_apply, beq_refl, le_top, inf_of_le_right]
        grw [beq_symm y₂, beq_trans]
      · rw [ZFSet.toBVSet_beq_toBVSet_of_ne fun ne => by
          rw [toZFSet_injective.eq_iff] at ne; simp [ne] at ho₂]
        simp
    · rw [ZFSet.toBVSet_beq_toBVSet_of_ne fun ne => by
        rw [toZFSet_injective.eq_iff] at ne; simp [ne] at ho₁]
      simp
  · rw [isInjective, IsExtentional.iInf_bmem_toBVSet_himp (by fun_prop)]
    refine le_iInf fun ⟨x₁, hx₁⟩ => ?_
    simp only [mem_toZFSet_iff] at hx₁
    rcases hx₁ with ⟨o₁, ho₁, rfl⟩
    rw [IsExtentional.iInf_bmem_toBVSet_himp (by fun_prop)]
    refine le_iInf fun ⟨x₂, hx₂⟩ => ?_
    simp only [mem_toZFSet_iff] at hx₂
    rcases hx₂ with ⟨o₂, ho₂, rfl⟩
    refine le_iInf fun y => ?_
    grw [← le_himp, le_himp_iff, top_inf_eq, bmem_sep' (by fun_prop),
      inf_le_right (a := _ ∈ᴮ prod _ _)]
    refine iSup_le fun o₁' => ?_
    rw [kpair_beq_kpair]
    by_cases ho₁' : o₁' = Ordinal.ToType.mk ⟨o₁, ho₁⟩
    · subst ho₁'
      simp only [OrderIso.symm_apply_apply, beq_refl, le_top, inf_of_le_right, le_himp_iff]
      grw [bmem_sep' (by fun_prop), inf_le_right (a := _ ∈ᴮ prod _ _), inf_iSup_eq]
      refine iSup_le fun o₂' => ?_
      rw [kpair_beq_kpair]
      by_cases ho₂' : o₂' = Ordinal.ToType.mk ⟨o₂, ho₂⟩
      · subst ho₂'
        simp only [OrderIso.symm_apply_apply, beq_refl, le_top, inf_of_le_right]
        grw [beq_symm y, beq_trans]
        by_cases h : o₁ = o₂
        · simp [h]
        · grw [cohenReal_ne_cohenReal (by simpa), bot_le]
      · rw [ZFSet.toBVSet_beq_toBVSet_of_ne fun ne => by
          rw [toZFSet_injective.eq_iff] at ne; simp [ne] at ho₂']
        simp
    · rw [ZFSet.toBVSet_beq_toBVSet_of_ne fun ne => by
        rw [toZFSet_injective.eq_iff] at ne; simp [ne] at ho₁']
      simp

theorem not_ch (h : 1 < α) :
    ⨆ x : BVSet.{u, u} 𝔹, ωᴮ <ᴮ x ⊓ x <ᴮ 𝒫ᴮ ωᴮ = (⊤ : 𝔹) := by
  rw [eq_top_iff]
  refine le_iSup_of_le (ω₁).toZFSet.toBVSet (le_inf ?_ ?_)
  · rw [omega_def, ZFSet.cardLT_toBVSet_of_card_lt_card (by
      simpa using Cardinal.aleph0_lt_aleph_one)]
  · grw [← cardLT_trans_cardLE (v := (ω_ α).toZFSet.toBVSet),
      ZFSet.cardLT_toBVSet_of_card_lt_card (by simpa), cardLE_powerset_omega, top_inf_eq]

open FirstOrder Language set

theorem not_ch' (h : 1 < α) :
    Sentence.bvrealize (BVSet.{u, u} 𝔹) CH = ⊥ := by
  simpa [set.continuumHypothesis, Sentence.bvrealize, Formula.bvrealize] using not_ch h

end BVSet.Cohen

namespace FirstOrder.Language.Theory.zf

open set

theorem zfc_not_entails_ch : ¬ ZFC ⊨ᵇ CH :=
  BVStructure.not_entails_of_bvrealize_ne_top
    ((BVSet.Cohen.not_ch'.{0} one_lt_two).trans_ne bot_ne_top)

end FirstOrder.Language.Theory.zf
