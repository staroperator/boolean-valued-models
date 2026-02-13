module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Heyting.Hom

@[expose] public section

class SMulOrderIso (α : Type*) [Monoid α] (β : Type*) [LE β] [SMul α β] where
  smul_le_smul_iff : ∀ (a : α) (b c : β), a • b ≤ a • c ↔ b ≤ c

export SMulOrderIso (smul_le_smul_iff)

variable {α β ι : Type*} [Group α] [MulAction α β] {a : α} {b c : β} {f : ι → β}

@[simps!]
def SMulOrderIso.toOrderIso [LE β] [SMulOrderIso α β] (a : α) : β ≃o β where
  toEquiv := MulAction.toPerm a
  map_rel_iff' {b c} := smul_le_smul_iff a b c

theorem SMulOrderIso.toOrderIso_one [LE β] [SMulOrderIso α β] :
    toOrderIso (1 : α) = OrderIso.refl β := by
  ext; simp

theorem SMulOrderIso.toOrderIso_mul [LE β] [SMulOrderIso α β] {b : α} :
    toOrderIso (a * b) = (toOrderIso b : β ≃o β).trans (toOrderIso a) := by
  ext; simp [mul_smul]

theorem SMulOrderIso.toOrderIso_inv [LE β] [SMulOrderIso α β] :
    toOrderIso (a⁻¹) = (toOrderIso a : β ≃o β).symm := by
  ext; simp [toOrderIso]

theorem smul_top [PartialOrder β] [OrderTop β] [SMulOrderIso α β] :
    a • (⊤ : β) = ⊤ :=
  (SMulOrderIso.toOrderIso a).map_top

theorem smul_bot [PartialOrder β] [OrderBot β] [SMulOrderIso α β] :
    a • (⊥ : β) = ⊥ :=
  (SMulOrderIso.toOrderIso a).map_bot

theorem smul_sup [SemilatticeSup β] [SMulOrderIso α β] :
    a • (b ⊔ c) = a • b ⊔ a • c :=
  (SMulOrderIso.toOrderIso a).map_sup b c

theorem smul_inf [SemilatticeInf β] [SMulOrderIso α β] :
    a • (b ⊓ c) = a • b ⊓ a • c :=
  (SMulOrderIso.toOrderIso a).map_inf b c

theorem smul_himp [HeytingAlgebra β] [SMulOrderIso α β] :
    a • (b ⇨ c) = a • b ⇨ a • c :=
  map_himp (SMulOrderIso.toOrderIso a) b c

theorem smul_compl [HeytingAlgebra β] [SMulOrderIso α β] :
    a • bᶜ = (a • b)ᶜ :=
  map_compl (SMulOrderIso.toOrderIso a) b

theorem smul_sdiff [CoheytingAlgebra β] [SMulOrderIso α β] :
    a • (b \ c) = a • b \ a • c :=
  map_sdiff (SMulOrderIso.toOrderIso a) b c

theorem smul_iSup [CompleteLattice β] [SMulOrderIso α β] :
    a • ⨆ i, f i = ⨆ i, a • f i :=
  (SMulOrderIso.toOrderIso a).map_iSup f

theorem smul_iInf [CompleteLattice β] [SMulOrderIso α β] :
    a • ⨅ i, f i = ⨅ i, a • f i :=
  (SMulOrderIso.toOrderIso a).map_iInf f
