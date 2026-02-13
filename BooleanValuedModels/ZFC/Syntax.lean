module

public import Mathlib.ModelTheory.Syntax

@[expose] public section

namespace FirstOrder.Language

inductive setFunc : Nat → Type
| empty : setFunc 0
| insert : setFunc 2
| sUnion : setFunc 1
| powerset : setFunc 1
| omega : setFunc 0

inductive setRel : Nat → Type
| mem : setRel 2

def set : Language where
  Functions := setFunc
  Relations := setRel

variable {α : Type*} {n : ℕ}

namespace set

def mem (t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  Relations.boundedFormula₂ .mem t₁ t₂

scoped infix:88 " ∈' " => mem

def subset (t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' t₁.relabel (Sum.map id Fin.castSucc)
    ⟹ &(Fin.last n) ∈' t₂.relabel (Sum.map id Fin.castSucc))

scoped infix:88 " ⊆' " => subset

instance : EmptyCollection (set.Term α) :=
  ⟨Constants.term .empty⟩

instance : Insert (set.Term α) (set.Term α) :=
  ⟨Functions.apply₂ .insert⟩

instance : Singleton (set.Term α) (set.Term α) :=
  ⟨(insert · ∅)⟩

def sUnion (t : set.Term α) : set.Term α :=
  Functions.apply₁ .sUnion t

scoped prefix:110 "⋃₀ " => sUnion

def powerset (t : set.Term α) : set.Term α :=
  Functions.apply₁ .powerset t

scoped prefix:100 "𝒫 " => powerset

def omega : set.Term α :=
  Constants.term .omega

scoped notation "ω" => omega

-- ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y
def axiomOfExtensionality : set.Sentence :=
  ∀' ∀' (∀' (&2 ∈' &0 ⇔ &2 ∈' &1) ⟹ &0 =' &1)

-- ∀ x, x ∉ ∅
def axiomOfEmpty : set.Sentence :=
  ∀' (∼ (&0 ∈' ∅))

-- ∀ x y z, z ∈ insert x y ↔ z = x ∨ z ∈ y
def axiomOfPairing : set.Sentence :=
  ∀' ∀' ∀' (&2 ∈' insert &0 &1 ⇔ &2 =' &0 ⊔ &2 ∈' &1)

-- ∀ x y, y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z
def axiomOfUnion : set.Sentence :=
  ∀' ∀' (&1 ∈' ⋃₀ &0 ⇔ ∃' (&2 ∈' &0 ⊓ &1 ∈' &2))

-- ∀ x y, y ∈ 𝒫 x ↔ y ⊆ x
def axiomOfPowerset : set.Sentence :=
  ∀' ∀' (&1 ∈' 𝒫 &0 ⇔ &1 ⊆' &0)

-- ∅ ∈ ω ∧ (∀ x ∈ ω, insert x x ∈ ω) ∧ ∀ x, ∅ ∈ x → (∀ y ∈ x, insert y y ∈ x) → ω ⊆ x
def axiomOfInfinity : set.Sentence :=
  ∅ ∈' ω ⊓ ∀' (&0 ∈' ω ⟹ insert &0 &0 ∈' ω)
    ⊓ ∀' (∅ ∈' &0 ⟹ ∀' (&1 ∈' &0 ⟹ insert &1 &1 ∈' &0) ⟹ ω ⊆' &1)

-- ∀ x, (∃ y, y ∈ x) → ∃ y ∈ x, ¬ (∃ z ∈ y, z ∈ x)
def axiomOfRegularity : set.Sentence :=
  ∀' (∃' (&1 ∈' &0) ⟹ ∃' (&1 ∈' &0 ⊓ ∼ (∃' (&2 ∈' &1 ⊓ &2 ∈' &0))))

-- -- ∀ x₁, ⋯, xₙ a, ∃ b, ∀ x, x ∈ b ↔ x ∈ a ∧ φ(x₁, ⋯, xₙ, x)
noncomputable def axiomOfSeparation [Finite α] (φ : set.Formula (α ⊕ Fin 1)) : set.Sentence :=
  Formula.iAlls α (∀' ∃' ∀'
    (&2 ∈' &1 ⇔ &2 ∈' &0 ⊓ BoundedFormula.relabel (k := 0) (Sum.map Sum.inr ![2]) φ))

-- ∀ x₁, ⋯, xₙ a, (∀ x ∈ a, ∃ y, φ(x₁, ⋯, xₙ, x, y)) → ∃ b, ∀ x, x ∈ a → ∃ y ∈ b ∧ φ(x₁, ⋯, xₙ, x, y)
noncomputable def axiomOfCollection [Finite α] (φ : set.Formula (α ⊕ Fin 2)) : set.Sentence :=
  Formula.iAlls α (∀' (
    (∀' (&1 ∈' &0 ⟹ ∃' (BoundedFormula.relabel (k := 0) (Sum.map Sum.inr ![1, 2]) φ)))
      ⟹ ∃' ∀' (&2 ∈' &0 ⟹ ∃' (&3 ∈' &1 ⊓ BoundedFormula.relabel (k := 0) (Sum.map Sum.inr ![2, 3]) φ))))

-- ∀ x₁, ⋯, xₙ a, (∀ x ∈ a, ∃! y, φ(x₁, ⋯, xₙ, x, y)) → ∃ b, ∀ y, x ∈ b ↔ ∃ x ∈ a ∧ φ(x₁, ⋯, xₙ, x y)
noncomputable def axiomOfReplacement [Finite α] (φ : set.Formula (α ⊕ Fin 2)) : set.Sentence :=
  Formula.iAlls α (∀' (
    (∀' (&1 ∈' &0 ⟹ ∃' (BoundedFormula.relabel (k := 0) (Sum.map Sum.inr ![1, 2]) φ)
      ⊓ ∀' ∀' (BoundedFormula.relabel (k := 0) (Sum.map Sum.inr ![1, 2]) φ
        ⟹ BoundedFormula.relabel (k := 0) (Sum.map Sum.inr ![1, 3]) φ
          ⟹ &2 =' &3)))
    ⟹ ∃' ∀' (&2 ∈' &1 ⇔ ∃' (&3 ∈' &0
      ⊓ BoundedFormula.relabel (k := 0) (Sum.map Sum.inr ![3, 2]) φ))))

def kpair (t₁ t₂ : set.Term α) : set.Term α :=
  {{t₁}, {t₁, t₂}}

-- ∀ z ∈ r, ∃ x ∈ a, ∃ y ∈ b, z = ⟪a, b⟫
def isRel (a b r : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' r.relabel (Sum.map id Fin.castSucc)
    ⟹ ∃' (&(Fin.last (n + 1)) ∈' a.relabel (Sum.map id (Fin.castAdd 2))
      ⊓ ∃' (&(Fin.last (n + 2)) ∈' b.relabel (Sum.map id (Fin.castAdd 3))
        ⊓ &((Fin.last n).castAdd 2) =' kpair &(Fin.last (n + 1)).castSucc &(Fin.last (n + 2)))))

-- ∀ x ∈ a, ∀ y₁ ∈ b, ∀ y₂ ∈ b, ⟪x, y₁⟫ ∈ r → ⟪x, y₂⟫ ∈ r → y₁ = y₂
def isUnique (a b r : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' a.relabel (Sum.map id Fin.castSucc)
    ⟹ ∀' (&(Fin.last (n + 1)) ∈' b.relabel (Sum.map id (Fin.castAdd 2))
      ⟹ ∀' (&(Fin.last (n + 2)) ∈' b.relabel (Sum.map id (Fin.castAdd 3))
        ⟹ kpair &((Fin.last n).castAdd 2) &(Fin.last (n + 1)).castSucc ∈' r.relabel (Sum.map id (Fin.castAdd 3))
          ⟹ kpair &((Fin.last n).castAdd 2) &(Fin.last (n + 2)) ∈' r.relabel (Sum.map id (Fin.castAdd 3))
            ⟹ &(Fin.last (n + 1)).castSucc =' &(Fin.last (n + 2)))))

-- ∀ x ∈ a, ∃ y ∈ b, ⟪x, y⟫ ∈ f
def isTotal (a b f : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' a.relabel (Sum.map id Fin.castSucc)
    ⟹ ∃' (&(Fin.last (n + 1)) ∈' b.relabel (Sum.map id (Fin.castAdd 2))
      ⊓ kpair &(Fin.last n).castSucc &(Fin.last (n + 1)) ∈' f.relabel (Sum.map id (Fin.castAdd 2))))

-- ∀ x₁ ∈ a, ∀ x₂ ∈ a, ∀ y ∈ b, ⟪x₁, y⟫ ∈ f → ⟪x₂, y⟫ ∈ f → x₁ = x₂
def isInjective (a b f : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' a.relabel (Sum.map id Fin.castSucc)
    ⟹ ∀' (&(Fin.last (n + 1)) ∈' a.relabel (Sum.map id (Fin.castAdd 2))
      ⟹ ∀' (&(Fin.last (n + 2)) ∈' b.relabel (Sum.map id (Fin.castAdd 3))
        ⟹ kpair &((Fin.last n).castAdd 2) &(Fin.last (n + 2)) ∈' f.relabel (Sum.map id (Fin.castAdd 3))
          ⟹ kpair &(Fin.last (n + 1)).castSucc &(Fin.last (n + 2)) ∈' f.relabel (Sum.map id (Fin.castAdd 3))
            ⟹ &((Fin.last n).castAdd 2) =' &(Fin.last (n + 1)).castSucc)))

-- ∀ y ∈ b, ∃ x ∈ a, ⟪x, y⟫ ∈ f
def isSurjective (a b f : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' b.relabel (Sum.map id Fin.castSucc)
    ⟹ ∃' (&(Fin.last (n + 1)) ∈' a.relabel (Sum.map id (Fin.castAdd 2))
      ⊓ kpair &(Fin.last (n + 1)) &(Fin.last n).castSucc ∈' f.relabel (Sum.map id (Fin.castAdd 2))))

def isFunc (a b f : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  isRel a b f ⊓ isTotal a b f ⊓ isUnique a b f

-- ∀ x, ∅ ∉ x → ∃ f, isFunc x (⋃₀ x) f ∧ ∀ y ∈ x, ∃ z ∈ y, ⟪y, z⟫ ∈ f
def axiomOfChoice : set.Sentence :=
  ∀' (∼ (∅ ∈' &0) ⟹ ∃' (isFunc &0 (⋃₀ &0) &1 ⊓ ∀' (&2 ∈' &0 ⟹ ∃' (&3 ∈' &2 ⊓ kpair &2 &3 ∈' &1))))

scoped notation "AC" => axiomOfChoice

-- ∃ f, isFunc a b f ∧ isInjective a b f
def cardLE (a b : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∃' (isFunc (a.relabel (Sum.map id Fin.castSucc)) (b.relabel (Sum.map id Fin.castSucc)) &(Fin.last n)
    ⊓ isInjective (a.relabel (Sum.map id Fin.castSucc)) (b.relabel (Sum.map id Fin.castSucc)) &(Fin.last n))

def cardLT (a b : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  cardLE a b ⊓ ∼ (cardLE b a)

-- ¬ ∃ x, |ω| < |x| ∧ |x| < |𝒫 ω|
def continuumHypothesis : set.Sentence :=
  ∼ (∃' (cardLT ω &0 ⊓ cardLT &0 (𝒫 ω)))

scoped notation "CH" => continuumHypothesis

end set

open set

inductive zfAxioms : set.Sentence → Prop
| extensionality : zfAxioms axiomOfExtensionality
| empty : zfAxioms axiomOfEmpty
| pairing : zfAxioms axiomOfPairing
| union : zfAxioms axiomOfUnion
| powerset : zfAxioms axiomOfPowerset
| infinity : zfAxioms axiomOfInfinity
| regularity : zfAxioms axiomOfRegularity
| separation {n} (φ : set.Formula (Fin n ⊕ Fin 1)) : zfAxioms (axiomOfSeparation φ)
| collection {n} (φ : set.Formula (Fin n ⊕ Fin 2)) : zfAxioms (axiomOfCollection φ)

def Theory.zf : set.Theory :=
  setOf zfAxioms

scoped[FirstOrder.Language.set] notation "ZF" => FirstOrder.Language.Theory.zf

def Theory.zfc : set.Theory :=
  ZF ∪ {AC}

scoped[FirstOrder.Language.set] notation "ZFC" => FirstOrder.Language.Theory.zfc

end FirstOrder.Language
