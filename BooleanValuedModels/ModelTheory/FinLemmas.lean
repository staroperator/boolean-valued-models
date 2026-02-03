import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation

@[simp]
theorem Fin.snoc_apply_zero' {α : Fin 1 → Sort*} {p : ∀ i : Fin 0, α i.castSucc} {x} :
    Fin.snoc p x 0 = x := rfl

@[simp]
theorem Fin.snoc_apply_one {α : Sort*} {n : ℕ} {p : Fin (n + 2) → α} {x : α} :
    Fin.snoc (α := fun _ => α) p x 1 = p 1 := rfl

@[simp]
theorem Fin.snoc_apply_one' {α : Fin 2 → Sort*} {p : ∀ i : Fin 1, α i.castSucc} {x} :
    Fin.snoc p x 1 = x := rfl

@[simp]
theorem Fin.snoc_apply_two {α : Sort*} {n : ℕ} {p : Fin (n + 3) → α} {x : α} :
    Fin.snoc (α := fun _ => α) p x 2 = p 2 := rfl

@[simp]
theorem Fin.snoc_apply_two' {α : Fin 3 → Sort*} {p : ∀ i : Fin 2, α i.castSucc} {x} :
    Fin.snoc p x 2 = x := rfl

@[simp]
theorem Fin.snoc_apply_three {α : Sort*} {n : ℕ} {p : Fin (n + 4) → α} {x : α} :
    Fin.snoc (α := fun _ => α) p x 3 = p 3 := rfl

@[simp]
theorem Fin.snoc_apply_three' {α : Fin 4 → Sort*} {p : ∀ i : Fin 3, α i.castSucc} {x} :
    Fin.snoc p x 3 = x := rfl

@[simp]
theorem Fin.castAdd_one {n} {x : Fin n} : Fin.castAdd 1 x = x.castSucc := rfl

@[simp]
theorem Fin.castAdd_two {n} {x : Fin n} : Fin.castAdd 2 x = x.castSucc.castSucc := rfl

theorem Matrix.comp_vecCons {α β : Type*} {n} {a : α} {v : Fin n → α} {f : α → β} :
    f ∘ vecCons a v = vecCons (f a) (f ∘ v) := Fin.comp_cons _ _ _

theorem Matrix.comp_vecEmpty {α β : Type*} {f : α → β} :
    f ∘ ![] = ![] := Matrix.empty_eq _
