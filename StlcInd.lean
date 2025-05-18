/-
  Proving type safety of a Simply Typed Lambda-Calculus in Lean
  adapted from Dafny (which was adapted from Coq)

  This version includes only the core lambda calculus without extensions,
  and uses inductive propositions instead of option types.
-/
import Mathlib.Data.Set.Basic
import LeanSketcher
set_option grind.warning false

-- Syntax

-- Types
inductive Ty : Type
| tbase : Ty                     -- (opaque base type)
| tarrow : Ty → Ty → Ty          -- T1 → T2
deriving DecidableEq

namespace Ty
  notation:40 T1 " ⟹ " T2 => tarrow T1 T2
end Ty

-- Terms
inductive Tm : Type
| tvar : Nat → Tm                -- x                (variable)
| tapp : Tm → Tm → Tm            -- t t              (application)
| tabs : Nat → Ty → Tm → Tm      -- λx:T.t           (abstraction)
deriving DecidableEq

-- Operational Semantics

-- Values
inductive Value : Tm → Prop
| abs : ∀ (x : Nat) (T : Ty) (t : Tm), Value (Tm.tabs x T t)

-- Free Variables
def fv : Tm → Set Nat
| (Tm.tvar id) => {id}
| (Tm.tapp f arg) => fv f ∪ fv arg
| (Tm.tabs x _ body) => fv body \ {x}  -- x is bound

-- Substitution
def subst : Nat → Tm → Tm → Tm
| x, s, (Tm.tvar x') => if x = x' then s else Tm.tvar x'
| x, s, (Tm.tapp t1 t2) => Tm.tapp (subst x s t1) (subst x s t2)
| x, s, (Tm.tabs x' T t1) => Tm.tabs x' T (if x = x' then t1 else subst x s t1)

-- Single-step reduction relation
inductive Step : Tm → Tm → Prop
| app_abs : ∀ (x : Nat) (T : Ty) (body arg : Tm),
    Value arg →
    Step (Tm.tapp (Tm.tabs x T body) arg) (subst x arg body)
| app1 : ∀ (f f' arg : Tm),
    Step f f' →
    Step (Tm.tapp f arg) (Tm.tapp f' arg)
| app2 : ∀ (f arg arg' : Tm),
    Value f →
    Step arg arg' →
    Step (Tm.tapp f arg) (Tm.tapp f arg')

-- Multi-step reduction relation
inductive MultiStep : Tm → Tm → Prop
| refl : ∀ (t : Tm), MultiStep t t
| step : ∀ (t t' t'' : Tm),
    Step t t' →
    MultiStep t' t'' →
    MultiStep t t''

-- Typing

-- A context is a partial map from variable names to types
def Context := List (Nat × Ty)

-- Typing relation as an inductive proposition
inductive HasType : Context → Tm → Ty → Prop
| var : ∀ (Γ : Context) (x : Nat) (T : Ty),
    (∃ i, Γ.get? i = some (x, T)) →
    HasType Γ (Tm.tvar x) T
| abs : ∀ (Γ : Context) (x : Nat) (T1 T2 : Ty) (t : Tm),
    HasType ((x, T1) :: Γ) t T2 →
    HasType Γ (Tm.tabs x T1 t) (Ty.tarrow T1 T2)
| app : ∀ (Γ : Context) (t1 t2 : Tm) (T1 T2 : Ty),
    HasType Γ t1 (Ty.tarrow T1 T2) →
    HasType Γ t2 T1 →
    HasType Γ (Tm.tapp t1 t2) T2

-- A term is closed if it has no free variables
def closed (t : Tm) : Prop := fv t = ∅

-- Type Safety Properties

-- Progress:
-- A well-typed term is either a value or it can step
theorem progress (t : Tm) (T : Ty) :
  HasType [] t T → Value t ∨ ∃ t', Step t t' := by
  intros htype
  generalize hΓ : [] = Γ at htype
  induction htype with
  | var Γ x T hlookup =>
      -- Variables can't be typed in empty context
      rw [← hΓ] at hlookup
      simp at hlookup
  | abs _ x T1 T2 body _ =>
      -- Abstractions are values
      left
      apply Value.abs
  | app Γ t1 t2 T1 T2 h1 h2 ih1 ih2 =>
      -- Application case
      right
      cases ih1 hΓ with
      | inl hval1 =>
          -- t1 is a value with arrow type
          cases ih2 hΓ with
          | inl hval2 =>
              -- t2 is a value
              cases hval1 with
              | abs x T1 body =>
                use subst x t2 body
                apply Step.app_abs x T1 body t2 hval2
          | inr hstep2 =>
              -- t2 can step
              obtain ⟨t2', hstep2'⟩ := hstep2
              use Tm.tapp t1 t2'
              apply Step.app2 t1 t2 t2' hval1 hstep2'
      | inr hstep1 =>
          -- t1 can step
          cases hstep1 with
          | intro t1' hstep1' =>
              exists (Tm.tapp t1' t2)
              apply Step.app1
              exact hstep1'

-- Lemma: If x is free in t and t is well-typed in context Γ,
-- then x must be bound in Γ
theorem free_in_context (Γ : Context) (x : Nat) (t : Tm) (T : Ty) :
  x ∈ fv t → HasType Γ t T → ∃ T', (∃ i, Γ.get? i = some (x, T')) := by
  intros hfv htype
  induction htype with
  | var Γ y T hlookup =>
      have Exy : x = y := by sorry
      subst Exy
      obtain ⟨i, hlookup'⟩ := hlookup
      use T
      use i
  | app Γ t1 t2 T1 T2 h1 h2 ih1 ih2 =>
      simp [fv] at hfv
      cases hfv with
      | inl h1 => exact ih1 h1
      | inr h2 => exact ih2 h2
  | abs Γ y T1 T2 body ih1 ih2 =>
      simp [fv] at hfv
      let ⟨hin, hnot⟩ := hfv
      let hex := ih2 hin
      obtain ⟨T', ⟨i', hlookup'⟩⟩ := hex
      use T'
      have Nxy : x ≠ y := by
        intro hxy
        apply hnot
        exact hxy
      cases i' with
      | zero =>
        simp at hlookup'
        let ⟨Exy, ETT'⟩ := hlookup'
        subst Exy
        contradiction
      | succ j =>
        use j
        simp [List.get?, List.get?] at hlookup'
        simp [List.get?]
        exact hlookup'

-- Corollary: If a term is well-typed in an empty context,
-- then it is closed
theorem typable_empty_closed (t : Tm) (T : Ty) :
  HasType [] t T → closed t := by
  sorry

-- Context invariance:
-- If a term t is well-typed in context Γ,
-- and context Γ' agrees with Γ on all free variables of t,
-- then the term t is well-typed in context Γ' with the same type
theorem context_invariance (Γ Γ' : Context) (t : Tm) (T : Ty) :
  HasType Γ t T →
  (∀ x, x ∈ fv t →
    (∃ Tx, (∃ i, Γ.get? i = some (x, Tx))) ↔
    (∃ Tx, (∃ i, Γ'.get? i = some (x, Tx)))) →
  HasType Γ' t T := by
  sorry  -- This proof would be by induction on the typing derivation

-- Substitution preserves typing:
-- If s has type S in an empty context,
-- and t has type T in a context extended with x having type S,
-- then [x -> s]t has type T in the empty context
theorem substitution_preserves_typing (x : Nat) (s t : Tm) (S T : Ty) :
  HasType [] s S →
  HasType [(x, S)] t T →
  HasType [] (subst x s t) T := by
  sorry  -- This proof would be by induction on the typing derivation of t

-- Preservation:
-- A well-typed term which steps preserves its type
theorem preservation (t t' : Tm) (T : Ty) :
  HasType [] t T →
  Step t t' →
  HasType [] t' T := by
  sorry

-- A normal form is a term that cannot step
def normal_form (t : Tm) : Prop := ¬ ∃ t', Step t t'

-- A stuck term is a normal form that is not a value
def stuck (t : Tm) : Prop := normal_form t ∧ ¬ Value t

-- Progress implies not stuck
lemma progress_not_stuck (t : Tm) :
  (Value t ∨ ∃ t', Step t t') →
  ¬ stuck t := by
  sorry

-- Type soundness:
-- A well-typed term cannot get stuck after any number of reduction steps
theorem soundness (t t' : Tm) (T : Ty) :
  HasType [] t T →
  MultiStep t t' →
  ¬ stuck t' := by
  sorry
