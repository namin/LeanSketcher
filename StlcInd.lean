/-
  Proving type safety of a Simply Typed Lambda-Calculus in Lean
  adapted from Dafny (which was adapted from Coq)

  This version includes only the core lambda calculus without extensions,
  and uses inductive propositions instead of option types.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
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

def lookup (Γ : Context) (x : Nat) : Option Ty :=
  match Γ with
  | [] => none
  | (y, T) :: Γ => if x = y then some T else lookup Γ x

-- Typing relation as an inductive proposition
inductive HasType : Context → Tm → Ty → Prop
| var : ∀ (Γ : Context) (x : Nat) (T : Ty),
    lookup Γ x = some T →
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
      contradiction
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
  x ∈ fv t → HasType Γ t T → ∃ T', lookup Γ x = some T' := by
  intros hfv htype
  induction htype with
  | var Γ y T hlookup =>
      simp [fv] at hfv
      subst hfv
      use T
  | app Γ t1 t2 T1 T2 h1 h2 ih1 ih2 =>
      simp [fv] at hfv
      cases hfv with
      | inl h1 => exact ih1 h1
      | inr h2 => exact ih2 h2
  | abs Γ y T1 T2 body ih1 ih2 =>
      simp [fv] at hfv
      let ⟨hin, hnot⟩ := hfv
      let hex := ih2 hin
      obtain ⟨T', hlookup'⟩ := hex
      use T'
      have Nxy : x ≠ y := by
        intro hxy
        apply hnot
        exact hxy
      simp [lookup] at hlookup'
      rw [if_neg hnot] at hlookup'
      exact hlookup'

-- Corollary: If a term is well-typed in an empty context,
-- then it is closed
theorem typable_empty_closed (t : Tm) (T : Ty) :
  HasType [] t T → closed t := by
  intro ht
  by_contra hne
  push_neg at hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨T', hi⟩ := free_in_context [] x t T hx ht
  simp [lookup] at hi

-- Context invariance:
-- If a term t is well-typed in context Γ,
-- and context Γ' agrees with Γ on all free variables of t,
-- then the term t is well-typed in context Γ' with the same type
theorem context_invariance (Γ Γ' : Context) (t : Tm) (T : Ty) :
  HasType Γ t T →
  (∀ x, x ∈ fv t → (lookup Γ' x) = (lookup Γ x)) →
  HasType Γ' t T := by
  -- This proof would be by induction on the typing derivation
  intros htype
  induction htype generalizing Γ' with
  | var Γ y T hlookup =>
      intros hinv
      let htype := HasType.var Γ y T hlookup
      have hfv : y ∈ fv (Tm.tvar y) := by
        simp [fv]
      let hxin := free_in_context Γ y (Tm.tvar y) T hfv htype
      obtain ⟨T', hget⟩ := hxin
      let hinvy := hinv y hfv
      rw [hlookup] at hinvy
      let htype' := HasType.var Γ' y T hinvy
      exact htype'
  | app Γ t1 t2 T1 T2 h1 h2 ih1 ih2 =>
      simp [fv]
      intros hfvs
      have hl1 : (∀ x ∈ fv t1, lookup Γ' x = lookup Γ x) := by
        intro x hx
        exact hfvs x (Or.inl hx)
      have hl2 : (∀ x ∈ fv t2, lookup Γ' x = lookup Γ x) := by
        intro x hx
        exact hfvs x (Or.inr hx)
      let htype' := HasType.app Γ' t1 t2 T1 T2 (ih1 Γ' hl1) (ih2 Γ' hl2)
      exact htype'
  | abs Γ y T1 T2 body ih1 ih2 =>
      intros hinv
      simp [fv] at hinv
      have ha : (∀ x ∈ fv body, lookup ((y, T1) :: Γ') x = lookup ((y, T1) :: Γ) x) := by
        intro x hx
        simp [lookup]
        by_cases hxy : x = y
        . rw [hxy]
          simp
        . simp only [if_neg hxy]
          apply hinv x hx
          exact hxy
      let ih2' := ih2 ((y, T1) :: Γ') ha
      let htype' := HasType.abs Γ' y T1 T2 body ih2'
      exact htype'

-- Substitution preserves typing:
-- If s has type S in an empty context,
-- and t has type T in a context extended with x having type S,
-- then [x -> s]t has type T in the empty context
theorem substitution_preserves_typing (Γ : Context) (x : Nat) (s t : Tm) (S T : Ty) :
  HasType [] s S →
  HasType ((x, S)::Γ) t T →
  HasType Γ (subst x s t) T := by
  intros Hs Ht
  induction t with
  | tvar y =>
    by_cases hxy : x = y
    . rw [hxy]
      subst hxy
      simp [subst]
      cases Ht with
      | var Γ x' T' hlookup =>
        simp [lookup] at hlookup
        subst hlookup
        let hc := typable_empty_closed s S Hs
        simp [closed] at hc
        let hc2 : ∀ x ∈ fv s, lookup Γ x = lookup [] x := by
          intro x hx
          rw [hc] at hx
          cases hx
        let hci := context_invariance [] Γ s S Hs hc2
        exact hci
    . simp [subst]
      simp only [if_neg hxy]
      cases Ht with
      | var Γ x' T' hlookup =>
        simp [lookup] at hlookup
        have h : y ≠ x := Ne.symm hxy
        rw [if_neg h] at hlookup
        let hc := typable_empty_closed s S Hs
        simp [closed] at hc
        let hc2 : ∀ x ∈ fv s, lookup Γ x = lookup [] x := by
          intro x hx
          rw [hc] at hx
          cases hx
        let hci := context_invariance [] Γ s S Hs hc2
        sorry
  | tapp t1 t2 =>
    sorry
  | tabs y Ty t ih =>
    by_cases hxy : x = y
    . simp [subst]
      subst hxy
      rw [if_pos rfl]
      let hc := context_invariance ((x, S)::Γ) Γ (Tm.tabs x Ty t) T Ht
      apply hc
      intros x' hfv'
      simp [fv] at hfv'
      simp [lookup]
      sorry
    . sorry

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
