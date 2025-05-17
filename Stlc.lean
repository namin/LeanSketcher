/-
  Proving type safety of a Simply Typed Lambda-Calculus in Lean
  adapted from Dafny (which was adapted from Coq)

  This version includes only the core lambda calculus without extensions.

  See Dafny version at:
  https://github.com/namin/dafny-sandbox/blob/master/Stlc.dfy
-/

import Mathlib.Data.Set.Basic

-- Syntax

-- Types
inductive Ty : Type
| tbase : Ty                     -- (opaque base type)
| tarrow : Ty → Ty → Ty          -- T1 → T2
deriving DecidableEq

-- Terms
inductive Tm : Type
| tvar : Nat → Tm                -- x                (variable)
| tapp : Tm → Tm → Tm            -- t t              (application)
| tabs : Nat → Ty → Tm → Tm      -- λx:T.t           (abstraction)
deriving DecidableEq

-- Operational Semantics

-- Values
def value : Tm → Bool
| (Tm.tabs _ _ _) => true
| _ => false

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

-- Reduction step
def step : Tm → Option Tm
| (Tm.tapp (Tm.tabs x _ body) arg) =>
    if value arg then Option.some (subst x arg body)  -- AppAbs
    else Option.none
| (Tm.tapp f arg) =>
    match step f with
    | Option.some f' => Option.some (Tm.tapp f' arg)  -- App1
    | Option.none =>
        if value f then
          match step arg with
          | Option.some arg' => Option.some (Tm.tapp f arg')  -- App2
          | Option.none => Option.none
        else Option.none
| _ => Option.none

-- Multistep reduction
def reduces_to : Tm → Tm → Nat → Prop
| t, t', 0 => t = t'
| t, t', n+1 =>
    match step t with
    | Option.some t_step => reduces_to t_step t' n
    | Option.none => t = t'

-- Typing

-- A context is a partial map from variable names to types
def Context := List (Nat × Ty)

-- Look up a variable in the context
def find : Context → Nat → Option Ty
| [], _ => Option.none
| (x, T) :: rest, y => if x = y then Option.some T else find rest y

-- Extend the context with a new binding
def extend : Nat → Ty → Context → Context
| x, T, Γ => (x, T) :: Γ

-- Typing relation
def has_type : Context → Tm → Option Ty
| Γ, (Tm.tvar id) => find Γ id  -- Var
| Γ, (Tm.tabs x T body) =>  -- Abs
    match has_type (extend x T Γ) body with
    | Option.some ty_body => Option.some (Ty.tarrow T ty_body)
    | Option.none => Option.none
| Γ, (Tm.tapp f arg) =>  -- App
    match has_type Γ f, has_type Γ arg with
    | Option.some (Ty.tarrow T1 T2), Option.some ty_arg =>
        if T1 = ty_arg then Option.some T2 else Option.none
    | _, _ => Option.none

-- A term is closed if it has no free variables
def closed (t : Tm) : Prop := fv t = ∅

-- Type Safety Properties

-- Progress:
-- A well-typed term is either a value or it can step
theorem progress (t : Tm) : Option.isSome (has_type [] t) → value t ∨ Option.isSome (step t) := by
  -- This is where the proof would go
  sorry

-- Lemma: If x is free in t and t is well-typed in some context,
-- then this context must contain x
theorem free_in_context (Γ : Context) (x : Nat) (t : Tm) :
  x ∈ fv t → Option.isSome (has_type Γ t) → Option.isSome (find Γ x) := by
  -- Proof by induction on t
  sorry

-- Corollary: If a term can be well-typed in an empty context,
-- then it is closed
theorem typable_empty_closed (t : Tm) :
  Option.isSome (has_type [] t) → closed t := by
  -- Proof sketch:
  -- Suppose t is not closed, then there exists some x ∈ fv t
  -- By free_in_context, we'd have Option.isSome (find [] x)
  -- But find [] x = Option.none, which is a contradiction
  sorry

-- Context invariance:
-- If a term t is well-typed in context Γ,
-- and context Γ' agrees with Γ on all free variables of t,
-- then the term t is well-typed in context Γ',
-- with the same type as in context Γ
theorem context_invariance (Γ Γ' : Context) (t : Tm) :
  Option.isSome (has_type Γ t) →
  (∀ x, x ∈ fv t → find Γ x = find Γ' x) →
  has_type Γ t = has_type Γ' t := by
  -- Proof by induction on t
  sorry

-- Substitution preserves typing:
-- If s has type S in an empty context,
-- and t has type T in a context extended with x having type S,
-- then [x -> s]t has type T as well
theorem substitution_preserves_typing (Γ : Context) (x : Nat) (s t : Tm) (S: Ty):
  has_type [] s = some S →
  (has_type (extend x S []) t).isSome →
  has_type Γ (subst x s t) = has_type (extend x S Γ) t := by
  -- Proof by induction on t
  sorry

-- Preservation:
-- A well-typed term which steps preserves its type
theorem preservation (t : Tm) (t' : Tm):
  (has_type [] t).isSome →
  step t = some t' →
  has_type [] t' = has_type [] t := by
  -- Proof would use substitution_preserves_typing for the case of beta-reduction
  sorry

-- A normal form cannot step
def normal_form (t : Tm) : Prop := ¬ Option.isSome (step t)

-- A stuck term is a normal form that is not a value
def stuck (t : Tm) : Prop := normal_form t ∧ ¬ value t

-- Type soundness:
-- A well-typed term cannot get stuck
theorem soundness (t t' : Tm) (T : Ty) (n : Nat) :
  has_type [] t = Option.some T →
  reduces_to t t' n →
  ¬ stuck t' := by
  -- Proof by induction on n using progress and preservation
  intros ht hr
  have hc : (has_type [] t).isSome = true := by
      rw [ht]
      rfl
  have hp := progress t hc
  induction n
  case zero =>
    simp [reduces_to] at hr
    have hv := progress t hc
    cases hv
    case inl hv =>
      simp [stuck]
      intro
      rw [hr] at hv
      assumption
    case inr hs =>
      simp [stuck, normal_form]
      intro hs'
      rw [hr] at hs
      rw [hs', Option.isSome] at hs
      contradiction
  case succ n ih =>
    sorry
