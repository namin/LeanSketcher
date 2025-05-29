import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

-- Syntax

-- Types
inductive Ty : Type
| tbase : Ty                     -- (opaque base type)
| tarrow : Ty → Ty → Ty          -- T1 → T2
| tnat : Ty                      -- natural numbers
deriving DecidableEq

namespace Ty
  notation:40 T1 " ⟹ " T2 => tarrow T1 T2
end Ty

-- Terms
inductive Tm : Type
| tvar : Nat → Tm                -- x                (variable)
| tapp : Tm → Tm → Tm            -- t t              (application)
| tabs : Nat → Ty → Tm → Tm      -- λx:T.t           (abstraction)
| tzero : Tm                     -- natural numbers
| tsucc : Tm → Tm
| tprev : Tm → Tm
deriving DecidableEq

-- Operational Semantics

-- Values
inductive Peano : Tm → Prop
| zero : Peano Tm.tzero
| succ : ∀ (t: Tm), Peano t -> Peano (Tm.tsucc t)

inductive Value : Tm → Prop
| abs : ∀ (x : Nat) (T : Ty) (t : Tm), Value (Tm.tabs x T t)
| number : ∀ (t: Tm), Peano t -> Value t

-- Free Variables
def fv : Tm → Set Nat
| (Tm.tvar id) => {id}
| (Tm.tapp f arg) => fv f ∪ fv arg
| (Tm.tabs x _ body) => fv body \ {x}  -- x is bound
| (Tm.tzero) => ∅
| (Tm.tsucc t) => fv t
| (Tm.tprev t) => fv t

-- Substitution
def subst : Nat → Tm → Tm → Tm
| x, s, (Tm.tvar x') => if x = x' then s else Tm.tvar x'
| x, s, (Tm.tapp t1 t2) => Tm.tapp (subst x s t1) (subst x s t2)
| x, s, (Tm.tabs x' T t1) => Tm.tabs x' T (if x = x' then t1 else subst x s t1)
| _, _, (Tm.tzero) => Tm.tzero
| x, s, (Tm.tsucc t) => Tm.tsucc (subst x s t)
| x, s, (Tm.tprev t) => Tm.tprev (subst x s t)

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
| prev_zero : Step (Tm.tprev Tm.tzero) Tm.tzero
| prev_succ : ∀ (t: Tm), Step (Tm.tprev (Tm.tsucc t)) t
| prev1 : ∀ (t t' : Tm), Step t t' -> Step (Tm.tprev t) (Tm.tprev t')
| succ1 : ∀ (t t' : Tm), Step t t' -> Step (Tm.tsucc t) (Tm.tsucc t')

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
| zero : ∀ (Γ : Context), HasType Γ Tm.tzero Ty.tnat
| prev : ∀ (Γ : Context) (t : Tm), HasType Γ t Ty.tnat → HasType Γ (Tm.tprev t) Ty.tnat
| succ : ∀ (Γ : Context) (t : Tm), HasType Γ t Ty.tnat → HasType Γ (Tm.tsucc t) Ty.tnat

-- A term is closed if it has no free variables
def closed (t : Tm) : Prop := fv t = ∅
