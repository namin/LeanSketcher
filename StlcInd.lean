/-
  Proving type safety of a Simply Typed Lambda-Calculus in Lean
  adapted from Dafny (which was adapted from Coq)

  This version includes only the core lambda calculus without extensions,
  and uses inductive propositions instead of option types.

  See Dafny version at:
  https://github.com/namin/dafny-sandbox/blob/master/Stlc.dfy

  See the original Coq version at:
  https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html
  https://softwarefoundations.cis.upenn.edu/plf-current/StlcProp.html
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

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
  intro htype
  generalize hΓ : [] = Γ at htype
  induction htype with
  | var Γ x T hlookup =>
      rw [← hΓ] at hlookup
      simp [lookup] at hlookup
  | abs _ x T1 T2 body _ =>
      left
      apply Value.abs
  | app Γ t1 t2 T1 T2 h1 h2 ih1 ih2 =>
      right
      cases ih1 hΓ with
      | inl hval1 =>
          cases ih2 hΓ with
          | inl hval2 =>
              cases hval1 with
              | abs x T1 body =>
                  exists (subst x t2 body)
                  apply Step.app_abs; assumption
          | inr hstep2 =>
              obtain ⟨t2', hstep2'⟩ := hstep2
              exists (Tm.tapp t1 t2')
              apply Step.app2 <;> assumption
      | inr hstep1 =>
          obtain ⟨t1', hstep1'⟩ := hstep1
          exists (Tm.tapp t1' t2)
          apply Step.app1; assumption

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
  (∀ x, x ∈ fv t → lookup Γ' x = lookup Γ x) →
  HasType Γ' t T := by
  intros htype hinv
  induction htype generalizing Γ' with
  | var Γ y T hlookup =>
    apply HasType.var
    rw [hinv]
    · exact hlookup
    · simp [fv]
  | app Γ t1 t2 T1 T2 h1 h2 ih1 ih2 =>
    apply HasType.app
    · apply ih1
      intro x hx
      apply hinv
      simp [fv]
      exact Or.inl hx
    · apply ih2
      intro x hx
      apply hinv
      simp [fv]
      exact Or.inr hx
  | abs Γ y T1 T2 body _ ih2 =>
    apply HasType.abs
    apply ih2
    intro x hx
    simp [lookup]
    split_ifs with h
    · rfl  -- x = y case
    · apply hinv  -- x ≠ y case
      simp [fv]
      exact ⟨hx, h⟩

-- Lookup invariance under context permutation:
-- If two variables x,y are distinct, then looking up any variable z
-- in contexts that differ only by the order of x,y bindings gives the same result
theorem lookup_invariance_swap {Γ : Context} {x y : Nat} {S Ty : Ty} (h' : x ≠ y) :
  ∀ z, lookup ((x, S) :: (y, Ty) :: Γ) z = lookup ((y, Ty) :: (x, S) :: Γ) z := by
  intro z
  simp [lookup]
  by_cases h₁ : z = x
  · rw [if_pos h₁]
    have h₁y : z ≠ y := by
      intro hxy
      apply h'
      rw [←h₁, hxy]
    rw [if_neg h₁y]
    rw [if_pos h₁]
  · by_cases h₂ : z = y
    · rw [if_neg h₁, if_pos h₂]
      rw [if_pos h₂]
    · rw [if_neg h₁, if_neg h₂]
      rw [if_neg h₂, if_neg h₁]

-- Substitution preserves typing:
-- If s has type S in an empty context,
-- and t has type T in a context extended with x having type S,
-- then [x -> s]t has type T in the empty context
theorem substitution_preserves_typing (Γ : Context) (x : Nat) (s t : Tm) (S T : Ty) :
  HasType [] s S →
  HasType ((x, S)::Γ) t T →
  HasType Γ (subst x s t) T := by
  intros Hs Ht
  induction t generalizing T Γ with
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
        exact (HasType.var Γ y T hlookup)
  | tapp t1 t2 ih1 ih2 =>
    simp [subst]
    cases Ht with
    | app Γ t1 t2 T1 T2 htype1 htype2 =>
      apply HasType.app
      . exact ih1 Γ (T1 ⟹ T) htype1
      . exact ih2 Γ T1 htype2
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
      let ⟨hfv1, nxy⟩ := hfv'
      simp only [if_neg nxy]
    . simp [subst]
      have h' : x ≠ y := Ne.intro hxy
      rw [if_neg h']
      cases Ht with
      | abs Γ y Ty T body htype =>
        let hc := context_invariance ((y, Ty)::(x, S)::Γ) ((x, S)::(y, Ty)::Γ) t T htype
        have h : (∀ x_1 ∈ fv t, lookup ((x, S) :: (y, Ty) :: Γ) x_1 = lookup ((y, Ty) :: (x, S) :: Γ) x_1) := by
          intro x₁ hx
          apply lookup_invariance_swap h'
        let h0 := ih ((y, Ty)::Γ) T (hc h)
        apply HasType.abs
        · exact h0

-- Preservation:
-- A well-typed term which steps preserves its type
theorem preservation (t t' : Tm) (T : Ty) :
  HasType [] t T →
  Step t t' →
  HasType [] t' T := by
  intros Ht Hs
  induction Hs generalizing T with
  | app_abs x Ty body arg hval =>
    cases Ht with
    | app Γ f arg T1 T2 htype1 htype2 =>
      cases htype1 with
      | abs Γ x Ty T body htype =>
        have h := substitution_preserves_typing [] x arg body Ty T htype2 htype
        exact h
  | app1 f f' arg hstep ih =>
    cases Ht with
    | app Γ f arg T1 T2 htype1 htype2 =>
      apply HasType.app
      · exact ih (T1 ⟹ T) htype1
      · exact htype2
  | app2 f arg arg' hval hstep ih=>
    cases Ht with
    | app Γ f arg T1 T2 htype1 htype2 =>
      apply HasType.app
      · exact htype1
      · exact ih T1 htype2

-- A normal form is a term that cannot step
def normal_form (t : Tm) : Prop := ¬ ∃ t', Step t t'

-- A stuck term is a normal form that is not a value
def stuck (t : Tm) : Prop := normal_form t ∧ ¬ Value t

-- Progress implies not stuck
lemma progress_not_stuck (t : Tm) :
  (Value t ∨ ∃ t', Step t t') →
  ¬ stuck t := by
  intro hp
  cases hp with
  | inl hv =>
      simp [stuck]
      intro
      assumption
   | inr hs =>
      simp [stuck]
      intro hn
      contradiction

-- Type soundness:
-- A well-typed term cannot get stuck after any number of reduction steps
theorem soundness (t t' : Tm) (T : Ty) :
  HasType [] t T →
  MultiStep t t' →
  ¬ stuck t' := by
  intros Ht Hs
  induction Hs with
  | refl t =>
    have hp := progress t T Ht
    have ns := progress_not_stuck t hp
    exact ns
  | step t t' t'' hstep ih iht =>
    have he := preservation t t' T Ht hstep
    exact (iht he)
