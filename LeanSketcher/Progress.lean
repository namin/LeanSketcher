import Lean
import Lean.PrettyPrinter.Delaborator
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Apply

namespace LeanSketcher

open Lean Macro Elab Tactic Meta Syntax Parser.Tactic Parser.Term
open Lean.PrettyPrinter.Delaborator

syntax (name := forceCasesTerm) "force_cases " term : tactic

@[tactic forceCasesTerm]
def evalforceCasesTerm : Tactic := fun
  | `(tactic| force_cases $t:term) => do
      -- Directly evaluate a cases tactic on the term
      evalTactic (← `(tactic| cases $t:term))
  | _ => throwUnsupportedSyntax


elab "invert_all_pred" pred:term : tactic => do
  withMainContext do
    let predExpr ← elabTerm pred none
    let predName := (← whnf predExpr).getAppFn.constName?
    unless predName.isSome do
      throwError "Expected a constant predicate name"

    let lctx ← getLCtx
    for localDecl in lctx do
      let type ← whnf (← instantiateMVars localDecl.type)
      match type.getAppFnArgs with
      | (fn, _) =>
        if fn == predName then
          let hypIdent : TSyntax `ident := mkIdent localDecl.userName
          evalTactic (← `(tactic| have h_copy := $hypIdent))
          evalTactic (← `(tactic| cases $hypIdent:ident))

partial def isExistsType (type : Expr) : MetaM Bool := do
  let type ← whnf type -- weak head normal form, unfolds definitions
  match type with
  | Expr.forallE _ _ body _ => isExistsType body -- peel off pi-types
  | Expr.app fn _ =>
    match fn.getAppFn with
    | Expr.const name _ => pure (name == ``Exists)
    | _ => pure false
  | _ => pure false

elab "invert_all_Exists" : tactic => do
  withMainContext do
  let lctx ← getLCtx
  for localDecl in lctx do
    let type ← instantiateMVars localDecl.type
    --logInfo m!"Checking hypothesis: {localDecl.userName} : {localDecl.type}"
    if ← isExistsType type then
      let hypIdent : TSyntax `ident := mkIdent localDecl.userName
      evalTactic (← `(tactic| cases $hypIdent:ident))

syntax (name := stepSolveWith) "stepSolveWith " "[" term,* "]" : tactic

@[tactic stepSolveWith] def evalStepSolveWith : Tactic := fun stx => do
  let ctorSyntaxes := stx[2]!.getSepArgs

  let tacticStxs ← ctorSyntaxes.mapM fun ctor => do
    let termStx : TSyntax `term := ⟨ctor⟩
    `(tactic| apply $termStx <;> assumption)

  let rec tryAll : List (TSyntax `tactic) → TacticM Unit
    | [] => throwError "None of the tactics succeeded"
    | tac :: rest => try evalTactic tac catch _ => tryAll rest

  tryAll tacticStxs.toList


-- Wrap ident as elimTarget node (needed by `cases`)
def asElimTarget (id : Syntax) : TSyntax ``elimTarget :=
  ⟨Syntax.node Lean.SourceInfo.none `elimTarget #[id]⟩

-- Helper function containing the common logic
def dischargeCaseProgressImpl (p : Name) (ihs : Array Syntax) (ctorTerms : Array Syntax) : TacticM Unit := do
  -- Build `cases ih1 <;> cases ih2`
  let tacticSeq ←
    if ihs.isEmpty then
      `(tactic| skip)
    else
      let mut acc ← `(tactic| force_cases $(⟨ihs[0]!⟩))
      for ih in ihs[1:] do
        acc ← `(tactic| $acc <;> force_cases $(⟨ih⟩))
      pure acc

  -- Build TSepArray [Ctor1, Ctor2, ...] with commas
  let elemsAndSeps :=
    List.intersperse (Syntax.atom SourceInfo.none ",") ctorTerms.toList |>.toArray
  let ctorArray : TSepArray `term "," := { elemsAndSeps := elemsAndSeps }

  -- Final tactic: exact (stepSolveWith [Ctor1, Ctor2, ...])
  let full ← `(tactic|
    $tacticSeq
    <;> invert_all_pred $(mkIdent p)
    <;> invert_all_Exists
    <;> apply Exists.intro _
    <;> stepSolveWith [$ctorArray,*]
  )

  evalTactic full

syntax (name := dischargeCaseProgress)
  "discharge_case_progress " ident "[" term,* "]" "[" term,* "]" : tactic

@[tactic dischargeCaseProgress]
def evalDischargeCaseProgress : Tactic := fun stx => do
  let p := stx[1].getId
  let ihs := stx[3].getSepArgs
  let ctorTerms := stx[6].getSepArgs
  dischargeCaseProgressImpl p ihs ctorTerms

def getInductiveConstructors (typeName : Name) : MetaM (List Name) := do
  let env ← getEnv
  match env.find? typeName with
  | some (ConstantInfo.inductInfo info) =>
    pure info.ctors
  | _ => throwError s!"Type {typeName} is not an inductive type"

syntax (name := dischargeCaseProgressAuto)
  "discharge_case_progress_auto " ident ident "[" term,* "]" : tactic

@[tactic dischargeCaseProgressAuto]
def evalDischargeCaseProgressAuto : Tactic := fun stx => do
  let typeName := stx[1].getId
  let p := stx[2].getId
  let ihs := stx[4].getSepArgs

  -- Get constructors automatically
  let ctorNames ← getInductiveConstructors typeName
  let ctorTerms ← ctorNames.mapM fun name => do
    let ident := mkIdent name
    pure ident.raw

  dischargeCaseProgressImpl p ihs ctorTerms.toArray

end LeanSketcher
