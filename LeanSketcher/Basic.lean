import Lean
import Lean.Meta

namespace LeanSketcher

open Std
open Lean Elab Tactic Meta Parser Term Parser.Tactic

def isLikelySimpable (n : Name) : TacticM Bool := do
  match (← getEnv).find? n with
  | some (ConstantInfo.defnInfo _) => pure true
  | some (ConstantInfo.thmInfo _) => pure true
  | some (ConstantInfo.axiomInfo _) => pure true
  | some _ =>
    try
      let t ← liftMetaM (inferType (mkConst n))
      return !(← liftMetaM (isType t))
    catch _ => return false
  | none => pure false

def isType (t : Expr) : MetaM Bool := do
  let ty ← inferType t
  return ty.isSort

def getSimpNamesFromGoal : TacticM (List Name) := do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let lctx ← getLCtx
  let hyps := lctx.getFVarIds.map (fun id => (lctx.get! id).type)
  let exprs := tgt :: hyps.toList
  let init : Std.HashSet Name := {}
  let names := exprs.foldl (init := init) fun acc e =>
    e.foldConsts acc (fun n acc => acc.insert n)
  names.toList.filterM isLikelySimpable

/-- Build a simp tactic with given lemma names and a star. -/
-- NB: because the names and the final star have different types,
-- I couldn't build the syntax object directly.
def mkSimpSyntax (names : List Name) : TacticM (TSyntax `tactic) := do
  -- Build a string representation of the command
  let nameList := String.intercalate ", " (names.map toString)
  let simpCmdStr := s!"simp [{nameList}, *]"
  -- Parse the string into a syntax object
  match Lean.Parser.runParserCategory (← getEnv) `tactic simpCmdStr "<mkSimpSyntax>" with
  | Except.ok stx => pure $ TSyntax.mk stx
  | Except.error msg => throwError msg

/-- Apply simp with explicit names -/
def applySimpImpl (names : List Name) : TacticM Unit := do
  --logInfo m!"Names for simp: {names}"
  let stx ← mkSimpSyntax names
  evalTactic stx

/-- Syntax for apply_simp tactic that can take function names -/
syntax (name := applySimp) "apply_simp" Parser.ident* : tactic

/-- Implementation of apply_simp tactic -/
@[tactic applySimp]
def evalApplySimp : Tactic
  | `(tactic| apply_simp $funcNames*) => do
    applySimpImpl (funcNames.map (·.getId)).toList
  | _ => throwUnsupportedSyntax

/-- Custom simp tactic that automatically uses functions from the goal as simp lemmas -/
syntax (name := autoSimp) "auto_simp" : tactic

@[tactic autoSimp]
def evalAutoSimp : Tactic
  | `(tactic| auto_simp) => do
    let names ← getSimpNamesFromGoal
    applySimpImpl names
  | _ => throwUnsupportedSyntax

/-- Tactic for automatically solving optimize_optimal theorems -/
syntax (name := autoInduction) "auto_induction" term : tactic

@[tactic autoInduction]
def evalAutoInduction : Tactic := fun
  | `(tactic| auto_induction $t:term) => do
      let names ← getSimpNamesFromGoal
      let simpTactic ← mkSimpSyntax names
      let grindArgs ← names.mapM fun n => do
        let id := Lean.mkIdent n
        `(grindParam| $(id):ident)
      let grindTactic ← `(tactic| grind +ring [$grindArgs.toArray,*])

      let goal ← getMainGoal

      -- Try sequence 1: grind <;> simp
      try
        setGoals [goal]
        evalTactic (← `(tactic|
          induction $t:term <;>
          $simpTactic <;>
          $grindTactic
        ))
        if (← getUnsolvedGoals).isEmpty then return ()
      catch _ => pure ()

      -- Try sequence 2: split <;> simp
      try
        setGoals [goal]
        evalTactic (← `(tactic|
          induction $t:term <;>
          $simpTactic <;>
          split <;>
          $simpTactic
        ))
        if (← getUnsolvedGoals).isEmpty then return ()
      catch _ => pure ()

      throwError "auto_induction failed: all strategies left goals unsolved"
  | _ => throwUnsupportedSyntax

end LeanSketcher
