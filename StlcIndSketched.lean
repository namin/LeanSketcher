import LeanSketcher
import StlcInd

theorem progress_sketched (t : Tm) (T : Ty) :
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
      (discharge_case_progress Value [ih1 hΓ, ih2 hΓ] [Step.app_abs, Step.app2, Step.app1])
