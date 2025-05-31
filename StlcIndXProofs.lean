import LeanSketcher
import StlcIndX

lemma canonical_forms_abs (t : Tm) (T₁ T₂ : Ty) :
  Value t → HasType [] t (T₁ ⟹ T₂) → ∃ x body, t = Tm.tabs x T₁ body := by
  intro hval htype
  cases hval with
  | abs x T1 body =>
    have h : T₁ = T1 := by
      cases htype
      rfl
    subst h
    exists x
    exists body
  | number n iv =>
    induction iv with
    | zero =>
      cases htype
    | succ n iv =>
      cases htype

lemma canonical_forms_number (t : Tm) :
  Value t → HasType [] t Ty.tnat → Peano t := by
  intro hval htype
  cases hval with
  | abs x T1 body =>
    cases htype
  | number n iv =>
    assumption

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
            rw [← hΓ] at h1
            rcases canonical_forms_abs t1 T1 T2 hval1 h1 with ⟨x, body, h⟩
            subst h
            exists (subst x t2 body)
            apply Step.app_abs
            assumption
          | inr hstep2 =>
              obtain ⟨t2', hstep2'⟩ := hstep2
              exists (Tm.tapp t1 t2')
              apply Step.app2 <;> assumption
      | inr hstep1 =>
          obtain ⟨t1', hstep1'⟩ := hstep1
          exists (Tm.tapp t1' t2)
          apply Step.app1; assumption
  | zero Γ =>
      left
      apply Value.number
      apply Peano.zero
  | prev Γ n htype ih =>
      right
      cases ih hΓ with
      | inl hval1 =>
        rw [← hΓ] at htype
        let h := canonical_forms_number n hval1 htype
        cases h with
        | zero =>
          exists Tm.tzero
          apply Step.prev_zero
        | succ n iv =>
          exists n
          apply Step.prev_succ
      | inr hstep1 =>
          obtain ⟨t1', hstep1'⟩ := hstep1
          exists (Tm.tprev t1')
          apply Step.prev1; assumption
  | succ Γ n htype ih =>
      cases ih hΓ with
      | inl hval1 =>
        rw [← hΓ] at htype
        let h := canonical_forms_number n hval1 htype
        left
        apply Value.number
        apply Peano.succ
        assumption
      | inr hstep1 =>
          right
          obtain ⟨t1', hstep1'⟩ := hstep1
          exists (Tm.tsucc t1')
          apply Step.succ1; assumption

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
  | zero Γ =>
      simp [fv] at hfv
  | prev Γ n htype ih =>
      simp [fv] at hfv
      exact ih hfv
  | succ Γ n htype ih =>
      simp [fv] at hfv
      exact ih hfv

theorem typable_empty_closed (t : Tm) (T : Ty) :
  HasType [] t T → closed t := by
  intro ht
  by_contra hne
  push_neg at hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨T', hi⟩ := free_in_context [] x t T hx ht
  simp [lookup] at hi

theorem context_invariance_v2 (Γ Γ' : Context) (t : Tm) (T : Ty) :
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
  | zero Γ =>
    apply HasType.zero
  | prev Γ n htype ih =>
    apply HasType.prev
    apply ih
    apply hinv
  | succ Γ n htype ih =>
    apply HasType.succ
    apply ih
    apply hinv
