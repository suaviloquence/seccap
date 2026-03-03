import Seccap.Basic
import Seccap.Finmap
import Seccap.AlphaEquiv

inductive CType where
| unit
| nat
| arrow (t1 t2 : CType)


inductive CExpr.Type : Finmap Var CType → CExpr → CType → Prop where
| unit Γ : CExpr.Type Γ .unit .unit
| nat Γ n : CExpr.Type Γ (.nat n) .nat
| var Γ x τ (h : Γ x = some τ) : CExpr.Type Γ (.var x) τ
| abs Γ x e τ₁ τ₂:
  CExpr.Type (Γ.insert x τ₁) e τ₂ →
  CExpr.Type Γ (.abs x e) (.arrow τ₁ τ₂)
| app Γ e₁ e₂ τ₁ τ₂ : CExpr.Type Γ e₁ (.arrow τ₁ τ₂) →
  CExpr.Type Γ e₂ τ₂ →
  CExpr.Type Γ (.app e₁ e₂) τ₁
| set Γ x e τ (h: Γ x = some τ ): CExpr.Type Γ e τ →
  CExpr.Type Γ (.set x e) .unit
| comp Γ e₁ e₂ τ₂ : CExpr.Type Γ e₁ .unit →
  CExpr.Type Γ e₂ τ₂ →
  CExpr.Type Γ (.comp e₁ e₂) τ₂

notation:40 Γ " ⊢ " e " : " τ => CExpr.Type Γ e τ

lemma CExpr.Type.unit_canonical Γ (v: CVal) :
  (Γ ⊢ v.expr : .unit) → v = .unit := by
  intro ht
  cases v with cases ht <;> rfl

lemma CExpr.Type.nat_canonical Γ (v: CVal) :
  (Γ ⊢ v.expr : .nat) → ∃ n, v = .nat n := by
  intro ht
  cases v with cases ht
  | nat n => use n

lemma CExpr.Type.arrow_canonical Γ (v: CVal) τ₁ τ₂:
  (Γ ⊢ v.expr : .arrow τ₁ τ₂) →
  (∃ x e, v = .abs x e ∧ (Γ.insert x τ₁ ⊢ e : τ₂)) := by
  intro ht
  cases v with cases ht
  | abs x e => use x,e

lemma CExpr.Type.weakening Γ e τ Γ':
  (∀ x ∈ Γ.support, Γ x = Γ' x) →
  (Γ ⊢ e : τ) →
  (Γ' ⊢ e : τ) := by
  intro hΓ hτ
  induction hτ generalizing Γ' with try (constructor; done)
  | var Γ x τ h =>
    constructor
    rw [← hΓ]
    assumption
    apply (Γ.mem_support_is_some x).mpr
    simp [h]
  | abs Γ x e τ₁ τ₂ he ih =>
    constructor
    apply ih
    intro y hy
    simp [Finmap.insert]
    simp [Finmap.insert] at hy
    split_ifs with h
    · rfl
    · apply hΓ
      simp [hy.resolve_left h]
  | app Γ e₁ e₂ τ₁ τ₂ he₁ he₂ ih₁ ih₂ =>
    constructor
    · apply ih₁
      exact hΓ
    · apply ih₂
      exact hΓ
  | set Γ x e τ hτ he ih =>
    constructor
    · rw [← hΓ]
      · exact hτ
      apply (Γ.mem_support_is_some x).mpr
      exact Option.isSome_of_mem hτ
    · apply ih; exact hΓ
  | comp Γ e₁ e₂ τ₂ he₁ he₂ ih₁ ih₂ =>
    constructor
    · apply ih₁
      exact hΓ
    · apply ih₂
      exact hΓ


lemma CExpr.Type.progress Γ c₁ c₂ τ (hΓ: ∀ x, (hμ: x ∈ c₁.μ.dom) → ∃ (hΓ: x ∈ Γ.support),  Γ ⊢ (c₁.μ.get x hμ).expr: Γ.get x hΓ):
  (Γ ⊢ c₁.e : τ) →
  (c₁ ⟶ c₂) →
  ∃ Γ', ((∀ x ∈ Γ.support, Γ x = Γ' x) ∧ Γ' ⊢ c₂.e : τ) := by
  intro ht he
  induction he generalizing τ with
  | var x μ h =>
    cases ht with | var _ _ _ hΓ' =>
    simp
    simp [fvs] at h
    use Γ
    constructor
    · intro x hx
      rfl
    · obtain ⟨a, b⟩ :=  hΓ x (by simp [h])
      simp [Finmap.get, hΓ'] at b
      exact b
  | app_l' e₁ e₂ μ h h₁ e₁' μ' h₁' hμ hs ih =>
    cases ht with | app _ _ _ _ τ₂ ht₁ ht₂ =>
    simp
    simp at ih
    simp at hΓ
    obtain ⟨Γ', ⟨hμΓ, hτ'⟩⟩ := ih (τ.arrow τ₂) hΓ ht₁
    use Γ'
    constructor
    · exact hμΓ
    · apply app (τ₂ := τ₂)
      · exact hτ'
      · refine weakening _ _ _ _ ?_ ht₂
        simp
        exact hμΓ
  | app_r' v e₂ μ h h₂ e₂' μ' h₂' hμ he₂ ih =>
    cases ht with | app _ _ _ _ τ₂ hτ₁ hτ₂ =>
    obtain ⟨Γ', ⟨hμΓ, hτ'⟩⟩ := ih τ₂ hΓ hτ₂
    use Γ'
    constructor
    · exact hμΓ
    · simp
      constructor
      · refine weakening _ _ _ _ ?_ hτ₁
        exact hμΓ
      · exact hτ'
  | app_abs x e v μ h y hy =>
    cases ht with | app _ _ _ _ τ₂ hτ₁ hτ₂ =>
    use (Γ.insert y τ₂)
    constructor
    · intro x hx
      simp [Finmap.insert]
      intro contra
      sorry
  | set' x e μ h h₁ e' μ' h' hμ' he ih =>
    cases ht with







-- lemma CExpr.Type.same_var Γ e τ :
--   (Γ ⊢ e : τ) → ∀
