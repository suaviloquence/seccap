import Seccap.Basic
import Seccap.Finmap

inductive CType where
| unit
| nat
| arrow (t1 t2 : CType)


inductive CExpr.Type : Finmap Var CType → CExpr → CType → Prop where
| unit Γ : CExpr.Type Γ .unit .unit
| nat Γ n : CExpr.Type Γ (.nat n) .nat
| var Γ x τ (h : Γ x = some τ) : CExpr.Type Γ (.var x) τ
| abs Γ x e τ₁ τ₂ :
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
