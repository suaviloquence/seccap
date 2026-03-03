import Mathlib.Order.Lattice
import Seccap.Basic

inductive BType where
| unit
| nat

inductive SType L [SemilatticeSup L] where
| base (b : BType) (l: L)
| arrow (t1 t2 : SType L) (pc : L)

inductive SExpr L [SemilatticeSup L] where
| unit
| nat (n: ℕ)
| abs (x: Var) (e: SExpr L)
--- val
| var (x: Var) (l: L)
| app (e₁ e₂ : SExpr L)
| set (x: Var) (e: SExpr L) (l: L)
| comp (e₁ e₂ : SExpr L)

variable {L} [SemilatticeSup L] (e: SExpr L)

def SExpr.cexpr : SExpr L → CExpr
| unit => .unit
| nat n => .nat n
| abs x e => .abs x e.cexpr
| var x _ => .var x
| app e₁ e₂ => .app e₁.cexpr e₂.cexpr
| set x e _ => .set x e.cexpr
| comp e₁ e₂ => .comp e₁.cexpr e₂.cexpr

abbrev SExpr.fvs := e.cexpr.fvs
abbrev SExpr.bvs := e.cexpr.bvs
