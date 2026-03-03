import Seccap.Basic
import Seccap.Finmap

inductive CExpr.DeBruijn where
| unit
| nat (n: ℕ)
| bvar (n: ℕ)
| fvar (x: Var)
| abs (e: DeBruijn)
| app (e₁ e₂ : DeBruijn)
| comp (e₁ e₂ : DeBruijn)
| setb (n : ℕ) (e : DeBruijn)
| setf (x: Var) (e: DeBruijn)

namespace CExpr.DeBruijn
def fvs : DeBruijn → Finset Var
| fvar x => {x}
| abs e => e.fvs
| app e₁ e₂ | comp e₁ e₂ => e₁.fvs ∪ e₂.fvs
| setf x e => {x} ∪ e.fvs
| _ => ∅

def fromExpr (e: CExpr) : DeBruijn :=
  helper 0 0 (by simp) e
  where helper (Γ: Finmap Var ℕ) (d : ℕ) (hΓ : ∀ x, (h : x ∈ Γ.support) → Γ.get x h < d): CExpr → DeBruijn
  | .unit => .unit
  | .nat n => .nat n
  | .var x => match Γ x with
    | some n => .bvar n
    | none => .fvar x
  | .abs x e => helper (Finmap.insert (Finsupp.mk
    Γ.support
    (Γ · |>.map (· + 1))
    (by
      intro a
      rw [Finmap.mem_support_is_some]
      constructor
      · intro h
        simp
        apply Option.isSome_iff_exists.mp at h
        have ⟨a, ha⟩ := h
        rw [ha]
        simp
      · intro h
        simp [OfNat.ofNat, Zero.zero] at h
        exact Option.isSome_iff_ne_none.mpr h
    )
  ) x 0) (d + 1) (by
    simp
    intro x' h
    simp [Finmap.insert, Finmap.get]
    cases h with
    | inl h =>
      subst h
      simp
    | inr h =>
      split_ifs
      · simp
      · simp
        apply hΓ
        exact Finsupp.mem_support_iff.mpr h
  ) e
  | .set x e =>
    let e' := helper Γ d hΓ e
    match Γ x with
    | some n => .setb n e'
    | none => .setf x e'
  | .app e₁ e₂ => .app (helper Γ d hΓ e₁) (helper Γ d hΓ e₂)
  | .comp e₁ e₂ => .comp (helper Γ d hΓ e₁) (helper Γ d hΓ e₂)
end DeBruijn
