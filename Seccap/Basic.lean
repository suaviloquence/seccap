import Mathlib.Data.Finsupp.Defs
-- import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finset.Defs

import Seccap.Finmap

structure Var where
    val : String
deriving DecidableEq

inductive CExpr where
| nat (n : Nat)
| unit
| abs (x : Var) (e : CExpr)
-- val ^^
| var (x : Var)
| app (e1 : CExpr) (e2 : CExpr)
| set (x : Var) (e2 : CExpr)
| comp (e1: CExpr) (e2: CExpr)

inductive CVal where
| nat (n : Nat)
| unit
| abs (x : Var) (e : CExpr)

abbrev CVal.expr : CVal → CExpr
| nat n => .nat n
| unit => .unit
| abs x e => .abs x e



def CExpr.fvs : CExpr → Finset Var
| .abs x e => e.fvs \ {x}
| .var x => {x}
| .app e1 e2 | .comp e1 e2 => e1.fvs ∪ e2.fvs
| .set x e => {x} ∪ e.fvs
| _ => {}

abbrev CVal.fvs (v : CVal) := v.expr.fvs

def CExpr.subst (e: CExpr) (y: Var) (z: Var): CExpr := match e with
| .abs x e => .abs x (if x = y then e else e.subst y z)
| .var x => .var (if x = y then z else x)
| .app e1 e2 => .app (e1.subst y z) (e2.subst y z)
| .comp e1 e2 => .comp (e1.subst y z) (e2.subst y z)
| .set x e => .set (if x = y then z else x) (e.subst y z)
| e => e

lemma CExpr.mem_subst_fvs_iff (e : CExpr) x y z (hy : x ≠ y) (hz : x ≠ z):
    x ∈ e.fvs ↔ x ∈ (e.subst y z).fvs := by
    induction e with (simp [subst, fvs]; try tauto)
    | abs x' e ih =>
      intro h; constructor
      · intro h2
        split_ifs
        · assumption
        · exact ih.mp h2
      · intro h2
        split_ifs at h2
        · try assumption
        · exact ih.mpr h2
    | set x' e ih =>
      constructor <;> intro h
      · cases h with
        | inl c => subst c; rw [if_neg hy]; left; rfl
        | inr c => right; exact ih.mp c
      · cases h with
        | inl c =>
          split_ifs at c
          · cases hz c
          · left; exact c
        | inr c => right; exact ih.mpr c
    | var x' =>
      constructor <;> intro h
      · split_ifs with c
        · subst c; cases hy h
        · exact h
      · split_ifs at h
        · cases hz h
        · exact h


lemma CExpr.mem_fvs_subst (e: CExpr) x y z (hy: x ≠ y) :
    x ∈ e.fvs → x ∈ (e.subst y z).fvs := by
    induction e with (simp [subst, fvs]; try tauto)
    | abs x' e ih =>
      intro h h2
      constructor
      · split_ifs
        · assumption
        · exact ih h
      · exact h2
    | set x' e ih =>
      intro h
      cases h with
      | inl c => subst c; rw [if_neg hy]; left; rfl
      | inr c => right; exact ih c
    | var x' =>
      intro h
      split_ifs with c
      · subst c; cases hy h
      · exact h


lemma CExpr.z_mem_subst_fvs (e: CExpr) (y z : Var) (h: z ∉ e.fvs):
      z ∈ (e.subst y z).fvs → y ∈ e.fvs := by
    induction e with (simp [fvs] at h;  simp [subst, fvs, h]; try tauto)
    | abs x e ih =>
      split_ifs with H
      · subst H
        intro a b
        cases b (h a)
      · intro a b
        constructor
        · apply ih
          intro contra
          exact b (h contra)
          exact a
        · exact Ne.symm H
lemma CExpr.y_mem_subst_fvs (e: CExpr) y z :
    y ∈ (e.subst y z).fvs → y = z := by
    induction e with simp [subst, fvs]
    | abs x e ih =>
      split_ifs with h
      · subst h
        intro a b
        cases b rfl
      · intro a b
        exact ih a
    | var x =>
      split_ifs with h
      · tauto
      · intro c
        cases h c.symm
    | app e1 e2 ih1 ih2 =>
      intro c
      exact Or.elim c ih1 ih2
    | set x e ih =>
      split_ifs with h
      · intro c
        cases c with
        | inl c => exact c
        | inr c => exact ih c
      · intro c
        cases c with
        | inl c => cases h c.symm
        | inr c => exact ih c
    | comp e1 e2 ih1 ih2 =>
      intro c
      exact Or.elim c ih1 ih2



structure CapsuleStore where
    f : Finmap Var CVal
    h : ∀ x, (h': x ∈ f.support) → ((f x).get ((f.mem_support_is_some x).mp h')).fvs ⊆ f.support

-- @[simp]
abbrev CapsuleStore.dom (μ : CapsuleStore) := μ.f.support

abbrev CapsuleStore.get (μ : CapsuleStore) x (h: x ∈ μ.dom) := (μ.f x).get ((μ.f.mem_support_is_some x).mp h)

abbrev CapsuleStore.insert (μ : CapsuleStore) y (v: CVal) (h : v.fvs ⊆ μ.dom ∪ {y}) : CapsuleStore :=
    ⟨ μ.f.insert y v, (by
      intro x v'
      simp [Finmap.insert]
      split_ifs with H
      · simp at h; simpa
      · intro fv h'
        apply Finset.mem_insert_of_mem
        apply μ.h x
        exact h'
        simp [Finmap.insert, H] at v'
        simpa
    ) ⟩



lemma CapsuleStore.get_closed (μ: CapsuleStore) (x : Var) (h : x ∈ μ.dom) :
    (μ.get x h).fvs ⊆ μ.dom := by
    simp [get]
    exact μ.h x h

structure Capsule where
    e : CExpr
    μ : CapsuleStore
    h : e.fvs ⊆ μ.dom


inductive CExpr.Step : Capsule → Capsule → Prop where
| var x μ h: Step
    ⟨ .var x, μ, h ⟩
    (have h': x ∈ μ.dom := by simp [CExpr.fvs] at h; simpa
    ⟨ (μ.get x h').expr, μ, μ.h x h' ⟩)
| app_l' e1 e2 μ h h1 e1' μ' h1' (hμ: μ.dom ⊆ μ'.dom):
    Step ⟨ e1, μ, h1 ⟩ ⟨ e1', μ', h1' ⟩ →
    Step ⟨ .app e1 e2, μ, h ⟩
         ⟨ .app e1' e2, μ', (by
            simp [fvs]
            apply Finset.union_subset
            · assumption
            · apply Finset.Subset.trans (s₂ := μ.dom)
              · simp [fvs] at h
                apply Finset.union_subset_right h
              · assumption
         ) ⟩
| app_r' (v: CVal) e2 μ h h2 e2' μ' h2' (hμ: μ.dom ⊆ μ'.dom) :
    Step ⟨ e2, μ, h2 ⟩ ⟨ e2', μ', h2' ⟩ →
    Step ⟨ .app v.expr e2, μ, h ⟩ ⟨ .app v.expr e2', μ', (by
        simp [fvs]
        apply Finset.union_subset
        · apply Finset.Subset.trans (s₂ := μ.dom)
          · simp [fvs] at h
            apply Finset.union_subset_left h
          · assumption
        · assumption
    )⟩
| app_abs x e (v: CVal) μ h y (hy: y ∉ μ.dom) :
    Step ⟨ .app (.abs x e) v.expr, μ, h ⟩
         ⟨ e.subst x y, μ.insert y v (by
            simp [fvs] at h
            apply Finset.Subset.trans (s₂ := μ.dom)
            · apply Finset.union_subset_right h
            · apply Finset.subset_union_left
         ), (by
             simp [CapsuleStore.insert, Finmap.insert]
             simp [fvs] at h
             intro z hz
             by_cases hx : x = z
             · subst hx
               have : x = y := by
                 apply CExpr.y_mem_subst_fvs
                 exact hz
               subst this
               apply Finset.mem_insert_self
             · by_cases hyz : y = z
               · subst hyz
                 apply Finset.mem_insert_self
               · apply Finset.mem_insert_of_mem
                 apply Finset.mem_of_subset (s₁ := e.fvs \ {x})
                 · exact Finset.union_subset_left h
                 · simp; constructor
                   · rw [mem_subst_fvs_iff]
                     · exact hz
                     · exact Ne.symm hx
                     · exact Ne.symm hyz
                   · exact Ne.symm hx
         ) ⟩
| set' x e μ h h1 e' μ' h' (hμ: μ.dom ⊆ μ'.dom):
    Step ⟨ e, μ, h ⟩ ⟨ e', μ', h' ⟩ →
    Step ⟨ .set x e, μ, h1 ⟩ ⟨ .set x e', μ', (by
        simp [fvs]
        apply Finset.insert_subset
        · simp [fvs] at h1
          apply Finset.mem_of_subset
          · exact hμ
          · apply Finset.mem_of_subset
            · exact h1
            · apply Finset.mem_insert_self
        · exact h'
    )⟩
| setv x (v: CVal) μ h :
    Step ⟨ .set x v.expr, μ, h ⟩ ⟨ .unit, μ.insert x v (by
      simp [fvs] at h
      apply Finset.Subset.trans (s₂ := μ.dom)
      · apply Finset.Subset.trans (s₂ := insert x v.fvs)
        · apply Finset.subset_insert
        · exact h
      · apply Finset.subset_union_left

    ), by simp [fvs] ⟩
| comp_l' e1 e2 μ h h1 e1' μ' h1' (hμ : μ.dom ⊆ μ'.dom) :
    Step ⟨ e1, μ, h1 ⟩ ⟨ e1', μ', h1' ⟩ →
    Step ⟨ .comp e1 e2, μ, h ⟩ ⟨ .comp e1' e2, μ', (by
        simp [fvs]
        apply Finset.union_subset
        · assumption
        · apply Finset.Subset.trans (s₂ := μ.dom)
          · simp [fvs] at h
            apply Finset.union_subset_right h
          · assumption
    )⟩
| comp e2 μ h :
  Step ⟨ .comp .unit e2, μ, h ⟩ ⟨ e2, μ, (by simp [fvs] at h; assumption )⟩


lemma CExpr.Step.store_subset (c1 c2) :
    Step c1 c2 → c1.μ.dom ⊆ c2.μ.dom := by
    intro hs
    induction hs with (try simp [Finmap.insert, CapsuleStore.dom]; try assumption)
