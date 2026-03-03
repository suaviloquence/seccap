import Std.Data.ExtTreeMap.Basic
import Std.Data.ExtTreeMap.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Defs

variable {𝔸 : Type} [DecidableEq 𝔸]

inductive Perm 𝔸 where
| id
| prod (π: Perm 𝔸) (a b : 𝔸) (h: a ≠ b)


def transpose (a b : 𝔸) : 𝔸 → 𝔸  :=
  fun x => if x = a then b else if x = b then a else x

lemma transpose_involutive (a b: 𝔸): Function.Involutive (transpose a b) := by
  intro x
  simp [transpose]
  aesop

@[simp]
lemma transpose_a (a b : 𝔸): (transpose a b) a = b := by simp [transpose]

@[simp]
lemma transpose_b (a b : 𝔸): (transpose a b) b = a := by simp [transpose]

def Perm.toEquiv : Perm 𝔸 → Equiv.Perm 𝔸
| id => {
    toFun := _root_.id
    invFun := _root_.id
  }
| prod π a b h => {
    toFun := π.toEquiv ∘ transpose a b
    invFun := transpose a b ∘ π.toEquiv.symm
    left_inv := by
      intro x
      simp
      apply transpose_involutive
    right_inv := by
      intro x
      simp
      rw [transpose_involutive]
      simp
  }

@[ext]
axiom perm_ext (π₁ π₂ : Perm 𝔸):
  π₁.toEquiv = π₂.toEquiv → π₁ = π₂

instance : EquivLike (Perm 𝔸) 𝔸 𝔸 where
  coe := (·.toEquiv)
  inv := (·.toEquiv.symm)
  left_inv := (·.toEquiv.left_inv)
  right_inv := (·.toEquiv.right_inv)
  coe_injective' := by
    intro x y ha hb
    ext a
    rw [ha]




@[simp]
lemma Perm.coe_eq (π: Perm 𝔸) (a: 𝔸) :
  π a = π.toEquiv.toFun a := rfl


def Perm.vars : Perm 𝔸 → Finset 𝔸
| id => ∅
| prod π a b _ => π.vars ∪ {a, b}

def Perm.support (π: Perm 𝔸) : Finset 𝔸 :=
  {x ∈ π.vars | π x ≠ x}

lemma Perm.support_iff (π : Perm 𝔸) :
  ∀ x, x ∈ π.support ↔ π x ≠ x := by
  intro x
  constructor
  · simp [support]
  · intro hx
    induction π generalizing x with
    | id => absurd hx; rfl
    | prod π a b h ih =>
      simp [] at hx
      by_cases ha: x = a
      · subst ha
        simp [toEquiv, transpose] at hx
        simp [support, toEquiv, vars, transpose]
        exact hx
      · by_cases hb: x = b
        · subst hb
          simp [toEquiv] at hx
          simp [support, vars, toEquiv, hx]
        · simp [support, vars, toEquiv, ha, hb, transpose]
          simp [toEquiv, transpose, ha, hb] at hx
          constructor
          · specialize ih x hx
            simp [support] at ih
            exact ih.left
          · exact hx

def Perm.difference_set (π₁ π₂ : Perm 𝔸) :=
  {a ∈ π₁.support ∪ π₂.support | π₁ a ≠ π₂ a}

infix:80 "∆"  => Perm.difference_set

lemma Perm.difference_set_iff (π₁ π₂ : Perm 𝔸):
  ∀ a, a ∈ π₁ ∆ π₂ ↔ π₁ a ≠ π₂ a := by
  intro a
  simp [difference_set]
  intro h
  by_cases h': π₁ a = a
  · right
    rw [support_iff]
    intro c
    apply h
    simp at h'
    simp at c
    rw [h', c]
  · left
    rw [support_iff]
    exact h'


lemma Perm.difference_set_refl (π : Perm 𝔸) : π ∆ π = ∅ :=
  by simp [difference_set]

lemma Perm.difference_set_symm (π₁ π₂ : Perm 𝔸) :
  π₁ ∆ π₂ = π₂ ∆ π₁ := by
  ext a
  simp [difference_set_iff]
  tauto

theorem Perm.difference_set_triangle (π₁ π₂ π₃ : Perm 𝔸) :
    π₁ ∆ π₃ ⊆ π₁ ∆ π₂ ∪ π₂ ∆ π₃ := by
  intro a ha
  rw [Perm.difference_set_iff] at ha
  simp [Finset.mem_union, Perm.difference_set_iff, Perm.difference_set_iff]
  by_cases h: (π₁ a = π₂ a)
  · right; exact h ▸ ha
  · left; exact h


def Perm.comp (π₁ : Perm 𝔸) : Perm 𝔸 → Perm 𝔸
| id => π₁
| prod π₂ a b h => (π₁.comp π₂).prod a b h

infix:70 " ∘ₚ " => Perm.comp


omit [DecidableEq 𝔸] in
@[simp]
lemma Perm.id_comp (π : Perm 𝔸) : id ∘ₚ π = π := by
  induction π with
  | id => simp [comp]
  | prod π a b h ih => simp [comp, ih]

lemma Perm.comp_coe (π₁ π₂ : Perm 𝔸): (π₁ ∘ₚ π₂).toEquiv = π₁.toEquiv ∘ π₂.toEquiv := by
  induction π₂ generalizing π₁ with
  | id => simp [comp, toEquiv]
  | prod π a b h ih =>
    simp [comp, toEquiv, ih, Function.comp_assoc]

lemma Perm.comp_assoc (π₁ π₂ π₃ : Perm 𝔸) :
  (π₁ ∘ₚ π₂) ∘ₚ π₃ = π₁ ∘ₚ (π₂ ∘ₚ π₃) := by
  ext x
  simp [comp_coe]

def Perm.inv : Perm 𝔸 → Perm 𝔸
| id => id
| prod π a b h => (id.prod a b h) ∘ₚ π.inv

@[simp]
lemma Perm.inv_toEquiv (π : Perm 𝔸):
  π.inv.toEquiv = π.toEquiv.symm := by
  ext x
  induction π with simp [inv, toEquiv, comp_coe, *]

variable {𝔸 𝕏 C: Type} [DecidableEq 𝔸]
inductive Term 𝔸 𝕏 C where
| atom (a: 𝔸)
| unknown (π: Perm 𝔸) (X: 𝕏)
| abs (a: 𝔸) (t: Term 𝔸 𝕏 C)
| app (t₁ t₂: Term 𝔸 𝕏 C)
| const (c: C)

namespace Term

abbrev unknown' (X: 𝕏) : Term 𝔸 𝕏 C :=
  unknown .id X

def atoms : Term 𝔸 𝕏 C → Finset 𝔸
| atom a => {a}
| unknown π _ => π.support
| abs a t => {a} ∪ t.atoms
| app t₁ t₂ => t₁.atoms ∪ t₂.atoms
| const _ => ∅

def perm_action (π: Perm 𝔸) : Term 𝔸 𝕏 C → Term 𝔸 𝕏 C
| atom a => atom (π a)
| unknown π' X => unknown (π ∘ₚ π') X
| abs a t =>  abs (π a) (t.perm_action π)
| app t₁ t₂ => app (t₁.perm_action π) (t₂.perm_action π)
| const c => const c

infix:80 " · " => perm_action

def subst (σ : 𝕏 → Term 𝔸 𝕏 C) : Term 𝔸 𝕏 C → Term 𝔸 𝕏 C
| atom a => atom a
| unknown π X => π · (σ X)
| abs a t => abs a (t.subst σ)
| app t₁ t₂ => app (t₁.subst σ) (t₂.subst σ)
| const c => const c

abbrev FreshnessCtx 𝔸 𝕏 := Finset (𝔸 × 𝕏)

inductive Fresh (Δ : FreshnessCtx 𝔸 𝕏): 𝔸 → Term 𝔸 𝕏 C → Prop where
| F_hyp a X : (a, X) ∈ Δ → Fresh Δ a (unknown' X)
| F_atom (a b : 𝔸) (h: a ≠ b): Fresh Δ a (atom b)
| F_unknown a π X : Fresh Δ (π.toEquiv.symm a) (unknown' X) → Fresh Δ a (unknown π X)
| F_absa a t : Fresh Δ a (abs a t)
| F_absb a b t (h: a ≠ b) : Fresh Δ a t → Fresh Δ a (abs b t)
| F_app a t₁ t₂ : Fresh Δ a t₁ → Fresh Δ a t₂ → Fresh Δ a (app t₁ t₂)
| F_const a c : Fresh Δ a (const c)

notation:50 Δ:50 " ⊢ " a:50 " # " t:50 => Term.Fresh Δ a t

namespace Fresh

lemma weakening Δ Γ a (t: Term 𝔸 𝕏 C) : Δ ⊢ a#t → Δ ⊆ Γ → Γ ⊢ a#t := by
  intro hf hΔ
  induction hf with constructor <;> try assumption
  | F_hyp a X h => exact hΔ h

end Fresh


abbrev Theory := Finset (FreshnessCtx 𝔸 𝕏 × Term 𝔸 𝕏 C × Term 𝔸 𝕏 C)

inductive NominalEq (T: Theory) (Δ: FreshnessCtx 𝔸 𝕏) : Term 𝔸 𝕏 C → Term 𝔸 𝕏 C → Prop where
| N_refl t : NominalEq T Δ t t
| N_symm t u : NominalEq T Δ t u → NominalEq T Δ u t
| N_trans t u v : NominalEq T Δ t u → NominalEq T Δ u v → NominalEq T Δ t v
| N_perm a b t (h: a ≠ b) : (Δ ⊢ a#t) → (Δ ⊢ b#t) → NominalEq T Δ ((.prod .id a b h)·t) t
| N_cngAbs a t u : NominalEq T Δ t u → NominalEq T Δ (abs a t) (abs a u)
| N_cngApp t₁ t₂ u₁ u₂ : NominalEq T Δ t₁ u₁ → NominalEq T Δ t₂ u₂ → NominalEq T Δ (app t₁ t₂) (app u₁ u₂)
| N_ax Γ t u π σ : (Γ, t, u) ∈ T → ∀ p ∈ Γ, (Δ ⊢ p.fst # (unknown' p.snd).subst σ) →
  NominalEq T Δ (π ·(t.subst σ)) (π ·(u.subst σ))

namespace NominalEq

lemma equiv {T: @Theory 𝔸 𝕏 C} {Δ}: Equivalence (Term.NominalEq T Δ) where
  refl := N_refl
  symm := by apply N_symm
  trans := by apply N_trans

end NominalEq


def ground : Term 𝔸 𝕏 C → Bool
| atom _ | const _ => true
| unknown _ _ => false
| abs _ t => t.ground
| app t₁ t₂ => t₁.ground ∧ t₂.ground

abbrev CoreEq := @NominalEq 𝔸 𝕏 C _ ∅

-- inductive Term.CoreEq' (Δ : FreshnessCtx 𝔸 𝕏) : Term 𝔸 𝕏 C → Term 𝔸 𝕏 C → Prop where
-- | C_atom a : CoreEq' Δ (atom a) (atom a)
-- | C_unknown π₁ π₂ X : (∀ a ∈ π₁∆π₂, Term.Fresh (C := C) Δ a (unknown' X)) →
--   CoreEq' Δ (unknown π₁ X) (unknown π₂ X)
-- | C_absa a t u : CoreEq' Δ t u → CoreEq' Δ (abs a t) (abs a u)
-- | C_absb a b (h: a ≠ b) t u : Δ ⊢ b#t → CoreEq' Δ ((.prod .id a b h)·t) u →
--   CoreEq' Δ (abs a t) (abs b u)
-- | C_app t₁ t₂ u₁ u₂ : CoreEq' Δ t₁ u₁ → CoreEq' Δ t₂ u₂ →
--   CoreEq' Δ (app t₁ t₂) (app u₁ u₂)
-- | C_const c : CoreEq' Δ (const c) (const c)


lemma ground_notin_atoms (t: Term 𝔸 𝕏 C) a (hg: t.ground):
  a ∉ t.atoms → ∅ ⊢ a#t := by
  intro h
  induction t with simp [atoms] at h
  | atom b => apply Fresh.F_atom; assumption
  | unknown π x => simp [ground] at hg
  | abs x t ih =>
    simp [ground] at hg
    apply Fresh.F_absb
    exact h.left
    exact ih hg h.right
  | app t₁ t₂ ih₁ ih₂ =>
    simp [ground] at hg
    apply Fresh.F_app
    apply ih₁
    exact hg.left
    exact h.left
    apply ih₂
    exact hg.right
    exact h.right
  | const => apply Fresh.F_const

lemma ex_fresh' [Infinite 𝔸] (t: Term 𝔸 𝕏 C) :
  ∃ a, a ∉ t.atoms := Infinite.exists_notMem_finset t.atoms

lemma ex_fresh [Infinite 𝔸] (t: Term 𝔸 𝕏 C) (hg: t.ground):
  ∃ a, ∅ ⊢ a#t := by
  obtain ⟨a, ha⟩: ∃ a, a ∉ t.atoms := Infinite.exists_notMem_finset t.atoms
  use a
  apply ground_notin_atoms <;> assumption


lemma perm_action_ground (t: Term 𝔸 𝕏 C) π :
  (π·t).ground = t.ground := by
  induction t with simp [Term.perm_action, ground]
  | abs a t ih => exact ih
  | app t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

inductive GroundDeBruijn (𝔸 C) where
| bvar (n: ℕ)
| fvar (a: 𝔸)
| const (c: C)
| abs (t: GroundDeBruijn 𝔸 C)
| app (t₁ t₂ : GroundDeBruijn 𝔸 C)

namespace GroundDeBruijn
-- permute f vars
def perm_action (π : Perm 𝔸) : GroundDeBruijn 𝔸 C → GroundDeBruijn 𝔸 C
| fvar a => fvar (π a)
| abs t => abs (t.perm_action π)
| app t₁ t₂ => app (t₁.perm_action π) (t₂.perm_action π)
| t => t
end GroundDeBruijn

def debruijnify (t: Term 𝔸 𝕏 C) (ht: t.ground) : GroundDeBruijn 𝔸 C :=
  go {} t ht
  where go (l: List 𝔸) t (ht: t.ground) := match t with
  | const c => .const c
  | atom a => match l.idxOf? a with
    | some n => .bvar n
    | none => .fvar a
  | unknown .. => by simp [ground] at ht
  | abs a t => .abs <| go (a :: l) t (by simp [ground] at ht; exact ht)
  | app t₁ t₂ =>
    .app (go l t₁ (by simp [ground] at ht; exact ht.left))  (go l t₂ (by simp [ground] at ht; exact ht.right))

abbrev swap (t: Term 𝔸 𝕏 C) a b (h: a ≠ b):=
  (Perm.id.prod a b h)·t

lemma swap_fresh (t: Term 𝔸 𝕏 C) a b (h: a ≠ b) Δ (hb: Δ ⊢ b#t) (ht: t.ground):
  Δ ⊢ a#(t.swap a b h) := by
  induction t with
  | atom x =>
    cases hb
    expose_names
    apply Fresh.F_atom
    simp [Perm.toEquiv]
    intro c
    simp [transpose, h_1.symm] at c
    split_ifs at c with hc
    · subst hc; contradiction
    · cases hc c.symm
  -- todo
  | unknown π x => simp [ground] at ht
  | const c => simp [perm_action]; constructor
  | app t₁ t₂ ih₁ ih₂ =>
    cases hb
    expose_names
    simp [ground] at ht
    constructor
    apply ih₁
    exact h_1
    exact ht.left
    apply ih₂
    exact h_2
    exact ht.right
  | abs x t ih =>
    simp [ground] at ht
    cases hb with
    | F_absa =>
      simp [perm_action, Perm.toEquiv]
      apply Fresh.F_absa
    | F_absb _ _ _ hb hf =>
      apply Fresh.F_absb
      simp [Perm.toEquiv, transpose, hb.symm]
      split_ifs with hx
      · subst hx; assumption
      · intro c; cases hx c.symm
      apply ih <;> assumption

lemma perm_debruijn
  (t: Term 𝔸 𝕏 C) (ht: t.ground) l π:
    debruijnify.go (l.map (π.inv)) t ht = (debruijnify.go l (π·t) (by simp [perm_action_ground, ht])).perm_action π.inv
  := by
  induction t generalizing l π with
  | atom x =>
    simp [debruijnify.go, perm_action]
    induction l with
    | nil => simp [GroundDeBruijn.perm_action, Perm.inv_toEquiv]
    | cons a l ih =>
      cases h: (a == π x) with
      | true =>
        simp at h
        simp [List.idxOf?_cons, h, GroundDeBruijn.perm_action]
      | false =>
        simp at h
        simp [List.idxOf?_cons, h]
        have : (π.inv a ≠ x) := by
          intro c
          rw [← c] at h
          simp at h
        simp at this
        simp [this]
        simp at ih
        split at ih <;> split at ih <;> simp [GroundDeBruijn.perm_action] at ih
        · expose_names
          simp [heq, heq_1, ih, GroundDeBruijn.perm_action]
        · expose_names
          simp [heq, heq_1, GroundDeBruijn.perm_action]
  | unknown => simp [ground] at ht
  | abs x t ih =>
    simp [debruijnify.go, GroundDeBruijn.perm_action, perm_action]
    simp [ground] at ht
    rw [← ih]
    simp
    exact ht
  | app t₁ t₂ ih₁ ih₂ =>
    simp [ground] at ht
    obtain ⟨ht₁, ht₂⟩ := ht
    simp [debruijnify.go, GroundDeBruijn.perm_action, perm_action]
    constructor
    · simp [ih₁]
    · simp [ih₂]
  | const c => simp [perm_action, debruijnify.go, GroundDeBruijn.perm_action]


-- Proof that if CoreEq a b, we can find a renaming function to make a = b.
namespace CoreEq
lemma coreeq_ground {t₁ t₂ : Term 𝔸 𝕏 C} {Δ} (heq: CoreEq Δ t₁ t₂):
   t₁.ground = t₂.ground := by
  induction heq with
  | N_refl => rfl
  | N_symm => symm; assumption
  | N_trans t₁ t₂ t₃ h₁₂ h₂₃ ih₁ ih₂ => simp [ih₁, ih₂]
  | N_perm a b t h ha hb => apply Term.perm_action_ground
  | N_cngAbs a t₁ t₂ heq ih => simp [ground, ih]
  | N_cngApp t₁ t₂ u₁ u₂ heq₁ heq₂ ih₁ ih₂ => simp [ground, ih₁, ih₂]
  | N_ax _ _ _ _ _ hp => cases hp


theorem chain_de_bruijn [Infinite 𝔸] (t₁ t₂: Term 𝔸 𝕏 C) (hg₁: t₁.ground)
  (ht: Term.CoreEq ∅ t₁ t₂):
  debruijnify t₁ (hg₁) = debruijnify t₂ (by rw [← coreeq_ground ht]; exact hg₁) := by
  sorry


end CoreEq
end Term
























-- structure Permutation where
--   map : 𝔸 → 𝔸
--   map_bij : Function.Bijective map
--   support: Finset 𝔸
--   map_support_iff : ∀ a, a ∈ support ↔ map a ≠ a

-- def Permutation.transposition  [DecidableEq 𝔸] (a b : 𝔸) (h: a ≠ b) : Permutation 𝔸 :=
--   {
--     map := fun x => if x = a then b else if x = b then a else x
--     map_bij := by
--       constructor
--       · unfold Function.Injective
--         aesop
--       · intro x
--         by_cases x = b
--         · use a; aesop
--         · by_cases x = a
--           · use b; aesop
--           · use x; aesop
--     support := {a, b}
--     map_support_iff := by aesop
--   }

-- lemma Permutation.map_inj (π ρ : Permutation 𝔸):
--   π.map = ρ.map → π = ρ := by
--   intro h
--   obtain ⟨f₁, hi₁, sup₁, hs₁⟩ := π
--   obtain ⟨f₂, hi₂, sup₂, hs₂⟩ := ρ
--   simp
--   simp at h
--   constructor; try assumption
--   ext x
--   constructor
--   · intro h₁
--     apply (hs₂ x).mpr
--     rw [← h]
--     apply (hs₁ x).mp
--     exact h₁
--   · intro h₂
--     apply (hs₁ x).mpr
--     rw [h]
--     apply (hs₂ x).mp
--     exact h₂


-- instance : FunLike (Permutation 𝔸) 𝔸 𝔸 where
--   coe := (·.map)
--   coe_injective' := by intro a b; simp; apply Permutation.map_inj

-- variable (π : Permutation 𝔸)
-- lemma Permutation.closed x : x ∈ π.support ↔ π x ∈ π.support := by
--   constructor
--   · intro h
--     by_contra
--     have := (π.map_support_iff (π x)).mpr
--     contrapose this





-- def Permutation.inverse [DecidableEq 𝔸] (π : Permutation 𝔸): Permutation 𝔸 :=
--   {
--     support := π.support
--     map := fun x => if hx: x ∈ π.support then π.support.choose (fun a ↦ π a = x) (by

--     )  else x
--   }

-- variable (𝔸 𝕏: Type) [Infinite 𝔸]  [Infinite 𝕏] [DecidableEq 𝔸]

-- inductive Term where
-- | atom (a : 𝔸)
-- | unknown (π : Permutation 𝔸) (X : 𝕏)
-- |
