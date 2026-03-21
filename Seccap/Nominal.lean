import Std.Data.ExtTreeMap.Basic
import Std.Data.ExtTreeMap.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Defs

variable {𝔸 : Type} [DecidableEq 𝔸]

inductive Perm 𝔸 where
| id
| prod (π: Perm 𝔸) (a b : 𝔸) (h: a ≠ b)

abbrev Perm.swap := @Perm.id.prod (𝔸 := 𝔸)

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

instance : CoeFun (Perm 𝔸) (fun _ => 𝔸 → 𝔸) where
  coe π := π.toEquiv

lemma Perm.coe_eq (π: Perm 𝔸) (a: 𝔸) :
  π a = π.toEquiv.toFun a := rfl

@[simp]
lemma Perm.coe_id (a: 𝔸) :
  Perm.id.toEquiv a = a := rfl

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

@[simp]
lemma Perm.notin_supp {π : Perm 𝔸} {a} (ha: a ∉ π.support) : π a = a := by
  have := ha.imp (π.support_iff a).mpr
  simp at this
  simp [this]

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
lemma Perm.comp_id (π : Perm 𝔸) : π ∘ₚ id = π := rfl

omit [DecidableEq 𝔸] in
@[simp]
lemma Perm.id_comp (π : Perm 𝔸) : id ∘ₚ π = π := by
  induction π with
  | id => simp [comp]
  | prod π a b h ih => simp [comp, ih]

omit [DecidableEq 𝔸] in
lemma Perm.comp_prod (π₁ π₂ : Perm 𝔸) a b h :
  (π₁.prod a b h) ∘ₚ π₂ = π₁ ∘ₚ (swap a b h ∘ₚ π₂) := by
  induction π₂ with
  | id => simp [comp]
  | prod π₂ a' b' h' ih =>
    simp [comp, ih]

lemma Perm.comp_coe (π₁ π₂ : Perm 𝔸): (π₁ ∘ₚ π₂).toEquiv = π₁.toEquiv ∘ π₂.toEquiv := by
  induction π₂ generalizing π₁ with
  | id => simp [comp, toEquiv]
  | prod π a b h ih =>
    simp [comp, toEquiv, ih, Function.comp_assoc]

omit [DecidableEq 𝔸] in
lemma Perm.comp_assoc (π₁ π₂ π₃ : Perm 𝔸) :
  (π₁ ∘ₚ π₂) ∘ₚ π₃ = π₁ ∘ₚ (π₂ ∘ₚ π₃) := by
  induction π₂ generalizing π₁ π₃ with
  | id => simp
  | prod π₂ a b h ih =>
    simp [comp]
    rw [comp_prod, ih, ← comp_prod]

def Perm.inv : Perm 𝔸 → Perm 𝔸
| id => id
| prod π a b h => (id.prod a b h) ∘ₚ π.inv

@[simp]
lemma Perm.inv_toEquiv (π : Perm 𝔸):
  π.inv.toEquiv = π.toEquiv.symm := by
  ext x
  induction π with simp [inv, toEquiv, comp_coe, *]

omit [DecidableEq 𝔸] in
@[simp]
lemma Perm.swap_inv (a b : 𝔸) h :
  (swap a b h).inv = swap a b h := rfl

def Perm.ext_eq (π₁ π₂ : Perm 𝔸) := ∀ x, π₁ x = π₂ x

infix:50 " ≅ " => Perm.ext_eq

@[simp]
lemma Perm.swap_a (a b : 𝔸) (h: a ≠ b) : Perm.swap a b h a = b := by simp [toEquiv, transpose]

@[simp]
lemma Perm.swap_b (a b : 𝔸) (h: a ≠ b) : Perm.swap a b h b = a := by simp [toEquiv, transpose]

lemma Perm.swap_symm {a b : 𝔸} {h} :
  (swap a b h) ≅ (swap b a h.symm) := by
  intro x
  simp [toEquiv, transpose]
  split_ifs <;> subst_vars <;> rfl

variable {𝔸 𝕏 C: Type} [DecidableEq 𝔸]
inductive Term 𝔸 𝕏 C where
| atom (a: 𝔸)
| unknown (π: Perm 𝔸) (X: 𝕏)
| abs (a: 𝔸) (t: Term 𝔸 𝕏 C)
| asgn (a: 𝔸) (t: Term 𝔸 𝕏 C)
| app (t₁ t₂: Term 𝔸 𝕏 C)
| const (c: C)

namespace Term

abbrev unknown' (X: 𝕏) : Term 𝔸 𝕏 C :=
  unknown .id X

def atoms : Term 𝔸 𝕏 C → Finset 𝔸
| atom a => {a}
| unknown π _ => π.support
| abs a t => {a} ∪ t.atoms
| asgn a t => {a} ∪ t.atoms
| app t₁ t₂ => t₁.atoms ∪ t₂.atoms
| const _ => ∅

def perm_action (π: Perm 𝔸) : Term 𝔸 𝕏 C → Term 𝔸 𝕏 C
| atom a => atom (π a)
| unknown π' X => unknown (π ∘ₚ π') X
| abs a t =>  abs (π a) (t.perm_action π)
| asgn a t =>  asgn (π a) (t.perm_action π)
| app t₁ t₂ => app (t₁.perm_action π) (t₂.perm_action π)
| const c => const c

infix:80 " ⬝ " => perm_action

@[simp]
lemma id_action (t: Term 𝔸 𝕏 C) :
  Perm.id ⬝ t = t := by induction t <;> simp [*, perm_action]

def subst (σ : 𝕏 → Term 𝔸 𝕏 C) : Term 𝔸 𝕏 C → Term 𝔸 𝕏 C
| atom a => atom a
| unknown π X => π ⬝ (σ X)
| abs a t => abs a (t.subst σ)
| asgn a t => asgn a (t.subst σ )
| app t₁ t₂ => app (t₁.subst σ) (t₂.subst σ)
| const c => const c

abbrev FreshnessCtx 𝔸 𝕏 := Finset (𝔸 × 𝕏)

inductive Fresh (Δ : FreshnessCtx 𝔸 𝕏): 𝔸 → Term 𝔸 𝕏 C → Prop where
| F_hyp a X : (a, X) ∈ Δ → Fresh Δ a (unknown' X)
| F_atom (a b : 𝔸) (h: a ≠ b): Fresh Δ a (atom b)
| F_unknown a π X : Fresh Δ (π.toEquiv.symm a) (unknown' X) → Fresh Δ a (unknown π X)
| F_absa a t : Fresh Δ a (abs a t)
| F_absb a b t (h: a ≠ b) : Fresh Δ a t → Fresh Δ a (abs b t)
| F_asgn a b t (h: a ≠ b) : Fresh Δ a t → Fresh Δ a (asgn b t)
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
| N_perm a b t (h: a ≠ b) : (Δ ⊢ a#t) → (Δ ⊢ b#t) → NominalEq T Δ ((.prod .id a b h)⬝t) t
| N_cngAbs a t u : NominalEq T Δ t u → NominalEq T Δ (abs a t) (abs a u)
| N_cngApp t₁ t₂ u₁ u₂ : NominalEq T Δ t₁ u₁ → NominalEq T Δ t₂ u₂ → NominalEq T Δ (app t₁ t₂) (app u₁ u₂)
| N_ax Γ t u π σ : (Γ, t, u) ∈ T → ∀ p ∈ Γ, (Δ ⊢ p.fst # (unknown' p.snd).subst σ) →
  NominalEq T Δ (π ⬝(t.subst σ)) (π ⬝(u.subst σ))

namespace NominalEq

lemma equiv {T: @Theory 𝔸 𝕏 C} {Δ}: Equivalence (Term.NominalEq T Δ) where
  refl := N_refl
  symm := by apply N_symm
  trans := by apply N_trans

end NominalEq


def ground : Term 𝔸 𝕏 C → Bool
| atom _ | const _ => true
| unknown _ _ => false
| abs _ t | asgn _ t => t.ground
| app t₁ t₂ => t₁.ground ∧ t₂.ground

def size : Term 𝔸 𝕏 C → ℕ
| atom _ | unknown _ _ | const _ => 0
| abs _ t | asgn _ t => t.size + 1
| app t₁ t₂ => t₁.size + t₂.size + 1

@[simp]
lemma perm_action_size (t: Term 𝔸 𝕏 C) π : (π⬝t).size = t.size := by
  induction t <;> simp [perm_action, size, *]

abbrev CoreEq := @NominalEq 𝔸 𝕏 C _ ∅

-- inductive Term.CoreEq' (Δ : FreshnessCtx 𝔸 𝕏) : Term 𝔸 𝕏 C → Term 𝔸 𝕏 C → Prop where
-- | C_atom a : CoreEq' Δ (atom a) (atom a)
-- | C_unknown π₁ π₂ X : (∀ a ∈ π₁∆π₂, Term.Fresh (C := C) Δ a (unknown' X)) →
--   CoreEq' Δ (unknown π₁ X) (unknown π₂ X)
-- | C_absa a t u : CoreEq' Δ t u → CoreEq' Δ (abs a t) (abs a u)
-- | C_absb a b (h: a ≠ b) t u : Δ ⊢ b#t → CoreEq' Δ ((.prod .id a b h)⬝t) u →
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
  | asgn x t ih =>
    simp [ground] at hg
    exact Fresh.F_asgn _ _ _ h.left (ih hg h.right)
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
  (π⬝t).ground = t.ground := by
  induction t with simp [Term.perm_action, ground, *]

lemma ground_perm_action_ext {π₁ π₂ : Perm 𝔸} (h: π₁ ≅ π₂) (t: Term 𝔸 𝕏 C) (ht: t.ground):
  π₁⬝t = π₂⬝t := by induction t with simp [perm_action] <;> simp [ground] at ht
  | atom a => exact h a
  | abs a t ih => simp [h a, ih ht]
  | asgn a t ih => simp [h a, ih ht]
  | app t₁ t₂ ih₁ ih₂ => simp [ih₁ ht.left, ih₂ ht.right]


inductive GroundDeBruijn (𝔸 C) where
| bvar (n: ℕ)
| fvar (a: 𝔸)
| const (c: C)
| abs (t: GroundDeBruijn 𝔸 C)
| asgn_b (n : ℕ) (t: GroundDeBruijn 𝔸 C)
| asgn_f (a: 𝔸) (t: GroundDeBruijn 𝔸 C)
| app (t₁ t₂ : GroundDeBruijn 𝔸 C)

namespace GroundDeBruijn
-- permute f vars
def perm_action (π : Perm 𝔸) : GroundDeBruijn 𝔸 C → GroundDeBruijn 𝔸 C
| fvar a => fvar (π a)
| abs t => abs (t.perm_action π)
| asgn_b n t => asgn_b n (t.perm_action π)
| asgn_f a t => asgn_f (π a) (t.perm_action π)
| app t₁ t₂ => app (t₁.perm_action π) (t₂.perm_action π)
| t => t

@[simp]
lemma perm_action_id (t: GroundDeBruijn 𝔸 C) :
  t.perm_action .id = t := by induction t <;> simp [perm_action, *]

@[simp]
lemma perm_action_comp (t: GroundDeBruijn 𝔸 C) π₁ π₂ :
  (t.perm_action π₁).perm_action π₂ = t.perm_action (π₂ ∘ₚ π₁) := by
  induction t with simp [perm_action, *, Perm.comp_coe]

lemma perm_action_ext {π₁ π₂ : Perm 𝔸} (h: π₁ ≅ π₂) (t: GroundDeBruijn 𝔸 C) :
  t.perm_action π₁ = t.perm_action π₂ := by induction t with simp [perm_action, *]
  | fvar a => exact h a
  | asgn_f a => exact h a
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
  | asgn a t => match l.idxOf? a with
    | some n => .asgn_b n (go l t (by simp [ground] at ht; exact ht))
    | none => .asgn_f a (go l t (by simp [ground] at ht; exact ht))
  | app t₁ t₂ =>
    .app (go l t₁ (by simp [ground] at ht; exact ht.left))  (go l t₂ (by simp [ground] at ht; exact ht.right))

abbrev swap (t: Term 𝔸 𝕏 C) a b (h: a ≠ b):=
  (Perm.swap a b h)⬝t

lemma perm_action_prod (t : Term 𝔸 𝕏 C) π a b h :
  (π.prod a b h)⬝t = π⬝(t.swap a b h) := by
  induction t with simp [*, perm_action, Perm.toEquiv]
  | unknown π' X => rw [Perm.comp_prod]


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
  | asgn x t ih =>
    simp [ground] at ht
    cases hb
    expose_names
    specialize ih h_2 ht
    constructor <;> try assumption
    simp [Perm.toEquiv, transpose, Ne.symm h_1]
    split_ifs with hc
    · exact h
    · exact Ne.symm hc
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

lemma perm_debruijn'
  (t: Term 𝔸 𝕏 C) (ht: t.ground) l π:
    debruijnify.go (l.map (π.inv)) t ht = (debruijnify.go l (π⬝t) (by simp [perm_action_ground, ht])).perm_action π.inv
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
  | asgn x t ih =>
    simp [debruijnify.go, perm_action]
    simp [ground] at ht
    induction l with
    | nil =>
      simp [GroundDeBruijn.perm_action]
      specialize ih ht [] π
      simp at ih
      exact ih
    | cons a l l_ih =>
      by_cases h: (a = π x)
      · simp [List.idxOf?_cons, h, GroundDeBruijn.perm_action]
        specialize ih ht ((π x) :: l) π
        simp at ih
        exact ih
      · simp [List.idxOf?_cons, h]
        have : π.inv a ≠ x := by
          intro c
          rw [← c] at h
          simp at h
        simp at this
        simp [this]
        simp at l_ih
        split at l_ih <;> split at l_ih <;> simp [GroundDeBruijn.perm_action] at l_ih
        · expose_names
          simp [heq, heq_1, l_ih, GroundDeBruijn.perm_action]
          specialize ih ht (a :: l) π
          simp at ih
          exact ih
        · split <;> split <;> sorry
  | app t₁ t₂ ih₁ ih₂ =>
    simp [ground] at ht
    obtain ⟨ht₁, ht₂⟩ := ht
    simp [debruijnify.go, GroundDeBruijn.perm_action, perm_action]
    constructor
    · rw [← Perm.inv_toEquiv, ih₁]
    · rw [← Perm.inv_toEquiv, ih₂]
  | const c => simp [perm_action, debruijnify.go, GroundDeBruijn.perm_action]


theorem perm_debruijn
  (t: Term 𝔸 𝕏 C) (ht: t.ground) π:
    debruijnify t ht = (debruijnify (π⬝t) (by simp [perm_action_ground, ht])).perm_action π.inv := by
    unfold debruijnify
    simp
    rw [← List.map_nil]
    apply perm_debruijn'

lemma debruijn'_perm_fresh (t: Term 𝔸 𝕏 C) (ht: t.ground) l π (hf : ∀ a ∈ π.support, a ∈ l):
  debruijnify.go l t ht = (debruijnify.go l t ht).perm_action π := by
  induction t generalizing l with
  | const c => simp [debruijnify.go, GroundDeBruijn.perm_action]
  | unknown => simp [ground] at ht
  | atom a =>
    simp [debruijnify.go]
    split <;> simp [GroundDeBruijn.perm_action]
    expose_names
    specialize hf a
    simp at heq
    have : a ∉ π.support := heq.imp hf
    have := this.imp (π.support_iff a).mpr
    simp at this
    exact this.symm
  | abs a t ih =>
    simp [ground] at ht
    specialize ih ht
    simp [debruijnify.go, GroundDeBruijn.perm_action]
    rw [← ih]
    intro x hx
    right
    exact hf x hx
  | asgn a t ih =>
    simp [ground] at ht
    specialize ih ht l hf
    simp [debruijnify.go]
    split <;> simp [GroundDeBruijn.perm_action]
    · exact ih
    · expose_names
      simp at heq
      refine ⟨?_, ih⟩
      have : a ∉ π.support := heq.imp (hf a)
      exact (π.notin_supp this).symm
  | app t₁ t₂ ih₁ ih₂ =>
    simp [ground] at ht
    specialize ih₁ ht.left
    specialize ih₂ ht.right
    simp [debruijnify.go, GroundDeBruijn.perm_action]
    rw [← ih₁, ← ih₂]
    · tauto
    · assumption
    · assumption

lemma perm_action_swap
  (t: Term 𝔸 𝕏 C)
  (ht: t.ground)
  a b h l
  (hb : ∅ ⊢ b # t)
  (hlb: b ∈ l):
  (debruijnify.go l (t.swap a b h) (by simp [ht, perm_action_ground])).perm_action (Perm.swap a b h)
  =
  debruijnify.go l (t.swap a b h) (by simp [ht, perm_action_ground]) := by
  induction t generalizing l a b with
  | atom x =>
    cases hb
    expose_names
    simp [debruijnify.go, perm_action, Perm.toEquiv, transpose, h_1.symm]
    split <;> expose_names
    · simp [GroundDeBruijn.perm_action]
    · simp at heq
      simp [GroundDeBruijn.perm_action, Perm.toEquiv, transpose, h_1.symm]
      split
      · expose_names
        simp [h_2] at heq
        contradiction
      · rfl
  | unknown => simp [ground] at ht
  | abs x t ih =>
    simp [perm_action, debruijnify.go, Perm.toEquiv, transpose]
    cases hb with
    | F_absa =>
      simp [h.symm, GroundDeBruijn.perm_action]
      simp [ground] at ht
      have := debruijn'_perm_fresh (t.swap a x h) (by simp [perm_action_ground, ht]) (a :: l) (Perm.swap a x h)
      rw [← this]
      intro c
      simp [Perm.support, Perm.vars, Perm.toEquiv]
      rintro ⟨ha|hx⟩ h
      · left; rfl
      · subst_vars; right; exact hlb
    | F_absb _ _ _ hb hf =>
      simp [hb.symm, GroundDeBruijn.perm_action]
      simp [ground] at ht
      apply ih
      exact ht
      exact hf
      simp [hlb]
  | asgn x t ih =>
    cases hb
    expose_names
    simp [ground] at ht
    simp [perm_action, debruijnify.go]
    split <;> expose_names
    · simp [GroundDeBruijn.perm_action]
      apply ih <;> assumption
    · simp [GroundDeBruijn.perm_action]
      simp [Perm.toEquiv, transpose, h_1.symm, h_1]
      constructor
      · intro contra
        simp [Perm.toEquiv, transpose, contra] at heq
        contradiction
      · apply ih <;> assumption
  | app t₁ t₂ ih₁ ih₂ =>
    simp [ground] at ht
    obtain ⟨ht₁, ht₂⟩ := ht
    cases hb
    expose_names
    simp [perm_action, debruijnify.go, GroundDeBruijn.perm_action]
    rw [ih₁, ih₂] <;> try assumption
    tauto
  | const c => simp [debruijnify.go, perm_action, GroundDeBruijn.perm_action]

lemma fresh_swap_debruijn' (t: Term 𝔸 𝕏 C) (ht: t.ground) a b (h: a ≠ b) (ha: ∅ ⊢ a#t) (hb: ∅ ⊢ b#t) l (hla : a ∉ l) (hlb : b ∉ l):
  debruijnify.go l t ht = debruijnify.go l (t.swap a b h) (by simp [perm_action_ground, ht]) := by
  induction t generalizing l with
  | atom x =>
    simp  [debruijnify.go, perm_action]
    cases ha
    cases hb
    expose_names
    simp [Perm.toEquiv, transpose, h_1.symm, h_2.symm]
  | abs x t ih =>
    simp [ground] at ht
    specialize ih ht
    simp [perm_action, debruijnify.go, Perm.toEquiv]
    cases ha with
    | F_absa =>
      cases hb
      contradiction
      expose_names
      simp
      have : (a :: l) = (b :: l).map (Perm.swap a b h).inv := by
        simp [Perm.toEquiv]
        induction l with simp
        | cons l ls ih =>
          simp at hla
          simp at hlb
          simp [transpose, Ne.symm hla.left, Ne.symm hlb.left]
          exact ih hla.right hlb.right
      rw [this]
      have := perm_debruijn' t ht (b :: l) (Perm.swap a b h)
      rw [this]
      have := perm_action_swap t ht a b h (b :: l) h_2 (by simp)
      rw [← this]
      apply congrArg
      exact this
    | F_absb _ _ _ hx ha =>
      cases hb with
      | F_absa =>
          have : (b :: l) = (a :: l).map (Perm.swap a b h).inv := by
            simp [Perm.toEquiv]
            induction l with simp
            | cons l ls ih =>
              simp at hla
              simp at hlb
              simp [transpose, Ne.symm hla.left, Ne.symm hlb.left]
              exact ih hla.right hlb.right
          rw [this]
          have := perm_debruijn' t ht (a :: l) (Perm.swap a b h)
          rw [this]
          have := perm_action_swap t ht b a h.symm (a :: l) ha (by simp)
          simp only [Perm.swap_inv, transpose_b,
            show (Perm.swap a b h)⬝t = (Perm.swap b a h.symm)⬝t from
              ground_perm_action_ext Perm.swap_symm t ht]
          rw [GroundDeBruijn.perm_action_ext Perm.swap_symm]
          exact this
      | F_absb _ _ _ hxb hb =>
        simp [transpose, hx.symm, hxb.symm]
        apply ih ha hb
        simp [hx, hla]
        simp [hxb, hlb]
  | asgn x t ih =>
    simp [ground] at ht
    cases ha
    cases hb
    expose_names
    simp [debruijnify.go, perm_action, Perm.toEquiv, transpose, h_1.symm, h_3.symm]
    split <;> (simp; apply ih) <;> assumption
  | unknown => simp [ground] at ht
  | app t₁ t₂ ih₁ ih₂ =>
    cases ha
    cases hb
    simp [ground] at ht
    obtain ⟨h1, h2⟩ := ht
    simp [debruijnify.go, perm_action]
    rw [ih₁, ih₂] <;> try assumption
    tauto
  | const c => simp [perm_action]

-- lemma fresh_perm_debruijn' (t: Term 𝔸 𝕏 C) (ht: t.ground) π (hf : ∀ a ∈ π.support, ∅ ⊢ a#t) l:
--   debruijnify.go l t ht = debruijnify.go l (π⬝t)  (by simp [perm_action_ground, ht]) := by
--   induction π generalizing t with
--   | id => simp
--   | prod π a b h ih =>
--     simp [perm_action_prod t π a b h]
--     cases ha: (π.prod a b h a == a)
--     cases hb: (π.prod a b h b == b)
--     rw [← ih (ht := by simp [perm_action_ground, ht])]
--     apply fresh_swap_debruijn'
--     apply hf
--     rw [Perm.support_iff]
--     simp at ha
--     simp [ha]
--     apply hf
--     rw [Perm.support_iff]
--     simp at hb
--     simp [hb]
  -- induction t with
  -- | atom a =>
  --   simp [debruijnify.go, perm_action]
  --   cases h: (π a == a)
  --   simp at h
  --   have :=  π.support_iff a |>.mpr h
  --   cases hf a this
  --   contradiction
  --   simp at h
  --   simp [h]
  -- | unknown => simp [ground] at ht
  -- | abs a t ih =>
  --   simp [debruijnify.go, perm_action]

lemma debruijn'_list_eq (t: Term 𝔸 𝕏 C) (ht: t.ground) l₁ l₂ (hl: ∀ x, l₁.idxOf? x = l₂.idxOf? x ∨ ∅ ⊢ x#t) :
  debruijnify.go l₁ t ht = debruijnify.go l₂ t ht := by
  induction t generalizing l₁ l₂ with
  | atom a =>
    rcases hl a with h|h
    · simp [debruijnify.go, h]
    · cases h; contradiction
  | unknown => simp [ground] at ht
  | abs a t ih =>
    simp [ground] at ht
    specialize ih ht
    simp [debruijnify.go]
    apply ih
    intro x
    rcases hl x with h|h
    · rcases ha: (x == a) with _|_
      · simp at ha
        simp [List.idxOf?_cons, Ne.symm ha]
        simp [h]
      · simp at ha
        simp [ha, List.idxOf?_cons]
    · cases h with
      | F_absa => simp [List.idxOf?_cons]
      | F_absb => right; assumption
  | asgn x t ih =>
    simp [debruijnify.go]
    rcases hl x with h|h
    · rw [h]
      split <;> (simp; apply ih; {
        intro x'
        rcases hl x' with h'|h'
        · left; exact h'
        · right; cases h'; assumption
      })
    · cases h; contradiction
  | app t₁ t₂ ih₁ ih₂ =>
    simp [ground] at ht
    cases ht
    simp [debruijnify.go]
    constructor
    · apply ih₁
      intro x
      rcases hl x with h|h
      · simp [h]
      · cases h
        right
        assumption
    · apply ih₂
      intro x
      rcases hl x with h|h
      · simp [h]
      · cases h; right; assumption
  | const c => simp [debruijnify.go]

lemma list_map_support (π: Perm 𝔸) x (hx: x ∉ π.support) (l: List 𝔸) :
  l.idxOf? x = (l.map π).idxOf? x := by
  have := π.notin_supp hx
  simp at this
  induction l with
  | nil => simp
  | cons l ls ih =>
    simp
    simp [List.idxOf?_cons]
    split_ifs with ha hb hc
    · rfl
    · subst_vars
      contradiction
    · rw [← this] at hc
      simp at hc
      contradiction
    · simp [ih]




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


lemma chain_de_bruijn' (t₁ t₂ : Term 𝔸 𝕏 C) (hg₁ : t₁.ground)
  (ht: CoreEq ∅ t₁ t₂) l:
  debruijnify.go l t₁ (hg₁) = debruijnify.go l t₂ (by rw [← coreeq_ground ht]; exact hg₁) := by
  induction ht generalizing l with
  | N_ax => contradiction
  | N_refl => rfl
  | N_symm t u h ih => rw [← ih]
  | N_trans t u v ht₁ ht₂ ih₁ ih₂ => rw [ih₁, ← ih₂]
  | N_cngApp t₁ t₂ u₁ u₂ ht₁ ht₂ ih₁ ih₂ => simp [debruijnify.go, ih₁, ih₂]
  | N_cngAbs a t u ht ih => simp [debruijnify.go, ih]
  | N_perm a b t h ha hb =>
    induction t generalizing l with
    | atom x =>
      cases ha
      cases hb
      expose_names
      simp [debruijnify.go, perm_action, Perm.toEquiv, transpose, h_1.symm, h_2.symm]
    | unknown =>  simp [ground, perm_action_ground] at hg₁
    | const c => simp [perm_action]
    | abs x t ih =>
      simp [debruijnify.go, perm_action, Perm.toEquiv]
      cases ha with
      | F_absa =>
        cases hb
        { contradiction }
        simp
        simp [ground, perm_action_ground] at hg₁
        rw [← perm_action_swap]
        have h1 := perm_debruijn' t hg₁ (b :: l) (Perm.swap a b h)
        simp at h1
        rw [← h1]
        apply debruijn'_list_eq
        intro x
        simp [List.idxOf?_cons]
        split_ifs
        · tauto
        · rcases hb: (b == x) with _|h
          · simp at hb
            left
            rw [← list_map_support]
            expose_names
            simp [Perm.support, Perm.vars, Perm.toEquiv, transpose, Ne.symm h_3, Ne.symm hb]
          · simp at hb
            subst hb
            right; assumption
        exact hg₁
        assumption
        simp
      | F_absb _ _ _ ha hfa =>
        cases hb with
        | F_absa =>
          simp
          simp [ground, perm_action_ground] at hg₁
          simp only [show (Perm.swap a b h)⬝t = (Perm.swap b a h.symm)⬝t from
            ground_perm_action_ext Perm.swap_symm t hg₁]
          rw [← perm_action_swap (ht := hg₁)]
          have h1 := perm_debruijn' t hg₁ (a :: l) (Perm.swap b a h.symm)
          simp at h1
          rw [← h1]
          apply debruijn'_list_eq
          intro x
          simp [List.idxOf?_cons]
          split_ifs
          · tauto
          · rcases hx: (x == a) with _|h
            · simp at hx
              left
              rw [← list_map_support]
              expose_names
              simp [Perm.support, Perm.vars, hx, Ne.symm h_1,]
            · simp at hx
              subst hx
              right; assumption
          assumption
          simp
        | F_absb _ _ _ hb hfb =>
          simp [transpose, ha.symm, hb.symm]
          rw [ih] <;> assumption
    | asgn x t ih =>
      cases ha
      cases hb
      expose_names
      simp [perm_action, debruijnify.go, Perm.toEquiv, transpose, h_1.symm, h_3.symm]
      split <;> (simp; apply ih <;> assumption)
    | app t₁ t₂ ih₁ ih₂ =>
      cases ha
      cases hb
      simp [ground, perm_action_ground] at hg₁
      cases hg₁
      simp [debruijnify.go, perm_action]
      rw [ih₁, ih₂] <;> try assumption
      tauto

theorem chain_de_bruijn (t₁ t₂: Term 𝔸 𝕏 C) (hg₁: t₁.ground)
  (ht: Term.CoreEq ∅ t₁ t₂):
  debruijnify t₁ (hg₁) = debruijnify t₂ (by rw [← coreeq_ground ht]; exact hg₁) := by
  unfold debruijnify
  apply chain_de_bruijn' (ht := ht)

lemma list_idxOf?_eq_some_eq {l: List 𝔸} {a b n} (h1: l.idxOf? a = some n) (h2: l.idxOf? b = some n) :
  a = b := by
  induction l generalizing n with
  | nil => simp at h1
  | cons c ls ih =>
    simp [List.idxOf?_cons] at *
    split_ifs at h1 <;> split_ifs at h2
    · subst_vars; rfl
    · simp at h1;  subst_vars; simp at h2
    · simp at h2; subst_vars; simp at h1
    · simp at *
      obtain ⟨_, ⟨⟩⟩ := h1
      obtain ⟨_, ⟨⟩⟩ := h2
      grind


-- theorem debruijn'_nomeq [Infinite 𝔸] (t₁ t₂ : Term 𝔸 𝕏 C) (hg₁: t₁.ground) (hg₂ : t₂.ground) l
--   (hl: ∀ a, (∅ ⊢ a#t₁ ∧ ∅ ⊢ a#t₂) ∨ a ∈ l)
--   (hd : debruijnify.go l t₁ hg₁ = debruijnify.go l t₂ hg₂) :
--   Term.CoreEq ∅ t₁ t₂ := by
--   match t₁ with
--   | .atom x =>
--     simp [ground] at hg₁
--     simp [debruijnify.go] at hd
--     split at hd <;> expose_names
--     · cases t₂ <;> simp [debruijnify.go] at hd <;> simp [ground] at hg₂ <;> try (split at hd <;> simp at hd; done)
--       split at hd <;> simp at hd
--       expose_names
--       subst hd
--       have : x = a := by apply list_idxOf?_eq_some_eq; exact heq; assumption
--       subst this
--       constructor
--     · cases t₂ <;> simp [debruijnify.go] at hd <;> simp [ground] at hg₂ <;> try (split at hd <;> simp at hd; done)
--       split at hd <;> simp at hd
--       expose_names
--       subst hd
--       constructor
--   | .unknown _ _ => simp [ground] at hg₁
--   | .const c =>
--     cases t₂ <;> simp [debruijnify.go] at hd <;> try (split at hd <;> simp at hd; done)
--     · simp [ground] at hg₂
--     · subst hd; constructor
--   | .abs a t =>
--     simp [ground] at hg₁
--     cases t₂ <;> simp [debruijnify.go] at hd <;> simp [ground] at hg₂ <;> try (split at hd <;> simp at hd; done)
--     expose_names
--     cases ha: a == a_1 with
--     | false =>
--       simp at ha
--       have ⟨c, hc⟩ := Infinite.exists_notMem_finset (t.atoms ∪ t_1.atoms ∪ l.toFinset ∪ {a, a_1})
--       simp at hc
--       rw [t.fresh_swap_debruijn' hg₁ c a hc.left, t_1.fresh_swap_debruijn' hg₂ c a_1 hc.right.left] at hd
--       rw [debruijn'_list_eq (l₁ := a :: l) (l₂ := c :: l), debruijn'_list_eq (l₁ := a_1 :: l) (l₂ := c :: l)] at hd
--       sorry
--       sorry
--       sorry
--       sorry
--       sorry
--       sorry
--       sorry
--       sorry
--       sorry
--       sorry
--       sorry
--     | true =>
--       simp at ha
--       subst ha
--       apply NominalEq.N_cngAbs
--       exact debruijn'_nomeq t _ hg₁ hg₂ (a :: l) (by
--         intro a'
--         rcases hl a' with ⟨h₁, h₂⟩ | hmem
--         · cases h₁
--           · right; simp
--           · cases h₂ <;> try contradiction
--             left; constructor <;> assumption
--         · right; simp [hmem]
--       ) hd
--   | .app s₁ s₂ =>
--     simp [ground] at hg₁
--     cases t₂ <;> simp [debruijnify.go] at hd <;> simp [ground] at hg₂ <;> try (split at hd <;> simp at hd; done)
--     apply NominalEq.N_cngApp
--     · exact debruijn'_nomeq s₁ _ hg₁.left hg₂.left l (by
--         intro a'; rcases hl a' with ⟨⟨⟩, ⟨⟩⟩ | hmem
--         · left; constructor <;> assumption
--         · right; exact hmem
--       ) hd.left
--     · exact debruijn'_nomeq s₂ _ hg₁.right hg₂.right l (by
--         intro a'; rcases hl a' with ⟨⟨⟩, ⟨⟩⟩ | hmem
--         · left; constructor <;> assumption
--         · right; exact hmem
--       ) hd.right
--   termination_by t₁.size
--   decreasing_by all_goals (simp only [size]; omega)

end CoreEq

def MakeFresh (𝔸) [DecidableEq 𝔸] := (S: Finset 𝔸) → {a : 𝔸  // a ∉ S }

namespace GroundDeBruijn

def fvs : GroundDeBruijn 𝔸 C → Finset 𝔸
| fvar a => {a}
| bvar _ | const _ => ∅
| asgn_f a t => {a} ∪ t.fvs
| abs t | asgn_b _ t => t.fvs
| app t₁ t₂ => t₁.fvs ∪ t₂.fvs


def normalize (f: ℕ ↪ 𝔸)  (g: GroundDeBruijn 𝔸 C) [Inhabited 𝔸]: Term 𝔸 𝕏 C
  := (go 0 [] f g).snd
  where go (n: ℕ) (l: List 𝔸) f g : ℕ × Term 𝔸 𝕏 C := match g with
  | bvar a => (n, .atom l[a]!)
  | fvar a => (n, .atom a)
  | asgn_b a t =>
    let (n', t) := go n l f t
    (n', .asgn l[a]! t)
  | asgn_f a t =>
    let (n', t) := go n l f t
    (n', .asgn a t)
  | abs t =>
    let a := f n
    let (n', t') := go (n + 1) (a :: l) f t
    (n', .abs a t')
  | app g₁ g₂ =>
    let (n', t₁) := go n l f g₁
    let (n'', t₂) := go n' l f g₂
    (n'', .app t₁ t₂)
  | const c => (n, .const c)

omit [DecidableEq 𝔸] in
lemma normalize'_ground [Inhabited 𝔸] n l f (g: GroundDeBruijn 𝔸 C):
  (normalize.go l (𝕏 := 𝕏) n f g).2.ground := by
  induction g generalizing n l with simp [normalize.go, ground, *]

omit [DecidableEq 𝔸] in
lemma normalize_ground [Inhabited 𝔸] f g :
  (normalize f g : Term 𝔸 𝕏 C).ground := by unfold normalize; apply normalize'_ground



end GroundDeBruijn
end Term




-- debruijn to fresh names, fresh names to nominal equality.
-- annotated (hoare) step relaetion showing separation of capsules (possible hull of scope?)
-- reachability
-- capsules and separation
-- examples of good/bad terms - properties



















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
--       ⬝ unfold Function.Injective
--         aesop
--       ⬝ intro x
--         by_cases x = b
--         ⬝ use a; aesop
--         ⬝ by_cases x = a
--           ⬝ use b; aesop
--           ⬝ use x; aesop
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
--   ⬝ intro h₁
--     apply (hs₂ x).mpr
--     rw [← h]
--     apply (hs₁ x).mp
--     exact h₁
--   ⬝ intro h₂
--     apply (hs₁ x).mpr
--     rw [h]
--     apply (hs₂ x).mp
--     exact h₂


-- instance : FunLike (Permutation 𝔸) 𝔸 𝔸 where
--   coe := (⬝.map)
--   coe_injective' := by intro a b; simp; apply Permutation.map_inj

-- variable (π : Permutation 𝔸)
-- lemma Permutation.closed x : x ∈ π.support ↔ π x ∈ π.support := by
--   constructor
--   ⬝ intro h
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
