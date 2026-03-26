import Seccap.Nominal

namespace Term
def value {𝔸 𝕏 C}: Term 𝔸 𝕏 C → Bool
| const _ => true
| abs _ e => e.ground
| atom _ | asgn .. | unknown .. | app .. => false

abbrev Value (𝔸 C) := { t : Term 𝔸 Unit C // t.value }
abbrev Ground (𝔸 C) := { t : Term 𝔸 Unit C // t.ground }

lemma value_ground {t: Term 𝔸 𝕏 C} : t.value → t.ground := by
  induction t with simp_all [value, ground]

namespace Ground
variable {𝔸 C} [DecidableEq 𝔸] (a b: 𝔸) (t t₁ t₂ : Ground 𝔸 C)

abbrev atom : Ground 𝔸 C := ⟨.atom a, rfl⟩
abbrev abs : Ground 𝔸 C := ⟨.abs a t, by simp [ground, t.2]⟩
abbrev asgn : Ground 𝔸 C := ⟨.asgn a t, by simp [ground, t.2]⟩
abbrev app : Ground 𝔸 C := ⟨.app t₁ t₂, by simp [ground, t₁.2, t₂.2]⟩
abbrev const (c: C) : Ground 𝔸 C := ⟨.const c, rfl⟩

abbrev swap (h: a ≠ b) : Ground 𝔸 C := ⟨t.1.swap a b h, by simp [perm_action_ground, t.2]⟩

omit [DecidableEq 𝔸] in
lemma coe_abs a (t: Term 𝔸 Unit C) ht :
  ⟨t.abs a, ht⟩ = abs a ⟨t, by simp [ground] at ht; exact ht⟩ := rfl

omit [DecidableEq 𝔸] in
lemma coe_asgn a (t: Term 𝔸 Unit C) ht :
  ⟨t.asgn a, ht⟩ = asgn a ⟨t, by simp [ground] at ht; exact ht⟩ := rfl

omit [DecidableEq 𝔸] in
lemma coe_app (t₁ t₂: Term 𝔸 Unit C) ht :
  ⟨t₁.app t₂, ht⟩ = app ⟨t₁, by simp [ground] at ht; exact ht.left⟩ ⟨t₂, by simp [ground] at ht; exact ht.right⟩ := rfl

lemma coe_swap (t: Term 𝔸 Unit C) ht a b h :
  swap a b ⟨t, ht⟩ h = ⟨t.swap a b h, by simpa [perm_action_ground]⟩ := rfl

omit [DecidableEq 𝔸] in
@[simp]
lemma ground_ground : t.1.ground := t.2

end Ground

instance {𝔸 C}: Coe (Value 𝔸 C) (Ground 𝔸 C) where
  coe := fun ⟨t, ht⟩ => ⟨t, value_ground ht⟩

variable {𝔸 𝕏 C} [DecidableEq 𝔸] {t: Term 𝔸 𝕏 C}

def fvs : Term 𝔸 𝕏 C → Finset 𝔸
| atom a => {a}
| const .. | unknown .. => ∅
| abs a t => t.fvs \ {a}
| asgn a t => {a} ∪ t.fvs
| app t₁ t₂ => t₁.fvs ∪ t₂.fvs

lemma swap_fvs' {a b h x} (ha: x ≠ a) (hb: x ≠ b):
  x ∈ t.fvs ↔ x ∈ (t.swap a b h).fvs := by
  induction t with simp [fvs, perm_action, *] <;> simp [Perm.toEquiv, transpose] <;> grind

lemma swap_fvs {a b h} :
  t.fvs \ {a, b} = (t.swap a b h).fvs \ {a, b} := by
  ext x
  simp
  apply swap_fvs'

lemma fresh_fvs {a} (h : ∅ ⊢ a#t) : a ∉ t.fvs := by
  induction h with simp [fvs, *]

lemma fvs_fresh {a} (ht: t.ground) (h: a ∉ t.fvs) : ∅ ⊢ a#t := by
  induction t with (simp [fvs] at h; simp [ground] at ht) <;> try (constructor <;> grind)
  | abs b t ih =>
    specialize ih ht
    by_cases ha: a = b
    · rw [ha]; constructor
    · apply Fresh.F_absb
      · exact ha
      · apply ih
        intro contra
        cases ha (h contra)
end Term

def Store α β := List (α × β)

namespace Store
variable {α β} [DecidableEq α]

def dom: Store α β → Finset α
| [] => ∅
| (a, _)::s => {a} ∪ dom s

def getVal (s: Store α β) (a: α) (h: a ∈ s.dom) : β := match s with
| (b, v)::s => if ha: a = b then v else getVal s a (by simp [dom, ha] at h; exact h)
| [] => by simp [dom] at h

def getVal? (s : Store α β) (a: α) : Option β := match s with
| [] => none
| (b, v)::s => if a = b then some v else getVal? s a

instance : GetElem (Store α β) α β (fun s a => a ∈ s.dom) := ⟨getVal⟩
instance : GetElem? (Store α β) α β (fun s a => a ∈ s.dom) where
  getElem? := getVal?

lemma getVal_iff_getVal? (s : Store α β) a b :
  (∃ h, s.getVal a h = b) ↔ s.getVal? a = some b := by
  induction s with
  | nil => simp [dom, getVal?]
  | cons p s ih =>
    obtain ⟨x, y⟩ := p
    simp [dom, getVal, getVal?]
    split_ifs with h
    · subst h
      constructor
      · intro h
        rw [h.snd]
      · intro h
        simp at h
        simp [h]
    · constructor
      · intro hl
        obtain ⟨hl, hl'⟩ := hl
        simp [h] at hl
        apply ih.mp ⟨hl, hl'⟩
      · intro hr
        obtain ⟨h', hh'⟩ := ih.mpr hr
        exact ⟨Or.inr h', hh'⟩

def permute (s: Store α β) (π : Perm α) : Store α β := match s with
| [] => []
| (a, v)::s => (π a, v)::(permute s π)

abbrev swap (s: Store α β) a b h := s.permute (Perm.swap a b h)

lemma getVal?_permute {s: Store α β} {a π} :
  s.getVal? a = (s.permute π).getVal? (π a) := by induction s with
  | nil => simp [permute, getVal?]
  | cons b s ih =>
    obtain ⟨b, v⟩ := b
    simp [getVal?, permute]
    split_ifs
    · rfl
    · exact ih

end Store

structure Capsule (𝔸 C : Type) where
  t : Term.Ground 𝔸 C
  σ : Store 𝔸 (Term.Value 𝔸 C)

namespace Capsule
variable {𝔸 C} [DecidableEq 𝔸]

def valid (m: Capsule 𝔸 C) :=
  m.t.1.fvs ⊆ m.σ.dom ∧ (∀ a, (h: a ∈ m.σ.dom) → (m.σ.getVal a h).1.fvs ⊆ m.σ.dom)

lemma valid_app_l {t₁ t₂ : Term.Ground 𝔸 C} {σ} : valid ⟨.app t₁ t₂, σ⟩ → valid ⟨t₁, σ⟩ := by
  obtain ⟨t₁, hg₁⟩ := t₁
  simp [valid, Term.fvs]
  intro h₁ h₂
  constructor
  · apply Finset.union_subset_left
    exact h₁
  · exact h₂


lemma valid_app_r {t₁ t₂ : Term.Ground 𝔸 C} {σ} : valid ⟨.app t₁ t₂, σ⟩ → valid ⟨t₂, σ⟩ := by
  obtain ⟨t₂, hg₂⟩ := t₂
  simp [valid, Term.fvs]
  intro h₁ h₂
  constructor
  · apply Finset.union_subset_right
    exact h₁
  · exact h₂

lemma valid_asgn {a} {t : Term.Ground 𝔸 C} {σ} : valid ⟨t.asgn a, σ⟩ → valid ⟨t, σ⟩ := by
  obtain ⟨t, _⟩ := t
  simp [valid, Term.fvs]
  rw [Finset.insert_subset_iff]
  simp
  intro a b c
  simpa [b]

-- read/write types with names
-- separation/noninterference with partition σ + τ ⇒ v ∀ τ
-- indistinguishability relation over capsules that masks part of the store
-- inductively define store
-- try to understand a separaation logic proof of noninterference
-- separation for concurrency


inductive Step [DecidableEq 𝔸] : Capsule 𝔸 C → Capsule 𝔸 C → Prop where
| Var a σ (v: Term.Value 𝔸 C) (h: σ.getVal? a = some v): Step ⟨.atom a, σ⟩ ⟨v, σ⟩
| App t₁ t₂ σ t₁' σ' : Step ⟨t₁, σ⟩ ⟨t₁', σ'⟩ → Step ⟨.app t₁ t₂, σ⟩ ⟨.app t₁' t₂, σ'⟩
| AppV (v: Term.Value 𝔸 C) t₂ σ t₂' σ' : Step ⟨t₂, σ⟩ ⟨t₂', σ'⟩ → Step ⟨.app v t₂, σ⟩ ⟨.app v t₂', σ'⟩
-- this can probably be b#t.1?
| AppAbs a t (v: Term.Value 𝔸 C) σ b (h: b ∉ σ.dom ∪ t.1.atoms ∪ {a}) : Step ⟨.app (.abs a t) v, σ⟩ ⟨t.swap a b (by simp at h; exact Ne.symm h.left), (b, v)::σ⟩
| Asgn a t σ t' σ' : Step ⟨t, σ⟩ ⟨t', σ'⟩ → Step ⟨.asgn a t, σ⟩ ⟨.asgn a t', σ'⟩
| AsgnV a (v: Term.Value 𝔸 C) σ : Step ⟨.asgn a v, σ⟩ ⟨v, (a, v)::σ⟩

namespace Step
lemma dom_sub {c₁ c₂ : Capsule 𝔸 C} (h: Step c₁ c₂) : c₁.σ.dom ⊆ c₂.σ.dom := by
  induction h with simp [*, Store.dom]

lemma valid_step {c₁ c₂: Capsule 𝔸 C} (hc: c₁.valid) (h: Step c₁ c₂) : c₂.valid := by
  induction h with
  | Var a σ v h =>
    simp [valid, Term.fvs] at hc
    constructor
    · obtain ⟨hin, heq⟩ := (σ.getVal_iff_getVal? a v).mpr h
      simp
      rw [← heq]
      apply hc.right
      exact hin
    · simp
      exact hc.right
  | App t₁ t₂ σ t₁' σ' h ih =>
    specialize ih (valid_app_l hc)
    simp [valid, Term.fvs]
    constructor
    · intro a ha
      simp at ha
      rcases ha with ha|ha
      · simp [valid] at ih
        exact Finset.mem_of_subset ih.left ha
      · simp [valid, Term.fvs] at hc
        apply Finset.mem_of_subset _ ha
        apply Finset.Subset.trans
        · exact Finset.union_subset_right hc.left
        · exact dom_sub h
    · simp [valid] at ih
      exact ih.right
  | AppV v t₂ σ t₂' σ' h ih =>
    specialize ih (valid_app_r hc)
    simp [valid, Term.fvs]
    simp [valid, Term.fvs] at hc
    constructor
    · apply Finset.union_subset
      · apply Finset.Subset.trans _ (dom_sub h)
        simp
        exact Finset.union_subset_left hc.left
      · simp [valid] at ih
        exact ih.left
    · simp [valid] at ih
      exact ih.right
  | AppAbs a t v σ b h =>
    simp [valid]
    constructor
    · obtain ⟨t, ht⟩ := t
      intro c hc'
      simp at h
      have hf : ∅ ⊢ b#t := t.ground_notin_atoms b ht h.right.right
      have := t.fresh_fvs hf
      simp [Store.dom]
      by_cases hb: b = c
      · simp [hb]
      · simp [Ne.symm hb]
        by_cases ha: a = c
        · subst ha
          have := t.swap_fresh a b (Ne.symm hb) _ hf ht
          have := (mt (Term.fresh_fvs)) (not_not_intro hc')
          contradiction
        · rw [← t.swap_fvs'] at hc' <;> try (symm; assumption)
          simp [valid, Term.fvs] at hc
          grind
    · simp [valid] at hc
      simp [Store.dom]
      intro c hc'
      by_cases hb: c = b
      · subst hb
        simp [Store.getVal]
        simp [Term.fvs] at hc
        grind
      · simp [hb] at hc'
        simp [Store.getVal, hb]
        have := hc.right c hc'
        grind
  | Asgn a t σ t' σ' h ih =>
    specialize ih (valid_asgn hc)
    simp [valid] at ih
    simp [valid]
    apply And.intro _ ih.right
    simp [Term.fvs]
    apply Finset.insert_subset _ ih.left
    simp [valid, Term.fvs] at hc
    have : a ∈ σ.dom := by grind
    grind [dom_sub h]
  | AsgnV a v σ =>
    simp [valid, Store.dom]
    simp [valid, Term.fvs] at hc
    constructor
    · grind
    · intro b hb
      by_cases ha: b = a
      · subst ha
        simp [Store.getVal]
        grind
      · simp [Store.getVal, ha]
        grind
end Step
end Capsule

namespace Types
inductive BaseType (B: Type*) where
| base (b: B)
| arrow (T₁ T₂ : BaseType B)

class ConstantFamily (C: Type*) where
  bases: Type*
  type : C → bases

export ConstantFamily (bases type)

variable {𝔸 C : Type} [DecidableEq 𝔸] [ConstantFamily C]

inductive HasType : (Store 𝔸 (BaseType (bases C))) → Term.Ground 𝔸 C → BaseType (bases C) → Prop
| Const Γ c : HasType Γ (.const c) (.base (type c))
| Atom Γ  x τ : Γ.getVal? x = some τ → HasType Γ (.atom x) τ
| Abs Γ x t τ₁ τ₂ : HasType ((x, τ₁)::Γ) t τ₂ → HasType Γ (.abs x t) (τ₁.arrow τ₂)
| Asgn Γ x t τ : Γ.getVal? x = some τ → HasType Γ t τ → HasType Γ (.asgn x t) τ
| App Γ t₁ t₂ τ₁ τ₂ : HasType Γ t₁ (τ₁.arrow τ₂) → HasType Γ t₂ τ₁ → HasType Γ (.app t₁ t₂) (τ₂)


variable {t: Term.Ground 𝔸 C}

lemma type_ext {Γ Δ τ} (h: ∀ {a v}, Γ.getVal? a = some v → Δ.getVal? a = some v) (ht: HasType Γ t τ) :
  HasType Δ t τ := by induction ht generalizing Δ with
  | Const c => constructor
  | Atom Γ x τ ha => constructor; exact h ha
  | Abs Γ x t τ₁ τ₂ ht ih =>
    constructor
    apply ih
    intro a v ha
    simp [Store.getVal?]
    split_ifs with hx
    · simp [Store.getVal?, hx] at ha
      simp [ha]
    · simp [Store.getVal?, hx] at ha
      exact h ha
  | Asgn Γ x t τ hx ht ih =>
    constructor
    · exact h hx
    · exact ih h
  | App Γ t₁ t₂ τ₁ τ₂ ht₁ ht₂ ih₁ ih₂ =>
    constructor
    · exact ih₁ h
    · exact ih₂ h

lemma swap_type {a b h Γ τ} (ht: HasType Γ t τ) :
  HasType (Γ.swap a b h) (t.swap a b h) τ := by
  induction ht with
  | Const Δ c => simp [Term.Ground.swap, Term.perm_action]; constructor
  | Atom Δ x τ hx =>
    simp [Term.Ground.swap, Term.perm_action]
    constructor
    rw [← Store.getVal?_permute]
    exact hx
  | Abs Δ x t  τ₁ τ₂ hx ih =>
    simp [Term.Ground.swap, Term.perm_action, Perm.toEquiv]
    simp only [← Term.swap.eq_def]
    rw [Term.Ground.coe_abs, ← Term.Ground.coe_swap (ht := by simp)]
    constructor
    simp [Store.permute, Perm.toEquiv] at ih
    apply ih
  | App Γ t₁ t₂ τ₁ τ₂ ht₁ ht₂ ih₁ ih₂ =>
    simp [Term.Ground.swap, Term.perm_action]
    simp only [← Term.swap.eq_def]
    rw [Term.Ground.coe_app, ← Term.Ground.coe_swap (ht := by simp), ← Term.Ground.coe_swap (ht := by simp)]
    constructor
    · exact ih₁
    · exact ih₂
  | Asgn Γ x t τ hx ht ih =>
    simp [Term.Ground.swap, Term.perm_action, ← Term.swap.eq_def]
    rw [Term.Ground.coe_asgn, ← Term.Ground.coe_swap (ht := by simp)]
    constructor
    · rw [← Store.getVal?_permute]
      exact hx
    · exact ih


open Capsule in
lemma arrow_inversion {Γ τ₁ τ₂} (h: HasType Γ t (.arrow τ₁ τ₂)) (hv: t.1.value):
  ∃ x t', t = .abs x t' ∧ HasType ((x, τ₁)::Γ) t' τ₂ := by
  cases h with simp [Term.value] at hv
  | Abs _ x t _ _ h => use x,t

open Capsule in
lemma progress [Infinite 𝔸] {σ τ Γ} (hs: Γ.dom ⊆ σ.dom) (h: HasType Γ t τ) :
    t.1.value ∨ ∃ t' σ', Step ⟨t, σ⟩ ⟨t', σ'⟩ := by
  induction h generalizing σ with
  | Const => left; simp [Term.value]
  | Atom Γ x τ hx =>
    obtain ⟨hτ₁, hτ₂⟩ := (Γ.getVal_iff_getVal? _ _).mpr hx
    have hx := hs hτ₁
    have := (σ.getVal_iff_getVal? _ _).mp ⟨hx, rfl⟩
    right; use σ.getVal x hx, σ
    apply Step.Var
    exact this
  | Abs Γ x t τ₁ τ₂ ht ih => left; simp [Term.value, t.2]
  | Asgn Γ x t τ hx ht ih =>
    right
    rcases ih hs with hv|⟨t', ⟨σ', ht'⟩⟩
    · let v: Term.Value _ _ := ⟨t.1, hv⟩
      have : t = v := by simp [v]
      rw [this]
      use v, (x, v)::σ
      apply Step.AsgnV x v σ
    · use .asgn x t', σ'
      apply Step.Asgn
      exact ht'
  | App Γ t₁ t₂ τ₁ τ₂ ht₁ ht₂ ih₁ ih₂ =>
    right
    rcases ih₁ hs with hv₁|⟨t₁', ⟨σ', ht₁'⟩⟩
    · rcases ih₂ hs with hv₂|⟨t₂', ⟨σ', ht₂'⟩⟩
      · let v: Term.Value _ _ := ⟨t₂.1, hv₂⟩
        have: t₂ = v := by simp [v]
        obtain ⟨x, ⟨t, ⟨heq, ht⟩⟩⟩ := arrow_inversion ht₁ hv₁
        rw [this, heq]
        obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (σ.dom ∪ t.1.atoms ∪ {x})
        use t.swap x b (by simp at hb; exact Ne.symm hb.left), (b, v)::σ
        refine Step.AppAbs x t v σ b hb
      · let v: Term.Value _ _ := ⟨t₁.1, hv₁⟩
        use Term.Ground.app v t₂', σ'
        refine Step.AppV v t₂ σ t₂' σ' ht₂'
    · use t₁'.app t₂, σ'
      refine Step.App t₁ t₂ σ t₁' σ' ht₁'
end Types
