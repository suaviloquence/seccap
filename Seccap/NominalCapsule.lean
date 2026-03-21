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
variable {𝔸 C} (a b: 𝔸) (t t₁ t₂ : Ground 𝔸 C)

abbrev atom : Ground 𝔸 C := ⟨.atom a, rfl⟩
abbrev abs : Ground 𝔸 C := ⟨.abs a t, by simp [ground, t.2]⟩
abbrev asgn : Ground 𝔸 C := ⟨.asgn a t, by simp [ground, t.2]⟩
abbrev app : Ground 𝔸 C := ⟨.app t₁ t₂, by simp [ground, t₁.2, t₂.2]⟩
abbrev const (c: C) : Ground 𝔸 C := ⟨.const c, rfl⟩

abbrev swap [DecidableEq 𝔸] (h: a ≠ b) : Ground 𝔸 C := ⟨t.1.swap a b h, by simp [perm_action_ground, t.2]⟩

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
