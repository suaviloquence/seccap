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


variable {t t₁ t₂ : Term.Ground 𝔸 C} {a b x : 𝔸} {h: a ≠ b}

@[simp]
lemma swap_const : (const c).swap a b h = const c := rfl

@[simp]
lemma swap_atom : (atom x).swap (C := C) a b h = atom (transpose a b x) := rfl

@[simp]
lemma swap_abs : (abs x t).swap a b h = abs (transpose a b x) (t.swap a b h) := rfl

@[simp]
lemma swap_asgn : (asgn x t).swap a b h = asgn (transpose a b x) (t.swap a b h) := rfl

@[simp]
lemma swap_app : (app t₁ t₂).swap a b h = app (t₁.swap a b h) (t₂.swap a b h) := rfl

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

lemma fvs_atoms : t.fvs ⊆ t.atoms := by induction t with grind [fvs, atoms]

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

lemma getVal?_none {s: Store α β} {a} :
  s.getVal? a = none ↔ a ∉ s.dom := by
  induction s with grind [getVal?, dom]

lemma getVal_eq_getVal? {s s': Store α β} {a h₁ h₂} :
  s.getVal a h₁ = s'.getVal a h₂ → s.getVal? a = s'.getVal? a := by
  intro h
  have h₁: ∃ h, s.getVal a h = s.getVal a h₁ := ⟨h₁, rfl⟩
  have h₂: ∃ h, s'.getVal a h = s'.getVal a h₂ := ⟨h₂, rfl⟩
  apply (s.getVal_iff_getVal? _ _).mp at h₁
  apply (s'.getVal_iff_getVal? _ _).mp at h₂
  rw [h₁, h₂, h]

def permute (s: Store α β) (π : Perm α) : Store α β := match s with
| [] => []
| (a, v)::s => (π a, v)::(permute s π)

abbrev swap (s: Store α β) a b h := s.permute (Perm.swap a b h)

@[simp]
lemma swap_cons {s: Store α β} {a b h x v}:
  swap ((x, v)::s) a b h = (transpose a b x, v)::(s.swap a b h) := rfl

lemma permute_dom {s: Store α β} {π x} :
  x ∈ s.dom ↔ π x ∈ (s.permute π).dom := by
  induction s with simp [permute, dom, *]

lemma permute_getVal {s: Store α β} {π x} (h: x ∈ s.dom) :
  s.getVal x h = (s.permute π).getVal (π x) (permute_dom.mp h) := by
  induction s with simp [permute, getVal, *]

lemma permute_dom' {s: Store α β} {π x} :
  π.inv x ∈ s.dom ↔ x ∈ (s.permute π).dom := by
  have : x = π (π.inv x) := by simp
  conv =>
    rhs
    rw [this]
  apply permute_dom

lemma swap_dom' {s: Store α β} {a b h x} (ha: x ≠ a) (hb: x ≠ b):
  x ∈ s.dom ↔ x ∈ (s.swap a b h).dom := by
  have : x = (Perm.swap a b h) x := by simp [Perm.toEquiv, transpose, ha, hb]
  conv =>
    rhs
    rw [this]
  apply permute_dom

lemma getVal_swap' {s: Store α β} {a b h x} (ha: x ≠ a) (hb: x ≠ b) (hx: x ∈ s.dom):
  (s.swap a b h).getVal x ((swap_dom' ha hb).mp hx) = s.getVal x hx := by
  rw [s.permute_getVal (π := Perm.swap a b h)]
  simp [Perm.toEquiv, transpose, ha, hb]


lemma getVal?_permute {s: Store α β} {a π} :
  s.getVal? a = (s.permute π).getVal? (π a) := by induction s with
  | nil => simp [permute, getVal?]
  | cons b s ih =>
    obtain ⟨b, v⟩ := b
    simp [getVal?, permute]
    split_ifs
    · rfl
    · exact ih

def ext_le (s s' : Store α β) :=
  ∃ h: s.dom ⊆ s'.dom, ∀ {a} (ha: a ∈ s.dom),
    s.getVal a ha = s'.getVal a (h ha)

variable {s s' s'': Store α β}

@[simp]
lemma ext_le_refl : s.ext_le s := by simp [ext_le]

lemma ext_le_trans : s.ext_le s' → s'.ext_le s'' → s.ext_le s'' := by
  simp [ext_le]
  intro hs₁ h₁ hs₂ h₂
  use Finset.Subset.trans hs₁ hs₂
  intro a ha
  rw [h₁, ← h₂]

lemma ext_le_cons (h: a ∉ s.dom) :
  s.ext_le ((a, v)::s) := by
  refine ⟨?_, ?_⟩
  · simp [dom]
  · intro b hb
    grind [getVal]

def ext_eq (s s' : Store α β) :=
  ∀ a, s.getVal? a = s'.getVal? a

@[simp]
lemma ext_eq_rfl : s.ext_eq s := by simp [ext_eq]

@[symm]
lemma ext_eq_symm : s.ext_eq s' → s'.ext_eq s := by
  simp [ext_eq]
  intro h a
  exact (h a).symm

lemma ext_eq_trans : s.ext_eq s' → s'.ext_eq s'' → s.ext_eq s'' := by
  simp [ext_eq]
  intro h₁ h₂ a
  rw [h₁, ← h₂]

instance : Setoid (Store α β) where
  r := ext_eq
  iseqv := ⟨@ext_eq_rfl _ _ _, ext_eq_symm, ext_eq_trans⟩

lemma ext_eq_dom' : s.ext_eq s' → s.dom ⊆ s'.dom := by
  intro h a ha
  have := (s.getVal_iff_getVal? a (s.getVal a ha)).mp ⟨ha, rfl⟩
  rw [h a] at this
  apply (getVal_iff_getVal? _ _ _).mpr at this
  exact this.fst

lemma ext_eq_dom : s.ext_eq s' → s.dom = s'.dom := by
  intro h
  have h₁ := ext_eq_dom' h
  have h₂ := ext_eq_dom' (ext_eq_symm h)
  exact Finset.Subset.antisymm h₁ h₂

lemma ext_le_ext_eq :
  s.ext_le s' ∧ s'.ext_le s ↔ s.ext_eq s' := by
  constructor
  · rintro ⟨⟨hs₁, h₁⟩, ⟨hs₂, h₂⟩⟩
    intro a
    cases heq: s.getVal? a
    · symm
      apply getVal?_none.mpr
      apply getVal?_none.mp at heq
      exact heq.imp (hs₂ ·)
    · apply (getVal_iff_getVal? _ _ _).mpr at heq
      obtain ⟨h, heq⟩ := heq
      symm
      apply (getVal_iff_getVal? _ _ _).mp
      use hs₁ h
      rw [← h₁ h, heq]
  · intro h
    simp [ext_le, ext_eq_dom h]
    constructor
    · intro a ha
      have ha': a ∈ s.dom := by rwa [ext_eq_dom h]
      have h₁ := (s.getVal_iff_getVal? a (s.getVal a ha')).mp ⟨ha', rfl⟩
      have h₂ := (s'.getVal_iff_getVal? a (s'.getVal a ha)).mp ⟨ha, rfl⟩
      rw [← h a, h₁] at h₂
      simp at h₂
      exact h₂
    · intro a ha
      have ha': a ∈ s.dom := by rwa [ext_eq_dom h]
      have h₁ := (s.getVal_iff_getVal? a (s.getVal a ha')).mp ⟨ha', rfl⟩
      have h₂ := (s'.getVal_iff_getVal? a (s'.getVal a ha)).mp ⟨ha, rfl⟩
      rw [← h a, h₁] at h₂
      simp at h₂
      exact h₂.symm


@[simp]
lemma ext_eq_cons {a v} (h: s.ext_eq s') : ext_eq ((a, v)::s)  ((a, v)::s') := by
  intro x
  specialize h x
  simp [getVal?]
  split_ifs <;> trivial

-- this one is ugly
lemma shadow_ext_eq_swap :
  ext_eq
    ((a, v₁) :: (b, v₂) :: s)
    ((a, v₁) :: (b, v₂) :: (s.swap a b h)) := by
  simp [ext_eq, getVal?]
  intro x
  split_ifs <;> subst_vars <;> try trivial
  induction s <;> simp [getVal?, permute, swap]
  split_ifs <;> expose_names <;> (
    simp [Perm.toEquiv, transpose] at h_4
    grind
  )

lemma ext_eq_reorder (h: a ≠ b):
  ext_eq ((a, v₁)::(b, v₂)::s) ((b, v₂)::(a, v₁)::s) := by grind [ext_eq, getVal?]

lemma ext_eq_shadow :
  ext_eq ((a, v₁)::(a, v₂)::s) ((a, v₁)::s) := by grind [ext_eq, getVal?]
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
| AppAbs a t (v: Term.Value 𝔸 C) σ b (h: b ∉ σ.dom ∪ t.1.atoms ∪ v.1.atoms ∪ {a}) : Step ⟨.app (.abs a t) v, σ⟩ ⟨t.swap a b (by simp at h; exact Ne.symm h.left), (b, v)::σ⟩
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
      have hf : ∅ ⊢ b#t := t.ground_notin_atoms b ht h.right.right.left
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
| Atom Γ x τ : Γ.getVal? x = some τ → HasType Γ (.atom x) τ
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
    simp at ih
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
        obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (σ.dom ∪ t.1.atoms ∪ v.1.atoms ∪ {x})
        use t.swap x b (by simp at hb; exact Ne.symm hb.left), (b, v)::σ
        refine Step.AppAbs x t v σ b hb
      · let v: Term.Value _ _ := ⟨t₁.1, hv₁⟩
        use Term.Ground.app v t₂', σ'
        refine Step.AppV v t₂ σ t₂' σ' ht₂'
    · use t₁'.app t₂, σ'
      refine Step.App t₁ t₂ σ t₁' σ' ht₁'

lemma weakening {Γ Γ' τ} (ht: HasType Γ t τ) (hΓ: ∀ {a τ}, Γ.getVal? a = some τ → Γ'.getVal? a = some τ) :
  HasType Γ' t τ := by
  induction ht generalizing Γ' with
  | Const c => constructor
  | Atom Γ x τ hx => constructor; exact hΓ hx
  | Abs Γ x t τ₁ τ₂ ht ih =>
    constructor
    apply ih
    intro a τ
    simp [Store.getVal?]
    split_ifs
    · tauto
    · apply hΓ
  | Asgn Γ x t τ hx ht ih =>
    constructor
    · exact hΓ hx
    · exact ih hΓ
  | App Γ t₁ t₂ τ₁ τ₂ ht₁ ht₂ ih₁ ih₂ =>
    constructor
    · exact ih₁ hΓ
    · exact ih₂ hΓ

lemma weakening' {Γ Γ' τ} (ht: HasType Γ t τ) (h: Γ.ext_le Γ') :
  HasType Γ' t τ := by
  obtain ⟨h, hΓ⟩ := h
  apply weakening ht
  intro a τ ha
  obtain ⟨ha, hτ⟩ := (Γ.getVal_iff_getVal? a τ).mpr ha
  apply (Store.getVal_iff_getVal? _ _ _).mp
  use h ha
  rw [← hτ]
  symm
  apply hΓ

lemma strengthening {Γ Γ' τ} (ht: HasType Γ t τ) (h: ∀ a ∈ t.1.fvs, Γ.getVal? a = Γ'.getVal? a) :
  HasType Γ' t τ := by
  induction ht generalizing Γ' with simp [Term.fvs] at h
  | Const => constructor
  | Atom Γ x τ hx => constructor; rw [← h, hx]
  | Abs Γ x t τ₁ τ₂ ht ih =>
    constructor
    apply ih
    intro a ha
    simp [Store.getVal?]
    split_ifs with h'
    · rfl
    · exact h a ha h'
  | Asgn Γ x t τ hx ht ih =>
    constructor
    · rw [← h.left, hx]
    · exact ih h.right
  | App Γ t₁ t₂ τ₁ τ₂ ht₁ ht₂ ih₁ ih₂ =>
    constructor
    · apply ih₁
      intro a ha
      apply h
      simp [ha]
    · apply ih₂
      intro a ha
      apply h
      simp [ha]

lemma ext_eq {Γ Γ' τ} (ht: HasType Γ t τ) (h: Γ.ext_eq Γ') :
  HasType Γ' t τ := by
  induction ht generalizing Γ' with
  | Const => constructor
  | Atom => constructor; rwa [← h]
  | Abs Γ a t τ₁ τ₂ ht ih =>
    constructor
    apply ih
    exact Store.ext_eq_cons h
  | Asgn _ _ _ _ _ _ ih =>
    constructor
    · rwa [← h]
    · exact ih h
  | App _ _ _ _ _ _ _ ih₁ ih₂ =>
    constructor
    · exact ih₁ h
    · exact ih₂ h

lemma reorder {Γ a b τ₁ τ₂ τ} (h: a ≠ b) :
  HasType ((a, τ₁)::(b, τ₂)::Γ) t τ ↔ HasType ((b, τ₂)::(a, τ₁)::Γ) t τ := by
  constructor <;> (intro ht; refine ext_eq ht (Store.ext_eq_reorder ?_))
  · exact h
  · exact h.symm

lemma shadow {Γ a τ₁ τ₂ τ} :
  HasType ((a, τ₁)::(a, τ₂)::Γ) t τ ↔ HasType ((a, τ₁)::Γ) t τ := by
  constructor <;> (
    intro ht
    apply ext_eq ht
  )
  · apply Store.ext_eq_shadow
  · symm; apply Store.ext_eq_shadow

lemma rename_bound {Γ τ τ' a b h}  (ht: HasType ((a,τ')::Γ) t τ) (hb: b ∉ t.1.fvs) :
  HasType ((b,τ')::Γ) (t.swap a b h) τ := by
  generalize hΔ: (a, τ')::Γ = Δ at ht
  have hΔ' : Store.ext_eq ((a, τ')::Γ) Δ := by simp [hΔ]
  clear hΔ
  induction ht generalizing Γ τ' with simp [Term.fvs] at hb
  | Const => simp; constructor
  | Atom Δ x τ hx =>
    simp [transpose, Ne.symm hb]
    constructor
    simp [Store.getVal?, Ne.symm hb]
    split_ifs with ha
    · simp [← hΔ' a, Store.getVal?, ha] at hx
      simp [hx]
    · have : Store.getVal? Γ x = Δ.getVal? x := by
        rw [← hΔ']
        simp [Store.getVal?, ha]
      rw [this, hx]
  | Abs Δ x t τ₁ τ₂ ht ih =>
    simp
    constructor
    simp [transpose]
    split_ifs with h₁ h₂
    · apply shadow.mpr
      apply ih
      · intro c
        subst h₁
        cases h (hb c).symm
      · subst h₁
        simp [Store.ext_eq, Store.getVal?]
        simp [Store.ext_eq, Store.getVal?] at hΔ'
        grind
    · subst h₂
      have : HasType ((x, τ₁)::(a, τ')::Γ) t τ₂ := by
        apply ext_eq ht
        apply Store.ext_eq_cons
        symm
        exact hΔ'
      refine ext_eq (swap_type this) (Store.ext_eq_symm ?_)
      simp
      exact Store.shadow_ext_eq_swap
    · apply (reorder (Ne.symm h₂)).mp
      apply ih
      · exact h₂.imp (symm ∘ hb)
      · have ha: Store.ext_eq ((x, τ₁)::Δ) ((x, τ₁)::(a, τ')::Γ) := Store.ext_eq_symm (Store.ext_eq_cons hΔ')
        have hb: Store.ext_eq _ ((a, τ')::(x, τ₁)::Γ) := Store.ext_eq_reorder h₁
        symm
        apply Store.ext_eq_trans
        · exact ha
        · exact hb
  | Asgn Δ x t τ hx ht ih =>
    simp
    constructor
    simp [transpose, Ne.symm hb.left, Store.getVal?]
    split_ifs with ha
    · rw [← hΔ' x, Store.getVal?, ha] at hx
      simp at hx
      simp [hx]
    · have : Store.getVal? Γ x = Δ.getVal? x := by
        rw [← hΔ']
        simp [Store.getVal?, ha]
      rw [this, hx]
    apply ih
    · exact hb.right
    · exact hΔ'
  | App Δ t₁ t₂ τ₁ τ₂ ht₁ ht₂ ih₁ ih₂ =>
    simp
    constructor
    · exact ih₁ hb.left hΔ'
    · exact ih₂ hb.right hΔ'


open Capsule in
lemma preservation {c c': Capsule 𝔸 C} {Γ τ} (hc: c.valid)
  (hτ: HasType Γ c.t τ) (ht: Step c c') (hσ : Γ.dom = c.σ.dom)
  (hΓ: ∀ {a} (ha: a ∈ Γ.dom), HasType Γ (c.σ.getVal a (hσ ▸ ha)) (Γ.getVal a ha)) :
  ∃ Γ', HasType Γ' c'.t τ ∧
    (Γ.ext_le Γ') ∧
    (∃ hσ': (Γ'.dom = c'.σ.dom),
      (∀ {a} (ha: a ∈ Γ'.dom), HasType Γ' (c'.σ.getVal a (hσ' ▸ ha)) (Γ'.getVal a ha)))
  := by
  have hc' := Step.valid_step hc ht
  induction ht generalizing τ with
  | Var a σ v h =>
      use Γ
      simp [valid, Term.fvs] at hc
      constructor
      · simp
        simp at hτ
        cases hτ
        rename_i h'
        obtain ⟨_, h⟩ := (σ.getVal_iff_getVal? _ _).mpr h
        obtain ⟨_, hi⟩ := (Γ.getVal_iff_getVal? _ _).mpr h'
        rw [← h, ← hi]
        apply hΓ
      · simp
        use hσ
  | AppAbs a t v σ b hb =>
    set ta := t.abs a with heq
    simp at hτ
    obtain ⟨ta, hta⟩ := ta
    obtain ⟨v, hv⟩ := v
    cases hτ
    expose_names
    simp at heq
    subst heq
    obtain ⟨t, ht⟩ := t
    cases h_1
    expose_names
    simp at hb
    use (b, τ₁)::Γ
    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
    · simp
      apply rename_bound h_1
      intro c
      apply hb.right.right.left
      exact (t.1.fvs_atoms c)
    · apply Store.ext_le_cons
      rw [hσ]
      exact hb.right.left
    · simp [Store.dom, hσ]
    · intro x hx
      simp [Store.dom] at hx
      simp [Store.getVal]
      split_ifs with hbx
      · subst hbx
        apply strengthening h
        intro d hd
        simp [Store.getVal?]
        intro con
        subst con
        exfalso
        apply hb.right.right.right
        exact (t₂.1.fvs_atoms hd)
      · simp [hbx] at hx
        apply weakening (hΓ hx)
        intro d hd
        simp [Store.getVal?]
        intro h
        apply (Store.getVal_iff_getVal? _ _ _).mpr at h
        have : d ≠ b := by intro c; subst c; cases (hb.right.left (hσ ▸ h.fst))
        simp [this]
        apply (Store.getVal_iff_getVal? _ _ _).mp h
  | App t₁ t₂ σ t₁' σ' hc₁ ih =>
    obtain ⟨t₁, ht₁⟩ := t₁
    obtain ⟨t₂, ht₂⟩ := t₂
    cases hτ
    expose_names
    obtain ⟨Γ', ⟨hτ₁, hΓs⟩⟩ := ih (valid_app_l hc) h_1 hσ hΓ (valid_app_l hc')
    use Γ'
    refine ⟨?_, hΓs⟩
    constructor
    · exact hτ₁
    · exact weakening' h hΓs.left
  | AppV v t₂ σ t₂' σ' hc₂ ih =>
    obtain ⟨t₁, ht₁⟩ := v
    obtain ⟨t₂, ht₂⟩ := t₂
    cases hτ
    expose_names
    obtain ⟨Γ', ⟨hτ₂, hΓs⟩⟩ := ih (valid_app_r hc) h hσ hΓ (valid_app_r hc')
    use Γ'
    refine ⟨?_, hΓs⟩
    constructor
    · exact weakening' h_1 hΓs.left
    · exact hτ₂
  | Asgn x t σ t' σ' ht ih =>
    obtain ⟨t, hₜ⟩ := t
    cases hτ
    expose_names
    obtain ⟨Γ', ⟨hτ, hΓs⟩⟩ := ih (valid_asgn hc) h hσ hΓ (valid_asgn hc')
    refine ⟨Γ', ⟨?_, hΓs⟩⟩
    constructor
    · apply (Γ.getVal_iff_getVal? _ _).mpr at h_1
      apply (Γ'.getVal_iff_getVal? _ _).mp
      have ⟨⟨hsub, hs⟩, _⟩ := hΓs
      use hsub h_1.fst
      rw [← hs h_1.fst, h_1.snd]
    · exact hτ
  | AsgnV x v σ =>
    obtain ⟨v, hv⟩ := v
    cases hτ
    expose_names
    refine ⟨Γ, ⟨h, ⟨Store.ext_le_refl, ⟨?_, ?_⟩⟩⟩⟩
    · symm
      simp [Store.dom, hσ]
      have ⟨h', hs⟩ := (Γ.getVal_iff_getVal? _ _).mpr h_1
      exact hσ ▸ h'
    · simp [Store.getVal]
      intro a ha
      have ⟨h', hs⟩ := (Γ.getVal_iff_getVal? _ _).mpr h_1
      split_ifs with hax
      · simpa only [hax, hs]
      · apply hΓ
end Types

#print axioms Types.preservation
