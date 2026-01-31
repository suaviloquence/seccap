import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finset.Defs

instance Option.instZero {α} : Zero (Option α) := ⟨none⟩

abbrev Finmap α β := α →₀ Option β


lemma Finmap.mem_support_is_some {α β} (f : Finmap α β) :
    ∀ a, a ∈ f.support ↔ (f a).isSome := by
    intro a
    rw [Option.isSome_iff_ne_none]
    exact f.mem_support_iff

def Finmap.get {α β} (f : Finmap α β) x (h : x ∈ f.support) :=
  (f x).get ((f.mem_support_is_some x).mp h)

def Finmap.insert {α β} [DecidableEq α] (f: Finmap α β) (x: α) (y: β): Finmap α β :=
  ⟨f.support ∪ {x}, fun x' => if x' = x then y else f x', (by
        intro x
        simp
        constructor
        · intro H
          split_ifs with h'
          · simp
          · exact H.resolve_left h'
        · intro H
          split_ifs at H with h'
          · left; assumption
          · right; assumption
  ) ⟩

@[simp]
lemma Finmap.insert_dom {α β} [DecidableEq α] (f : Finmap α β) x y:
    (f.insert x y).support = f.support ∪ {x} := by
    simp [insert]
