import GaEmergence.Behaviour

/-!
# The center: why the first shared relation is "reach and hold back"

Two participants are directed at the same object (a *center*). For their relation to it to
be *shared*, each must stand in the same relation to the object: either both complete the
appropriation or neither does. Appropriation is exclusive: if both complete, they clash,
and a clash is a fight, not a shared relation. So the only peaceful shared relation to a
center is that both are directed at it and neither completes. That is exactly
`JointDeferral`.

**Limit.** `aim` is generic: any movement directed at an object counts, whether a reach, a
gaze or a point. The theorem therefore shows the necessity of *a shared, unappropriated
center*, not of *reaching* specifically. Reaching follows only if the participants'
directedness is appropriative, i.e. if their aimed movements are attempts to get.
-/

namespace GA.Behavioural

variable {P O C G : Type} (S : BScene P O C G)

/-- `p` and `q` are both directed at `o` and stand in the same relation to it
(the same completion status). -/
def SameRelation (t : Nat) (o : O) (p q : P) : Prop :=
  Reaches S t p o ∧ Reaches S t q o ∧ (Grasps S (t+1) p o ↔ Grasps S (t+1) q o)

/-- `p` and `q` both appropriate `o` at once. -/
def ClashBetween (t : Nat) (o : O) (p q : P) : Prop :=
  Grasps S t p o ∧ Grasps S t q o

/-- **The center theorem.** For two participants, joint deferral is *exactly* a shared,
peaceful relation to a common center. No mimesis, exhaustion or forcing is used. -/
theorem joint_deferral_iff_shared_peaceful (t : Nat) (o : O) (p q : P) :
    JointDeferral S t o p q ↔
      p ≠ q ∧ SameRelation S t o p q ∧ ¬ ClashBetween S (t+1) o p q := by
  constructor
  · rintro ⟨⟨hne, hp, hq⟩, hnp, hnq⟩
    exact ⟨hne, ⟨hp, hq, ⟨fun h => absurd h hnp, fun h => absurd h hnq⟩⟩,
      fun ⟨h, _⟩ => hnp h⟩
  · rintro ⟨hne, ⟨hp, hq, hiff⟩, hnc⟩
    have hnp : ¬ Grasps S (t+1) p o := fun h => hnc ⟨h, hiff.mp h⟩
    exact ⟨⟨hne, hp, hq⟩, hnp, fun h => hnp (hiff.mpr h)⟩

/-- The other ways two participants can be directed at one center are each *not* shared
or *not* peaceful: one takes it (different relations), or both take it (a clash). -/
theorem center_alternatives {t : Nat} {o : O} {p q : P}
    (hp : Reaches S t p o) (hq : Reaches S t q o) :
    JointDeferral S t o p q ∨ p = q ∨
      (Grasps S (t+1) p o ∧ ¬ Grasps S (t+1) q o) ∨
      (¬ Grasps S (t+1) p o ∧ Grasps S (t+1) q o) ∨
      ClashBetween S (t+1) o p q := by
  by_cases hne : p = q
  · exact Or.inr (Or.inl hne)
  by_cases hgp : Grasps S (t+1) p o <;> by_cases hgq : Grasps S (t+1) q o
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hgp, hgq⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨hgp, hgq⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hgp, hgq⟩)))
  · exact Or.inl ⟨⟨hne, hp, hq⟩, hgp, hgq⟩

end GA.Behavioural
