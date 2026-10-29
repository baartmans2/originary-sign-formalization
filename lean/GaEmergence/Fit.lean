import GaEmergence.Completion

/-!
# Direction of fit, and the redirected interdiction

Gans (as described in our discussion): the hearer cannot bring the object, so the
imperative "bring it" becomes "don't be present", addressed to the object. That command is
already fulfilled, because the object is absent. The declarative is an imperative obeyed
by the world as it already is.

This file makes that precise in the completion-based system:
* each mode gets a **satisfaction condition**;
* the imperative is **unsatisfied when made** and can be satisfied only by a change in the
  world (world-to-sign fit);
* a pure declarative is **satisfied when made** (sign-to-world fit). This follows from
  `salience`, so it depends on the kinematics axiom, and `fit_needs_kinematics` shows the
  dependence is real;
* **the interdiction is redirected**: in the ostensive the participants refrain from a
  present object; in the declarative the object "refrains" from presence;
* **an absent object can be addressed only through a sign** that descends from it, i.e. a
  node.
-/

namespace GA.Completion

set_option linter.constructorNameAsVariable false

variable {P O M : Type} (W : World P O M)

/-- A pure declarative on a gesture whose onset echoes a reach for `o`. -/
def PureDeclOn (t t' s : Nat) (r p q : P) (o : O) : Prop :=
  Declarative W t t' s r p q ∧ Pure W t p ∧ Pure W t' q ∧
  ∃ s0 r0 m0, s0 < t ∧ W.mv s0 r0 = some m0 ∧ W.heads s0 r0 o ∧
    (∃ m', W.mv t p = some m' ∧ W.opens m' m0) ∧
    (∃ m'', W.mv t' q = some m'' ∧ W.opens m'' m0)

/-- The imperative is satisfied when the object comes within the mover's reach. -/
def ImpSatisfiedAt (a : P) (o : O) (t : Nat) : Prop := W.within t a o

/-- The declarative's "don't be present" is satisfied when the object is out of reach. -/
def DeclSatisfiedAt (p : P) (o : O) (t : Nat) : Prop := ¬ W.within t p o

/-! ## Direction of fit -/

/-- **The imperative is unsatisfied when made.** (Definitional: the imperative is about an
object out of the mover's reach.) -/
theorem imperative_unsatisfied_when_made {t : Nat} {a h : P} {o : O}
    (hI : Imperative W t a h o) : ¬ ImpSatisfiedAt W a o t := hI.2

/-- **World-to-sign fit.** Satisfying an imperative requires the world to change: the
object goes from out of reach to within reach. -/
theorem imperative_needs_change {t t'' : Nat} {a h : P} {o : O}
    (hI : Imperative W t a h o) (hs : ImpSatisfiedAt W a o t'') :
    t'' ≠ t ∧ ¬ W.within t a o ∧ W.within t'' a o :=
  ⟨fun e => by subst e; exact hI.2 hs, hI.2, hs⟩

/-- **Sign-to-world fit.** A pure declarative's "don't be present" is fulfilled at the
moment it is made, for both participants. (Uses kinematics.) -/
theorem declarative_satisfied_when_made (hK : Kinematics W) {t t' s : Nat} {r p q : P}
    {o : O} (hD : PureDeclOn W t t' s r p q o) :
    DeclSatisfiedAt W p o t ∧ DeclSatisfiedAt W q o t' := by
  obtain ⟨hd, hp, hq, s0, r0, m0, hs0, hm0, hh0, hop, hoq⟩ := hD
  exact salience W hK hd hp hq hs0 hm0 hh0 hop hoq

/-! ## The interdiction redirected -/

/-- **Ostensive: we refrain.** In an ostensive the object is within both participants'
reach, and neither completes. -/
theorem ostensive_we_refrain (hA : Axioms W) {t t' : Nat} {o : O} {p q : P}
    (h : Ostensive W t t' o p q) :
    (W.within t p o ∧ ¬ W.contact (t+1) p o) ∧ (W.within t' q o ∧ ¬ W.contact (t'+1) q o) :=
  ⟨⟨hA.heads_within _ _ _ h.1.2.2.2.1.1, h.1.2.2.2.1.2⟩,
   ⟨hA.heads_within _ _ _ h.1.2.2.2.2.1.1, h.1.2.2.2.2.1.2⟩⟩

/-- **The same interdiction, redirected.** In an ostensive, the participants hold back
from a present object. In a pure declarative descended from a reach, the object is held
back from presence. -/
theorem interdiction_redirected (hA : Axioms W) (hK : Kinematics W)
    {t t' u u' s : Nat} {o : O} {p q p' q' r : P}
    (hO : Ostensive W t t' o p q) (hD : PureDeclOn W u u' s r p' q' o) :
    (W.within t p o ∧ W.within t' q o) ∧ (¬ W.within u p' o ∧ ¬ W.within u' q' o) :=
  ⟨⟨(ostensive_we_refrain W hA hO).1.1, (ostensive_we_refrain W hA hO).2.1⟩,
   declarative_satisfied_when_made W hK hD⟩

/-! ## Addressing an absent object -/

/-- Being about `o`: directly, or by taking up a movement that descends from `o`. -/
def AboutObject (t : Nat) (a h : P) (o : O) : Prop :=
  Takes W t a h (.obj o) ∨ ∃ s r, Takes W t a h (.act s r) ∧ Descends W s r o

/-- **An absent object can be addressed only through a sign.** If `o` is out of the
responder's reach throughout the response window, the only way to be about `o` is to take
up a movement that descends from `o`. -/
theorem absent_only_through_sign (hA : Axioms W) {t : Nat} {a h : P} {o : O}
    (hab : AboutObject W t a h o)
    (hun : ∀ t', t < t' → t' ≤ t + W.win → ¬ W.within t' h o) :
    ∃ s r, Takes W t a h (.act s r) ∧ Descends W s r o := by
  rcases hab with hT | hsign
  · obtain ⟨t', h1, h2, hw⟩ := takes_object_within W hA hT
    exact absurd hw (hun t' h1 h2)
  · exact hsign

/-! ## The models -/

open GA.Models

namespace E

theorem imperative_unsatisfied6 : ¬ ImpSatisfiedAt E.W .a .hammer 6 :=
  imperative_unsatisfied_when_made E.W E.imperative6

theorem imperative_satisfied8 : ImpSatisfiedAt E.W .a .hammer 8 := by
  simp [ImpSatisfiedAt, E.W]

theorem pureDecl : PureDeclOn E.W 11 12 10 .a .b .a .hammer :=
  ⟨E.declarative11, E.pure11, E.pure12, 0, .a, .g0, by omega, rfl, by simp [E.W, E.headsL],
    ⟨.g2, rfl, rfl⟩, ⟨.g2, rfl, rfl⟩⟩

/-- At t10, `b` is about the hammer only through the sign. -/
theorem about_through_sign : AboutObject E.W 10 .a .b .hammer ∧
    ¬ Takes E.W 10 .a .b (.obj .hammer) :=
  ⟨Or.inr ⟨10, .a, E.takes10, E.descends10⟩, E.no_imperative10⟩

end E

/-- **Without kinematics, the "already fulfilled" claim fails.** There is a pure
declarative on a gesture echoing a reach for the hammer, made while the hammer is
within reach: its "don't be present" is not fulfilled. -/
theorem fit_needs_kinematics :
    ∃ (W : World Pt Ob Fm), Axioms W ∧ ¬ Kinematics W ∧
      PureDeclOn W 1 2 0 .a .b .a .hammer ∧
      ¬ DeclSatisfiedAt W .b .hammer 1 ∧ ¬ DeclSatisfiedAt W .a .hammer 2 := by
  obtain ⟨hd, hp, hq, hw1, hw2⟩ := NoTransfer.declarative_in_presence
  exact ⟨NoTransfer.W, NoTransfer.axioms, NoTransfer.not_kinematics,
    ⟨hd, hp, hq, 0, .a, .g0, by omega, rfl, rfl, ⟨.g2, rfl, rfl⟩, ⟨.g2, rfl, rfl⟩⟩,
    fun h => h hw1, fun h => h hw2⟩

/-- **Direction of fit, exhibited.** In the emergence model:
* the imperative at t6 is unsatisfied when made and satisfied at t8, after the world changed;
* the pure declarative at t11–t12 is satisfied when made. -/
theorem direction_of_fit :
    ∃ (W : World Pt Ob Fm), Axioms W ∧ Kinematics W ∧
      Imperative W 6 .a .b .hammer ∧ ¬ ImpSatisfiedAt W .a .hammer 6 ∧
      ImpSatisfiedAt W .a .hammer 8 ∧
      PureDeclOn W 11 12 10 .a .b .a .hammer ∧
      DeclSatisfiedAt W .b .hammer 11 ∧ DeclSatisfiedAt W .a .hammer 12 :=
  ⟨E.W, E.axioms, E.kinematics, E.imperative6, E.imperative_unsatisfied6,
    E.imperative_satisfied8, E.pureDecl,
    (declarative_satisfied_when_made E.W E.kinematics E.pureDecl).1,
    (declarative_satisfied_when_made E.W E.kinematics E.pureDecl).2⟩

end GA.Completion
