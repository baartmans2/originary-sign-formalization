/-!
# From ostension to symbolic nodes: the basic vocabulary

This file contains **definitions only**. Nothing here is a theorem, and nothing here
names the ostensive, the imperative or the declarative as a *state* of the system.
The scene records three kinds of raw data:

* what was *done* (`deed`): a bodily form was produced, an object was fetched, or nothing;
* where it was done (`ctx`), with physical presence given by `present`;
* how, if at all, someone else *took it up* (`uptake`): as being about a physical object
  (`Target.phys`) or about an earlier act (`Target.occ`).

The modes of language are then *classifications of patterns in this record*
(see the section "Modes as properties of interaction" below).

## What is and is not assumed in advance

* Physical objects `O` exist in advance, and so do participants, contexts and bodily forms.
* Acts are events that happen at times, and `Target.occ t` refers to such an event. That an
  event *can* be attended to is assumption A5 (reflexive uptake). This makes event-referents
  part of the *possibility space*. It does not put any symbolic node into the *graph*: the
  vertices of the graph are only what has actually been taken up in the history
  (`Vertex`), and `Theorems.lean` proves that this set has no non-physical members until a
  declarative has occurred.
* `sim` (contextual recurrence) is an arbitrary relation. It is **not** assumed reflexive,
  symmetric or transitive, so it does not induce abstract sign-types. The emergence model
  uses a non-transitive `sim`.
* `forcing` is an arbitrary predicate. Its nature and origin are unspecified, as requested.
-/

namespace GA

/-- What an act can be taken up as being *about*. -/
inductive Target (O : Type) where
  /-- a physical object, given in advance -/
  | phys : O → Target O
  /-- the act that occurred at time `t`: an event, not an abstract sign -/
  | occ  : Nat → Target O

/-- Raw behaviour. A `sign` records only *who* produced *which bodily form*.
Its meaning is not part of the deed. -/
inductive Deed (P G O : Type) where
  /-- participant produces a bodily form (a gesture, a cry, ...) -/
  | sign  : P → G → Deed P G O
  /-- participant tries to bring a physical object into the context -/
  | fetch : P → O → Deed P G O
  | idle  : Deed P G O

/-- A *scene*: a world (presence and similarity) together with one discrete-time history.
Time is `Nat` and unbounded, so "indefinite repetition" is a meaningful notion. -/
structure Scene (P O C G : Type) where
  /-- physical presence of an object in a context -/
  present : C → O → Prop
  /-- contextual recurrence: the act-in-context `x` is felt to be like `y` (no laws assumed) -/
  sim     : G × C → G × C → Prop
  /-- what is done at each time -/
  deed    : Nat → Deed P G O
  /-- the context at each time -/
  ctx     : Nat → C
  /-- `some (h, τ)`: participant `h` takes the deed at this time as signifying `τ` -/
  uptake  : Nat → Option (P × Target O)
  /-- the unspecified forcing function: `forcing j t` means that at time `t` the participants
  are under compulsion with respect to the relation that was opened at time `j` -/
  forcing : Nat → Nat → Prop

section
variable {P O C G : Type} (S : Scene P O C G)

/-! ## Relations that can hold, fail, be completed or be preserved -/

/-- At time `j`, `a`'s act was taken up by `h` as being about `o`, but `o` is not present:
a *failed* (dangling) signifying relation. -/
def Failure (j : Nat) (a h : P) (o : O) : Prop :=
  (∃ g, S.deed j = .sign a g) ∧ S.uptake j = some (h, .phys o) ∧ ¬ S.present (S.ctx j) o

/-- `h`'s practical action at `k` brings `o` into the next context. -/
def Supplies (k : Nat) (h : P) (o : O) : Prop :=
  S.deed k = .fetch h o ∧ S.present (S.ctx (k+1)) o

/-- `h` produces a form at `k` that `a` takes up as being about the act at `j`. The relation
is kept between the two participants without the object being present. -/
def Preserves (j k : Nat) (a h : P) : Prop :=
  (∃ g, S.deed k = .sign h g) ∧ S.uptake k = some (a, .occ j)

/-- The failure opened at `j` is still unresolved at `t`. -/
def Open (j t : Nat) (a h : P) (o : O) : Prop :=
  Failure S j a h o ∧ ∀ k, j ≤ k → k < t → ¬ Supplies S k h o ∧ ¬ Preserves S j k a h

/-- At `t`, `h` makes an attempt on the open failure `j` that does not succeed: a fetch that
does not bring the object, or a form that is not taken up as being about `j`. -/
def Unsuccessful (j t : Nat) (a h : P) (o : O) : Prop :=
  Open S j t a h o ∧
    ((S.deed t = .fetch h o ∧ ¬ S.present (S.ctx (t+1)) o) ∨
     ((∃ g, S.deed t = .sign h g) ∧ ¬ Preserves S j t a h))

/-! ## Grounds on which an uptake can rest -/

/-- Ostensive grounding: the target is a physical object present in the context. -/
def OstGround (t : Nat) (τ : Target O) : Prop :=
  ∃ o, τ = .phys o ∧ S.present (S.ctx t) o

/-- Recurrence grounding: the form-in-context is like an earlier act that was taken up as
being about the same target. The target is inherited, so it may now be absent. -/
def RecGround (t : Nat) (g : G) (τ : Target O) : Prop :=
  ∃ s, s < t ∧ ∃ a' g' h', S.deed s = .sign a' g' ∧ S.uptake s = some (h', τ) ∧
    S.sim (g, S.ctx t) (g', S.ctx s)

/-- Reflexive grounding (assumption A5): an act by `a`, taken up by `h`, can be about an
earlier act `j` of `h` that `a` heard, *provided that relation is a still-open failure*. -/
def ReflGround (t : Nat) (a h : P) (τ : Target O) : Prop :=
  ∃ j, j < t ∧ τ = .occ j ∧ ∃ o, Open S j t h a o

end

/-! ## The axioms

Axioms 2 and 3 are refined into one grounding condition on uptake. Axiom 4 is split into
compulsion (`forced`) and untenability (`untenable`). Axiom 1 is not stated: it is
*derived* from other-directed recognition (`GA.plurality`). The existential content
("participants *can* ...") is collected in `Nontrivial`. -/

variable {P O C G : Type}

/-- Axioms 2 and 3 without A5. Every uptake is by someone other than the author, of a
produced form, and rests on presence or on recurrence. -/
structure Recognition₀ (S : Scene P O C G) : Prop where
  recog : ∀ t h τ, S.uptake t = some (h, τ) →
    ∃ a g, S.deed t = .sign a g ∧ a ≠ h ∧ (OstGround S t τ ∨ RecGround S t g τ)

/-- Axioms 2 and 3 with A5 (reflexive uptake) added as a third possible ground. -/
structure Recognition (S : Scene P O C G) : Prop where
  recog : ∀ t h τ, S.uptake t = some (h, τ) →
    ∃ a g, S.deed t = .sign a g ∧ a ≠ h ∧
      (OstGround S t τ ∨ RecGround S t g τ ∨ ReflGround S t a h τ)

/-- Axiom 4. While a failure is open and forcing is active, the hearer must *attempt* to
preserve the relation, by fetching the object or by producing a form. Unsuccessful
attempts cannot go on indefinitely. Success is not required. -/
structure ForcedPreservation (S : Scene P O C G) : Prop where
  forced : ∀ j t a h o, j < t → Open S j t a h o → S.forcing j t →
    S.deed t = .fetch h o ∨ ∃ g, S.deed t = .sign h g
  untenable : ∀ j a h o, Failure S j a h o →
    ∃ T, ∀ t, T < t → ¬ Unsuccessful S j t a h o

/-- The user's axioms, refined, without A5. -/
def Admissible₀ (S : Scene P O C G) : Prop := Recognition₀ S ∧ ForcedPreservation S

/-- The refined axioms with A5. -/
def Admissible (S : Scene P O C G) : Prop := Recognition S ∧ ForcedPreservation S

/-- The "participants can ..." clauses. Without these the axioms are satisfied vacuously,
for example by a history in which nothing happens. -/
structure Nontrivial (S : Scene P O C G) : Prop where
  plurality   : ∃ p q : P, p ≠ q
  ostension   : ∃ t h o, S.uptake t = some (h, .phys o) ∧ S.present (S.ctx t) o
  recurrenceInAbsence : ∃ j a h o, Failure S j a h o
  forcingBites : ∃ j t a h o, j < t ∧ Open S j t a h o ∧ S.forcing j t

/-! ## Modes as properties of interaction (definitions) -/

section
variable (S : Scene P O C G)

/-- Ostensive: an uptake whose physical target is present. -/
def Ostensive (t : Nat) (o : O) : Prop :=
  ∃ h, S.uptake t = some (h, .phys o) ∧ S.present (S.ctx t) o

/-- Imperative attempt: the hearer of a failure tries to supply the object. -/
def ImperativeAttempt (j k : Nat) : Prop :=
  ∃ a h o, Failure S j a h o ∧ j < k ∧ Open S j k a h o ∧ S.deed k = .fetch h o

/-- Imperative satisfied: the hearer of a failure supplies the object. -/
def ImperativeSatisfied (j k : Nat) : Prop :=
  ∃ a h o, Failure S j a h o ∧ j ≤ k ∧ Supplies S k h o

/-- Declarative act: an uptake whose target is an act rather than a physical object. -/
def Declarative (t : Nat) : Prop :=
  ∃ h j, S.uptake t = some (h, .occ j)

/-- Originary declarative: an open (unsatisfied) failure is preserved symbolically. -/
def OriginaryDeclarative (j k : Nat) : Prop :=
  ∃ a h o, Open S j k a h o ∧ Preserves S j k a h

/-- The chain of recurrence links ("this is like that") through which a sign descends.
It is a chain of local similarities, not membership in an abstract type. -/
inductive Lineage : Nat → Nat → Prop where
  | refl (t : Nat) : Lineage t t
  | echo {s u t : Nat} : Lineage s u → u < t →
      (∃ a g a' g', S.deed t = .sign a g ∧ S.deed u = .sign a' g' ∧
        S.sim (g, S.ctx t) (g', S.ctx u)) →
      Lineage s t

/-! ## The graph produced by the interaction (definitions) -/

/-- `v` is a vertex by time `n` if someone has actually taken something up as being about `v`. -/
def Vertex (n : Nat) (v : Target O) : Prop :=
  ∃ t h, t < n ∧ S.uptake t = some (h, v)

/-- Not a physical object. -/
def Symbolic (v : Target O) : Prop := ∀ o, v ≠ .phys o

def SymbolicNode (n : Nat) (v : Target O) : Prop := Vertex S n v ∧ Symbolic v

/-- An arc between vertices. A vertex that is itself a recognized act points to what that
act was about. This is the only way one vertex can be joined to another, so arcs exist
only once an act (a relation) has itself become a vertex, i.e. has been reified. -/
def Arc (n : Nat) (v w : Target O) : Prop :=
  Vertex S n v ∧ ∃ t h, v = .occ t ∧ t < n ∧ S.uptake t = some (h, w)

/-- Independently representable: a symbolic node that stands for an absent object and is
taken up in two different contexts, in neither of which the object is present. -/
def Independent (n : Nat) (v : Target O) : Prop :=
  SymbolicNode S n v ∧
  ∃ t₁ t₂ h₁ h₂ o, t₁ < n ∧ t₂ < n ∧ S.ctx t₁ ≠ S.ctx t₂ ∧
    S.uptake t₁ = some (h₁, v) ∧ S.uptake t₂ = some (h₂, v) ∧
    Arc S n v (.phys o) ∧ ¬ S.present (S.ctx t₁) o ∧ ¬ S.present (S.ctx t₂) o

end

end GA
