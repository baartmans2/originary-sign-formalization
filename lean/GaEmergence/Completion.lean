import GaEmergence.Models

/-!
# The completion-based system

A self-contained formalization of the revised axioms.

**Primitives** (fields of `World`):
* movement forms, with `opens m' m` (m' begins like m: its onset matches) and
  `sim m' m` (m' fully matches m);
* `mv t p`: the form of p's movement at t, if p moves;
* `heads t p o`: p's movement at t, continued, would end in contact with o;
* `contact t p o`: p is in contact with o;
* `within t p o`: o is within p's reach at t (this is all "presence" means);
* `perceives t q p`: q perceives p's movement at t (first-order only);
* `win`: the response window;
* `retained t p`: the unspecified retention function.

**Axioms** (`Axioms`): heading is physical (it needs reach and a movement), completion
completes a heading, perception is of another's actual movement, form-matching is a
tolerance relation that implies onset-matching, and retention yields a later similar
movement. `Kinematics` is a further axiom, kept separate because it was *discovered*
during formalization (see `salience`).

**Definitions:**
* one notion of directedness covering two kinds of target: an object (pending contact)
  or an earlier movement (pending match);
* taking-as by the response principle;
* one notion of center (`Joint`), with firstness: one participant is suspended first and
  the other, in response, strictly later;
* dependent response (`Dependent`): regularity across episodes, plus a contrast case. The
  ostensive is a center on an object with a dependent response; the declarative is a center
  on a movement with a dependent response;
* content by lineage (`Descends`).

There is no appropriation, rivalry, clash, mimesis, exhaustion, forcing, or sparagmos.
-/

namespace GA.Completion

set_option linter.constructorNameAsVariable false

/-- A target: a physical object, or the movement made by participant `r` at time `s`. -/
inductive Tgt (P O : Type) where
  | obj : O → Tgt P O
  | act : Nat → P → Tgt P O

structure World (P O M : Type) where
  opens     : M → M → Prop
  sim       : M → M → Prop
  mv        : Nat → P → Option M
  heads     : Nat → P → O → Prop
  contact   : Nat → P → O → Prop
  within    : Nat → P → O → Prop
  perceives : Nat → P → P → Prop
  win       : Nat
  retained  : Nat → P → Prop

variable {P O M : Type}

structure Axioms (W : World P O M) : Prop where
  /-- a movement can head only toward what is within reach -/
  heads_within : ∀ t p o, W.heads t p o → W.within t p o
  /-- only a movement can head toward anything -/
  heads_moving : ∀ t p o, W.heads t p o → ∃ m, W.mv t p = some m
  /-- completion completes a heading -/
  contact_heads : ∀ t p o, W.contact (t+1) p o → W.heads t p o
  /-- perception is of another participant's actual movement (first-order) -/
  perceives_other : ∀ t q p, W.perceives t q p → q ≠ p ∧ ∃ m, W.mv t p = some m
  /-- form-matching is a tolerance relation: reflexive, symmetric, not assumed transitive -/
  sim_refl : ∀ m, W.sim m m
  sim_symm : ∀ m m', W.sim m m' → W.sim m' m
  /-- a full match also begins like the model -/
  sim_opens : ∀ m m', W.sim m' m → W.opens m' m
  /-- retention (unspecified): a retained movement recurs, in a similar form -/
  retention : ∀ t p, W.retained t p →
    ∃ t' m m', t < t' ∧ W.mv t p = some m ∧ W.mv t' p = some m' ∧ W.sim m' m

/-- **Kinematic transfer** (discovered during formalization). A movement that begins like
one that headed toward `o`, made where `o` is within reach, also heads toward `o`.
Reproducing a reach where the object is reachable reaches it. -/
structure Kinematics (W : World P O M) : Prop where
  transfer : ∀ s t r p o m m', s < t → W.mv s r = some m → W.heads s r o →
    W.mv t p = some m' → W.opens m' m → W.within t p o → W.heads t p o

section
variable (W : World P O M)

/-- Directedness = a pending completion: contact with an object, or a match with a movement. -/
def DirectedAt (t : Nat) (p : P) : Tgt P O → Prop
  | .obj o => W.heads t p o
  | .act s r => s < t ∧ ∃ m m', W.mv s r = some m ∧ W.mv t p = some m' ∧ W.opens m' m

/-- Completion: contact, or a full match. -/
def Completes (t : Nat) (p : P) : Tgt P O → Prop
  | .obj o => W.contact (t+1) p o
  | .act s r => ∃ m m', W.mv s r = some m ∧ W.mv t p = some m' ∧ W.sim m' m

def Suspended (t : Nat) (p : P) (τ : Tgt P O) : Prop :=
  DirectedAt W t p τ ∧ ¬ Completes W t p τ

/-- `h`'s movement at `t'` is a response to `a`'s at `t`: `h` perceived it, and `t'`
falls within the window. -/
def Responds (t' : Nat) (h : P) (t : Nat) (a : P) : Prop :=
  W.perceives t h a ∧ t < t' ∧ t' ≤ t + W.win

/-- **The response principle.** `h` takes `a`'s movement at `t` as being about `τ` when
`h` responds with a movement directed at `τ`. -/
def Takes (t : Nat) (a h : P) (τ : Tgt P O) : Prop :=
  ∃ t', Responds W t' h t a ∧ DirectedAt W t' h τ

/-- **A center, with firstness.** `p` is suspended toward a target first. `q`, having
perceived it, is suspended toward the same target strictly later, within the window, and
`p` perceives that. The second suspension is a response to the first. -/
def Joint (t t' : Nat) (τ : Tgt P O) (p q : P) : Prop :=
  p ≠ q ∧ t < t' ∧ t' ≤ t + W.win ∧ Suspended W t p τ ∧ Suspended W t' q τ ∧
    W.perceives t q p ∧ W.perceives t' p q

/-- `q` had the opportunity to respond about `τ` just after `u`: for an object, it was
within `q`'s reach within the window; for a movement, that movement had already occurred. -/
def Opportunity (u : Nat) (q : P) : Tgt P O → Prop
  | .obj o => ∃ u', u < u' ∧ u' ≤ u + W.win ∧ W.within u' q o
  | .act s _ => s < u

/-- `p`'s movements at `t` and `t2` are of the same kind (the later fully matches the earlier). -/
def SameKind (t t2 : Nat) (p : P) : Prop :=
  ∃ m m2, W.mv t p = some m ∧ W.mv t2 p = some m2 ∧ W.sim m2 m

/-- **Dependent response: regularity with contrast.** `q`'s suspended response to `p`'s
movement at `t` is a real response if
* *regularity*: there is another such episode, at a different time, in which `p` makes the
  same kind of movement and `q` responds in the same way;
* *contrast*: there is a time `u` at which `q` had the opportunity, `p` made no movement of
  that kind, and `q` did not respond. -/
def Dependent (t : Nat) (τ : Tgt P O) (p q : P) : Prop :=
  (∃ t2 t2', t2 ≠ t ∧ Joint W t2 t2' τ p q ∧ SameKind W t t2 p) ∧
  (∃ u, Opportunity W u q τ ∧ ¬ SameKind W t u p ∧
    ∀ u', u < u' → u' ≤ u + W.win → ¬ Suspended W u' q τ)

/-- The ostensive: a center on an object, with a dependent response. -/
def Ostensive (t t' : Nat) (o : O) (p q : P) : Prop :=
  Joint W t t' (.obj o) p q ∧ Dependent W t (.obj o) p q

/-- The declarative: a center on a movement, with a dependent response. Same definition,
different target. -/
def Declarative (t t' s : Nat) (r p q : P) : Prop :=
  Joint W t t' (.act s r) p q ∧ Dependent W t (.act s r) p q

/-- The imperative: a movement taken as being about an object that is out of the mover's reach. -/
def Imperative (t : Nat) (a h : P) (o : O) : Prop :=
  Takes W t a h (.obj o) ∧ ¬ W.within t a o

/-- A movement directed at no object. -/
def Pure (t : Nat) (p : P) : Prop := ∀ o, ¬ W.heads t p o

/-- **Content by lineage.** A movement descends from an object if it is the *first*
movement of an ostensive center on that object (the sign; the second is its uptake), or
fully matches an earlier movement that descends from it. -/
inductive Descends : Nat → P → O → Prop where
  | root  {s t' : Nat} {p q : P} {o : O} : Ostensive W s t' o p q → Descends s p o
  | step  {s t : Nat} {r p : P} {o : O} {m m' : M} :
      s < t → W.mv s r = some m → W.mv t p = some m' → W.sim m' m →
      Descends s r o → Descends t p o

/-- A symbolic node: a movement that has become the target of a center. -/
def SymbolicNode (s : Nat) (r : P) : Prop := ∃ t t' p q, Declarative W t t' s r p q

/-- An arc from a symbolic node to the object it stands for (by lineage). -/
def Arc (s : Nat) (r : P) (o : O) : Prop := SymbolicNode W s r ∧ Descends W s r o

end

/-! ## Derivations (they hold in every world satisfying the axioms) -/

section
variable (W : World P O M)

/-- Centers need two participants. -/
theorem plurality {t t' : Nat} {τ : Tgt P O} {p q : P} (h : Joint W t t' τ p q) : p ≠ q := h.1

/-- **A center is a taking-as whose response is suspended**, together with the first
participant perceiving that response. The center is no longer a separate notion. -/
theorem joint_iff_suspended_taking (t t' : Nat) (τ : Tgt P O) (p q : P) :
    Joint W t t' τ p q ↔
      p ≠ q ∧ Suspended W t p τ ∧ Responds W t' q t p ∧ Suspended W t' q τ ∧
        W.perceives t' p q := by
  constructor
  · rintro ⟨hne, hlt, hwin, hsp, hsq, hpq, hqp⟩
    exact ⟨hne, hsp, ⟨hpq, hlt, hwin⟩, hsq, hqp⟩
  · rintro ⟨hne, hsp, ⟨hpq, hlt, hwin⟩, hsq, hqp⟩
    exact ⟨hne, hlt, hwin, hsp, hsq, hpq, hqp⟩

/-- In every center, the second participant takes the first's movement as being about
the target. -/
theorem center_takes {t t' : Nat} {τ : Tgt P O} {p q : P} (h : Joint W t t' τ p q) :
    Takes W t p q τ :=
  ⟨t', ⟨h.2.2.2.2.2.1, h.2.1, h.2.2.1⟩, h.2.2.2.2.1.1⟩

/-- **Coincidence is not a sign.** In a simultaneous stop nobody responds to anybody. -/
theorem simultaneous_no_response (t : Nat) (p q : P) : ¬ Responds W t q t p :=
  fun h => Nat.lt_irrefl t h.2.1

/-- A simultaneous joint stop is not a center. -/
theorem simultaneous_not_center (t : Nat) (τ : Tgt P O) (p q : P) : ¬ Joint W t t τ p q :=
  fun h => Nat.lt_irrefl t h.2.1

/-- **A one-off coincidence is not a sign.** If there is no other episode, the response
is not dependent. -/
theorem coincidence_not_dependent {t : Nat} {τ : Tgt P O} {p q : P}
    (honce : ∀ t2 t2', Joint W t2 t2' τ p q → t2 = t) : ¬ Dependent W t τ p q :=
  fun ⟨⟨t2, t2', hne, hj, _⟩, _⟩ => hne (honce t2 t2' hj)

/-- **An indiscriminate responder is not responding to the sign.** If `q` holds back
toward `τ` whenever it has the opportunity, regardless of `p`, there is no contrast. -/
theorem indiscriminate_not_dependent {t : Nat} {τ : Tgt P O} {p q : P}
    (hall : ∀ u, Opportunity W u q τ → ∃ u', u < u' ∧ u' ≤ u + W.win ∧ Suspended W u' q τ) :
    ¬ Dependent W t τ p q := by
  rintro ⟨_, u, hopp, _, hno⟩
  obtain ⟨u', h1, h2, hs⟩ := hall u hopp
  exact hno u' h1 h2 hs

/-- **Completion ends aboutness.** This was an axiom; it is now a consequence of the definitions. -/
theorem completion_ends_aboutness {t : Nat} {p : P} {τ : Tgt P O}
    (h : Completes W t p τ) : ¬ Suspended W t p τ := fun hs => hs.2 h

/-- The comment of every declarative is "not carried through": neither participant fully
reproduces the movement. -/
theorem declarative_unfinished {t t' s : Nat} {r p q : P} (h : Declarative W t t' s r p q) :
    ¬ Completes W t p (.act s r) ∧ ¬ Completes W t' q (.act s r) :=
  ⟨h.1.2.2.2.1.2, h.1.2.2.2.2.1.2⟩

/-- **The misfire is aimless.** A movement made where its object is out of reach is not
directed at that object. -/
theorem aimless_in_absence (hA : Axioms W) {t : Nat} {a : P} {o : O}
    (h : ¬ W.within t a o) : ¬ DirectedAt W t a (.obj o) :=
  fun hd => h (hA.heads_within _ _ _ hd)

/-- **The imperative's form is derived.** Taking a movement as being about an object
requires a response made where that object is within the responder's reach. If the object
is out of the mover's reach, the responder has to be where the object is. -/
theorem takes_object_within (hA : Axioms W) {t : Nat} {a h : P} {o : O}
    (hT : Takes W t a h (.obj o)) : ∃ t', t < t' ∧ t' ≤ t + W.win ∧ W.within t' h o := by
  obtain ⟨t', ⟨_, h1, h2⟩, hd⟩ := hT
  exact ⟨t', h1, h2, hA.heads_within _ _ _ hd⟩

/-- **When nothing can be reached, only movements can be targets.** If no object is
within the responder's reach during the window, whatever the responder takes the movement
as being about is a movement. This is the declarative's target, derived from physics. -/
theorem unreachable_only_acts (hA : Axioms W) {t : Nat} {a h : P} {τ : Tgt P O}
    (hT : Takes W t a h τ)
    (hun : ∀ t' o, t < t' → t' ≤ t + W.win → ¬ W.within t' h o) :
    ∃ s r, τ = .act s r := by
  cases τ with
  | obj o =>
    obtain ⟨t', h1, h2, hw⟩ := takes_object_within W hA hT
    exact absurd hw (hun t' o h1 h2)
  | act s r => exact ⟨s, r, rfl⟩

/-- **What a sign stands for was once within reach.** Every object a movement descends
from was within someone's reach at or before that movement. -/
theorem content_was_present (hA : Axioms W) {t : Nat} {p : P} {o : O}
    (hD : Descends W t p o) : ∃ s q, s ≤ t ∧ W.within s q o := by
  induction hD with
  | root hj => exact ⟨_, _, Nat.le_refl _, hA.heads_within _ _ _ hj.1.2.2.2.1.1⟩
  | step hst _ _ _ _ ih =>
    obtain ⟨s', q, h1, h2⟩ := ih
    exact ⟨s', q, by omega, h2⟩

/-- **Salience is derived (given kinematics).** If a center on a movement echoes the onset
of a movement that headed toward `o`, and neither participant is directed at any object
(the attention is purely to the movement), then `o` is out of both participants' reach.
Pure attention to a gesture is possible only in the object's absence. -/
theorem salience (hK : Kinematics W) {t t' s : Nat} {r p q : P} {o : O}
    (hD : Declarative W t t' s r p q) (hp : Pure W t p) (hq : Pure W t' q)
    {s0 : Nat} {r0 : P} {m0 : M} (hs0 : s0 < t) (hm0 : W.mv s0 r0 = some m0)
    (hh0 : W.heads s0 r0 o)
    (hop : ∃ m', W.mv t p = some m' ∧ W.opens m' m0)
    (hoq : ∃ m'', W.mv t' q = some m'' ∧ W.opens m'' m0) :
    ¬ W.within t p o ∧ ¬ W.within t' q o := by
  obtain ⟨⟨_, htt', _⟩, _⟩ := hD
  obtain ⟨m', hm', ho'⟩ := hop
  obtain ⟨m'', hm'', ho''⟩ := hoq
  exact ⟨fun hw => hp o (hK.transfer _ _ _ _ _ _ _ hs0 hm0 hh0 hm' ho' hw),
    fun hw => hq o (hK.transfer _ _ _ _ _ _ _ (by omega) hm0 hh0 hm'' ho'' hw)⟩

/-- **Without recurrence, no symbolic nodes.** If no movement ever begins like an earlier
one, nothing can be directed at a movement, so there are no declaratives. -/
theorem no_recurrence_no_symbol
    (hno : ∀ s t r p m m', s < t → W.mv s r = some m → W.mv t p = some m' → ¬ W.opens m' m)
    (s : Nat) (r : P) : ¬ SymbolicNode W s r := by
  rintro ⟨t, t', p, q, ⟨_, _, _, ⟨⟨hst, m, m', hm, hm', ho⟩, _⟩, _⟩, _⟩
  exact hno _ _ _ _ _ _ hst hm hm' ho

end

/-! ## Models -/

open GA.Models

inductive Fm | g0 | g1 | g2 | g3 | g4 deriving DecidableEq

/-- Full match. g0 ~ g1 ~ g3, but not g0 ~ g3: tolerance, not transitive. -/
def simF : Fm → Fm → Bool
  | .g0, .g0 | .g1, .g1 | .g2, .g2 | .g3, .g3 | .g4, .g4 => true
  | .g0, .g1 | .g1, .g0 | .g1, .g3 | .g3, .g1 => true
  | _, _ => false

/-- Onset match. g2 is the gesture begun and broken off: it opens g0 and g1, matching neither. -/
def opensF : Fm → Fm → Bool
  | .g2, .g0 | .g2, .g1 => true
  | x, y => simF x y

theorem simF_refl (m : Fm) : simF m m = true := by cases m <;> rfl
theorem simF_symm (m m' : Fm) (h : simF m m' = true) : simF m' m = true := by
  cases m <;> cases m' <;> simp [simF] at h ⊢
theorem simF_opens (m m' : Fm) (h : simF m' m = true) : opensF m' m = true := by
  cases m <;> cases m' <;> simp [simF, opensF] at h ⊢
theorem opens_not_sim (m m' : Fm) (h1 : opensF m' m = true) (h2 : ¬ simF m' m = true) :
    m' = .g2 := by
  cases m <;> cases m' <;> simp [simF, opensF] at h1 h2 ⊢

/-! ### The emergence model -/

/-- A movement table as a list, with lookup. (Large literal pattern matches are slow to
compile; a list is not.) -/
def look {M : Type} : List ((Nat × Pt) × M) → Nat → Pt → Option M
  | [], _, _ => none
  | ((t', p'), m) :: rest, t, p => if t = t' ∧ p = p' then some m else look rest t p

theorem look_mem {M : Type} {l : List ((Nat × Pt) × M)} {t : Nat} {p : Pt} {m : M}
    (h : look l t p = some m) : ((t, p), m) ∈ l := by
  induction l with
  | nil => simp [look] at h
  | cons hd rest ih =>
    obtain ⟨⟨t', p'⟩, m'⟩ := hd
    simp only [look] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      exact List.mem_cons_self _ _
    · exact List.mem_cons_of_mem _ (ih h)

namespace E

/-- Two ostensive episodes, with a contrast in between:
* t0: `a` reaches for the hammer (g0) and holds back; `b` sees it. t1: `b`, in response, does the same; `a` sees it.
* t2–t3 (contrast): the hammer is within reach, `a` doesn't reach, and `b` doesn't hold back toward it.
* t4, t5: the same episode again.

Then the imperative:
* t6: the hammer is gone; `a` makes g1 (~ g0); `b` sees it.
* t7: `b`, where the hammer is, heads for it.
* t8: the hammer is within `a`'s reach (satisfied).

Then two declarative episodes, with a contrast, on `a`'s movement at t10. The hammer is out of everyone's reach from t9 on.
* t10: `a` makes g1 again; `b` sees it.
* t11: `b` begins the gesture and breaks it off (g2); `a` sees it. t12: `a` does the same; `b` sees it.
* t13–t14 (contrast): `b` doesn't make g2, and `a` doesn't echo.
* t15, t16: the declarative episode again. -/
def mvL : List ((Nat × Pt) × Fm) :=
  [((0, .a), .g0), ((1, .b), .g0), ((4, .a), .g0), ((5, .b), .g0), ((6, .a), .g1),
   ((7, .b), .g4), ((10, .a), .g1), ((11, .b), .g2), ((12, .a), .g2), ((15, .b), .g2),
   ((16, .a), .g2)]

def mv (t : Nat) (p : Pt) : Option Fm := look mvL t p

def headsL : List (Nat × Pt) := [(0, .a), (1, .b), (4, .a), (5, .b), (7, .b)]
def percL : List (Nat × Pt × Pt) :=
  [(0, .b, .a), (1, .a, .b), (4, .b, .a), (5, .a, .b), (6, .b, .a), (10, .b, .a),
   (11, .a, .b), (12, .b, .a), (15, .a, .b), (16, .b, .a)]

def W : World Pt Ob Fm where
  opens x y := opensF x y = true
  sim x y := simF x y = true
  mv := mv
  heads t p _ := (t, p) ∈ headsL
  contact _ _ _ := False
  within t p _ := t ≤ 5 ∨ (t = 7 ∧ p = .b) ∨ (t = 8 ∧ p = .a)
  perceives t q p := (t, q, p) ∈ percL
  win := 1
  retained t p := t = 0 ∧ p = .a

theorem axioms : Axioms W where
  heads_within t p o h := by
    simp [W, headsL] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [W]
  heads_moving t p o h := by
    simp [W, headsL] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨.g0, rfl⟩
    · exact ⟨.g0, rfl⟩
    · exact ⟨.g0, rfl⟩
    · exact ⟨.g0, rfl⟩
    · exact ⟨.g4, rfl⟩
  contact_heads _ _ _ h := h.elim
  perceives_other t q p h := by
    simp [W, percL] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨by decide, .g0, rfl⟩
    · exact ⟨by decide, .g0, rfl⟩
    · exact ⟨by decide, .g0, rfl⟩
    · exact ⟨by decide, .g0, rfl⟩
    · exact ⟨by decide, .g1, rfl⟩
    · exact ⟨by decide, .g1, rfl⟩
    · exact ⟨by decide, .g2, rfl⟩
    · exact ⟨by decide, .g2, rfl⟩
    · exact ⟨by decide, .g2, rfl⟩
    · exact ⟨by decide, .g2, rfl⟩
  sim_refl m := simF_refl m
  sim_symm m m' h := simF_symm m m' h
  sim_opens m m' h := simF_opens m m' h
  retention t p h := by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨4, .g0, .g0, by omega, rfl, rfl, rfl⟩

theorem kinematics : Kinematics W where
  transfer s t r p o m m' hst _ _ hm' _ hw := by
    rcases hw with ht | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hmem := look_mem hm'
      simp [mvL] at hmem
      rcases hmem with ⟨⟨rfl, rfl⟩, _⟩ | ⟨⟨rfl, rfl⟩, _⟩ | ⟨⟨rfl, rfl⟩, _⟩ | ⟨⟨rfl, rfl⟩, _⟩ |
        ⟨⟨rfl, rfl⟩, _⟩ | ⟨⟨rfl, rfl⟩, _⟩ | ⟨⟨rfl, rfl⟩, _⟩ | ⟨⟨rfl, rfl⟩, _⟩ |
        ⟨⟨rfl, rfl⟩, _⟩ | ⟨⟨rfl, rfl⟩, _⟩ | ⟨⟨rfl, rfl⟩, _⟩ <;> first | omega | simp [W, headsL]
    · simp [W, headsL]
    · rw [show W.mv 8 .a = none from rfl] at hm'; cases hm'

/-- No suspension toward `τ` by `q` at the single moment after `u`, because `q` doesn't
move then. -/
theorem still {u : Nat} {q : Pt} {τ : Tgt Pt Ob} (hm : mv (u+1) q = none) :
    ∀ u', u < u' → u' ≤ u + W.win → ¬ Suspended W u' q τ := by
  intro u' h1 h2 hs
  have : u' = u + 1 := by simp [W] at h2; omega
  subst this
  cases τ with
  | obj o => obtain ⟨g, hg⟩ := axioms.heads_moving _ _ _ hs.1; rw [show W.mv (u+1) q = mv (u+1) q from rfl, hm] at hg; cases hg
  | act s r => obtain ⟨_, _, m', _, hm', _⟩ := hs.1; rw [show W.mv (u+1) q = mv (u+1) q from rfl, hm] at hm'; cases hm'

theorem joint (t : Nat) (p q : Pt) (hne : p ≠ q) (hsp : Suspended W t p (.obj .hammer))
    (hsq : Suspended W (t+1) q (.obj .hammer)) (h1 : W.perceives t q p)
    (h2 : W.perceives (t+1) p q) : Joint W t (t+1) (.obj .hammer) p q :=
  ⟨hne, by omega, by simp [W], hsp, hsq, h1, h2⟩

theorem susp_obj (t : Nat) (p : Pt) (h : (t, p) ∈ headsL) : Suspended W t p (.obj .hammer) :=
  ⟨h, fun h => h⟩

theorem episode0 : Joint W 0 1 (.obj .hammer) .a .b :=
  joint 0 .a .b (by decide) (susp_obj _ _ (by simp [headsL])) (susp_obj _ _ (by simp [headsL]))
    (by simp [W, percL]) (by simp [W, percL])

theorem episode4 : Joint W 4 5 (.obj .hammer) .a .b :=
  joint 4 .a .b (by decide) (susp_obj _ _ (by simp [headsL])) (susp_obj _ _ (by simp [headsL]))
    (by simp [W, percL]) (by simp [W, percL])

theorem ostensive0 : Ostensive W 0 1 .hammer .a .b :=
  ⟨episode0, ⟨4, 5, by decide, episode4, .g0, .g0, rfl, rfl, rfl⟩,
    ⟨2, ⟨3, by omega, by simp [W], by simp [W]⟩,
      (fun ⟨_, _, _, h, _⟩ => by rw [show W.mv 2 .a = none from rfl] at h; cases h),
      still rfl⟩⟩

theorem imperative6 : Imperative W 6 .a .b .hammer :=
  ⟨⟨7, ⟨by simp [W, percL], by omega, by simp [W]⟩, by simp [DirectedAt, W, headsL]⟩,
    by simp [W]⟩

/-- At t10, `b` cannot take `a`'s movement as being about the hammer: it is out of reach. -/
theorem no_imperative10 : ¬ Takes W 10 .a .b (.obj .hammer) := by
  intro hT
  obtain ⟨t', h1, h2, hw⟩ := takes_object_within W axioms hT
  have : t' = 11 := by simp [W] at h2; omega
  subst this
  simp [W] at hw

/-- But `b` does take it as being about the movement itself. -/
theorem takes10 : Takes W 10 .a .b (.act 10 .a) :=
  ⟨11, ⟨by simp [W, percL], by omega, by simp [W]⟩, by omega, .g1, .g2, rfl, rfl, rfl⟩

theorem susp_g2 {t : Nat} {p : Pt} (hm : mv t p = some .g2) (h : 10 < t) :
    Suspended W t p (.act 10 .a) := by
  refine ⟨⟨h, .g1, .g2, rfl, hm, rfl⟩, ?_⟩
  rintro ⟨m, m', hm1, hm2, hs⟩
  rw [show W.mv 10 .a = some Fm.g1 from rfl] at hm1
  cases hm1
  rw [show W.mv t p = mv t p from rfl, hm] at hm2
  cases hm2
  simp [W, simF] at hs

theorem dEpisode11 : Joint W 11 12 (.act 10 .a) .b .a :=
  ⟨by decide, by omega, by simp [W], susp_g2 rfl (by omega), susp_g2 rfl (by omega),
    by simp [W, percL], by simp [W, percL]⟩

theorem dEpisode15 : Joint W 15 16 (.act 10 .a) .b .a :=
  ⟨by decide, by omega, by simp [W], susp_g2 rfl (by omega), susp_g2 rfl (by omega),
    by simp [W, percL], by simp [W, percL]⟩

theorem declarative11 : Declarative W 11 12 10 .a .b .a :=
  ⟨dEpisode11, ⟨15, 16, by decide, dEpisode15, .g2, .g2, rfl, rfl, rfl⟩,
    ⟨13, (by omega : 10 < 13),
      (fun ⟨_, _, _, h, _⟩ => by rw [show W.mv 13 .b = none from rfl] at h; cases h),
      still rfl⟩⟩

theorem pure11 : Pure W 11 .b := fun _ h => by simp [W, headsL] at h
theorem pure12 : Pure W 12 .a := fun _ h => by simp [W, headsL] at h

theorem descends10 : Descends W 10 .a .hammer :=
  Descends.step (W := W) (s := 0) (r := .a) (m := Fm.g0) (m' := Fm.g1)
    (by omega) rfl rfl rfl (Descends.root ostensive0)

/-- The movement at t10 is a symbolic node standing for the absent hammer. -/
theorem arc : Arc W 10 .a .hammer := ⟨⟨11, 12, .b, .a, declarative11⟩, descends10⟩

theorem mv_g2 {t : Nat} {p : Pt} (h : mv t p = some .g2) : 11 ≤ t := by
  have hmem := look_mem h
  simp [mvL] at hmem
  rcases hmem with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega

/-- No declarative before t11. -/
theorem no_declarative_before : ∀ t t' s r p q, Declarative W t t' s r p q → 11 ≤ t := by
  rintro t t' s r p q ⟨⟨_, _, _, ⟨⟨_, m, m', hm, hm', ho⟩, hnc⟩, _⟩, _⟩
  have hns : ¬ simF m' m = true := fun hs => hnc ⟨m, m', hm, hm', hs⟩
  have := opens_not_sim m m' ho hns
  subst this
  exact mv_g2 hm'

/-- The hypotheses of `salience` hold for this declarative, so it is no accident that the
hammer is out of reach. -/
example : ¬ W.within 11 .b .hammer ∧ ¬ W.within 12 .a .hammer :=
  salience W kinematics declarative11 pure11 pure12 (s0 := 0) (r0 := .a) (m0 := .g0)
    (by omega) rfl (by simp [W, headsL]) ⟨.g2, rfl, rfl⟩ ⟨.g2, rfl, rfl⟩

theorem sim_not_transitive : ¬ ∀ x y z, W.sim x y → W.sim y z → W.sim x z :=
  fun h => absurd (h .g3 .g1 .g0 rfl rfl) (by simp [W, simF])

/-- One episode alone (t0–t1) would not have been a sign: dependence needed the repetition
at t4–t5 and the contrast at t2–t3. -/
example : Joint W 0 1 (.obj .hammer) .a .b ∧ Joint W 4 5 (.obj .hammer) .a .b :=
  ⟨episode0, episode4⟩

end E

/-! ### Joint gaze is not a center -/

namespace Gaze

/-- Both look at the hammer (g3), within reach, and see each other, but looking heads
toward no contact. -/
def W : World Pt Ob Fm where
  opens x y := opensF x y = true
  sim x y := simF x y = true
  mv t _ := if t = 0 then some .g3 else none
  heads _ _ _ := False
  contact _ _ _ := False
  within _ _ _ := True
  perceives t q p := t = 0 ∧ q ≠ p
  win := 1
  retained _ _ := False

theorem axioms : Axioms W where
  heads_within _ _ _ h := h.elim
  heads_moving _ _ _ h := h.elim
  contact_heads _ _ _ h := h.elim
  perceives_other t q p h := ⟨h.2, .g3, by simp [W, h.1]⟩
  sim_refl m := simF_refl m
  sim_symm m m' h := simF_symm m m' h
  sim_opens m m' h := simF_opens m m' h
  retention _ _ h := h.elim

theorem joint_looking :
    W.mv 0 .a = some .g3 ∧ W.mv 0 .b = some .g3 ∧ W.perceives 0 .a .b ∧
    W.perceives 0 .b .a ∧ W.within 0 .a .hammer ∧ W.within 0 .b .hammer :=
  ⟨rfl, rfl, ⟨rfl, by decide⟩, ⟨rfl, by decide⟩, trivial, trivial⟩

theorem no_center : ∀ t t' o p q, ¬ Ostensive W t t' o p q :=
  fun _ _ _ _ _ h => h.1.2.2.2.1.1

end Gaze

/-! ### Without kinematics, a "declarative" can happen with the object present -/

namespace NoTransfer

/-- t0: both reach for the hammer. Then two declarative episodes on `a`'s movement at t0,
with a contrast between them, all with the hammer within reach:
* t1: `b` makes g2; t2: `a` makes g2;
* t3–t4: contrast;
* t4: `b` makes g2 again; t5: `a` makes g2 again. -/
def mv : Nat → Pt → Option Fm
  | 0, _ => some .g0
  | 1, .b => some .g2
  | 2, .a => some .g2
  | 4, .b => some .g2
  | 5, .a => some .g2
  | _, _ => none

def percL : List (Nat × Pt × Pt) :=
  [(0, .b, .a), (0, .a, .b), (1, .a, .b), (2, .b, .a), (4, .a, .b), (5, .b, .a)]

def W : World Pt Ob Fm where
  opens x y := opensF x y = true
  sim x y := simF x y = true
  mv := mv
  heads t _ _ := t = 0
  contact _ _ _ := False
  within _ _ _ := True
  perceives t q p := (t, q, p) ∈ percL
  win := 1
  retained _ _ := False

theorem axioms : Axioms W where
  heads_within _ _ _ _ := trivial
  heads_moving t p o h := by
    have ht : t = 0 := h
    subst ht; exact ⟨.g0, rfl⟩
  contact_heads _ _ _ h := h.elim
  perceives_other t q p h := by
    simp [W, percL] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨by decide, .g0, rfl⟩
    · exact ⟨by decide, .g0, rfl⟩
    · exact ⟨by decide, .g2, rfl⟩
    · exact ⟨by decide, .g2, rfl⟩
    · exact ⟨by decide, .g2, rfl⟩
    · exact ⟨by decide, .g2, rfl⟩
  sim_refl m := simF_refl m
  sim_symm m m' h := simF_symm m m' h
  sim_opens m m' h := simF_opens m m' h
  retention _ _ h := h.elim

theorem not_kinematics : ¬ Kinematics W := fun hK => by
  have : W.heads 1 .b .hammer :=
    hK.transfer 0 1 .a .b .hammer .g0 .g2 (by omega) rfl rfl rfl rfl trivial
  exact absurd this (by simp [W])

theorem susp {t : Nat} {p : Pt} (hm : mv t p = some .g2) (h : 0 < t) :
    Suspended W t p (.act 0 .a) := by
  refine ⟨⟨h, .g0, .g2, rfl, hm, rfl⟩, ?_⟩
  rintro ⟨m, m', hm1, hm2, hs⟩
  simp [W, mv] at hm1
  subst hm1
  rw [show W.mv t p = mv t p from rfl, hm] at hm2
  cases hm2
  simp [W, simF] at hs

theorem declarative_in_presence :
    Declarative W 1 2 0 .a .b .a ∧ Pure W 1 .b ∧ Pure W 2 .a ∧
    W.within 1 .b .hammer ∧ W.within 2 .a .hammer := by
  refine ⟨⟨⟨by decide, by omega, by simp [W], susp rfl (by omega), susp rfl (by omega),
      by simp [W, percL], by simp [W, percL]⟩,
    ⟨4, 5, by decide, ⟨by decide, by omega, by simp [W], susp rfl (by omega),
      susp rfl (by omega), by simp [W, percL], by simp [W, percL]⟩, .g2, .g2, rfl, rfl, rfl⟩,
    ⟨3, (by omega : 0 < 3), fun ⟨_, _, _, h, _⟩ => by simp [W, mv] at h, ?_⟩⟩,
    fun _ h => by simp [W] at h, fun _ h => by simp [W] at h, trivial, trivial⟩
  intro u' h1 h2 hs
  have : u' = 4 := by simp [W] at h2; omega
  subst this
  obtain ⟨_, _, m', _, hm', _⟩ := hs.1
  simp [W, mv] at hm'

end NoTransfer

/-! ## Headline results -/

open GA.Models in
/-- **Emergence under the completion axioms.** A world satisfying the axioms and kinematics,
with:
* an ostensive (a center on the hammer, `a` first, `b` responding, repeated, with contrast);
* a satisfied imperative;
* a pure declarative on a movement (repeated, with contrast), whose node stands for the absent hammer;
* no declarative before t11;
* a non-transitive form-match relation. -/
theorem emergence :
    ∃ (W : World Pt Ob Fm), Axioms W ∧ Kinematics W ∧
      Ostensive W 0 1 .hammer .a .b ∧ Imperative W 6 .a .b .hammer ∧
      Declarative W 11 12 10 .a .b .a ∧ Pure W 11 .b ∧ Pure W 12 .a ∧ Arc W 10 .a .hammer ∧
      (∀ t t' s r p q, Declarative W t t' s r p q → 11 ≤ t) ∧
      ¬ (∀ x y z, W.sim x y → W.sim y z → W.sim x z) :=
  ⟨E.W, E.axioms, E.kinematics, E.ostensive0, E.imperative6, E.declarative11, E.pure11,
    E.pure12, E.arc, E.no_declarative_before, E.sim_not_transitive⟩

open GA.Models in
/-- **Kinematics is needed for salience.** Without it, a pure center on a gesture can form
while the object is within reach. -/
theorem kinematics_needed :
    ∃ (W : World Pt Ob Fm), Axioms W ∧ ¬ Kinematics W ∧
      Declarative W 1 2 0 .a .b .a ∧ Pure W 1 .b ∧ Pure W 2 .a ∧
      W.within 1 .b .hammer ∧ W.within 2 .a .hammer :=
  ⟨NoTransfer.W, NoTransfer.axioms, NoTransfer.not_kinematics,
    NoTransfer.declarative_in_presence⟩

open GA.Models in
/-- **Joint gaze is not a center.** Both look, within reach, and see each other, but
there is no ostensive. -/
theorem gaze_not_center :
    ∃ (W : World Pt Ob Fm), Axioms W ∧ W.perceives 0 .a .b ∧ W.perceives 0 .b .a ∧
      W.within 0 .a .hammer ∧ ∀ t t' o p q, ¬ Ostensive W t t' o p q :=
  ⟨Gaze.W, Gaze.axioms, Gaze.joint_looking.2.2.1, Gaze.joint_looking.2.2.2.1,
    trivial, Gaze.no_center⟩

end GA.Completion
