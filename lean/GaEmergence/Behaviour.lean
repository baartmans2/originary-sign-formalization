import GaEmergence.Models

/-!
# Taking-as defined as response, and restraint as exhaustion

This file is a self-contained system. It answers the two remaining assumptions identified
in `Originary.lean`.

**1. Uptake is no longer primitive.** A `BScene` has no `uptake` field. It records only
what each participant's body does at each time (`act`: move, grasp, fetch, or rest),
where things are, and which movements are aimed at what. *Taking an act as being about
something* is the inductive predicate `Takes`, defined from those records. What the act
is taken to be about is read off what the response is directed at:

| what `h` does in response to `a`'s movement | `Takes t a h τ` |
|---|---|
| both reached for `o` and both refrained | `τ = phys o` (ostensive) |
| movement echoes one taken as about `o`; `h` goes and fetches `o` | `τ = phys o` (imperative) |
| `a`, who failed to supply what `h` asked for at `j`, echoes that act; `h` answers in kind | `τ = occ j` (declarative) |
| movement echoes one taken as about act `j`; `h` answers in kind | `τ = occ j` (re-presentation) |

Answering in kind, with no object to reach for, is what makes the target the sign itself.

**2. Restraint is exhaustion, not catastrophe.** A clash can happen, possibly many times.
The only assumption is that clashes over an object cannot recur indefinitely
(`Exhausting`). This is the untenability clause of Axiom 4 applied to fighting. Whether a
sign results then depends on whether desire outlasts the capacity to fight.
-/

namespace GA.Behavioural
open GA

-- Bound variables named `a` (a participant) are intended, not the constructor `Pt.a`.
set_option linter.constructorNameAsVariable false

/-- What a body does at a moment. -/
inductive Act (G O : Type) where
  | move  : G → Act G O
  | grasp : O → Act G O
  | fetch : O → Act G O
  | rest  : Act G O

/-- Behaviour only: no signs, no uptake. -/
structure BScene (P O C G : Type) where
  present : C → O → Prop
  aim     : G → C → O → Prop
  sim     : G × C → G × C → Prop
  ctx     : Nat → C
  act     : Nat → P → Act G O
  /-- unspecified forcing with respect to a failure opened at `j`, at time `t` -/
  forcing : Nat → Nat → Prop

section
variable {P O C G : Type} (S : BScene P O C G)

def Reaches (t : Nat) (p : P) (o : O) : Prop :=
  ∃ g, S.act t p = .move g ∧ S.aim g (S.ctx t) o

def Grasps (t : Nat) (p : P) (o : O) : Prop := S.act t p = .grasp o

def Converge (t : Nat) (o : O) (p q : P) : Prop :=
  p ≠ q ∧ Reaches S t p o ∧ Reaches S t q o

def Clash (t : Nat) (o : O) : Prop :=
  ∃ p q, p ≠ q ∧ Grasps S t p o ∧ Grasps S t q o

def JointDeferral (t : Nat) (o : O) (p q : P) : Prop :=
  Converge S t o p q ∧ ¬ Grasps S (t+1) p o ∧ ¬ Grasps S (t+1) q o

/-- `h` fetches `o` at `k`, and `o` is present afterwards. -/
def Supplied (k : Nat) (h : P) (o : O) : Prop :=
  S.act k h = .fetch o ∧ S.present (S.ctx (k+1)) o

/-- **Taking-as, defined by response.** `Takes t a h τ`: `h` takes `a`'s movement at `t` as
being about `τ`. Every premise is a fact about bodies, places and similarity, or an
earlier instance of `Takes`. -/
inductive Takes : Nat → P → P → Target O → Prop where
  /-- ostensive: `a` and `h` both reached for `o` and both refrained -/
  | defer {t : Nat} {a h : P} {o : O} :
      JointDeferral S t o a h → Takes t a h (.phys o)
  /-- imperative: `a`'s movement echoes one taken as about `o`, and `h` fetches `o` -/
  | fetch {t s : Nat} {a h a' h' : P} {g g' : G} {o : O} :
      S.act t a = .move g → s < t → S.act s a' = .move g' → Takes s a' h' (.phys o) →
      S.sim (g, S.ctx t) (g', S.ctx s) → a ≠ h → S.act (t+1) h = .fetch o →
      Takes t a h (.phys o)
  /-- originary declarative: `a` failed to supply `o` for `h`'s act at `j` (whose object
  was absent), makes a movement echoing that act, and `h` answers in kind -/
  | declare {t j : Nat} {a h : P} {g gj g'' : G} {o : O} :
      j < t → S.act j h = .move gj → Takes j h a (.phys o) → ¬ S.present (S.ctx j) o →
      (∀ k, j ≤ k → k < t → ¬ Supplied S k a o) →
      S.act t a = .move g → S.sim (g, S.ctx t) (gj, S.ctx j) → a ≠ h →
      S.act (t+1) h = .move g'' → S.sim (g'', S.ctx (t+1)) (g, S.ctx t) →
      Takes t a h (.occ j)
  /-- re-presentation: `a`'s movement echoes one taken as about act `j`; `h` answers in kind -/
  | echo {t s j : Nat} {a h a' h' : P} {g g' g'' : G} :
      S.act t a = .move g → s < t → S.act s a' = .move g' → Takes s a' h' (.occ j) →
      S.sim (g, S.ctx t) (g', S.ctx s) → a ≠ h →
      S.act (t+1) h = .move g'' → S.sim (g'', S.ctx (t+1)) (g, S.ctx t) →
      Takes t a h (.occ j)

/-- `a`'s movement at `j` was taken by `h` as being about `o`, which is absent. -/
def Failed (j : Nat) (a h : P) (o : O) : Prop :=
  (∃ g, S.act j a = .move g) ∧ Takes S j a h (.phys o) ∧ ¬ S.present (S.ctx j) o

/-- The failure at `j` has been neither supplied nor taken up as being about itself. -/
def Unresolved (j t : Nat) (a h : P) (o : O) : Prop :=
  Failed S j a h o ∧ ∀ k, j ≤ k → k < t → ¬ Supplied S k h o ∧ ¬ Takes S k h a (.occ j)

def Unavailing (j t : Nat) (a h : P) (o : O) : Prop :=
  Unresolved S j t a h o ∧
    ((S.act t h = .fetch o ∧ ¬ S.present (S.ctx (t+1)) o) ∨
     ((∃ g, S.act t h = .move g) ∧ ¬ Takes S t h a (.occ j)))

/-- An unsatisfied failure, followed by the failed party's movement, which the original
author answers with a movement. -/
def OriginaryDecl (j k : Nat) : Prop :=
  ∃ a h o, j < k ∧ Failed S j h a o ∧ (∀ k', j ≤ k' → k' < k → ¬ Supplied S k' a o) ∧
    (∃ g, S.act k a = .move g) ∧ (∃ g'', S.act (k+1) h = .move g'')

def Vertex (n : Nat) (v : Target O) : Prop := ∃ t a h, t < n ∧ Takes S t a h v

def Independent (n : Nat) (v : Target O) : Prop :=
  Vertex S n v ∧ Symbolic v ∧
  ∃ t₁ t₂ a₁ h₁ a₂ h₂ o, t₁ < n ∧ t₂ < n ∧ S.ctx t₁ ≠ S.ctx t₂ ∧
    Takes S t₁ a₁ h₁ v ∧ Takes S t₂ a₂ h₂ v ∧
    (∃ j a h, v = .occ j ∧ Takes S j a h (.phys o)) ∧
    ¬ S.present (S.ctx t₁) o ∧ ¬ S.present (S.ctx t₂) o

end

/-! ## Axioms -/

variable {P O C G : Type}

/-- Physical constraints (as in `Originary.lean`). -/
structure Practice (S : BScene P O C G) : Prop where
  directed  : ∀ g c o, S.aim g c o → S.present c o
  completes : ∀ t p o, Grasps S (t+1) p o → Reaches S t p o

/-- Mimetic symmetry: between converging participants, neither completes the grab unless the other does. -/
def Symmetric (S : BScene P O C G) : Prop :=
  ∀ t o p q, Converge S t o p q → (Grasps S (t+1) p o ↔ Grasps S (t+1) q o)

/-- **Exhaustion**: clashes over an object cannot recur indefinitely.
No catastrophe is assumed. Any number of fights may happen first. -/
def Exhausting (S : BScene P O C G) : Prop :=
  ∀ o, ∃ T, ∀ t, T < t → ¬ Clash S t o

/-- Desire outlasts fighting: convergence on `o` keeps recurring. -/
def PersistentDesire (S : BScene P O C G) (o : O) : Prop :=
  ∀ T, ∃ t, T < t ∧ ∃ p q, Converge S t o p q

/-- Axiom 4, stated behaviourally. -/
structure ForcedPreservation (S : BScene P O C G) : Prop where
  forced : ∀ j t a h o, j < t → Unresolved S j t a h o → S.forcing j t →
    S.act t h = .fetch o ∨ ∃ g, S.act t h = .move g
  untenable : ∀ j a h o, Failed S j a h o →
    ∃ T, ∀ t, T < t → ¬ Unavailing S j t a h o

/-! ## General theorems -/

section
variable (S : BScene P O C G)

theorem JointDeferral.symm {t : Nat} {o : O} {p q : P} (h : JointDeferral S t o p q) :
    JointDeferral S t o q p :=
  ⟨⟨fun e => h.1.1 e.symm, h.1.2.2, h.1.2.1⟩, h.2.2, h.2.1⟩

/-- Only movements are taken up, and only by someone other than the mover. -/
theorem takes_mover {t : Nat} {a h : P} {τ : Target O} (hT : Takes S t a h τ) :
    (∃ g, S.act t a = .move g) ∧ a ≠ h := by
  cases hT with
  | defer hj => exact ⟨⟨_, hj.1.2.1.choose_spec.1⟩, hj.1.1⟩
  | fetch hm _ _ _ _ hne _ => exact ⟨⟨_, hm⟩, hne⟩
  | declare _ _ _ _ _ hm _ hne _ _ => exact ⟨⟨_, hm⟩, hne⟩
  | echo hm _ _ _ _ hne _ _ => exact ⟨⟨_, hm⟩, hne⟩

/-- **Where every taking-as comes from.** Every relation to an object descends from a joint
deferral of a reach for it. Every relation to an act descends from an originary
declarative about that act. (Induction on `Takes`.) -/
theorem takes_origin {t : Nat} {a h : P} {τ : Target O} (hT : Takes S t a h τ) :
    (∀ o, τ = .phys o → ∃ s p q, s ≤ t ∧ JointDeferral S s o p q) ∧
    (∀ j, τ = .occ j → ∃ k, j < k ∧ k ≤ t ∧ OriginaryDecl S j k) := by
  induction hT with
  | @defer t a h o hj =>
    refine ⟨fun o' ho => ?_, fun _ ho => by cases ho⟩
    cases ho
    exact ⟨t, a, h, Nat.le_refl t, hj⟩
  | @fetch t s _ _ _ _ _ _ _ _ hs _ _ _ _ _ ih =>
    refine ⟨fun o' ho => ?_, fun _ ho => by cases ho⟩
    cases ho
    obtain ⟨s₀, p, q, hs₀, hj⟩ := ih.1 _ rfl
    exact ⟨s₀, p, q, by omega, hj⟩
  | @declare t j a h g gj g'' o hjt hmj hTj hp hns hm _ _ hm' _ _ =>
    refine ⟨fun _ ho => (by cases ho), fun j' ho => ?_⟩
    cases ho
    exact ⟨t, hjt, Nat.le_refl t, a, h, o, hjt, ⟨⟨gj, hmj⟩, hTj, hp⟩, hns, ⟨g, hm⟩, ⟨g'', hm'⟩⟩
  | @echo t s _ _ _ _ _ _ _ _ _ hs _ _ _ _ _ _ ih =>
    refine ⟨fun _ ho => (by cases ho), fun j' ho => ?_⟩
    obtain ⟨k, h1, h2, h3⟩ := ih.2 j' ho
    exact ⟨k, h1, by omega, h3⟩

/-- **The imperative is constituted by fetching.** Taking a movement as being about an
*absent* object consists in going to fetch it. (Uses only: aiming requires presence.) -/
theorem failed_fetched (hdir : ∀ g c o, S.aim g c o → S.present c o) {j : Nat} {a h : P} {o : O}
    (hf : Failed S j a h o) : S.act (j+1) h = .fetch o := by
  obtain ⟨_, hT, hp⟩ := hf
  cases hT with
  | defer hj =>
    obtain ⟨_, _, haim⟩ := hj.1.2.1
    exact absurd (hdir _ _ _ haim) hp
  | fetch _ _ _ _ _ _ hf => exact hf

/-- **The Gansian order, behaviourally.** Any act taken as being about an act descends from
a joint deferral at `s`, a failed movement at `j` and an originary declarative at `k`, with
`s < j < k ≤ t`. (Uses only: aiming requires presence.) -/
theorem gansian_order (hdir : ∀ g c o, S.aim g c o → S.present c o) {t j : Nat} {a h : P}
    (hT : Takes S t a h (.occ j)) :
    ∃ s k o p q h' a', s < j ∧ j < k ∧ k ≤ t ∧
      JointDeferral S s o p q ∧ Failed S j h' a' o ∧ OriginaryDecl S j k := by
  obtain ⟨k, hjk, hkt, hod⟩ := (takes_origin S hT).2 j rfl
  obtain ⟨a', h', o, _, hf, _⟩ := id hod
  obtain ⟨s, p, q, hsj, hjd⟩ := (takes_origin S hf.2.1).1 o rfl
  have hsj' : s < j := by
    rcases Nat.lt_or_eq_of_le hsj with hlt | heq
    · exact hlt
    · subst heq
      obtain ⟨_, _, haim⟩ := hjd.1.2.1
      exact absurd (hdir _ _ _ haim) hf.2.2
  exact ⟨s, k, o, p, q, h', a', hsj', hjk, hkt, hjd, hf, hod⟩

/-- Before the first originary declarative, every vertex is physical. -/
theorem no_symbolic_before_declarative (n : Nat)
    (hnone : ∀ j k, k < n → ¬ OriginaryDecl S j k) :
    ∀ v, Vertex S n v → ¬ Symbolic v := by
  rintro v ⟨t, a, h, htn, hT⟩ hsym
  cases v with
  | phys o => exact hsym o rfl
  | occ j =>
    obtain ⟨k, _, hkt, hk⟩ := (takes_origin S hT).2 j rfl
    exact hnone j k (by omega) hk

/-- **No deferral, no taking-as at all.** -/
theorem no_signs_without_deferral (hnone : ∀ t o p q, ¬ JointDeferral S t o p q) :
    ∀ t a h τ, ¬ Takes S t a h τ := by
  intro t a h τ hT
  cases τ with
  | phys o =>
    obtain ⟨s, p, q, _, hj⟩ := (takes_origin S hT).1 o rfl
    exact hnone s o p q hj
  | occ j =>
    obtain ⟨_, _, _, _, _, o, _, hf, _⟩ := (takes_origin S hT).2 j rfl
    obtain ⟨s, p, q, _, hj⟩ := (takes_origin S hf.2.1).1 o rfl
    exact hnone s o p q hj

/-! ### Exhaustion instead of catastrophe -/

/-- Once clashing over `o` is exhausted, a symmetric convergence on `o` is necessarily
deferred. (Uses: symmetry. No forcing beyond exhaustion.) -/
theorem deferral_after_exhaustion (hsym : Symmetric S) {T t : Nat} {o : O} {p q : P}
    (hT : ∀ t', T < t' → ¬ Clash S t' o) (ht : T ≤ t) (hc : Converge S t o p q) :
    JointDeferral S t o p q := by
  have hnp : ¬ Grasps S (t+1) p o := fun hp =>
    hT (t+1) (by omega) ⟨p, q, hc.1, hp, (hsym t o p q hc).mp hp⟩
  exact ⟨hc, hnp, fun hq => hnp ((hsym t o p q hc).mpr hq)⟩

/-- **The ostensive from fatigue.** If clashing is exhausted but desire persists, a joint
deferral occurs, and each participant takes the other's reach as being about the object.
The ostensive emerges historically, after any number of fights. -/
theorem ostensive_of_exhaustion (hsym : Symmetric S) (hex : Exhausting S) {o : O}
    (hdes : PersistentDesire S o) :
    ∃ t p q, JointDeferral S t o p q ∧ Takes S t p q (.phys o) ∧ Takes S t q p (.phys o) := by
  obtain ⟨T, hT⟩ := hex o
  obtain ⟨t, hTt, p, q, hc⟩ := hdes T
  have hj := deferral_after_exhaustion S hsym hT (Nat.le_of_lt hTt) hc
  exact ⟨t, p, q, hj, .defer hj, .defer (hj.symm S)⟩

/-! ### Forced preservation, behaviourally -/

theorem resolution_of_persistent_forcing (hF : ForcedPreservation S)
    {j : Nat} {a h : P} {o : O} (hfail : Failed S j a h o)
    (hforce : ∀ t, j < t → S.forcing j t) :
    ∃ k, j ≤ k ∧ (Supplied S k h o ∨ Takes S k h a (.occ j)) := by
  obtain ⟨T, hT⟩ := hF.untenable j a h o hfail
  obtain ⟨t, hTt, hjt⟩ : ∃ t, T < t ∧ j < t := ⟨T + j + 1, by omega, by omega⟩
  have hnot := hT t hTt
  by_cases hop : Unresolved S j t a h o
  · rcases hF.forced j t a h o hjt hop (hforce t hjt) with hd | ⟨g, hd⟩
    · by_cases hp : S.present (S.ctx (t+1)) o
      · exact ⟨t, by omega, Or.inl ⟨hd, hp⟩⟩
      · exact absurd ⟨hop, Or.inl ⟨hd, hp⟩⟩ hnot
    · by_cases hp : Takes S t h a (.occ j)
      · exact ⟨t, by omega, Or.inr hp⟩
      · exact absurd ⟨hop, Or.inr ⟨⟨g, hd⟩, hp⟩⟩ hnot
  · apply Classical.byContradiction
    intro hno
    exact hop ⟨hfail, fun k hk _ =>
      ⟨fun hs => hno ⟨k, hk, Or.inl hs⟩, fun hp => hno ⟨k, hk, Or.inr hp⟩⟩⟩

/-- Persistent forcing on an object that never returns entails that the failed party's
movement is eventually *answered in kind*, which is what taking it as being about the
failed act consists in. -/
theorem declarative_of_forcing (hF : ForcedPreservation S)
    {j : Nat} {a h : P} {o : O} (hfail : Failed S j a h o)
    (hforce : ∀ t, j < t → S.forcing j t)
    (hunavail : ∀ t, j < t → ¬ S.present (S.ctx t) o) :
    ∃ k, j < k ∧ Takes S k h a (.occ j) := by
  obtain ⟨k, hk, hs | hp⟩ := resolution_of_persistent_forcing S hF hfail hforce
  · exact absurd hs.2 (hunavail (k+1) (by omega))
  · refine ⟨k, ?_, hp⟩
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact hlt
    · subst heq
      obtain ⟨k', hjk, hkj, _⟩ := (takes_origin S hp).2 _ rfl
      omega

end

/-! ## Models -/

open GA.Models

def aimB : Gs → Cx → Ob → Bool
  | .g0, .scene, .hammer => true
  | _, _, _ => false

theorem aimB_directed (g : Gs) (c : Cx) (o : Ob) (h : aimB g c o = true) :
    presentB c o = true := by
  cases g <;> cases c <;> cases o <;> simp [aimB, presentB] at h ⊢

/-- Felt similarity. Again not transitive. -/
def simB : Gs × Cx → Gs × Cx → Bool
  | (.g1, .absent), (.g0, .scene)  => true
  | (.g2, .absent), (.g1, .absent) => true
  | (.g3, .later),  (.g2, .absent) => true
  | (.g2, .later),  (.g3, .later)  => true
  | _, _ => false

/-! ### Fights, then fatigue, then the full chain -/

namespace Fight

/-- t0–t3: `a` and `b` reach for the hammer and fight over it, twice.
t4–t5: they reach again and, exhausted, both refrain (the ostensive).
t6: elsewhere, `a` makes g1, which echoes g0; t7, t8: `b` fetches, in vain.
t9: `b` makes g2, echoing g1; t10: in a later context, `a` answers in kind with g3.
t11: `b` answers in kind with g2. -/
def act : Nat → Pt → Act Gs Ob
  | 0, _ | 2, _ | 4, _ => .move .g0
  | 1, _ | 3, _ => .grasp .hammer
  | 6, .a => .move .g1
  | 7, .b | 8, .b => .fetch .hammer
  | 9, .b => .move .g2
  | 10, .a => .move .g3
  | 11, .b => .move .g2
  | _, _ => .rest

def ctx : Nat → Cx
  | 0 | 1 | 2 | 3 | 4 | 5 => .scene
  | 6 | 7 | 8 | 9 => .absent
  | _ => .later

def S : BScene Pt Ob Cx Gs where
  present c o := presentB c o = true
  aim g c o := aimB g c o = true
  sim x y := simB x y = true
  ctx := ctx
  act := act
  forcing j _ := j = 6

theorem reaches_inv {t : Nat} {p : Pt} {o : Ob} (h : Reaches S t p o) :
    t = 0 ∨ t = 2 ∨ t = 4 := by
  obtain ⟨g, hm, haim⟩ := h
  cases o
  revert hm haim
  match t, p with
  | 0, _ | 2, _ | 4, _ => intros; simp
  | 6, .a | 9, .b | 10, .a | 11, .b =>
    intro hm haim; simp [S, act] at hm; subst hm; simp [S, ctx, aimB] at haim
  | 1, _ | 3, _ | 5, _ | 7, .a | 7, .b | 8, .a | 8, .b | _ + 12, _ => intro hm; simp [S, act] at hm
  | 6, .b | 9, .a | 10, .b | 11, .a => intro hm; simp [S, act] at hm

theorem grasps_inv {t : Nat} {p : Pt} {o : Ob} (h : Grasps S t p o) : t = 1 ∨ t = 3 := by
  revert h
  match t, p with
  | 1, _ | 3, _ => intros; simp
  | 0, _ | 2, _ | 4, _ | 5, _ | 7, .a | 7, .b | 8, .a | 8, .b | _ + 12, _ => intro h; simp [Grasps, S, act] at h
  | 6, .a | 6, .b | 9, .a | 9, .b | 10, .a | 10, .b | 11, .a | 11, .b =>
    intro h; simp [Grasps, S, act] at h

theorem practice : Practice S where
  directed g c o h := aimB_directed g c o h
  completes t p o h := by
    have ht : t = 0 ∨ t = 2 := by rcases grasps_inv h with h1 | h1 <;> omega
    rcases ht with rfl | rfl <;> cases o <;> exact ⟨.g0, rfl, rfl⟩

theorem symmetric : Symmetric S := by
  intro t o p q hc
  rcases reaches_inv hc.2.1 with rfl | rfl | rfl <;> cases o <;> simp [Grasps, S, act]

theorem exhausting : Exhausting S := by
  intro o
  exact ⟨3, fun t ht ⟨p, _, _, hp, _⟩ => by have := grasps_inv hp; omega⟩

theorem clashes : Clash S 1 .hammer ∧ Clash S 3 .hammer :=
  ⟨⟨.a, .b, by decide, rfl, rfl⟩, ⟨.a, .b, by decide, rfl, rfl⟩⟩

theorem converge4 : Converge S 4 .hammer .a .b :=
  ⟨by decide, ⟨.g0, rfl, rfl⟩, ⟨.g0, rfl, rfl⟩⟩

/-- The deferral at t4 is *entailed* by symmetry and exhaustion. It is not stipulated. -/
theorem deferral4 : JointDeferral S 4 .hammer .a .b := by
  obtain ⟨T, hT⟩ : ∃ T, T = 3 ∧ ∀ t, T < t → ¬ Clash S t .hammer :=
    ⟨3, rfl, fun t ht ⟨p, _, _, hp, _⟩ => by have := grasps_inv hp; omega⟩
  exact deferral_after_exhaustion S symmetric hT.2 (by omega) converge4

theorem takes4 : Takes S 4 .a .b (.phys .hammer) := .defer deferral4

theorem takes6 : Takes S 6 .a .b (.phys .hammer) :=
  .fetch (S := S) (g := Gs.g1) (g' := Gs.g0) rfl (by omega) rfl takes4 rfl (by decide) rfl

theorem no_supply : ∀ k, 6 ≤ k → k < 9 → ¬ Supplied S k .b .hammer := by
  intro k h1 h2 ⟨hf, hp⟩
  rcases (by omega : k = 6 ∨ k = 7 ∨ k = 8) with rfl | rfl | rfl <;>
    simp [S, act, ctx, presentB] at hf hp

theorem takes9 : Takes S 9 .b .a (.occ 6) :=
  .declare (S := S) (g := Gs.g2) (gj := Gs.g1) (g'' := Gs.g3) (by omega) rfl takes6
    (by simp [S, ctx, presentB]) no_supply rfl rfl (by decide) rfl rfl

theorem takes10 : Takes S 10 .a .b (.occ 6) :=
  .echo (S := S) (g := Gs.g3) (g' := Gs.g2) (g'' := Gs.g2) rfl (by omega) rfl takes9 rfl (by decide) rfl rfl

theorem fetch_inv {t : Nat} {p : Pt} {o : Ob} (h : S.act t p = .fetch o) :
    (t = 7 ∨ t = 8) ∧ p = .b := by
  revert h
  match t, p with
  | 7, .b | 8, .b => intros; simp
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | _ + 12, _ => intro h; simp [S, act] at h
  | 6, .a | 6, .b | 7, .a | 8, .a | 9, .a | 9, .b | 10, .a | 10, .b | 11, .a | 11, .b =>
    intro h; simp [S, act] at h

theorem failed_inv {j : Nat} {a h : Pt} {o : Ob} (hf : Failed S j a h o) :
    j = 6 ∧ a = .a ∧ h = .b ∧ o = .hammer := by
  have hfetch := failed_fetched S practice.directed hf
  obtain ⟨⟨g, hm⟩, _, _⟩ := hf
  cases o
  obtain ⟨hj, rfl⟩ := fetch_inv hfetch
  rcases (by omega : j = 6 ∨ j = 7) with rfl | rfl <;> cases a <;> simp [S, act] at hm ⊢

theorem forcedPreservation : ForcedPreservation S := by
  constructor
  · intro j t a h o hjt hop _
    obtain ⟨rfl, rfl, rfl, rfl⟩ := failed_inv hop.1
    rcases (by omega : t = 7 ∨ t = 8 ∨ t = 9 ∨ 10 ≤ t) with rfl | rfl | rfl | ht
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨.g2, rfl⟩
    · exact absurd takes9 (hop.2 9 (by omega) (by omega)).2
  · intro j a h o hf
    obtain ⟨rfl, rfl, rfl, rfl⟩ := failed_inv hf
    exact ⟨9, fun t ht hu => (hu.1.2 9 (by omega) (by omega)).2 takes9⟩

/-- Up to t9, every vertex is physical. -/
theorem no_symbolic_yet : ∀ v, Vertex S 9 v → ¬ Symbolic v := by
  apply no_symbolic_before_declarative S 9
  rintro j k hk ⟨a, h, o, hjk, hf, _, ⟨g, hm⟩, _⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ := failed_inv hf
  rcases (by omega : k = 7 ∨ k = 8) with rfl | rfl <;> simp [S, act] at hm

/-- By t11, the movement at t6 is an independent symbolic node. -/
theorem independent : Independent S 11 (.occ 6) :=
  ⟨⟨9, .b, .a, by omega, takes9⟩, fun _ h => (by cases h),
    9, 10, .b, .a, .a, .b, .hammer, by omega, by omega, by simp [S, ctx], takes9, takes10,
    ⟨6, .a, .b, rfl, takes6⟩, by simp [S, ctx, presentB], by simp [S, ctx, presentB]⟩

/-- The movement at t6 is physically aimless: the hammer isn't there. -/
theorem aimless6 : ∀ o, ¬ Reaches S 6 .a o := fun _ h => by
  have := reaches_inv h; omega

end Fight

/-! ### Countermodels: each ingredient of `ostensive_of_exhaustion` is needed -/

/-- They fight forever: symmetric, desire persists, no exhaustion. -/
def Brawl : BScene Pt Ob Cx Gs where
  present c o := presentB c o = true
  aim g c o := aimB g c o = true
  sim _ _ := False
  ctx _ := .scene
  act t _ := if t % 2 = 0 then .move .g0 else .grasp .hammer
  forcing _ _ := False

/-- They fight once, then walk away: symmetric, exhausting, desire does not persist. -/
def WalkAway : BScene Pt Ob Cx Gs :=
  { Brawl with act := fun t _ => if t = 0 then .move .g0 else if t = 1 then .grasp .hammer else .rest }

/-- `a` always wins: exhausting (no clash ever), desire persists, not symmetric. -/
def Hier : BScene Pt Ob Cx Gs :=
  { Brawl with
    act := fun t p => if t % 2 = 0 then .move .g0 else
      match p with
      | .a => .grasp .hammer
      | .b => .rest }

theorem reach_even {S : BScene Pt Ob Cx Gs}
    (hS : ∀ t p g, S.act t p = .move g → t % 2 = 0) {t : Nat} {p : Pt} {o : Ob}
    (h : Reaches S t p o) : t % 2 = 0 := by
  obtain ⟨g, hm, _⟩ := h; exact hS t p g hm

theorem brawl_move : ∀ t p g, Brawl.act t p = .move g → t % 2 = 0 := by
  intro t p g h
  by_cases ht : t % 2 = 0
  · exact ht
  · simp [Brawl, ht] at h

theorem hier_move : ∀ t p g, Hier.act t p = .move g → t % 2 = 0 := by
  intro t p g h
  by_cases ht : t % 2 = 0
  · exact ht
  · cases p <;> simp [Hier, Brawl, ht] at h

theorem walk_move : ∀ t p g, WalkAway.act t p = .move g → t = 0 := by
  intro t p g h
  by_cases h0 : t = 0
  · exact h0
  · by_cases h1 : t = 1 <;> simp [WalkAway, h0, h1] at h

theorem brawl_practice : Practice Brawl where
  directed g c o h := aimB_directed g c o h
  completes t p o h := by
    have ht : t % 2 = 0 := by
      by_cases h' : (t+1) % 2 = 0
      · simp [Grasps, Brawl, h'] at h
      · omega
    cases o
    exact ⟨.g0, by simp [Brawl, ht], rfl⟩

theorem brawl_symmetric : Symmetric Brawl := by
  intro t o p q _; simp [Grasps, Brawl]

theorem brawl_desire : PersistentDesire Brawl .hammer := by
  intro T
  have he : (2*T+2) % 2 = 0 := by omega
  exact ⟨2*T+2, by omega, .a, .b, by decide,
    ⟨.g0, by simp [Brawl, he], rfl⟩, ⟨.g0, by simp [Brawl, he], rfl⟩⟩

theorem brawl_no_deferral : ∀ t o p q, ¬ JointDeferral Brawl t o p q := by
  rintro t o p q ⟨hc, hp, _⟩
  have ht := reach_even brawl_move hc.2.1
  have ht' : ¬ (t+1) % 2 = 0 := by omega
  cases o
  exact hp (by simp [Grasps, Brawl, ht'])

theorem brawl_not_exhausting : ¬ Exhausting Brawl := by
  intro h
  obtain ⟨T, hT⟩ := h .hammer
  have ho : ¬ (2*T+1) % 2 = 0 := by omega
  exact hT (2*T+1) (by omega) ⟨.a, .b, by decide, by simp [Grasps, Brawl, ho],
    by simp [Grasps, Brawl, ho]⟩

theorem walk_practice : Practice WalkAway where
  directed g c o h := aimB_directed g c o h
  completes t p o h := by
    have ht : t = 0 := by
      by_cases h0 : t = 0
      · exact h0
      · have : t + 1 ≠ 1 := by omega
        simp [Grasps, WalkAway, this] at h
    subst ht; cases o
    exact ⟨.g0, by simp [WalkAway], rfl⟩

theorem walk_symmetric : Symmetric WalkAway := by
  intro t o p q _; simp [Grasps, WalkAway]

theorem walk_exhausting : Exhausting WalkAway := by
  intro o
  refine ⟨1, fun t ht ⟨p, _, _, hp, _⟩ => ?_⟩
  have h0 : t ≠ 0 := by omega
  have h1 : t ≠ 1 := by omega
  simp [Grasps, WalkAway, h0, h1] at hp

theorem walk_converge : Converge WalkAway 0 .hammer .a .b :=
  ⟨by decide, ⟨.g0, by simp [WalkAway], rfl⟩, ⟨.g0, by simp [WalkAway], rfl⟩⟩

theorem walk_no_deferral : ∀ t o p q, ¬ JointDeferral WalkAway t o p q := by
  rintro t o p q ⟨hc, hp, _⟩
  have ht := reach_even (S := WalkAway)
    (fun t p g h => by have := walk_move t p g h; omega) hc.2.1
  have h0 := walk_move t p _ hc.2.1.choose_spec.1
  subst h0
  cases o
  exact hp (by simp [Grasps, WalkAway])

theorem walk_desire_fades : ¬ PersistentDesire WalkAway .hammer := by
  intro h
  obtain ⟨t, ht, _, _, hc⟩ := h 0
  have := walk_move t _ _ hc.2.1.choose_spec.1
  omega

theorem hier_practice : Practice Hier where
  directed g c o h := aimB_directed g c o h
  completes t p o h := by
    have ht : t % 2 = 0 := by
      by_cases h' : (t+1) % 2 = 0
      · cases p <;> simp [Grasps, Hier, Brawl, h'] at h
      · omega
    cases o
    exact ⟨.g0, by cases p <;> simp [Hier, Brawl, ht], rfl⟩

theorem hier_exhausting : Exhausting Hier := by
  intro o
  refine ⟨0, fun t _ ⟨p, q, hne, hp, hq⟩ => ?_⟩
  by_cases ht : t % 2 = 0
  · cases p <;> simp [Grasps, Hier, Brawl, ht] at hp
  · cases p <;> cases q <;> simp [Grasps, Hier, Brawl, ht] at hp hq hne

theorem hier_desire : PersistentDesire Hier .hammer := by
  intro T
  have he : (2*T+2) % 2 = 0 := by omega
  exact ⟨2*T+2, by omega, .a, .b, by decide,
    ⟨.g0, by simp [Hier, Brawl, he], rfl⟩, ⟨.g0, by simp [Hier, Brawl, he], rfl⟩⟩

theorem hier_no_deferral : ∀ t o p q, ¬ JointDeferral Hier t o p q := by
  rintro t o p q ⟨hc, hp, hq⟩
  have ht := reach_even hier_move hc.2.1
  have ht' : ¬ (t+1) % 2 = 0 := by omega
  cases o
  cases p
  · exact hp (by simp [Grasps, Hier, Brawl, ht'])
  · cases q
    · exact hq (by simp [Grasps, Hier, Brawl, ht'])
    · exact hc.1 rfl

theorem hier_not_symmetric : ¬ Symmetric Hier := by
  intro h
  have he : (0:Nat) % 2 = 0 := rfl
  have hc : Converge Hier 0 .hammer .a .b :=
    ⟨by decide, ⟨.g0, by simp [Hier, Brawl], rfl⟩, ⟨.g0, by simp [Hier, Brawl], rfl⟩⟩
  have := (h 0 .hammer .a .b hc).mp (by simp [Grasps, Hier, Brawl])
  simp [Grasps, Hier, Brawl] at this

/-! ## Headline results -/

/-- **The full chain, with no primitive uptake, no assumed ostensive and no catastrophe.**
In this scene, taking-as is defined by response. The participants fight over the hammer
twice. Exhaustion plus mimetic symmetry then entail a joint deferral, which is the
ostensive. The ostensive is followed by an imperative (a fetch), its failure, an originary
declarative and the re-presentation of an independent symbolic node. -/
theorem emergence_by_response :
    ∃ (P O C G : Type) (S : BScene P O C G),
      Practice S ∧ Symmetric S ∧ Exhausting S ∧ ForcedPreservation S ∧
      (∃ t o, Clash S t o) ∧
      (∃ j a h o, Failed S j a h o) ∧
      (∃ n, ∀ v, Vertex S n v → ¬ Symbolic v) ∧
      ∃ n v, Independent S n v :=
  ⟨Pt, Ob, Cx, Gs, Fight.S, Fight.practice, Fight.symmetric, Fight.exhausting,
    Fight.forcedPreservation, ⟨1, .hammer, Fight.clashes.1⟩,
    ⟨6, .a, .b, .hammer, ⟨⟨.g1, rfl⟩, Fight.takes6, by simp [Fight.S, Fight.ctx, presentB]⟩⟩,
    ⟨9, Fight.no_symbolic_yet⟩, 11, .occ 6, Fight.independent⟩

/-- **Each ingredient is needed.** Fighting forever (no exhaustion), walking away (desire
fades) and a dominance hierarchy (no symmetry) each satisfy the physical axioms and the
other two ingredients, and in each nothing is ever taken as signifying anything. -/
theorem fatigue_hypotheses_needed :
    (∃ S : BScene Pt Ob Cx Gs, Practice S ∧ Symmetric S ∧ PersistentDesire S .hammer ∧
        ¬ Exhausting S ∧ ∀ t a h τ, ¬ Takes S t a h τ) ∧
    (∃ S : BScene Pt Ob Cx Gs, Practice S ∧ Symmetric S ∧ Exhausting S ∧
        Converge S 0 .hammer .a .b ∧ ¬ PersistentDesire S .hammer ∧
        ∀ t a h τ, ¬ Takes S t a h τ) ∧
    (∃ S : BScene Pt Ob Cx Gs, Practice S ∧ Exhausting S ∧ PersistentDesire S .hammer ∧
        ¬ Symmetric S ∧ ∀ t a h τ, ¬ Takes S t a h τ) :=
  ⟨⟨Brawl, brawl_practice, brawl_symmetric, brawl_desire, brawl_not_exhausting,
      no_signs_without_deferral Brawl brawl_no_deferral⟩,
   ⟨WalkAway, walk_practice, walk_symmetric, walk_exhausting, walk_converge,
      walk_desire_fades, no_signs_without_deferral WalkAway walk_no_deferral⟩,
   ⟨Hier, hier_practice, hier_exhausting, hier_desire, hier_not_symmetric,
      no_signs_without_deferral Hier hier_no_deferral⟩⟩

/-- **Minimal existence.** The only assumption is the physical fact that one can aim
only at what is present. No mimesis, exhaustion, restraint, reward, forcing or division
is assumed. There is a scene with no symbolic vertex up to some time, and an independent
symbolic node later. Together with `takes_origin`, `gansian_order`,
`no_symbolic_before_declarative` and `no_signs_without_deferral`, which use the same
single assumption or none at all, this is the minimal theory. -/
theorem minimal_emergence :
    ∃ (P O C G : Type) (S : BScene P O C G),
      (∀ g c o, S.aim g c o → S.present c o) ∧
      (∃ n, ∀ v, Vertex S n v → ¬ Symbolic v) ∧
      ∃ n v, Independent S n v :=
  ⟨Pt, Ob, Cx, Gs, Fight.S, Fight.practice.directed, ⟨9, Fight.no_symbolic_yet⟩,
    11, .occ 6, Fight.independent⟩

end GA.Behavioural
