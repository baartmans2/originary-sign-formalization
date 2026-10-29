import GaEmergence.Theorems

/-!
# Models

Three concrete scenes over the same small world: two participants `a` and `b`, one
physical object (a hammer), three contexts, four bodily forms.

* `Emergence`: all axioms hold, including A5. An ostensive is followed by a failed
  recurrence, two failed fetches and an originary declarative. The new symbolic node is then
  re-presented in a new context by the other participant. `sim` is non-transitive.
* `Collapse`: all axioms hold, including A5, but the hearer's symbolic attempt is not
  taken up and forcing lapses. No symbolic node ever arises. The declarative is possible,
  not inevitable.
* `Satisfied`: all axioms hold. The hearer brings the hammer, so the imperative is satisfied
  and the ostensive restored. No symbolic node ever arises.
-/

namespace GA.Models
open GA

-- Bound variables named `a` (a participant) are intended, not the constructor `Pt.a`.
set_option linter.constructorNameAsVariable false

inductive Pt | a | b deriving DecidableEq
inductive Ob | hammer deriving DecidableEq
inductive Cx | scene | absent | later deriving DecidableEq
inductive Gs | g0 | g1 | g2 | g3 deriving DecidableEq

/-- The hammer is present only in the original scene. -/
def presentB : Cx → Ob → Bool
  | .scene, .hammer => true
  | _, _ => false

/-- Felt similarity between acts-in-context. Note that (g3,later) ~ (g2,absent) ~ (g1,absent)
but not (g3,later) ~ (g1,absent): the relation is not transitive. -/
def simB : Gs × Cx → Gs × Cx → Bool
  | (.g1, .absent), (.g0, .scene)  => true
  | (.g2, .absent), (.g1, .absent) => true
  | (.g3, .later),  (.g2, .absent) => true
  | _, _ => false

/-! ## The emergence model -/

namespace Emergence

/-- t0: `a` makes form g0 at the hammer; `b` takes it up (ostensive).
t1: elsewhere, `a` makes g1, which is like g0; `b` takes it up as being about the absent hammer.
t2, t3: `b` tries to fetch the hammer and fails.
t4: `b` makes g2; `a` takes it up as being about the act at t1 (originary declarative).
t5: in a later context `a` makes g3, which is like g2; `b` takes it up as being about t1.
After that, nothing happens. Forcing is maximal (always on). -/
def S : Scene Pt Ob Cx Gs where
  present c o := presentB c o = true
  sim x y := simB x y = true
  deed
    | 0 => .sign .a .g0
    | 1 => .sign .a .g1
    | 2 => .fetch .b .hammer
    | 3 => .fetch .b .hammer
    | 4 => .sign .b .g2
    | 5 => .sign .a .g3
    | _ => .idle
  ctx
    | 0 => .scene
    | 1 | 2 | 3 | 4 => .absent
    | _ => .later
  uptake
    | 0 => some (.b, .phys .hammer)
    | 1 => some (.b, .phys .hammer)
    | 4 => some (.a, .occ 1)
    | 5 => some (.b, .occ 1)
    | _ => none
  forcing _ _ := True

theorem failure_inv {j : Nat} {a h : Pt} {o : Ob} (hf : Failure S j a h o) :
    j = 1 ∧ a = .a ∧ h = .b ∧ o = .hammer := by
  obtain ⟨⟨g, hd⟩, hu, hp⟩ := hf
  cases o
  revert hd hu hp
  match j with
  | 0 => intro _ _ hp; simp [S, presentB] at hp
  | 1 => intro hd hu _; simp [S] at hd hu; exact ⟨rfl, hd.1.symm, hu.symm, rfl⟩
  | 2 | 3 | 4 | 5 => intro _ hu _; simp [S] at hu
  | _ + 6 => intro _ hu _; simp [S] at hu

theorem failure1 : Failure S 1 .a .b .hammer :=
  ⟨⟨.g1, rfl⟩, rfl, by simp [S, presentB]⟩

theorem preserves14 : Preserves S 1 4 .a .b := ⟨⟨.g2, rfl⟩, rfl⟩

theorem open14 : Open S 1 4 .a .b .hammer := by
  refine ⟨failure1, fun k hk1 hk2 => ?_⟩
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl <;>
    simp [Supplies, Preserves, S, presentB]

theorem not_open_late {t : Nat} (ht : 5 ≤ t) : ¬ Open S 1 t .a .b .hammer :=
  fun ⟨_, h⟩ => (h 4 (by omega) (by omega)).2 preserves14

theorem recognition : Recognition S := by
  constructor
  intro t h τ
  match t with
  | 0 => intro hu; simp [S] at hu; obtain ⟨rfl, rfl⟩ := hu
         exact ⟨.a, .g0, rfl, by decide, Or.inl ⟨.hammer, rfl, rfl⟩⟩
  | 1 => intro hu; simp [S] at hu; obtain ⟨rfl, rfl⟩ := hu
         exact ⟨.a, .g1, rfl, by decide,
           Or.inr (Or.inl ⟨0, by omega, .a, .g0, .b, rfl, rfl, rfl⟩)⟩
  | 4 => intro hu; simp [S] at hu; obtain ⟨rfl, rfl⟩ := hu
         exact ⟨.b, .g2, rfl, by decide,
           Or.inr (Or.inr ⟨1, by omega, rfl, .hammer, open14⟩)⟩
  | 5 => intro hu; simp [S] at hu; obtain ⟨rfl, rfl⟩ := hu
         exact ⟨.a, .g3, rfl, by decide,
           Or.inr (Or.inl ⟨4, by omega, .b, .g2, .a, rfl, rfl, rfl⟩)⟩
  | 2 | 3 => intro hu; simp [S] at hu
  | _ + 6 => intro hu; simp [S] at hu

theorem forcedPreservation : ForcedPreservation S := by
  constructor
  · intro j t a h o hjt hop _
    obtain ⟨rfl, rfl, rfl, rfl⟩ := failure_inv hop.1
    rcases (by omega : t = 2 ∨ t = 3 ∨ t = 4 ∨ 5 ≤ t) with rfl | rfl | rfl | ht
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨.g2, rfl⟩
    · exact absurd hop (not_open_late ht)
  · intro j a h o hf
    obtain ⟨rfl, rfl, rfl, rfl⟩ := failure_inv hf
    exact ⟨4, fun t ht hu => not_open_late (by omega) hu.1⟩

theorem admissible : Admissible S := ⟨recognition, forcedPreservation⟩

theorem nontrivial : Nontrivial S where
  plurality := ⟨.a, .b, by decide⟩
  ostension := ⟨0, .b, .hammer, rfl, rfl⟩
  recurrenceInAbsence := ⟨1, .a, .b, .hammer, failure1⟩
  forcingBites := ⟨1, 4, .a, .b, .hammer, by omega, open14, trivial⟩

/-- Recurrence here is not an equivalence relation, so it induces no sign-types. -/
theorem sim_not_transitive : ¬ ∀ x y z, S.sim x y → S.sim y z → S.sim x z :=
  fun h => absurd (h (.g3, .later) (.g2, .absent) (.g1, .absent) rfl rfl) (by simp [S, simB])

/-! The modes, read off the history. -/

theorem ostensive0 : Ostensive S 0 .hammer := ⟨.b, rfl, rfl⟩
theorem imperative_attempts : ImperativeAttempt S 1 2 ∧ ImperativeAttempt S 1 3 := by
  refine ⟨⟨.a, .b, .hammer, failure1, by omega, ?_, rfl⟩,
          ⟨.a, .b, .hammer, failure1, by omega, ?_, rfl⟩⟩ <;>
  refine ⟨failure1, fun k hk1 hk2 => ?_⟩ <;>
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl <;>
  simp [Supplies, Preserves, S, presentB]
theorem originary_declarative : OriginaryDeclarative S 1 4 :=
  ⟨.a, .b, .hammer, open14, preserves14⟩
theorem declarative5 : Declarative S 5 := ⟨.b, 1, rfl⟩

/-! The graph. -/

/-- Up to time 4 there are only physical vertices and no arcs. -/
theorem no_graph_yet : (∀ v, Vertex S 4 v → ¬ Symbolic v) ∧ (∀ v w, ¬ Arc S 4 v w) := by
  apply no_graph_before_declarative S recognition
  rintro j k hk ⟨a, h, o, _, _, hu⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp [S] at hu

/-- By time 6 the act at t1 has become a symbolic node. It has an arc to the absent hammer
and is taken up in two different contexts, by different hearers, with the hammer absent in both. -/
theorem independent_node : Independent S 6 (.occ 1) := by
  have hv : Vertex S 6 (.occ 1) := ⟨4, .a, by omega, rfl⟩
  exact ⟨⟨hv, fun _ h => by cases h⟩, 4, 5, .a, .b, .hammer, by omega, by omega,
    by simp [S], rfl, rfl, ⟨hv, 1, .b, rfl, by omega, rfl⟩, by simp [S, presentB],
    by simp [S, presentB]⟩

/-- The hypotheses of `GA.symbolic_node_of_forcing` hold here, so the general theorem
explains this declarative: it is entailed, not merely exhibited. -/
theorem unavailable : ∀ t, 1 < t → ¬ S.present (S.ctx t) .hammer := by
  intro t ht
  match t with
  | 0 | 1 => omega
  | 2 | 3 | 4 | 5 => simp [S, presentB]
  | _ + 6 => simp [S, presentB]

example : ∃ k, 1 < k ∧ SymbolicNode S (k+1) (.occ 1) ∧ Arc S (k+1) (.occ 1) (.phys .hammer) :=
  symbolic_node_of_forcing S admissible failure1 (fun _ _ => trivial) unavailable

end Emergence

/-! ## The collapse model -/

namespace Collapse

/-- As in `Emergence` up to t2. At t3 `b` makes g2, but `a` does not take it up.
Forcing lapses after t3 and nothing more happens. -/
def S : Scene Pt Ob Cx Gs where
  present c o := presentB c o = true
  sim x y := simB x y = true
  deed
    | 0 => .sign .a .g0
    | 1 => .sign .a .g1
    | 2 => .fetch .b .hammer
    | 3 => .sign .b .g2
    | _ => .idle
  ctx
    | 0 => .scene
    | _ => .absent
  uptake
    | 0 => some (.b, .phys .hammer)
    | 1 => some (.b, .phys .hammer)
    | _ => none
  forcing _ t := t ≤ 3

theorem uptake_phys {k : Nat} {h : Pt} {τ : Target Ob} (hu : S.uptake k = some (h, τ)) :
    τ = .phys .hammer := by
  revert hu
  match k with
  | 0 | 1 => intro hu; simp [S] at hu; exact hu.2.symm
  | _ + 2 => intro hu; simp [S] at hu

theorem failure_inv {j : Nat} {a h : Pt} {o : Ob} (hf : Failure S j a h o) :
    j = 1 ∧ a = .a ∧ h = .b ∧ o = .hammer := by
  obtain ⟨⟨g, hd⟩, hu, hp⟩ := hf
  cases o
  revert hd hu hp
  match j with
  | 0 => intro _ _ hp; simp [S, presentB] at hp
  | 1 => intro hd hu _; simp [S] at hd hu; exact ⟨rfl, hd.1.symm, hu.symm, rfl⟩
  | _ + 2 => intro _ hu _; simp [S] at hu

theorem failure1 : Failure S 1 .a .b .hammer := ⟨⟨.g1, rfl⟩, rfl, by simp [S, presentB]⟩

/-- The failure is never resolved. -/
theorem open_forever : ∀ t, 1 < t → Open S 1 t .a .b .hammer := by
  intro t _
  refine ⟨failure1, fun k hk _ => ⟨fun ⟨_, hp⟩ => ?_, fun ⟨_, hu⟩ => ?_⟩⟩
  · -- the context after any time is `absent`, so a fetch never brings the hammer
    simp [S, presentB] at hp
  · cases uptake_phys hu

theorem deed_late {t : Nat} (ht : 3 < t) : S.deed t = .idle := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 4 := ⟨t - 4, by omega⟩
  rfl

theorem admissible : Admissible S := by
  refine ⟨⟨fun t h τ => ?_⟩, ⟨?_, ?_⟩⟩
  · match t with
    | 0 => intro hu; simp [S] at hu; obtain ⟨rfl, rfl⟩ := hu
           exact ⟨.a, .g0, rfl, by decide, Or.inl ⟨.hammer, rfl, rfl⟩⟩
    | 1 => intro hu; simp [S] at hu; obtain ⟨rfl, rfl⟩ := hu
           exact ⟨.a, .g1, rfl, by decide,
             Or.inr (Or.inl ⟨0, by omega, .a, .g0, .b, rfl, rfl, rfl⟩)⟩
    | _ + 2 => intro hu; simp [S] at hu
  · intro j t a h o hjt hop hforce
    obtain ⟨rfl, rfl, rfl, rfl⟩ := failure_inv hop.1
    have : t ≤ 3 := hforce
    rcases (by omega : t = 2 ∨ t = 3) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨.g2, rfl⟩
  · intro j a h o hf
    obtain ⟨rfl, rfl, rfl, rfl⟩ := failure_inv hf
    refine ⟨3, fun t ht ⟨_, hu⟩ => ?_⟩
    rw [deed_late ht] at hu
    rcases hu with ⟨hd, _⟩ | ⟨⟨_, hd⟩, _⟩ <;> cases hd

theorem nontrivial : Nontrivial S where
  plurality := ⟨.a, .b, by decide⟩
  ostension := ⟨0, .b, .hammer, rfl, rfl⟩
  recurrenceInAbsence := ⟨1, .a, .b, .hammer, failure1⟩
  forcingBites := ⟨1, 2, .a, .b, .hammer, by omega, open_forever 2 (by omega), by simp [S]⟩

/-- Recognition is not universal: `b`'s act at t3 is taken up by no one. -/
theorem unrecognized_act : (∃ p g, S.deed 3 = .sign p g) ∧ S.uptake 3 = none :=
  ⟨⟨.b, .g2, rfl⟩, rfl⟩

theorem never_symbolic : ∀ n v, Vertex S n v → ¬ Symbolic v := by
  intro n v hv hsym
  obtain ⟨t, h, _, hu⟩ := hv
  exact hsym .hammer (uptake_phys hu)

end Collapse

/-! ## The satisfied-imperative model -/

namespace Satisfied

/-- As in `Emergence` up to t1. At t2 `b` fetches the hammer and it arrives, so the context
at t3 is again the scene, where `a` makes g0 and `b` takes it up ostensively. -/
def S : Scene Pt Ob Cx Gs where
  present c o := presentB c o = true
  sim x y := simB x y = true
  deed
    | 0 => .sign .a .g0
    | 1 => .sign .a .g1
    | 2 => .fetch .b .hammer
    | 3 => .sign .a .g0
    | _ => .idle
  ctx
    | 0 => .scene
    | 1 | 2 => .absent
    | _ => .scene
  uptake
    | 0 => some (.b, .phys .hammer)
    | 1 => some (.b, .phys .hammer)
    | 3 => some (.b, .phys .hammer)
    | _ => none
  forcing _ _ := True

theorem uptake_phys {k : Nat} {h : Pt} {τ : Target Ob} (hu : S.uptake k = some (h, τ)) :
    τ = .phys .hammer := by
  revert hu
  match k with
  | 0 | 1 | 3 => intro hu; simp [S] at hu; exact hu.2.symm
  | 2 => intro hu; simp [S] at hu
  | _ + 4 => intro hu; simp [S] at hu

theorem failure_inv {j : Nat} {a h : Pt} {o : Ob} (hf : Failure S j a h o) :
    j = 1 ∧ a = .a ∧ h = .b ∧ o = .hammer := by
  obtain ⟨⟨g, hd⟩, hu, hp⟩ := hf
  cases o
  revert hd hu hp
  match j with
  | 0 | 3 => intro _ _ hp; simp [S, presentB] at hp
  | 1 => intro hd hu _; simp [S] at hd hu; exact ⟨rfl, hd.1.symm, hu.symm, rfl⟩
  | 2 => intro _ hu _; simp [S] at hu
  | _ + 4 => intro _ hu _; simp [S] at hu

theorem failure1 : Failure S 1 .a .b .hammer := ⟨⟨.g1, rfl⟩, rfl, by simp [S, presentB]⟩
theorem supplies2 : Supplies S 2 .b .hammer := ⟨rfl, rfl⟩

theorem open12 : Open S 1 2 .a .b .hammer := by
  refine ⟨failure1, fun k hk1 hk2 => ?_⟩
  obtain rfl : k = 1 := by omega
  simp [Supplies, Preserves, S]

theorem not_open_late {t : Nat} (ht : 3 ≤ t) : ¬ Open S 1 t .a .b .hammer :=
  fun ⟨_, h⟩ => (h 2 (by omega) (by omega)).1 supplies2

theorem admissible : Admissible S := by
  refine ⟨⟨fun t h τ => ?_⟩, ⟨?_, ?_⟩⟩
  · match t with
    | 0 => intro hu; simp [S] at hu; obtain ⟨rfl, rfl⟩ := hu
           exact ⟨.a, .g0, rfl, by decide, Or.inl ⟨.hammer, rfl, rfl⟩⟩
    | 1 => intro hu; simp [S] at hu; obtain ⟨rfl, rfl⟩ := hu
           exact ⟨.a, .g1, rfl, by decide,
             Or.inr (Or.inl ⟨0, by omega, .a, .g0, .b, rfl, rfl, rfl⟩)⟩
    | 3 => intro hu; simp [S] at hu; obtain ⟨rfl, rfl⟩ := hu
           exact ⟨.a, .g0, rfl, by decide, Or.inl ⟨.hammer, rfl, rfl⟩⟩
    | 2 => intro hu; simp [S] at hu
    | _ + 4 => intro hu; simp [S] at hu
  · intro j t a h o hjt hop _
    obtain ⟨rfl, rfl, rfl, rfl⟩ := failure_inv hop.1
    rcases (by omega : t = 2 ∨ 3 ≤ t) with rfl | ht
    · exact Or.inl rfl
    · exact absurd hop (not_open_late ht)
  · intro j a h o hf
    obtain ⟨rfl, rfl, rfl, rfl⟩ := failure_inv hf
    exact ⟨2, fun t ht hu => not_open_late (by omega) hu.1⟩

theorem nontrivial : Nontrivial S where
  plurality := ⟨.a, .b, by decide⟩
  ostension := ⟨0, .b, .hammer, rfl, rfl⟩
  recurrenceInAbsence := ⟨1, .a, .b, .hammer, failure1⟩
  forcingBites := ⟨1, 2, .a, .b, .hammer, by omega, open12, trivial⟩

theorem imperative_satisfied : ImperativeSatisfied S 1 2 :=
  ⟨.a, .b, .hammer, failure1, by omega, supplies2⟩

/-- The completed imperative restores the ostensive. -/
theorem ostensive_restored : Ostensive S 3 .hammer := ⟨.b, rfl, rfl⟩

theorem never_symbolic : ∀ n v, Vertex S n v → ¬ Symbolic v := by
  intro n v hv hsym
  obtain ⟨t, h, _, hu⟩ := hv
  exact hsym .hammer (uptake_phys hu)

end Satisfied

/-! ## Headline results -/

/-- **Existence.** There is a nontrivial model of the refined axioms (with A5) in which
* similarity is not transitive (no abstract sign-identity),
* for an initial stretch of the history the interaction graph has only physical vertices and no arcs,
* later an independently representable symbolic node arises, with an arc to an absent
  physical object, taken up in two distinct contexts. -/
theorem emergence_is_possible :
    ∃ (P O C G : Type) (S : Scene P O C G),
      Admissible S ∧ Nontrivial S ∧
      ¬ (∀ x y z, S.sim x y → S.sim y z → S.sim x z) ∧
      (∃ n, (∀ v, Vertex S n v → ¬ Symbolic v) ∧ ∀ v w, ¬ Arc S n v w) ∧
      ∃ n v, Independent S n v :=
  ⟨Pt, Ob, Cx, Gs, Emergence.S, Emergence.admissible, Emergence.nontrivial,
    Emergence.sim_not_transitive, ⟨4, Emergence.no_graph_yet⟩, 6, .occ 1,
    Emergence.independent_node⟩

/-- **Non-inevitability.** There is a nontrivial model of the same axioms, with the same
world and with A5 available, in which no symbolic node ever arises: the failure is
neither satisfied nor preserved, and forcing lapses. -/
theorem emergence_not_inevitable :
    ∃ (P O C G : Type) (S : Scene P O C G),
      Admissible S ∧ Nontrivial S ∧ ∀ n v, Vertex S n v → ¬ Symbolic v :=
  ⟨Pt, Ob, Cx, Gs, Collapse.S, Collapse.admissible, Collapse.nontrivial,
    Collapse.never_symbolic⟩

end GA.Models
