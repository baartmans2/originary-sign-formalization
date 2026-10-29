import GaEmergence.Models

/-!
# Removing the ostensive from the axioms

In `Basic.lean` the ostensive is assumed: `OstGround` makes "the object is present" a
primitive ground for taking an act as being about it. This file removes that ground and
replaces it with a **practical layer** that contains no signs and no aboutness:

* bodies make movements, and a movement can be physically *aimed* at an object, which
  must therefore be there (`aim`; this is geometry, not reference);
* bodies *grasp* objects;
* two participants *converge* when both reach for the same object at the same time;
* a *clash* is two participants grasping the same object at once;
* `restraint` is an unspecified forcing function that makes a clash untenable. It plays
  the role of the forcing in Axiom 4, but in the originary scene.

The ostensive then becomes a derived pattern: a **joint deferral**, i.e. convergent reaches
that are not completed. The only ground for taking an act as being about a *present*
object is now that the hearer has jointly deferred the same appropriation (`OrigGround`).

What remains primitive is `uptake` itself, the record of one participant *taking* another's
act as signifying something. What is no longer primitive is that physical presence alone
can ground such taking.
-/

namespace GA

-- Bound variables named `a` (a participant) are intended, not the constructor `Pt.a`.
set_option linter.constructorNameAsVariable false

/-- A scene with a practical layer. The `Scene` part is unchanged. The new fields record
what every participant's body does, which allows simultaneous convergence. -/
structure OScene (P O C G : Type) extends Scene P O C G where
  /-- movement form `g` in context `c` is physically directed at `o` -/
  aim       : G → C → O → Prop
  /-- the movement (if any) each participant makes at each time -/
  moves     : Nat → P → Option G
  /-- the object (if any) each participant appropriates at each time -/
  grasps    : Nat → P → Option O
  /-- unspecified forcing in the originary scene: at `t`, a clash over `o` is untenable -/
  restraint : Nat → O → Prop

section
variable {P O C G : Type} (S : OScene P O C G)

def Reaches (t : Nat) (p : P) (o : O) : Prop :=
  ∃ g, S.moves t p = some g ∧ S.aim g (S.ctx t) o

def Grasps (t : Nat) (p : P) (o : O) : Prop := S.grasps t p = some o

/-- Two distinct participants reach for the same object at the same time. -/
def Converge (t : Nat) (o : O) (p q : P) : Prop :=
  p ≠ q ∧ Reaches S t p o ∧ Reaches S t q o

def Clash (t : Nat) (o : O) : Prop :=
  ∃ p q, p ≠ q ∧ Grasps S t p o ∧ Grasps S t q o

/-- Convergent reaches that neither participant completes. This is the aborted gesture of
appropriation, defined purely in practical terms. -/
def JointDeferral (t : Nat) (o : O) (p q : P) : Prop :=
  Converge S t o p q ∧ ¬ Grasps S (t+1) p o ∧ ¬ Grasps S (t+1) q o

/-- The originary ground, which replaces `OstGround`. The hearer `h` can take the author's
movement as being about `o` because both reached for `o` and both refrained. -/
def OrigGround (t : Nat) (h : P) (τ : Target O) : Prop :=
  ∃ a o, τ = .phys o ∧ (∃ g, S.deed t = .sign a g) ∧ JointDeferral S t o a h

end

variable {P O C G : Type}

/-- Physical constraints on the practical layer (nothing semiotic):
a movement can be aimed only at something present, an author's recorded movement is
something its body does, and one can grasp only what one has just reached for. -/
structure Practice (S : OScene P O C G) : Prop where
  directed  : ∀ g c o, S.aim g c o → S.present c o
  embodied  : ∀ t a g, S.deed t = .sign a g → S.moves t a = some g
  completes : ∀ t p o, Grasps S (t+1) p o → Reaches S t p o

/-- Gans's minimal hypothesis, with the reason for restraint left unspecified.
`symmetric`: between converging participants, neither completes the appropriation unless
the other does too (mimetic symmetry, with no hierarchy to settle who gets the object).
`restrained`: where restraint holds, a clash does not occur. -/
structure MimeticCrisis (S : OScene P O C G) : Prop where
  symmetric  : ∀ t o p q, Converge S t o p q → (Grasps S (t+1) p o ↔ Grasps S (t+1) q o)
  restrained : ∀ t o, S.restraint t o → ¬ Clash S t o

/-- Recognition with **no ostensive ground**: an uptake rests on joint deferral, on
recurrence, or (A5) on reflexivity. -/
structure RecognitionO (S : OScene P O C G) : Prop where
  recog : ∀ t h τ, S.uptake t = some (h, τ) →
    ∃ a g, S.deed t = .sign a g ∧ a ≠ h ∧
      (OrigGround S t h τ ∨ RecGround S.toScene t g τ ∨ ReflGround S.toScene t a h τ)

section
variable (S : OScene P O C G)

/-- **The ostensive ground is now a theorem.** Joint deferral yields an object that is
present, because aiming is physical. (Uses: Practice.directed.) -/
theorem OrigGround.toOstGround (hP : Practice S) {t : Nat} {h : P} {τ : Target O}
    (hg : OrigGround S t h τ) : OstGround S.toScene t τ := by
  obtain ⟨_, o, rfl, _, ⟨_, ⟨_, _, haim⟩, _⟩, _, _⟩ := hg
  exact ⟨o, rfl, hP.directed _ _ _ haim⟩

/-- **Bridge.** A scene satisfying the ostensive-free axioms satisfies the earlier ones.
Hence every theorem in `Theorems.lean` (the Gansian order, no graph before the
declarative, the forcing results) holds for scenes in which the ostensive is not assumed. -/
theorem RecognitionO.toRecognition (hP : Practice S) (hR : RecognitionO S) :
    Recognition S.toScene := by
  refine ⟨fun t h τ hu => ?_⟩
  obtain ⟨a, g, hd, hne, hg⟩ := hR.recog t h τ hu
  refine ⟨a, g, hd, hne, ?_⟩
  rcases hg with hg | hr | hr
  · exact Or.inl (OrigGround.toOstGround S hP hg)
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr hr)

/-- **Deferral is entailed by the crisis.** Under mimetic symmetry and restraint, convergent
reaching cannot be completed by either participant. (Uses: MimeticCrisis.) -/
theorem deferral_entailed (hM : MimeticCrisis S) {t : Nat} {o : O} {p q : P}
    (hc : Converge S t o p q) (hr : S.restraint (t+1) o) : JointDeferral S t o p q := by
  have hnp : ¬ Grasps S (t+1) p o := fun hp =>
    hM.restrained (t+1) o hr ⟨p, q, hc.1, hp, (hM.symmetric t o p q hc).mp hp⟩
  exact ⟨hc, hnp, fun hq => hnp ((hM.symmetric t o p q hc).mpr hq)⟩

/-- Consequently, whenever an author and a hearer converge under restraint, the originary
ground for an uptake is available: the ostensive is *licensed* by the crisis. -/
theorem ostensive_licensed (hM : MimeticCrisis S) {t : Nat} {o : O} {a h : P} {g : G}
    (hd : S.deed t = .sign a g) (hc : Converge S t o a h) (hr : S.restraint (t+1) o) :
    OrigGround S t h (.phys o) :=
  ⟨a, o, rfl, ⟨g, hd⟩, deferral_entailed S hM hc hr⟩

/-- **Every sign descends from an aborted gesture of appropriation.** Each relation to an
object descends, through a chain of local recurrences, from a joint deferral of a
convergent reach for that object. (Uses: RecognitionO. Proof by strong induction.) -/
theorem genealogyO (hR : RecognitionO S) (o : O) :
    ∀ t h, S.uptake t = some (h, .phys o) →
      ∃ s p q, s ≤ t ∧ JointDeferral S s o p q ∧ Lineage S.toScene s t := by
  intro t
  induction t using strongInd with
  | step t ih =>
    intro h hu
    obtain ⟨a, g, hd, _, hg⟩ := hR.recog t h _ hu
    rcases hg with ⟨a', o', ho', _, hjd⟩ | ⟨s, hs, a', g', h', hd', hu', hsim⟩ | ⟨_, _, hτ, _⟩
    · cases ho'
      exact ⟨t, a', h, Nat.le_refl t, hjd, .refl t⟩
    · obtain ⟨s₀, p, q, hs₀, hj, hlin⟩ := ih s hs h' hu'
      exact ⟨s₀, p, q, by omega, hj, .echo hlin hs ⟨a, g, a', g', hd, hd', hsim⟩⟩
    · cases hτ

/-- **No deferral, no signs at all.** If convergent appropriation is never jointly deferred,
nothing is ever taken up as signifying anything: no ostensive, imperative or declarative.
(Uses: Practice, RecognitionO.) -/
theorem no_signs_without_deferral (hP : Practice S) (hR : RecognitionO S)
    (hnone : ∀ t o p q, ¬ JointDeferral S t o p q) : ∀ t, S.uptake t = none := by
  have hphys : ∀ t h o, S.uptake t ≠ some (h, .phys o) := by
    intro t h o hu
    obtain ⟨s, p, q, _, hj, _⟩ := genealogyO S hR o t h hu
    exact hnone s o p q hj
  intro t
  cases hu : S.uptake t with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨h, τ⟩ := x
    cases τ with
    | phys o => exact hphys t h o hu
    | occ j =>
      obtain ⟨_, _, _, _, h', o, hopen, _⟩ :=
        declarative_origin S.toScene (RecognitionO.toRecognition S hP hR) t h j hu
      exact hphys j h' o hopen.1.2.1

end

/-! ## Models -/

namespace Originary
open GA.Models

/-- In the original scene, movement g0 is aimed at the hammer. No other movement is aimed
at anything: g1, made where the hammer is absent, is physically aimless. -/
def aimB : Gs → Cx → Ob → Bool
  | .g0, .scene, .hammer => true
  | _, _, _ => false

theorem aimB_directed (g : Gs) (c : Cx) (o : Ob) (h : aimB g c o = true) :
    presentB c o = true := by
  cases g <;> cases c <;> cases o <;> simp [aimB, presentB] at h ⊢

/-! ### The full chain, with the ostensive derived -/

/-- `Emergence.S`, plus a body for every participant. At t0 *both* `a` and `b` reach for the
hammer, and no one ever grasps anything. Restraint holds everywhere. -/
def OE : OScene Pt Ob Cx Gs where
  toScene := Emergence.S
  aim g c o := aimB g c o = true
  moves
    | 0, _ => some .g0
    | 1, .a => some .g1
    | 4, .b => some .g2
    | 5, .a => some .g3
    | _, _ => none
  grasps _ _ := none
  restraint _ _ := True

theorem practice : Practice OE where
  directed g c o h := aimB_directed g c o h
  embodied t a g := by
    match t with
    | 0 | 1 | 4 | 5 =>
      intro hd; simp [OE, Emergence.S] at hd; obtain ⟨rfl, rfl⟩ := hd; rfl
    | 2 | 3 => intro hd; simp [OE, Emergence.S] at hd
    | _ + 6 => intro hd; simp [OE, Emergence.S] at hd
  completes _ _ _ h := by simp [Grasps, OE] at h

theorem crisis : MimeticCrisis OE where
  symmetric _ _ _ _ _ :=
    ⟨fun h => by simp [Grasps, OE] at h, fun h => by simp [Grasps, OE] at h⟩
  restrained _ _ _ := fun ⟨_, _, _, h, _⟩ => by simp [Grasps, OE] at h

theorem converge0 : Converge OE 0 .hammer .a .b :=
  ⟨by decide, ⟨.g0, rfl, rfl⟩, ⟨.g0, rfl, rfl⟩⟩

/-- The deferral at t0 is not stipulated: it follows from convergence, mimetic symmetry
and restraint. -/
theorem deferral0 : JointDeferral OE 0 .hammer .a .b :=
  deferral_entailed OE crisis converge0 trivial

theorem recognitionO : RecognitionO OE := by
  constructor
  intro t h τ
  match t with
  | 0 => intro hu; simp [OE, Emergence.S] at hu; obtain ⟨rfl, rfl⟩ := hu
         exact ⟨.a, .g0, rfl, by decide,
           Or.inl (ostensive_licensed OE crisis rfl converge0 trivial)⟩
  | 1 => intro hu; simp [OE, Emergence.S] at hu; obtain ⟨rfl, rfl⟩ := hu
         exact ⟨.a, .g1, rfl, by decide,
           Or.inr (Or.inl ⟨0, by omega, .a, .g0, .b, rfl, rfl, rfl⟩)⟩
  | 4 => intro hu; simp [OE, Emergence.S] at hu; obtain ⟨rfl, rfl⟩ := hu
         exact ⟨.b, .g2, rfl, by decide,
           Or.inr (Or.inr ⟨1, by omega, rfl, .hammer, Emergence.open14⟩)⟩
  | 5 => intro hu; simp [OE, Emergence.S] at hu; obtain ⟨rfl, rfl⟩ := hu
         exact ⟨.a, .g3, rfl, by decide,
           Or.inr (Or.inl ⟨4, by omega, .b, .g2, .a, rfl, rfl, rfl⟩)⟩
  | 2 | 3 => intro hu; simp [OE, Emergence.S] at hu
  | _ + 6 => intro hu; simp [OE, Emergence.S] at hu

/-- The inappropriate ostensive at t1 is a physically aimless movement: g1 is aimed at nothing. -/
theorem aimless1 : ∀ o, ¬ Reaches OE 1 .a o := by
  rintro o ⟨g, hm, haim⟩
  simp [OE] at hm
  subst hm
  cases o
  simp [OE, aimB] at haim

/-! ### Each hypothesis of `deferral_entailed` is needed -/

/-- **Hierarchy.** Both reach for the hammer and restraint holds, but `a` is dominant: `a`
grasps and `b` does not. There is no clash, so restraint is respected, but symmetry fails
and nothing is deferred jointly. -/
def Hier : OScene Pt Ob Cx Gs where
  present c o := presentB c o = true
  sim x y := simB x y = true
  deed
    | 0 => .sign .a .g0
    | _ => .idle
  ctx _ := .scene
  uptake _ := none
  forcing _ _ := False
  aim g c o := aimB g c o = true
  moves
    | 0, _ => some .g0
    | _, _ => none
  grasps
    | 1, .a => some .hammer
    | _, _ => none
  restraint _ _ := True

theorem hier_practice : Practice Hier where
  directed g c o h := aimB_directed g c o h
  embodied t a g := by
    match t with
    | 0 => intro hd; simp [Hier] at hd; obtain ⟨rfl, rfl⟩ := hd; rfl
    | _ + 1 => intro hd; simp [Hier] at hd
  completes t p o h := by
    match t, p with
    | 0, .a => cases o; exact ⟨.g0, rfl, rfl⟩
    | 0, .b => simp [Grasps, Hier] at h
    | _ + 1, .a => simp [Grasps, Hier] at h
    | _ + 1, .b => simp [Grasps, Hier] at h

theorem hier_restrained : ∀ t o, Hier.restraint t o → ¬ Clash Hier t o := by
  rintro t o _ ⟨p, q, hne, hp, hq⟩
  match t, p, q with
  | 1, .a, .a => exact hne rfl
  | 1, .b, _ => simp [Grasps, Hier] at hp
  | 1, .a, .b => simp [Grasps, Hier] at hq
  | 0, _, _ => simp [Grasps, Hier] at hp
  | _ + 2, _, _ => simp [Grasps, Hier] at hp

theorem hier_converge : Converge Hier 0 .hammer .a .b :=
  ⟨by decide, ⟨.g0, rfl, rfl⟩, ⟨.g0, rfl, rfl⟩⟩

theorem hier_not_symmetric :
    ¬ ∀ t o p q, Converge Hier t o p q → (Grasps Hier (t+1) p o ↔ Grasps Hier (t+1) q o) :=
  fun h => by
    have := (h 0 .hammer .a .b hier_converge).mp rfl
    simp [Grasps, Hier] at this

theorem hier_no_deferral : ¬ JointDeferral Hier 0 .hammer .a .b :=
  fun ⟨_, ha, _⟩ => ha rfl

/-- **Rivalry.** Symmetric, but with no restraint: both grasp, which is a clash. -/
def Rival : OScene Pt Ob Cx Gs :=
  { Hier with
    grasps := fun t _ => if t = 1 then some .hammer else none
    restraint := fun _ _ => False }

theorem rival_practice : Practice Rival where
  directed g c o h := aimB_directed g c o h
  embodied := hier_practice.embodied
  completes t p o h := by
    have ht : t = 0 := by
      by_cases h0 : t = 0
      · exact h0
      · simp [Grasps, Rival, h0] at h
    subst ht
    cases o
    exact ⟨.g0, rfl, rfl⟩

theorem rival_symmetric : ∀ t o p q, Converge Rival t o p q →
    (Grasps Rival (t+1) p o ↔ Grasps Rival (t+1) q o) := by
  intro t o p q _
  simp [Grasps, Rival]

theorem rival_converge : Converge Rival 0 .hammer .a .b :=
  ⟨by decide, ⟨.g0, rfl, rfl⟩, ⟨.g0, rfl, rfl⟩⟩

theorem rival_clash : Clash Rival 1 .hammer := ⟨.a, .b, by decide, rfl, rfl⟩

theorem rival_no_deferral : ¬ JointDeferral Rival 0 .hammer .a .b :=
  fun ⟨_, ha, _⟩ => ha rfl

end Originary

/-! ## Headline results -/

open GA.Models GA.Originary in
/-- **Emergence without an assumed ostensive.** There is a scene satisfying
* the practical axioms and Gans's minimal hypothesis (mimetic symmetry, unspecified restraint),
* recognition with *no ostensive ground*, and forced preservation,

in which the only scene-setting condition is practical (two participants converge on an
object under restraint). In it, a joint deferral is *entailed*, that deferral grounds an
ostensive, the ostensive is followed by a failure and imperative attempts, and an
independently representable symbolic node arises. -/
theorem emergence_from_practice :
    ∃ (P O C G : Type) (S : OScene P O C G),
      Practice S ∧ MimeticCrisis S ∧ RecognitionO S ∧ ForcedPreservation S.toScene ∧
      (∃ t o p q, Converge S t o p q ∧ S.restraint (t+1) o) ∧
      (∃ j a h o, Failure S.toScene j a h o) ∧
      (∃ n, (∀ v, Vertex S.toScene n v → ¬ Symbolic v) ∧ ∀ v w, ¬ Arc S.toScene n v w) ∧
      ∃ n v, Independent S.toScene n v :=
  ⟨Pt, Ob, Cx, Gs, OE, practice, crisis, recognitionO, Emergence.forcedPreservation,
    ⟨0, .hammer, .a, .b, converge0, trivial⟩, ⟨1, .a, .b, .hammer, Emergence.failure1⟩,
    ⟨4, no_graph_before_declarative OE.toScene
          (RecognitionO.toRecognition OE practice recognitionO) 4
          (by
            rintro j k hk ⟨a, h, o, _, _, hu⟩
            rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
              simp [OE, Emergence.S] at hu)⟩,
    6, .occ 1, Emergence.independent_node⟩

open GA.Models GA.Originary in
/-- **Each half of the crisis is needed.** Convergence under restraint without symmetry
(hierarchy), and convergence with symmetry but without restraint (rivalry), both satisfy
the physical axioms and both fail to produce a joint deferral. -/
theorem crisis_hypotheses_needed :
    (∃ S : OScene Pt Ob Cx Gs, Practice S ∧
        (∀ t o, S.restraint t o → ¬ Clash S t o) ∧
        Converge S 0 .hammer .a .b ∧ S.restraint 1 .hammer ∧
        ¬ JointDeferral S 0 .hammer .a .b) ∧
    (∃ S : OScene Pt Ob Cx Gs, Practice S ∧
        (∀ t o p q, Converge S t o p q → (Grasps S (t+1) p o ↔ Grasps S (t+1) q o)) ∧
        Converge S 0 .hammer .a .b ∧
        ¬ JointDeferral S 0 .hammer .a .b) :=
  ⟨⟨Hier, hier_practice, hier_restrained, hier_converge, trivial, hier_no_deferral⟩,
   ⟨Rival, rival_practice, rival_symmetric, rival_converge, rival_no_deferral⟩⟩

end GA
