import GaEmergence.Completion

/-!
# Falsehood requires drift

Under kinematics, a pure declarative whose gesture *begins like* a reach for `o` is always
fulfilled when made. So in the systems so far, no declarative could be false.

Here:
* a **false declarative** is a pure declarative on a movement standing for `o` (by
  lineage), made while `o` is within reach: its "don't be present" is unfulfilled;
* **coherence** says onset-matching survives full matching: whatever begins like `m`
  also begins like anything `m` fully matches;
* `no_falsehood_without_drift`: with coherence and kinematics, **no declarative is
  false**. Falsehood needs a lineage along which the onset has been lost;
* `false_requires_arbitrary`: in a false declarative, the movement made with the object
  in reach does not begin like any earlier reach for that object. The sign has become
  arbitrary;
* `Drift`: a model satisfying every axiom, kinematics included, in which a lineage drifts
  (g0 ~ g1 ~ g2, not g0 ~ g2) and a false declarative occurs.
-/

namespace GA.Completion

set_option linter.constructorNameAsVariable false

section
variable {P O M : Type} (W : World P O M)

/-- A pure declarative whose node stands for `o` by lineage. -/
def DeclStandsFor (t t' s : Nat) (r p q : P) (o : O) : Prop :=
  Declarative W t t' s r p q ∧ Pure W t p ∧ Pure W t' q ∧ Descends W s r o

/-- False: "don't be present" is unfulfilled, i.e. `o` is within reach of a participant. -/
def FalseDecl (t t' s : Nat) (r p q : P) (o : O) : Prop :=
  DeclStandsFor W t t' s r p q o ∧ (W.within t p o ∨ W.within t' q o)

/-- True: `o` is out of both participants' reach. -/
def TrueDecl (t t' s : Nat) (r p q : P) (o : O) : Prop :=
  DeclStandsFor W t t' s r p q o ∧ ¬ W.within t p o ∧ ¬ W.within t' q o

/-- Onset-matching survives full matching. Its failure is *drift*. -/
def Coherent : Prop := ∀ m' m m0, W.opens m' m → W.sim m m0 → W.opens m' m0

/-- Under coherence, beginning like a movement that descends from `o` means beginning
like some earlier movement that actually headed for `o`. -/
theorem lineage_root (hC : Coherent W) {s : Nat} {r : P} {o : O} (hD : Descends W s r o) :
    ∀ m m', W.mv s r = some m → W.opens m' m →
      ∃ s0 r0 m0, s0 ≤ s ∧ W.mv s0 r0 = some m0 ∧ W.heads s0 r0 o ∧ W.opens m' m0 := by
  induction hD with
  | @root s t' p q o hj =>
    intro m m' hm ho
    exact ⟨s, p, m, Nat.le_refl _, hm, hj.1.2.2.2.1.1, ho⟩
  | @step s t r p o m1 m2 hst hmr hmp hsim _ ih =>
    intro m m' hm ho
    rw [hmp] at hm
    cases hm
    obtain ⟨s0, r0, m0, h1, h2, h3, h4⟩ := ih m1 m' hmr (hC _ _ _ ho hsim)
    exact ⟨s0, r0, m0, by omega, h2, h3, h4⟩

/-- **No falsehood without drift.** With coherence and kinematics, every declarative that
stands for an object is fulfilled when made. -/
theorem no_falsehood_without_drift (hK : Kinematics W) (hC : Coherent W)
    {t t' s : Nat} {r p q : P} {o : O} : ¬ FalseDecl W t t' s r p q o := by
  rintro ⟨⟨hd, hp, hq, hD⟩, hw⟩
  obtain ⟨⟨_, htt', _, ⟨⟨hst, m, m', hm, hm', ho⟩, _⟩, ⟨⟨hst', n, n', hn, hn', hon⟩, _⟩, _⟩, _⟩ := hd
  rcases hw with hw | hw
  · obtain ⟨s0, r0, m0, h1, h2, h3, h4⟩ := lineage_root W hC hD m m' hm ho
    exact hp o (hK.transfer _ _ _ _ _ _ _ (by omega) h2 h3 hm' h4 hw)
  · obtain ⟨s0, r0, m0, h1, h2, h3, h4⟩ := lineage_root W hC hD n n' hn hon
    exact hq o (hK.transfer _ _ _ _ _ _ _ (by omega) h2 h3 hn' h4 hw)

/-- **Falsehood requires arbitrariness.** A pure movement made with `o` in reach does not
begin like any earlier reach for `o`. So in a false declarative, the movement made in the
object's presence has lost the shape of the reach it descends from. -/
theorem false_requires_arbitrary (hK : Kinematics W) {t : Nat} {p : P} {o : O}
    (hp : Pure W t p) (hw : W.within t p o) :
    ∀ s0 r0 m0 m', s0 < t → W.mv s0 r0 = some m0 → W.heads s0 r0 o →
      W.mv t p = some m' → ¬ W.opens m' m0 :=
  fun _ _ _ _ hs hm0 hh hm' ho => hp o (hK.transfer _ _ _ _ _ _ _ hs hm0 hh hm' ho hw)

end

/-! ## A drifting lineage -/

open GA.Models

/-- Forms: `r0` is the reach; `r1` ~ `r0`; `r2` ~ `r1` but not ~ `r0` (drift);
`x` begins like `r2` and breaks off. It begins like neither `r1` nor `r0`. -/
inductive Fm2 | r0 | r1 | r2 | x deriving DecidableEq

def sim2 : Fm2 → Fm2 → Bool
  | .r0, .r0 | .r1, .r1 | .r2, .r2 | .x, .x => true
  | .r0, .r1 | .r1, .r0 | .r1, .r2 | .r2, .r1 => true
  | _, _ => false

def opens2 : Fm2 → Fm2 → Bool
  | .x, .r2 => true
  | a, b => sim2 a b

namespace Drift

/-- Two ostensive episodes with a contrast (t0–t5), then drift, then two declarative
episodes with a contrast, all with the hammer back within reach:
* t0: `a` reaches (r0) and holds back; t1: `b` responds likewise. t2–t3: contrast.
  t4, t5: the episode again.
* t6: hammer out of reach; `a` makes r1 (~ r0). t7: `a` makes r2 (~ r1, not ~ r0).
* t8: the hammer is back. `b` begins r2 and breaks off (x); t9: `a` does the same.
  t10–t11: contrast. t12, t13: the declarative episode again.

The declarative on the t7 movement stands for the hammer and is made while the hammer is
present: false. -/
def mvL : List ((Nat × Pt) × Fm2) :=
  [((0, .a), .r0), ((1, .b), .r0), ((4, .a), .r0), ((5, .b), .r0), ((6, .a), .r1),
   ((7, .a), .r2), ((8, .b), .x), ((9, .a), .x), ((12, .b), .x), ((13, .a), .x)]

def mv (t : Nat) (p : Pt) : Option Fm2 := look mvL t p

def headsL : List (Nat × Pt) := [(0, .a), (1, .b), (4, .a), (5, .b)]
def percL : List (Nat × Pt × Pt) :=
  [(0, .b, .a), (1, .a, .b), (4, .b, .a), (5, .a, .b), (8, .a, .b), (9, .b, .a),
   (12, .a, .b), (13, .b, .a)]

def W : World Pt Ob Fm2 where
  opens x y := opens2 x y = true
  sim x y := sim2 x y = true
  mv := mv
  heads t p _ := (t, p) ∈ headsL
  contact _ _ _ := False
  within t _ _ := t ≤ 5 ∨ (8 ≤ t ∧ t ≤ 13)
  perceives t q p := (t, q, p) ∈ percL
  win := 1
  retained t p := t = 0 ∧ p = .a

theorem axioms : Axioms W where
  heads_within t p o h := by
    simp [W, headsL] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [W]
  heads_moving t p o h := by
    simp [W, headsL] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨.r0, rfl⟩
  contact_heads _ _ _ h := h.elim
  perceives_other t q p h := by
    simp [W, percL] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨by decide, .r0, rfl⟩
    · exact ⟨by decide, .r0, rfl⟩
    · exact ⟨by decide, .r0, rfl⟩
    · exact ⟨by decide, .r0, rfl⟩
    · exact ⟨by decide, .x, rfl⟩
    · exact ⟨by decide, .x, rfl⟩
    · exact ⟨by decide, .x, rfl⟩
    · exact ⟨by decide, .x, rfl⟩
  sim_refl m := by cases m <;> rfl
  sim_symm m m' h := by cases m <;> cases m' <;> simp [W, sim2] at h ⊢
  sim_opens m m' h := by cases m <;> cases m' <;> simp [W, sim2, opens2] at h ⊢
  retention t p h := by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨4, .r0, .r0, by omega, rfl, rfl, rfl⟩

/-- Everything that heads for the hammer has the reach form r0. -/
theorem heads_form {s : Nat} {r : Pt} {o : Ob} {m : Fm2} (hh : W.heads s r o)
    (hm : W.mv s r = some m) : m = .r0 := by
  simp [W, headsL] at hh
  rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · have h2 := look_mem hm
    simp [mvL] at h2
    subst h2; rfl

theorem kinematics : Kinematics W where
  transfer s t r p o m m' hst hm hh hm' ho hw := by
    have hm0 := heads_form hh hm
    subst hm0
    have hmem := look_mem hm'
    simp [mvL] at hmem
    rcases hmem with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ |
      ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ |
      ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;>
    first
      | (simp [W, headsL]; done)
      | (simp [W, opens2, sim2] at ho; done)
      | (simp [W] at hw; done)

theorem still {u : Nat} {q : Pt} {τ : Tgt Pt Ob} (hm : mv (u+1) q = none) :
    ∀ u', u < u' → u' ≤ u + W.win → ¬ Suspended W u' q τ := by
  intro u' h1 h2 hs
  have : u' = u + 1 := by simp [W] at h2; omega
  subst this
  cases τ with
  | obj o =>
    obtain ⟨g, hg⟩ := axioms.heads_moving _ _ _ hs.1
    rw [show W.mv (u+1) q = mv (u+1) q from rfl, hm] at hg; cases hg
  | act s r =>
    obtain ⟨_, _, m', _, hm', _⟩ := hs.1
    rw [show W.mv (u+1) q = mv (u+1) q from rfl, hm] at hm'; cases hm'

theorem episode (t : Nat) (h1 : (t, Pt.a) ∈ headsL) (h2 : (t+1, Pt.b) ∈ headsL)
    (h3 : (t, Pt.b, Pt.a) ∈ percL) (h4 : (t+1, Pt.a, Pt.b) ∈ percL) :
    Joint W t (t+1) (.obj .hammer) .a .b :=
  ⟨by decide, by omega, by simp [W], ⟨h1, fun h => h⟩, ⟨h2, fun h => h⟩, h3, h4⟩

theorem ostensive0 : Ostensive W 0 1 .hammer .a .b :=
  ⟨episode 0 (by simp [headsL]) (by simp [headsL]) (by simp [percL]) (by simp [percL]),
    ⟨4, 5, by decide,
      episode 4 (by simp [headsL]) (by simp [headsL]) (by simp [percL]) (by simp [percL]),
      .r0, .r0, rfl, rfl, rfl⟩,
    ⟨2, ⟨3, by omega, by simp [W], by simp [W]⟩,
      (fun ⟨_, _, _, h, _⟩ => by rw [show W.mv 2 .a = none from rfl] at h; cases h),
      still rfl⟩⟩

theorem descends7 : Descends W 7 .a .hammer :=
  Descends.step (W := W) (s := 6) (r := .a) (m := Fm2.r1) (m' := Fm2.r2) (by omega) rfl rfl rfl
    (Descends.step (W := W) (s := 0) (r := .a) (m := Fm2.r0) (m' := Fm2.r1) (by omega) rfl rfl
      rfl (Descends.root ostensive0))

theorem not_sim : ¬ W.sim Fm2.x Fm2.r2 := by simp [W, sim2]

theorem susp_x {t : Nat} {p : Pt} (hm : mv t p = some .x) (h : 7 < t) :
    Suspended W t p (.act 7 .a) := by
  refine ⟨⟨h, .r2, .x, rfl, hm, rfl⟩, ?_⟩
  rintro ⟨m, m', hm1, hm2, hs⟩
  rw [show W.mv 7 .a = some Fm2.r2 from rfl] at hm1
  cases hm1
  rw [show W.mv t p = mv t p from rfl, hm] at hm2
  cases hm2
  exact not_sim hs

theorem dEpisode (t : Nat) (hb : mv t .b = some .x) (ha : mv (t+1) .a = some .x) (h7 : 7 < t)
    (h3 : (t, Pt.a, Pt.b) ∈ percL) (h4 : (t+1, Pt.b, Pt.a) ∈ percL) :
    Joint W t (t+1) (.act 7 .a) .b .a :=
  ⟨by decide, by omega, by simp [W], susp_x hb h7, susp_x ha (by omega), h3, h4⟩

theorem false89 : FalseDecl W 8 9 7 .a .b .a .hammer :=
  ⟨⟨⟨dEpisode 8 rfl rfl (by omega) (by simp [percL]) (by simp [percL]),
      ⟨12, 13, by decide, dEpisode 12 rfl rfl (by omega) (by simp [percL]) (by simp [percL]),
        .x, .x, rfl, rfl, rfl⟩,
      ⟨10, (by omega : 7 < 10),
        (fun ⟨_, _, _, h, _⟩ => by rw [show W.mv 10 .b = none from rfl] at h; cases h),
        still rfl⟩⟩,
    fun _ h => by simp [W, headsL] at h, fun _ h => by simp [W, headsL] at h, descends7⟩,
    Or.inl (by simp [W])⟩

theorem not_coherent : ¬ Coherent W := fun h => by
  have := h .x .r2 .r1 rfl rfl
  simp [W, opens2, sim2] at this

theorem drift : W.sim .r2 .r1 ∧ W.sim .r1 .r0 ∧ ¬ W.sim .r2 .r0 :=
  ⟨rfl, rfl, by simp [W, sim2]⟩

theorem arbitrary : ¬ W.opens .x .r0 := by simp [W, opens2, sim2]

end Drift

/-- **Falsehood from drift.** A model satisfying every axiom, kinematics included, in which
the lineage drifts (r2 ~ r1 ~ r0, not r2 ~ r0), coherence fails, and a declarative standing
for the hammer is made while the hammer is present. Its form has lost the reach's onset. -/
theorem falsehood_from_drift :
    ∃ (W : World Pt Ob Fm2), Axioms W ∧ Kinematics W ∧ ¬ Coherent W ∧
      FalseDecl W 8 9 7 .a .b .a .hammer ∧
      (W.sim .r2 .r1 ∧ W.sim .r1 .r0 ∧ ¬ W.sim .r2 .r0) ∧ ¬ W.opens .x .r0 :=
  ⟨Drift.W, Drift.axioms, Drift.kinematics, Drift.not_coherent, Drift.false89,
    Drift.drift, Drift.arbitrary⟩

end GA.Completion
