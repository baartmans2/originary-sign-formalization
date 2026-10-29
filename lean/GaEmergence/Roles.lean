import GaEmergence.Graphs

/-!
# Roles require order

**Unordered claims can only express symmetric relations.** A claim on two targets is
symmetric: `claim_symm`. So it is the same event read either way round. A reading of
claims (a proposition assigned to each claim event) is *faithful* to a relation `R` if every
claim about `o1, o2` is read as `R o1 o2`. Then `unordered_only_symmetric`: `R o1 o2 ↔ R o2 o1`
for every claimed pair. A relation with roles, such as succession (`Succ`, which is
asymmetric), has no faithful unordered reading as soon as any pair is claimed:
`succession_not_unordered`, shown in a concrete world built by the universal construction.

**Ordered claims escape this.** An ordered claim (`OClaim`) is a center on the first target
and then, two steps later, a center on the second, by the same participants. This is
firstness inside the claim. If ordered claims determine what they are about,
`ordered_faithful` gives every relation, asymmetric ones included, a faithful reading. The
`Ord` model has claims "A then B" (true) and "B then A" (false) in the same world, read
faithfully as succession: `succession_ordered`.

The directedness relation carries no role labels, so within one movement nothing tells two
targets apart. Time is the asymmetry the primitives provide.
-/

namespace GA.Completion

set_option linter.constructorNameAsVariable false

section
variable {P O M : Type} (W : World P O M)

/-- A claim on two targets is the same event read either way round. -/
theorem claim_symm {t t' : Nat} {τ1 τ2 : Tgt P O} {p q : P} (h : Claim W t t' τ1 τ2 p q) :
    Claim W t t' τ2 τ1 p q :=
  ⟨fun e => h.1 e.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem claimAbout_symm {t t' : Nat} {p q : P} {o1 o2 : O} (h : ClaimAbout W t t' p q o1 o2) :
    ClaimAbout W t t' p q o2 o1 := by
  obtain ⟨s1, r1, s2, r2, hc, h1, h2⟩ := h
  exact ⟨s2, r2, s1, r1, claim_symm W hc, h2, h1⟩

/-- A reading of unordered claims assigns a proposition to each claim event `(t, t', p, q)`.
It is faithful to `R` if every claim about `o1, o2` is read as `R o1 o2`. -/
def FaithfulUnordered (ρ : Nat → Nat → P → P → Prop) (R : O → O → Prop) : Prop :=
  ∀ t t' p q o1 o2, ClaimAbout W t t' p q o1 o2 → (ρ t t' p q ↔ R o1 o2)

/-- **Unordered claims express only symmetric relations.** -/
theorem unordered_only_symmetric {ρ : Nat → Nat → P → P → Prop} {R : O → O → Prop}
    (hf : FaithfulUnordered W ρ R) {t t' : Nat} {p q : P} {o1 o2 : O}
    (h : ClaimAbout W t t' p q o1 o2) : R o1 o2 ↔ R o2 o1 :=
  (hf _ _ _ _ _ _ h).symm.trans (hf _ _ _ _ _ _ (claimAbout_symm W h))

/-- So if some claimed pair stands in `R` one way but not the other, `R` has no faithful
unordered reading. -/
theorem no_asymmetric_unordered {R : O → O → Prop} {t t' : Nat} {p q : P} {o1 o2 : O}
    (h : ClaimAbout W t t' p q o1 o2) (hR : R o1 o2) (hR' : ¬ R o2 o1) :
    ¬ ∃ ρ, FaithfulUnordered W ρ R :=
  fun ⟨_, hf⟩ => hR' ((unordered_only_symmetric W hf h).mp hR)

/-- **Succession**: both were within someone's reach, and every presence of `o1` precedes
every presence of `o2`. A relation with roles, defined from reach and time. -/
def Succ (o1 o2 : O) : Prop :=
  (∃ s r, W.within s r o1) ∧ (∃ s r, W.within s r o2) ∧
  ∀ s r s' r', W.within s r o1 → W.within s' r' o2 → s < s'

theorem succ_asymm {o1 o2 : O} (h : Succ W o1 o2) : ¬ Succ W o2 o1 := by
  obtain ⟨⟨s1, r1, w1⟩, ⟨s2, r2, w2⟩, h12⟩ := h
  rintro ⟨_, _, h21⟩
  have a := h12 s1 r1 s2 r2 w1 w2
  have b := h21 s2 r2 s1 r1 w2 w1
  omega

/-- **An ordered claim** (firstness inside the claim): a center on `τ1`, then a center on
`τ2`, by the same participants, each with a dependent response. -/
def OClaim (t : Nat) (τ1 τ2 : Tgt P O) (p q : P) : Prop :=
  τ1 ≠ τ2 ∧ (Joint W t (t+1) τ1 p q ∧ Dependent W t τ1 p q) ∧
    (Joint W (t+2) (t+3) τ2 p q ∧ Dependent W (t+2) τ2 p q)

/-- An ordered claim about `o1` first and `o2` second. -/
def OClaimAbout (t : Nat) (p q : P) (o1 o2 : O) : Prop :=
  ∃ s1 r1 s2 r2, OClaim W t (.act s1 r1) (.act s2 r2) p q ∧
    Descends W s1 r1 o1 ∧ Descends W s2 r2 o2

def FaithfulOrdered (ρ : Nat → P → P → Prop) (R : O → O → Prop) : Prop :=
  ∀ t p q o1 o2, OClaimAbout W t p q o1 o2 → (ρ t p q ↔ R o1 o2)

/-- **Ordered claims can express any relation.** If an ordered claim event determines what
it is about, every relation, asymmetric ones included, has a faithful ordered reading. -/
theorem ordered_faithful (R : O → O → Prop)
    (huniq : ∀ t p q o1 o2 o1' o2', OClaimAbout W t p q o1 o2 → OClaimAbout W t p q o1' o2' →
      o1 = o1' ∧ o2 = o2') :
    FaithfulOrdered W (fun t p q => ∃ o1 o2, OClaimAbout W t p q o1 o2 ∧ R o1 o2) R := by
  intro t p q o1 o2 h
  constructor
  · rintro ⟨o1', o2', h', hR⟩
    obtain ⟨rfl, rfl⟩ := huniq _ _ _ _ _ _ _ h' h
    exact hR
  · exact fun hR => ⟨o1, o2, h, hR⟩

end

/-! ## Unordered claims cannot express succession: a concrete world -/

open Univ in
/-- In the universal construction with two objects, one edge and nothing together, the claim
about objects 0 and 1 exists, and 0 precedes 1. So succession has no faithful unordered
reading. -/
theorem succession_not_unordered :
    ¬ ∃ ρ, FaithfulUnordered (W 2 [(0, 1)] []) ρ (Succ (W 2 [(0, 1)] [])) := by
  have hc : ClaimAbout (W 2 [(0, 1)] []) 16 17 .b .a 0 1 :=
    ⟨6, .a, 14, .a, claim_edge (n := 2) (G := [(0, 1)]) (H := []) (k := 0) (i := 0) (j := 1)
      rfl (by omega) (by omega) (by omega),
      descends_vertex (n := 2) (i := 0) (by omega), descends_vertex (n := 2) (i := 1) (by omega)⟩
  have hs : Succ (W 2 [(0, 1)] []) 0 1 := by
    refine ⟨⟨0, .a, Or.inl ⟨by omega, by omega, by omega, Or.inl rfl⟩⟩,
      ⟨8, .a, Or.inl ⟨by omega, by omega, by omega, Or.inl rfl⟩⟩, ?_⟩
    intro s r s' r' h1 h2
    rcases h1 with ⟨_, h1, _, _⟩ | ⟨_, _, _, hH, _⟩
    · rcases h2 with ⟨_, h2, _, _⟩ | ⟨_, _, _, hH, _⟩
      · omega
      · simp at hH
    · simp at hH
  exact no_asymmetric_unordered _ hc hs (succ_asymm _ hs)

/-! ## Ordered claims can: the `Ord` model -/

namespace Ord
open GA.Models

inductive Obj2 | A | B deriving DecidableEq

/-- Forms: the reach for `o`, its sign (which matches the reach), and the held-back mark of
that sign (which begins like the sign and matches nothing else). -/
inductive F3 | reach (o : Obj2) | sign (o : Obj2) | mark (o : Obj2) deriving DecidableEq

def sim3 : F3 → F3 → Prop
  | .reach o, .reach o' => o = o'
  | .sign o, .sign o' => o = o'
  | .mark o, .mark o' => o = o'
  | .reach o, .sign o' => o = o'
  | .sign o, .reach o' => o = o'
  | _, _ => False

def opens3 (m' m : F3) : Prop := sim3 m' m ∨ ∃ o, m' = .mark o ∧ m = .sign o

def objOf : F3 → Obj2
  | .reach o => o
  | .sign o => o
  | .mark o => o

/-- * A: ostensive episodes at t0–t1 and t4–t5 (contrast t2–t3); `a`'s sign for A at t6.
* B: ostensive episodes at t8–t9 and t12–t13 (contrast t10–t11); `a`'s sign for B at t14.
* "A then B" at t16–t19, repeated at t22–t25 (contrast t20–t21).
* "B then A" at t28–t31.

A is within reach only at t0–t5 and B only at t8–t13, so A precedes B. -/
def mvL : List ((Nat × Pt) × F3) :=
  [((0, .a), .reach .A), ((1, .b), .reach .A), ((4, .a), .reach .A), ((5, .b), .reach .A),
   ((6, .a), .sign .A),
   ((8, .a), .reach .B), ((9, .b), .reach .B), ((12, .a), .reach .B), ((13, .b), .reach .B),
   ((14, .a), .sign .B),
   ((16, .b), .mark .A), ((17, .a), .mark .A), ((18, .b), .mark .B), ((19, .a), .mark .B),
   ((22, .b), .mark .A), ((23, .a), .mark .A), ((24, .b), .mark .B), ((25, .a), .mark .B),
   ((28, .b), .mark .B), ((29, .a), .mark .B), ((30, .b), .mark .A), ((31, .a), .mark .A)]

def mv (t : Nat) (p : Pt) : Option F3 := look mvL t p

def within (t : Nat) (_ : Pt) (o : Obj2) : Prop :=
  (o = .A ∧ t ≤ 5) ∨ (o = .B ∧ 8 ≤ t ∧ t ≤ 13)

def W : World Pt Obj2 F3 where
  opens := opens3
  sim := sim3
  mv := mv
  heads t p o := mv t p = some (.reach o) ∧ within t p o
  contact _ _ _ := False
  within := within
  perceives t q p := q ≠ p ∧ ∃ m, mv t p = some m
  win := 1
  retained _ _ := False

theorem sign_out_of_reach {t : Nat} {p : Pt} {o : Obj2} (h : mv t p = some (.sign o)) :
    ¬ within t p o := by
  have hm := look_mem h
  simp [mvL] at hm
  rcases hm with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;> simp [within]

theorem axioms : Axioms W where
  heads_within _ _ _ h := h.2
  heads_moving _ _ _ h := ⟨_, h.1⟩
  contact_heads _ _ _ h := h.elim
  perceives_other _ _ _ h := h
  sim_refl m := by cases m <;> simp [W, sim3]
  sim_symm m m' h := by cases m <;> cases m' <;> simp [W, sim3] at h ⊢ <;> exact h.symm
  sim_opens _ _ h := Or.inl h
  retention _ _ h := h.elim

theorem kinematics : Kinematics W where
  transfer s t r p o m m' _ hm hh hm' ho hw := by
    have h1 : mv s r = some m := hm
    rw [hh.1] at h1
    cases h1
    rcases ho with hs | ⟨o', _, he⟩
    · cases m' with
      | reach o' =>
        have he : o' = o := hs
        subst he
        exact ⟨hm', hw⟩
      | sign o' =>
        have he : o' = o := hs
        subst he
        exact absurd hw (sign_out_of_reach hm')
      | mark o' => exact hs.elim
    · cases he

/-! ### What a sign stands for is fixed by its form -/

theorem sim_objOf {m' m : F3} (h : sim3 m' m) : objOf m' = objOf m := by
  cases m' <;> cases m <;> simp [sim3, objOf] at h ⊢ <;> exact h

theorem descends_obj {s : Nat} {r : Pt} {o : Obj2} (hD : Descends W s r o) :
    ∃ m, mv s r = some m ∧ objOf m = o := by
  induction hD with
  | root hj => exact ⟨_, hj.1.2.2.2.1.1.1, rfl⟩
  | @step s t r p o m1 m2 _ hmr hmp hsim _ ih =>
    obtain ⟨m, hm, ho⟩ := ih
    have hm1 : mv s r = some m1 := hmr
    rw [hm1] at hm
    cases hm
    exact ⟨m2, hmp, by rw [sim_objOf hsim]; exact ho⟩

/-- A suspended movement directed at a movement that stands for `o` has `o` as the object of
its form. -/
theorem target_obj {t s : Nat} {p r : Pt} {o : Obj2} (hs : Suspended W t p (.act s r))
    (hD : Descends W s r o) : ∃ m, mv t p = some m ∧ objOf m = o := by
  obtain ⟨⟨_, m, m', hm, hm', ho⟩, hnc⟩ := hs
  rcases ho with hsim | ⟨o', rfl, rfl⟩
  · exact absurd ⟨m, m', hm, hm', hsim⟩ hnc
  · obtain ⟨m0, hm0, hobj⟩ := descends_obj hD
    have hm1 : mv s r = some (.sign o') := hm
    rw [hm1] at hm0
    cases hm0
    exact ⟨_, hm', hobj⟩

/-- **Ordered claims determine what they are about.** -/
theorem uniq : ∀ t p q o1 o2 o1' o2', OClaimAbout W t p q o1 o2 → OClaimAbout W t p q o1' o2' →
    o1 = o1' ∧ o2 = o2' := by
  rintro t p q o1 o2 o1' o2' ⟨s1, r1, s2, r2, hc, h1, h2⟩ ⟨s1', r1', s2', r2', hc', h1', h2'⟩
  obtain ⟨m1, hm1, ho1⟩ := target_obj hc.2.1.1.2.2.2.1 h1
  obtain ⟨m1', hm1', ho1'⟩ := target_obj hc'.2.1.1.2.2.2.1 h1'
  obtain ⟨m2, hm2, ho2⟩ := target_obj hc.2.2.1.2.2.2.1 h2
  obtain ⟨m2', hm2', ho2'⟩ := target_obj hc'.2.2.1.2.2.2.1 h2'
  rw [hm1] at hm1'; rw [hm2] at hm2'
  cases hm1'; cases hm2'
  exact ⟨ho1.symm.trans ho1', ho2.symm.trans ho2'⟩

/-! ### The episodes -/

theorem none_at {t : Nat} {p : Pt} (h : mv t p = none) {τ : Tgt Pt Obj2} :
    ¬ Suspended W t p τ := by
  intro hs
  cases τ with
  | obj o =>
    have h2 : mv t p = some (.reach o) := hs.1.1
    rw [h] at h2; cases h2
  | act s r =>
    obtain ⟨_, _, m', _, hm', _⟩ := hs.1
    have h2 : mv t p = some m' := hm'
    rw [h] at h2; cases h2

theorem still {u : Nat} {q : Pt} {τ : Tgt Pt Obj2} (hm : mv (u+1) q = none) :
    ∀ u', u < u' → u' ≤ u + W.win → ¬ Suspended W u' q τ := by
  intro u' h1 h2
  have : u' = u + 1 := by simp [W] at h2; omega
  subst this
  exact none_at hm

theorem susp_reach (t : Nat) (p : Pt) (o : Obj2) (hm : mv t p = some (.reach o))
    (hw : within t p o) : Suspended W t p (.obj o) := ⟨⟨hm, hw⟩, fun h => h⟩

theorem susp_mark {t s : Nat} {p r : Pt} {o : Obj2} (hs : mv s r = some (.sign o))
    (hm : mv t p = some (.mark o)) (hst : s < t) : Suspended W t p (.act s r) := by
  refine ⟨⟨hst, _, _, hs, hm, Or.inr ⟨o, rfl, rfl⟩⟩, ?_⟩
  rintro ⟨m, m', h1, h2, hsim⟩
  have h1' : mv s r = some m := h1
  have h2' : mv t p = some m' := h2
  rw [hs] at h1'; rw [hm] at h2'
  cases h1'; cases h2'
  exact hsim

theorem perc {t : Nat} {q p : Pt} {m : F3} (hne : q ≠ p) (hm : mv t p = some m) :
    W.perceives t q p := ⟨hne, m, hm⟩

theorem jointO (t : Nat) (o : Obj2) (h1 : mv t .a = some (.reach o)) (w1 : within t .a o)
    (h2 : mv (t+1) .b = some (.reach o)) (w2 : within (t+1) .b o) :
    Joint W t (t+1) (.obj o) .a .b :=
  ⟨by decide, by omega, by show _ ≤ _ + 1; omega, susp_reach _ _ _ h1 w1,
    susp_reach _ _ _ h2 w2, perc (by decide) h1, perc (by decide) h2⟩

theorem ostA : Ostensive W 0 1 .A .a .b :=
  ⟨jointO 0 .A rfl (Or.inl ⟨rfl, by omega⟩) rfl (Or.inl ⟨rfl, by omega⟩),
    ⟨4, 5, by decide, jointO 4 .A rfl (Or.inl ⟨rfl, by omega⟩) rfl (Or.inl ⟨rfl, by omega⟩),
      _, _, rfl, rfl, rfl⟩,
    ⟨2, ⟨3, by omega, by show _ ≤ _ + 1; omega, Or.inl ⟨rfl, by omega⟩⟩,
      (fun ⟨_, _, _, h, _⟩ => by
        have h' : mv 2 .a = some _ := h
        rw [show mv 2 .a = none from rfl] at h'; cases h'),
      still rfl⟩⟩

theorem ostB : Ostensive W 8 9 .B .a .b :=
  ⟨jointO 8 .B rfl (Or.inr ⟨rfl, by omega, by omega⟩) rfl (Or.inr ⟨rfl, by omega, by omega⟩),
    ⟨12, 13, by decide,
      jointO 12 .B rfl (Or.inr ⟨rfl, by omega, by omega⟩) rfl (Or.inr ⟨rfl, by omega, by omega⟩),
      _, _, rfl, rfl, rfl⟩,
    ⟨10, ⟨11, by omega, by show _ ≤ _ + 1; omega, Or.inr ⟨rfl, by omega, by omega⟩⟩,
      (fun ⟨_, _, _, h, _⟩ => by
        have h' : mv 10 .a = some _ := h
        rw [show mv 10 .a = none from rfl] at h'; cases h'),
      still rfl⟩⟩

theorem descA : Descends W 6 .a .A :=
  Descends.step (W := W) (s := 0) (r := .a) (m := F3.reach .A) (m' := F3.sign .A)
    (by omega) rfl rfl rfl (Descends.root ostA)

theorem descB : Descends W 14 .a .B :=
  Descends.step (W := W) (s := 8) (r := .a) (m := F3.reach .B) (m' := F3.sign .B)
    (by omega) rfl rfl rfl (Descends.root ostB)

/-- A center by `b` then `a` on a sign, both making its mark. -/
theorem jointM (t s : Nat) (o : Obj2) (hs : mv s .a = some (.sign o)) (hst : s < t)
    (h1 : mv t .b = some (.mark o)) (h2 : mv (t+1) .a = some (.mark o)) :
    Joint W t (t+1) (.act s .a) .b .a :=
  ⟨by decide, by omega, by show _ ≤ _ + 1; omega, susp_mark hs h1 hst,
    susp_mark hs h2 (by omega), perc (by decide) h1, perc (by decide) h2⟩

/-- The contrast at t20–t21, shared by every claim center. -/
theorem contrast (t s : Nat) (o : Obj2) (hst : s < 20) (_h1 : mv t .b = some (.mark o)) :
    ∃ u, Opportunity W u .a (.act s .a) ∧ ¬ SameKind W t u .b ∧
      ∀ u', u < u' → u' ≤ u + W.win → ¬ Suspended W u' .a (.act s .a) :=
  ⟨20, hst, (fun ⟨_, _, _, h, _⟩ => by
    have h' : mv 20 .b = some _ := h
    rw [show mv 20 .b = none from rfl] at h'; cases h'), still rfl⟩

theorem depM {t t2 s : Nat} {o : Obj2} (hs : mv s .a = some (.sign o)) (_hst : s < t)
    (hst2 : s < t2) (hs20 : s < 20) (hne : t2 ≠ t)
    (h1 : mv t .b = some (.mark o)) (h2 : mv t2 .b = some (.mark o))
    (h3 : mv (t2+1) .a = some (.mark o)) : Dependent W t (.act s .a) .b .a :=
  ⟨⟨t2, t2+1, hne, jointM t2 s o hs hst2 h2 h3, _, _, h1, h2, by cases o <;> rfl⟩,
    contrast t s o hs20 h1⟩

/-- "A then B" at t16. -/
theorem claimAB : OClaimAbout W 16 .b .a .A .B :=
  ⟨6, .a, 14, .a,
    ⟨(fun h => by cases h),
      ⟨jointM 16 6 .A rfl (by omega) rfl rfl,
        depM (t2 := 22) rfl (by omega) (by omega) (by omega) (by omega) rfl rfl rfl⟩,
      ⟨jointM 18 14 .B rfl (by omega) rfl rfl,
        depM (t2 := 24) rfl (by omega) (by omega) (by omega) (by omega) rfl rfl rfl⟩⟩,
    descA, descB⟩

/-- "B then A" at t28. -/
theorem claimBA : OClaimAbout W 28 .b .a .B .A :=
  ⟨14, .a, 6, .a,
    ⟨(fun h => by cases h),
      ⟨jointM 28 14 .B rfl (by omega) rfl rfl,
        depM (t2 := 18) rfl (by omega) (by omega) (by omega) (by omega) rfl rfl rfl⟩,
      ⟨jointM 30 6 .A rfl (by omega) rfl rfl,
        depM (t2 := 16) rfl (by omega) (by omega) (by omega) (by omega) rfl rfl rfl⟩⟩,
    descB, descA⟩

theorem succAB : Succ W .A .B := by
  refine ⟨⟨0, .a, Or.inl ⟨rfl, by omega⟩⟩, ⟨8, .a, Or.inr ⟨rfl, by omega, by omega⟩⟩, ?_⟩
  rintro s r s' r' (⟨_, h1⟩ | ⟨h, _⟩) (⟨h, _⟩ | ⟨_, h2, _⟩)
  · cases h
  · omega
  · cases h
  · cases h

/-- Order is what distinguishes them: the claim at t16 is not a claim with its targets swapped. -/
theorem order_matters : ¬ OClaim W 16 (.act 14 .a) (.act 6 .a) .b .a := by
  rintro ⟨_, ⟨⟨_, _, _, hs, _⟩, _⟩, _⟩
  obtain ⟨⟨_, m, m', hm, hm', ho⟩, _⟩ := hs
  have h1 : mv 14 .a = some m := hm
  have h2 : mv 16 .b = some m' := hm'
  rw [show mv 14 .a = some (.sign .B) from rfl] at h1
  rw [show mv 16 .b = some (.mark .A) from rfl] at h2
  cases h1; cases h2
  rcases ho with h | ⟨_, h1, h2⟩
  · exact h
  · cases h1; cases h2

end Ord

/-- **Firstness suffices for roles.** In the `Ord` model, satisfying every axiom (kinematics
included), succession has a faithful ordered reading, under which "A then B" (t16) is true
and "B then A" (t28) is false. -/
theorem succession_ordered :
    ∃ ρ, FaithfulOrdered Ord.W ρ (Succ Ord.W) ∧ ρ 16 .b .a ∧ ¬ ρ 28 .b .a := by
  refine ⟨_, ordered_faithful Ord.W (Succ Ord.W) Ord.uniq, ⟨_, _, Ord.claimAB, Ord.succAB⟩, ?_⟩
  rintro ⟨o1, o2, h, hs⟩
  obtain ⟨rfl, rfl⟩ := Ord.uniq _ _ _ _ _ _ _ h Ord.claimBA
  exact succ_asymm _ Ord.succAB hs

theorem ord_axioms : Axioms Ord.W ∧ Kinematics Ord.W := ⟨Ord.axioms, Ord.kinematics⟩

end GA.Completion
