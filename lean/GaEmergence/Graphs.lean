import GaEmergence.Completion

/-!
# From the originary declarative to arbitrary grounded graphs

**Compound claims.** A claim is a center on *two* distinct targets at once: both
participants' movements are suspended toward both, each with a dependent response.
`claim_iff_two_declaratives`: a claim on two movements is exactly two declaratives made by
the same pair of movements. Nothing new is added; the claim is generated.

**Co-reach.** `Together t o1 o2`: someone has both objects within reach at `t`. This is
defined from reach, so no new primitive is needed.

**Truth.** A claim's "don't be together" (`ClaimTrue`) is the originary "don't be present
[with us]" with its second term made explicit. It concerns a relation between objects, and
it can be evaluated where neither speaker is.

**Universality** (`universality`). For any `n` objects, any graph `G` on them and any
physical arrangement `H` (which pairs are together), there is a history satisfying every
axiom, kinematics included, in which:
1. every object has a sign grounded in an ostensive;
2. every edge of `G` is a claim whose two arcs go to exactly its endpoints' signs;
3. each claim is true iff its objects are not together according to `H` (thick, displaced
   truth and falsehood);
4. there are no other claims: the claim graph is exactly `G`.
-/

namespace GA.Completion

set_option linter.constructorNameAsVariable false

/-! ## Claims, in general -/

section
variable {P O M : Type} (W : World P O M)

/-- A compound claim: one center on two distinct targets at once, with a dependent response
for each. The claim-node is the first participant's movement; its two arcs go to `τ1` and `τ2`. -/
def Claim (t t' : Nat) (τ1 τ2 : Tgt P O) (p q : P) : Prop :=
  τ1 ≠ τ2 ∧ Joint W t t' τ1 p q ∧ Joint W t t' τ2 p q ∧
    Dependent W t τ1 p q ∧ Dependent W t τ2 p q

/-- **Generated, not added.** A claim on two movements is exactly two declaratives made by
the same pair of movements. -/
theorem claim_iff_two_declaratives (t t' s1 s2 : Nat) (r1 r2 p q : P) :
    Claim W t t' (.act s1 r1) (.act s2 r2) p q ↔
      (Tgt.act s1 r1 : Tgt P O) ≠ .act s2 r2 ∧
        Declarative W t t' s1 r1 p q ∧ Declarative W t t' s2 r2 p q := by
  constructor
  · rintro ⟨hne, hj1, hj2, hd1, hd2⟩
    exact ⟨hne, ⟨hj1, hd1⟩, ⟨hj2, hd2⟩⟩
  · rintro ⟨hne, ⟨hj1, hd1⟩, ⟨hj2, hd2⟩⟩
    exact ⟨hne, hj1, hj2, hd1, hd2⟩

/-- Co-reach: someone has both objects within reach at the same time. -/
def Together (t : Nat) (o1 o2 : O) : Prop := ∃ r, W.within t r o1 ∧ W.within t r o2

/-- The claim's "don't be together". -/
def ClaimTrue (t : Nat) (o1 o2 : O) : Prop := ¬ Together W t o1 o2

/-- A claim about `o1` and `o2`: its targets stand for them by lineage. -/
def ClaimAbout (t t' : Nat) (p q : P) (o1 o2 : O) : Prop :=
  ∃ s1 r1 s2 r2, Claim W t t' (.act s1 r1) (.act s2 r2) p q ∧
    Descends W s1 r1 o1 ∧ Descends W s2 r2 o2

/-- **Grounding.** Whatever a claim is about was once within someone's reach. -/
theorem claim_grounded (hA : Axioms W) {t t' : Nat} {p q : P} {o1 o2 : O}
    (h : ClaimAbout W t t' p q o1 o2) :
    (∃ s r, W.within s r o1) ∧ (∃ s r, W.within s r o2) := by
  obtain ⟨s1, r1, s2, r2, _, hd1, hd2⟩ := h
  obtain ⟨u1, q1, _, hw1⟩ := content_was_present W hA hd1
  obtain ⟨u2, q2, _, hw2⟩ := content_was_present W hA hd2
  exact ⟨⟨u1, q1, hw1⟩, ⟨u2, q2, hw2⟩⟩

end

/-! ## The universal construction -/

/-- Participants: the two speakers, and a witness `w x y` for each pair of objects that is
together. -/
inductive Pp | a | b | w (x y : Nat) deriving DecidableEq

/-- Forms: the reach for object `i`, the sign for `i` (which matches the reach), and the
claim form for `i, j` (which begins like both signs and matches neither). -/
inductive Frm | reach (i : Nat) | sign (i : Nat) | claim (i j : Nat) deriving DecidableEq

def simR : Frm → Frm → Prop
  | .reach i, .reach j => i = j
  | .sign i, .sign j => i = j
  | .claim i j, .claim k l => i = k ∧ j = l
  | .reach i, .sign j => i = j
  | .sign i, .reach j => i = j
  | _, _ => False

def opensR (m' m : Frm) : Prop :=
  simR m' m ∨ ∃ i j, m' = .claim i j ∧ (m = .sign i ∨ m = .sign j)

namespace Univ

/-- In the object region, at time `8i + r`: `a` reaches at r = 0, 4 and `b` at r = 1, 5. -/
abbrev vcond (t : Nat) (p : Pp) : Prop :=
  ((t % 8 = 0 ∨ t % 8 = 4) ∧ p = .a) ∨ ((t % 8 = 1 ∨ t % 8 = 5) ∧ p = .b)

/-- In the claim region, at time `8n + 8k + r`: `b` makes the claim at r = 0, 4 and `a` at r = 1, 5. -/
abbrev econd (n t : Nat) (p : Pp) : Prop :=
  (((t - 8*n) % 8 = 0 ∨ (t - 8*n) % 8 = 4) ∧ p = .b) ∨
  (((t - 8*n) % 8 = 1 ∨ (t - 8*n) % 8 = 5) ∧ p = .a)

/-- Object `i` occupies times `8i … 8i+7`: two ostensive episodes (r = 0–1 and 4–5) with a
contrast (r = 2–3), then `a`'s sign for `i` at r = 6, made out of the object's reach. Edge
`k` of `G` occupies times `8n + 8k …`: two claim episodes (r = 0–1 and 4–5) with a
contrast (r = 2–3). -/
def mv (n : Nat) (G : List (Nat × Nat)) (t : Nat) (p : Pp) : Option Frm :=
  if t < 8 * n then
    (if vcond t p then some (.reach (t / 8))
     else if t % 8 = 6 ∧ p = .a then some (.sign (t / 8)) else none)
  else
    match G[(t - 8 * n) / 8]? with
    | some (i, j) => if econd n t p then some (.claim i j) else none
    | none => none

def heads (n t : Nat) (p : Pp) (o : Nat) : Prop := t < 8 * n ∧ o = t / 8 ∧ vcond t p

/-- Speakers have object `i` within reach during the ostensive part of its block. Witness
`w x y` has `x` and `y` within reach, if that pair is together in `H`. -/
def within (n : Nat) (H : List (Nat × Nat)) (t : Nat) (p : Pp) (o : Nat) : Prop :=
  (t < 8 * n ∧ o = t / 8 ∧ t % 8 ≤ 5 ∧ (p = .a ∨ p = .b)) ∨
  ∃ x y, p = .w x y ∧ (x, y) ∈ H ∧ (o = x ∨ o = y)

def perceives (n : Nat) (G : List (Nat × Nat)) (t : Nat) (q p : Pp) : Prop :=
  (t < 8 * n ∧ (((t % 8 = 0 ∨ t % 8 = 4) ∧ q = .b ∧ p = .a) ∨
                ((t % 8 = 1 ∨ t % 8 = 5) ∧ q = .a ∧ p = .b))) ∨
  (8 * n ≤ t ∧ (∃ e, G[(t - 8 * n) / 8]? = some e) ∧
    ((((t - 8*n) % 8 = 0 ∨ (t - 8*n) % 8 = 4) ∧ q = .a ∧ p = .b) ∨
     (((t - 8*n) % 8 = 1 ∨ (t - 8*n) % 8 = 5) ∧ q = .b ∧ p = .a)))

def W (n : Nat) (G H : List (Nat × Nat)) : World Pp Nat Frm where
  opens := opensR
  sim := simR
  mv := mv n G
  heads := heads n
  contact _ _ _ := False
  within := within n H
  perceives := perceives n G
  win := 1
  retained _ _ := False

variable {n : Nat} {G H : List (Nat × Nat)}

/-! ### The movement table -/

theorem mv_cases {t : Nat} {p : Pp} {m : Frm} (h : mv n G t p = some m) :
    (t < 8*n ∧ vcond t p ∧ m = .reach (t/8)) ∨
    (t < 8*n ∧ t % 8 = 6 ∧ p = .a ∧ m = .sign (t/8)) ∨
    (8*n ≤ t ∧ econd n t p ∧ ∃ i j, G[(t - 8*n)/8]? = some (i, j) ∧ m = .claim i j) := by
  unfold mv at h
  by_cases ht : t < 8 * n
  · rw [if_pos ht] at h
    by_cases hc : vcond t p
    · rw [if_pos hc] at h; cases h; exact Or.inl ⟨ht, hc, rfl⟩
    · rw [if_neg hc] at h
      by_cases h6 : t % 8 = 6 ∧ p = .a
      · rw [if_pos h6] at h; cases h; exact Or.inr (Or.inl ⟨ht, h6.1, h6.2, rfl⟩)
      · rw [if_neg h6] at h; cases h
  · rw [if_neg ht] at h
    cases hg : G[(t - 8 * n) / 8]? with
    | none => rw [hg] at h; cases h
    | some e =>
      obtain ⟨i, j⟩ := e
      rw [hg] at h
      by_cases hc : econd n t p
      · have h' : (if econd n t p then some (Frm.claim i j) else none) = some m := h
        rw [if_pos hc] at h'; cases h'
        exact Or.inr (Or.inr ⟨by omega, hc, i, j, rfl, rfl⟩)
      · have h' : (if econd n t p then some (Frm.claim i j) else none) = some m := h
        rw [if_neg hc] at h'; cases h'

theorem mv_reach {t : Nat} {p : Pp} {o : Nat} (ht : t < 8*n) (hc : vcond t p)
    (ho : o = t / 8) : mv n G t p = some (.reach o) := by
  unfold mv; rw [if_pos ht, if_pos hc, ho]

theorem mv_sign {t : Nat} {o : Nat} (ht : t < 8*n) (h6 : t % 8 = 6) (ho : o = t / 8) :
    mv n G t .a = some (.sign o) := by
  have hc : ¬ vcond t .a := by simp [vcond]; omega
  unfold mv; rw [if_pos ht, if_neg hc, if_pos ⟨h6, rfl⟩, ho]

theorem mv_none_v {t : Nat} {p : Pp} (ht : t < 8*n) (hc : ¬ vcond t p)
    (h6 : ¬ (t % 8 = 6 ∧ p = .a)) : mv n G t p = none := by
  unfold mv; rw [if_pos ht, if_neg hc, if_neg h6]

theorem mv_claim {t : Nat} {p : Pp} {i j : Nat} (ht : 8*n ≤ t)
    (hg : G[(t - 8*n)/8]? = some (i, j)) (hc : econd n t p) :
    mv n G t p = some (.claim i j) := by
  unfold mv
  rw [if_neg (by omega), hg]
  show (if econd n t p then some (Frm.claim i j) else none) = _
  rw [if_pos hc]

theorem mv_none_e {t : Nat} {p : Pp} (ht : 8*n ≤ t) (hc : ¬ econd n t p) :
    mv n G t p = none := by
  unfold mv
  rw [if_neg (by omega)]
  cases hg : G[(t - 8 * n) / 8]? with
  | none => rfl
  | some e =>
    obtain ⟨i, j⟩ := e
    show (if econd n t p then some (Frm.claim i j) else none) = none
    rw [if_neg hc]

/-! ### Axioms and kinematics -/

theorem axioms : Axioms (W n G H) where
  heads_within t p o h := by
    obtain ⟨ht, ho, hc⟩ := h
    refine Or.inl ⟨ht, ho, ?_, ?_⟩
    · rcases hc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · rcases hc with ⟨_, hp⟩ | ⟨_, hp⟩ <;> simp [hp]
  heads_moving t p o h := ⟨_, mv_reach h.1 h.2.2 rfl⟩
  contact_heads _ _ _ h := h.elim
  perceives_other t q p h := by
    rcases h with ⟨ht, ⟨hr, rfl, rfl⟩ | ⟨hr, rfl, rfl⟩⟩ |
      ⟨ht, ⟨⟨i, j⟩, hg⟩, ⟨hr, rfl, rfl⟩ | ⟨hr, rfl, rfl⟩⟩
    · exact ⟨by decide, _, mv_reach ht (Or.inl ⟨hr, rfl⟩) rfl⟩
    · exact ⟨by decide, _, mv_reach ht (Or.inr ⟨hr, rfl⟩) rfl⟩
    · exact ⟨by decide, _, mv_claim ht hg (Or.inl ⟨hr, rfl⟩)⟩
    · exact ⟨by decide, _, mv_claim ht hg (Or.inr ⟨hr, rfl⟩)⟩
  sim_refl m := by cases m <;> simp [W, simR]
  sim_symm m m' h := by
    cases m <;> cases m' <;> simp [W, simR] at h ⊢ <;> omega
  sim_opens _ _ h := Or.inl h
  retention _ _ h := h.elim

theorem kinematics : Kinematics (W n G H) where
  transfer s t r p o m m' _ hm hh hm' ho hw := by
    obtain ⟨hs8, hos, hcs⟩ := hh
    have hm0 : m = .reach o := by
      have h1 : mv n G s r = some (.reach o) := mv_reach hs8 hcs hos
      have h2 : mv n G s r = some m := hm
      rw [h1] at h2; cases h2; rfl
    subst hm0
    have hm'' : mv n G t p = some m' := hm'
    rcases ho with hsim | ⟨i, j, rfl, hx⟩
    · cases m' with
      | reach o' =>
        have he : o' = o := hsim
        subst he
        rcases mv_cases hm'' with ⟨ht, hc, he⟩ | ⟨_, _, _, he⟩ | ⟨_, _, _, _, _, he⟩
        · cases he; exact ⟨ht, rfl, hc⟩
        · cases he
        · cases he
      | sign o' =>
        have he : o' = o := hsim
        subst he
        rcases mv_cases hm'' with ⟨_, _, he⟩ | ⟨_, h6, hp, he⟩ | ⟨_, _, _, _, _, he⟩
        · cases he
        · subst hp
          rcases hw with ⟨_, _, h5, _⟩ | ⟨x, y, hpw, _⟩
          · omega
          · cases hpw
        · cases he
      | claim i j => exact hsim.elim
    · rcases hx with h | h <;> cases h

/-! ### Each object gets a grounded sign -/

theorem joint_v {i : Nat} (hi : i < n) (r : Nat) (hr : r = 0 ∨ r = 4) :
    Joint (W n G H) (8*i+r) (8*i+r+1) (.obj i) .a .b :=
  ⟨by decide, by omega, by show _ ≤ _ + 1; omega,
    ⟨⟨by omega, by omega, Or.inl ⟨by omega, rfl⟩⟩, fun h => h⟩,
    ⟨⟨by omega, by omega, Or.inr ⟨by omega, rfl⟩⟩, fun h => h⟩,
    Or.inl ⟨by omega, Or.inl ⟨by omega, rfl, rfl⟩⟩,
    Or.inl ⟨by omega, Or.inr ⟨by omega, rfl, rfl⟩⟩⟩

theorem ostensive_vertex {i : Nat} (hi : i < n) :
    Ostensive (W n G H) (8*i) (8*i+1) i .a .b := by
  refine ⟨joint_v hi 0 (Or.inl rfl), ⟨8*i+4, 8*i+4+1, by omega, joint_v hi 4 (Or.inr rfl),
    .reach i, .reach i, mv_reach (by omega) (Or.inl ⟨by omega, rfl⟩) (by omega),
    mv_reach (by omega) (Or.inl ⟨by omega, rfl⟩) (by omega), rfl⟩,
    ⟨8*i+2, ⟨8*i+3, by omega, by show _ ≤ _ + 1; omega,
      Or.inl ⟨by omega, by omega, by omega, Or.inr rfl⟩⟩, ?_, ?_⟩⟩
  · rintro ⟨_, _, _, h2, _⟩
    have : mv n G (8*i+2) .a = none :=
      mv_none_v (by omega) (by simp [vcond]; omega) (fun h => by omega)
    rw [show (W n G H).mv (8*i+2) .a = mv n G (8*i+2) .a from rfl, this] at h2
    cases h2
  · intro u' h1 h2 hs
    have hu : u' = 8*i+3 := by simp [W] at h2; omega
    subst hu
    obtain ⟨_, _, hc⟩ := hs.1
    rcases hc with ⟨_, h⟩ | ⟨h, _⟩
    · cases h
    · omega

/-- Every object has a sign, `a`'s movement at `8i + 6`, that descends from an ostensive on it. -/
theorem descends_vertex {i : Nat} (hi : i < n) : Descends (W n G H) (8*i+6) .a i :=
  Descends.step (W := W n G H) (s := 8*i) (r := .a) (m := Frm.reach i) (m' := Frm.sign i)
    (by omega) (mv_reach (by omega) (Or.inl ⟨by omega, rfl⟩) (by omega))
    (mv_sign (by omega) (by omega) (by omega)) rfl
    (Descends.root (ostensive_vertex hi))

/-! ### Each edge gets a claim -/

theorem hg_at {k i j : Nat} (hk : G[k]? = some (i, j)) (r : Nat) (hr : r < 8) :
    G[(8*n + 8*k + r - 8*n)/8]? = some (i, j) := by
  rw [show (8*n + 8*k + r - 8*n)/8 = k by omega]; exact hk

theorem susp_claim {k i j x : Nat} (hk : G[k]? = some (i, j)) (hx : x = i ∨ x = j)
    (hxn : x < n) {r : Nat} {p : Pp} (hr : r < 8) (hc : econd n (8*n+8*k+r) p) :
    Suspended (W n G H) (8*n+8*k+r) p (.act (8*x+6) .a) := by
  have hs : mv n G (8*x+6) .a = some (.sign x) := mv_sign (by omega) (by omega) (by omega)
  have hcl : mv n G (8*n+8*k+r) p = some (.claim i j) := mv_claim (by omega) (hg_at hk r hr) hc
  refine ⟨⟨by omega, .sign x, .claim i j, hs, hcl, Or.inr ⟨i, j, rfl, ?_⟩⟩, ?_⟩
  · rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro ⟨m, m', h1, h2, hsim⟩
    have h1' : mv n G (8*x+6) .a = some m := h1
    have h2' : mv n G (8*n+8*k+r) p = some m' := h2
    rw [hs] at h1'; rw [hcl] at h2'
    cases h1'; cases h2'
    exact hsim

theorem joint_e {k i j x : Nat} (hk : G[k]? = some (i, j)) (hx : x = i ∨ x = j)
    (hxn : x < n) (r : Nat) (hr : r = 0 ∨ r = 4) :
    Joint (W n G H) (8*n+8*k+r) (8*n+8*k+r+1) (.act (8*x+6) .a) .b .a :=
  ⟨by decide, by omega, by show _ ≤ _ + 1; omega,
    susp_claim hk hx hxn (by omega) (Or.inl ⟨by omega, rfl⟩),
    susp_claim (r := r+1) hk hx hxn (by omega) (Or.inr ⟨by omega, rfl⟩),
    Or.inr ⟨by omega, ⟨_, hg_at hk r (by omega)⟩, Or.inl ⟨by omega, rfl, rfl⟩⟩,
    Or.inr ⟨by omega, ⟨_, hg_at hk (r+1) (by omega)⟩, Or.inr ⟨by omega, rfl, rfl⟩⟩⟩

theorem dependent_e {k i j x : Nat} (hk : G[k]? = some (i, j)) (hx : x = i ∨ x = j)
    (hxn : x < n) : Dependent (W n G H) (8*n+8*k) (.act (8*x+6) .a) .b .a := by
  have hcl : ∀ r, r < 8 → econd n (8*n+8*k+r) .b →
      mv n G (8*n+8*k+r) .b = some (.claim i j) :=
    fun r hr hc => mv_claim (by omega) (hg_at hk r hr) hc
  refine ⟨⟨8*n+8*k+4, 8*n+8*k+4+1, by omega, joint_e hk hx hxn 4 (Or.inr rfl),
      .claim i j, .claim i j, hcl 0 (by omega) (Or.inl ⟨by omega, rfl⟩),
      hcl 4 (by omega) (Or.inl ⟨by omega, rfl⟩), ⟨rfl, rfl⟩⟩,
    ⟨8*n+8*k+2, (by omega : 8*x+6 < 8*n+8*k+2), ?_, ?_⟩⟩
  · rintro ⟨_, _, _, h2, _⟩
    have : mv n G (8*n+8*k+2) .b = none := mv_none_e (by omega) (by simp [econd]; omega)
    rw [show (W n G H).mv (8*n+8*k+2) .b = mv n G (8*n+8*k+2) .b from rfl, this] at h2
    cases h2
  · intro u' h1 h2 hs
    have hu : u' = 8*n+8*k+3 := by simp [W] at h2; omega
    subst hu
    obtain ⟨_, _, _, _, h3, _⟩ := hs.1
    have : mv n G (8*n+8*k+3) .a = none := mv_none_e (by omega) (by simp [econd]; omega)
    rw [show (W n G H).mv (8*n+8*k+3) .a = mv n G (8*n+8*k+3) .a from rfl, this] at h3
    cases h3

/-- Edge `k = (i, j)` is represented by a claim made at `8n + 8k`, with arcs to the signs
for `i` and `j`. -/
theorem claim_edge {k i j : Nat} (hk : G[k]? = some (i, j)) (hi : i < n) (hj : j < n)
    (hij : i ≠ j) :
    Claim (W n G H) (8*n+8*k) (8*n+8*k+1) (.act (8*i+6) .a) (.act (8*j+6) .a) .b .a :=
  ⟨fun h => hij (by injection h with h1; omega),
    joint_e hk (Or.inl rfl) hi 0 (Or.inl rfl), joint_e hk (Or.inr rfl) hj 0 (Or.inl rfl),
    dependent_e hk (Or.inl rfl) hi, dependent_e hk (Or.inr rfl) hj⟩

/-! ### Truth is about the world's arrangement -/

/-- In the claim region, two distinct objects are together exactly when `H` says so. -/
theorem together_iff {t i j : Nat} (ht : 8*n ≤ t) (hij : i ≠ j) :
    Together (W n G H) t i j ↔ (i, j) ∈ H ∨ (j, i) ∈ H := by
  constructor
  · rintro ⟨r, h1, h2⟩
    rcases h1 with ⟨h, _⟩ | ⟨x, y, rfl, hxy, hix⟩
    · omega
    · rcases h2 with ⟨h, _⟩ | ⟨x', y', he, _, hjx⟩
      · omega
      · cases he
        rcases hix with rfl | rfl <;> rcases hjx with h | h
        · exact absurd h.symm hij
        · subst h; exact Or.inl hxy
        · subst h; exact Or.inr hxy
        · exact absurd h.symm hij
  · rintro (h | h)
    · exact ⟨.w i j, Or.inr ⟨i, j, rfl, h, Or.inl rfl⟩, Or.inr ⟨i, j, rfl, h, Or.inr rfl⟩⟩
    · exact ⟨.w j i, Or.inr ⟨j, i, rfl, h, Or.inr rfl⟩, Or.inr ⟨j, i, rfl, h, Or.inl rfl⟩⟩

/-- **Displaced.** At claim time, neither speaker has any object within reach. -/
theorem displaced {t : Nat} (ht : 8*n ≤ t) (o : Nat) :
    ¬ (W n G H).within t .a o ∧ ¬ (W n G H).within t .b o := by
  constructor <;> rintro (⟨h, _⟩ | ⟨_, _, h, _⟩)
  · omega
  · cases h
  · omega
  · cases h

/-! ### There are no other claims -/

theorem susp_obj_mv {t : Nat} {p : Pp} {o : Nat} (h : Suspended (W n G H) t p (.obj o)) :
    mv n G t p = some (.reach o) := by
  obtain ⟨⟨ht, ho, hc⟩, _⟩ := h
  exact mv_reach ht hc ho

theorem susp_act_mv {t s : Nat} {p r : Pp} (h : Suspended (W n G H) t p (.act s r)) :
    ∃ i j x, mv n G t p = some (.claim i j) ∧ mv n G s r = some (.sign x) ∧
      (x = i ∨ x = j) := by
  obtain ⟨⟨_, m, m', hm, hm', ho⟩, hnc⟩ := h
  rcases ho with hs | ⟨i, j, rfl, hx⟩
  · exact absurd ⟨m, _, hm, hm', hs⟩ hnc
  · rcases hx with rfl | rfl
    · exact ⟨i, j, i, hm', hm, Or.inl rfl⟩
    · exact ⟨i, j, j, hm', hm, Or.inr rfl⟩

theorem sign_at {s x : Nat} {r : Pp} (h : mv n G s r = some (.sign x)) :
    s = 8*x+6 ∧ r = .a := by
  rcases mv_cases h with ⟨_, _, h'⟩ | ⟨_, h6, hr, h'⟩ | ⟨_, _, _, _, _, h'⟩
  · cases h'
  · cases h'; exact ⟨by omega, hr⟩
  · cases h'

theorem claim_at {t i j : Nat} {p : Pp} (h : mv n G t p = some (.claim i j)) : (i, j) ∈ G := by
  rcases mv_cases h with ⟨_, _, h'⟩ | ⟨_, _, _, h'⟩ | ⟨_, _, i', j', hg, h'⟩
  · cases h'
  · cases h'
  · cases h'; exact List.mem_iff_getElem?.mpr ⟨_, hg⟩

/-- **The claim graph is exactly `G`.** Every claim in the world has its two arcs going to
the signs for the endpoints of an edge of `G`. -/
theorem only_edges {t t' : Nat} {τ1 τ2 : Tgt Pp Nat} {p q : Pp}
    (h : Claim (W n G H) t t' τ1 τ2 p q) :
    ∃ e ∈ G, (τ1 = .act (8*e.1+6) .a ∧ τ2 = .act (8*e.2+6) .a) ∨
             (τ1 = .act (8*e.2+6) .a ∧ τ2 = .act (8*e.1+6) .a) := by
  obtain ⟨hne, hj1, hj2, _, _⟩ := h
  have hs1 := hj1.2.2.2.1
  have hs2 := hj2.2.2.2.1
  cases τ1 with
  | obj o1 =>
    have h1 := susp_obj_mv hs1
    cases τ2 with
    | obj o2 =>
      have h2 := susp_obj_mv hs2
      rw [h1] at h2; cases h2; exact absurd rfl hne
    | act s2 r2 =>
      obtain ⟨i, j, x, h2, _⟩ := susp_act_mv hs2
      rw [h1] at h2; cases h2
  | act s1 r1 =>
    obtain ⟨i, j, x1, hc1, hs1', hx1⟩ := susp_act_mv hs1
    cases τ2 with
    | obj o2 =>
      have h2 := susp_obj_mv hs2
      rw [hc1] at h2; cases h2
    | act s2 r2 =>
      obtain ⟨i', j', x2, hc2, hs2', hx2⟩ := susp_act_mv hs2
      rw [hc1] at hc2; cases hc2
      obtain ⟨rfl, rfl⟩ := sign_at hs1'
      obtain ⟨rfl, rfl⟩ := sign_at hs2'
      refine ⟨(i, j), claim_at hc1, ?_⟩
      have hx : x1 ≠ x2 := fun e => hne (by rw [e])
      rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl
      · exact absurd rfl hx
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hx

end Univ

/-! ## Headline -/

open Univ in
/-- **Universality.** For any `n` objects, any graph `G` on them (no loops) and any physical
arrangement `H` of which pairs are together, there is a history satisfying every axiom,
kinematics included, in which:
* every object `i` has a sign (`a`'s movement at `8i + 6`) descending from an ostensive on it;
* every edge of `G` is a claim whose two arcs go to the signs for its endpoints;
* that claim is true iff its objects are not together according to `H`;
* every claim in the history comes from an edge of `G` in this way. -/
theorem universality (n : Nat) (G H : List (Nat × Nat))
    (hG : ∀ e ∈ G, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) :
    ∃ W : World Pp Nat Frm, Axioms W ∧ Kinematics W ∧
      (∀ i, i < n → Descends W (8*i+6) .a i) ∧
      (∀ e ∈ G, ∃ t t', Claim W t t' (.act (8*e.1+6) .a) (.act (8*e.2+6) .a) .b .a ∧
          (ClaimTrue W t e.1 e.2 ↔ ¬ ((e.1, e.2) ∈ H ∨ (e.2, e.1) ∈ H))) ∧
      (∀ t t' τ1 τ2 p q, Claim W t t' τ1 τ2 p q → ∃ e ∈ G,
          (τ1 = .act (8*e.1+6) .a ∧ τ2 = .act (8*e.2+6) .a) ∨
          (τ1 = .act (8*e.2+6) .a ∧ τ2 = .act (8*e.1+6) .a)) := by
  refine ⟨W n G H, axioms, kinematics, fun i hi => descends_vertex hi, ?_,
    fun _ _ _ _ _ _ h => only_edges h⟩
  intro e he
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  obtain ⟨h1, h2, h12⟩ := hG e he
  obtain ⟨i, j⟩ := e
  exact ⟨8*n+8*k, 8*n+8*k+1, claim_edge hk h1 h2 h12,
    by unfold ClaimTrue; rw [together_iff (by omega) h12]⟩

open Univ in
/-- **Thick falsehood, instantiated.** Three objects; claims "0 — 1" and "1 — 2"; in the
world, 0 and 1 are together. The first claim is false and the second true, and both are made
where neither speaker has any object within reach. -/
example : ∃ W : World Pp Nat Frm, Axioms W ∧ Kinematics W ∧
    (∃ t t', Claim W t t' (.act 6 .a) (.act 14 .a) .b .a ∧ ¬ ClaimTrue W t 0 1) ∧
    (∃ t t', Claim W t t' (.act 14 .a) (.act 22 .a) .b .a ∧ ClaimTrue W t 1 2) := by
  refine ⟨W 3 [(0, 1), (1, 2)] [(0, 1)], axioms, kinematics,
    ⟨24, 25, claim_edge (n := 3) (G := [(0, 1), (1, 2)]) (H := [(0, 1)]) (k := 0) (i := 0)
      (j := 1) rfl (by omega) (by omega) (by omega), ?_⟩,
    ⟨32, 33, claim_edge (n := 3) (G := [(0, 1), (1, 2)]) (H := [(0, 1)]) (k := 1) (i := 1)
      (j := 2) rfl (by omega) (by omega) (by omega), ?_⟩⟩
  · unfold ClaimTrue; rw [together_iff (by omega) (by omega)]; simp
  · unfold ClaimTrue; rw [together_iff (by omega) (by omega)]; simp

end GA.Completion
