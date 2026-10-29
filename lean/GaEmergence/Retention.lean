import GaEmergence.Behaviour

/-!
# Retention: what makes a movement worth repeating

The answer here is deliberately unprescriptive, mirroring Axiom 4.

> **Retention.** Some unspecified retention function makes participants, under certain
> circumstances, produce again a movement like one they produced before, in a context
> similar to (not identical with) the earlier one. Its nature is unspecified (habit, reward
> and salience are possible realizations), and retention is not guaranteed.

Retention plays the speaker's part, explaining why anyone makes the movement again.
Forcing plays the hearer's part, explaining why anyone responds when it misfires. Both are
left unspecified.

Because retention is keyed to *similar* contexts, the repeated movement can occur where
the object is absent. That is the "inappropriate ostensive", and it needs no further
association axiom.

Results:
* `no_retention_only_ostensives`: if no movement ever echoes an earlier one, every
  taking-as is a joint deferral. There is no imperative, no declarative and no graph,
  whatever forcing does.
* `chain_from_one_chance`: one chance joint deferral, retained once, under forcing and with
  the object no longer available, *entails* an imperative, its failure and a symbolic node.
* `retention_needed`: a scene with a joint deferral, maximal forcing and an unavailable
  object, but no retention, in which nothing follows.
* `chain_hypotheses_consistent`: the hypotheses of `chain_from_one_chance` hold together
  in the `Fight` model.
-/

namespace GA.Behavioural
open GA

set_option linter.constructorNameAsVariable false

section
variable {P O C G : Type} (S : BScene P O C G)

/-- `a`'s movement at `t` is like `a`'s movement at `s`, in a similar context. -/
def Echoes (s t : Nat) (a : P) : Prop :=
  s < t ∧ ∃ g g', S.act s a = .move g ∧ S.act t a = .move g' ∧ S.sim (g', S.ctx t) (g, S.ctx s)

/-- A movement echoing one taken as being about `o`, made where `o` is absent: the
inappropriate ostensive, identified before anyone responds to it. -/
def Dangling (t : Nat) (a : P) (o : O) : Prop :=
  ∃ s a' h' g g', s < t ∧ S.act t a = .move g ∧ S.act s a' = .move g' ∧
    Takes S s a' h' (.phys o) ∧ S.sim (g, S.ctx t) (g', S.ctx s) ∧ ¬ S.present (S.ctx t) o

/-- Axiom 4 on the hearer's side, at the imperative. Under forcing, a dangling movement
compels someone else to try to supply the object. -/
def ForcedSupply : Prop :=
  ∀ t a o, Dangling S t a o → S.forcing t (t+1) → ∃ h, h ≠ a ∧ S.act (t+1) h = .fetch o

/-- **Without repetition, only ostensives.** If no movement ever resembles an earlier one,
every instance of taking-as is a joint deferral of a reach for a physical object. -/
theorem no_retention_only_ostensives
    (hno : ∀ s t a a' g g', s < t → S.act s a' = .move g' → S.act t a = .move g →
      ¬ S.sim (g, S.ctx t) (g', S.ctx s))
    {t : Nat} {a h : P} {τ : Target O} (hT : Takes S t a h τ) :
    ∃ o, τ = .phys o ∧ JointDeferral S t o a h := by
  cases hT with
  | defer hj => exact ⟨_, rfl, hj⟩
  | fetch hm hs hm' _ hsim _ _ => exact absurd hsim (hno _ _ _ _ _ _ hs hm' hm)
  | declare hjt hmj _ _ _ hm hsim _ _ _ => exact absurd hsim (hno _ _ _ _ _ _ hjt hmj hm)
  | echo hm hs hm' _ hsim _ _ _ => exact absurd hsim (hno _ _ _ _ _ _ hs hm' hm)

/-- **One chance deferral, retained once, entails the rest.** Assume:
* `a` and `h` once jointly refrained from the object (by chance, for any reason);
* retention: `a` later makes a similar movement (at `t`);
* after time `T` the object is unavailable, and forcing applies to what happens at `t`.

Then someone fetches in vain (imperative and failure), and eventually that person's
movement is taken as being about the failed act (a symbolic node). -/
theorem chain_from_one_chance (hFS : ForcedSupply S) (hF : ForcedPreservation S)
    {s t T : Nat} {o : O} {a h : P}
    (hjd : JointDeferral S s o a h)
    (hret : Echoes S s t a) (hTt : T < t)
    (hforce : ∀ u, t < u → S.forcing t u)
    (hunavail : ∀ u, T < u → ¬ S.present (S.ctx u) o) :
    ∃ h' k, Failed S t a h' o ∧ t < k ∧ Takes S k h' a (.occ t) := by
  obtain ⟨hst, g, g', hgs, hgt, hsim⟩ := hret
  have hd : Dangling S t a o :=
    ⟨s, a, h, g', g, hst, hgt, hgs, .defer hjd, hsim, hunavail t hTt⟩
  obtain ⟨h', hne, hfetch⟩ := hFS t a o hd (hforce (t+1) (Nat.lt_succ_self t))
  have hfail : Failed S t a h' o :=
    ⟨⟨g', hgt⟩, .fetch hgt hst hgs (.defer hjd) hsim (fun e => hne e.symm) hfetch,
      hunavail t hTt⟩
  obtain ⟨k, hk, hT⟩ := declarative_of_forcing S hF hfail hforce
    (fun u hu => hunavail u (by omega))
  exact ⟨h', k, hfail, hk, hT⟩

end

/-! ## Models -/

open GA.Models

/-- The `Fight` model satisfies the forced-supply axiom. -/
theorem Fight.forcedSupply : ForcedSupply Fight.S := by
  intro t a o hd hf
  have ht : t = 6 := hf
  subst ht
  obtain ⟨_, _, _, g, _, _, hm, _⟩ := hd
  cases o
  cases a
  · exact ⟨.b, by decide, rfl⟩
  · simp [Fight.S, Fight.act] at hm

/-- The hypotheses of `chain_from_one_chance` are jointly satisfiable. In `Fight`: the
deferral at t4, its retention at t6, unavailability after t5, and forcing on t6. -/
theorem chain_hypotheses_consistent :
    ForcedSupply Fight.S ∧ ForcedPreservation Fight.S ∧
    JointDeferral Fight.S 4 .hammer .a .b ∧ Echoes Fight.S 4 6 .a ∧
    (∀ u, 6 < u → Fight.S.forcing 6 u) ∧
    (∀ u, 5 < u → ¬ Fight.S.present (Fight.S.ctx u) .hammer) := by
  refine ⟨Fight.forcedSupply, Fight.forcedPreservation, Fight.deferral4,
    ⟨by omega, .g0, .g1, rfl, rfl, rfl⟩, fun _ _ => rfl, fun u hu => ?_⟩
  match u with
  | 0 | 1 | 2 | 3 | 4 | 5 => omega
  | 6 | 7 | 8 | 9 => simp [Fight.S, Fight.ctx, presentB]
  | _ + 10 => simp [Fight.S, Fight.ctx, presentB]

namespace Lone

/-- `a` and `b` reach for the hammer once and both refrain. The hammer is then gone,
forcing is maximal, and nobody ever moves again. -/
def S : BScene Pt Ob Cx Gs where
  present c o := presentB c o = true
  aim g c o := aimB g c o = true
  sim x y := simB x y = true
  ctx | 0 | 1 => .scene | _ => .absent
  act | 0, _ => .move .g0 | _, _ => .rest
  forcing _ _ := True

theorem move_zero {t : Nat} {p : Pt} {g : Gs} (h : S.act t p = .move g) : t = 0 := by
  match t with
  | 0 => rfl
  | _ + 1 => simp [S] at h

theorem no_echo : ∀ s t a a' g g', s < t → S.act s a' = .move g' → S.act t a = .move g →
    ¬ S.sim (g, S.ctx t) (g', S.ctx s) := by
  intro s t _ _ _ _ hst _ hm
  have := move_zero hm
  omega

theorem no_failure : ∀ j a h o, ¬ Failed S j a h o := by
  rintro j a h o ⟨_, hT, hp⟩
  obtain ⟨_, he, hj⟩ := no_retention_only_ostensives S no_echo hT
  cases he
  obtain ⟨_, _, haim⟩ := hj.1.2.1
  exact hp (aimB_directed _ _ _ haim)

theorem retention_needed :
    ForcedSupply S ∧ ForcedPreservation S ∧ (∀ j u, S.forcing j u) ∧
    JointDeferral S 0 .hammer .a .b ∧ (∀ u, 1 < u → ¬ S.present (S.ctx u) .hammer) ∧
    (∀ a t, ¬ Echoes S 0 t a) ∧
    (∀ t a h τ, Takes S t a h τ → ∃ o, τ = .phys o) ∧ (∀ j a h o, ¬ Failed S j a h o) := by
  refine ⟨?_, ⟨?_, ?_⟩, fun _ _ => trivial,
    ⟨⟨by decide, ⟨.g0, rfl, rfl⟩, ⟨.g0, rfl, rfl⟩⟩, by simp [Grasps, S], by simp [Grasps, S]⟩,
    ?_, ?_, ?_, no_failure⟩
  · rintro t a o ⟨_, _, _, _, _, hst, hm, _⟩ _
    have := move_zero hm; omega
  · intro j t a h o _ hop _; exact absurd hop.1 (no_failure j a h o)
  · intro j a h o hf; exact absurd hf (no_failure j a h o)
  · intro u hu
    match u with
    | 0 | 1 => omega
    | _ + 2 => simp [S, presentB]
  · rintro a t ⟨hlt, _, _, _, hm, _⟩
    have := move_zero hm; omega
  · intro t a h τ hT
    obtain ⟨o, he, _⟩ := no_retention_only_ostensives S no_echo hT
    exact ⟨o, he⟩

end Lone

end GA.Behavioural
