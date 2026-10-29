import GaEmergence.Basic

/-!
# General theorems

Each result is quantified over **every** scene satisfying the stated axioms, so these are
derivations, not facts about one constructed model. Each docstring names the axioms used.
-/

namespace GA

/-- Strong induction on time, proved here because core Lean has no ready-made version in this form. -/
theorem strongInd {motive : Nat → Prop} (t : Nat)
    (step : ∀ t, (∀ s, s < t → motive s) → motive t) : motive t := by
  have : ∀ n, ∀ s, s < n → motive s := by
    intro n
    induction n with
    | zero => intro s hs; exact absurd hs (Nat.not_lt_zero _)
    | succ n ih => intro s hs; exact step s (fun r hr => ih r (by omega))
  exact this (t+1) t (Nat.lt_succ_self t)

variable {P O C G : Type} (S : Scene P O C G)

/-- A5 only adds possibilities: every scene satisfying the axioms without A5 also
satisfies them with it. -/
theorem Admissible₀.toAdmissible (h : Admissible₀ S) : Admissible S := by
  refine ⟨⟨fun t p τ hu => ?_⟩, h.2⟩
  obtain ⟨a, g, hd, hne, hg⟩ := h.1.recog t p τ hu
  exact ⟨a, g, hd, hne, hg.elim Or.inl (fun r => Or.inr (Or.inl r))⟩

/-- **Axiom 1 is derivable.** If anything is recognized at all, there are at least two
participants, because recognition is other-directed. (Axiom used: Recognition.) -/
theorem plurality (hR : Recognition S) (hu : ∃ t h τ, S.uptake t = some (h, τ)) :
    ∃ p q : P, p ≠ q := by
  obtain ⟨t, h, τ, hu⟩ := hu
  obtain ⟨a, _, _, hne, _⟩ := hR.recog t h τ hu
  exact ⟨a, h, hne⟩

/-- **Necessity of A5.** Without reflexive uptake, everything ever taken up is a physical
object. No symbolic vertex can arise, whatever forcing does. (Axioms used: Recognition₀.
Proof by strong induction on time.) -/
theorem phys_only₀ (hR : Recognition₀ S) :
    ∀ t h τ, S.uptake t = some (h, τ) → ∃ o, τ = .phys o := by
  intro t
  induction t using strongInd with
  | step t ih =>
    intro h τ hu
    obtain ⟨_, _, _, _, hg⟩ := hR.recog t h τ hu
    rcases hg with ⟨o, ho, _⟩ | ⟨s, hs, _, _, h', _, hu', _⟩
    · exact ⟨o, ho⟩
    · exact ih s hs h' τ hu'

theorem no_symbolic_vertex₀ (hR : Recognition₀ S) (n : Nat) (v : Target O) :
    Vertex S n v → ¬ Symbolic v := by
  rintro ⟨t, h, _, hu⟩ hsym
  obtain ⟨o, rfl⟩ := phys_only₀ S hR t h v hu
  exact hsym o rfl

/-- **The imperative presupposes recurrence.** A failed relation cannot be grounded in
presence or in reflexivity, so it can only rest on recurrence of an earlier act.
(Axiom used: Recognition.) -/
theorem failure_is_recurrence (hR : Recognition S) {j : Nat} {a h : P} {o : O}
    (hf : Failure S j a h o) : ∃ g, S.deed j = .sign a g ∧ RecGround S j g (.phys o) := by
  obtain ⟨⟨g₀, hd₀⟩, hu, hp⟩ := hf
  obtain ⟨a', g, hd, _, hg⟩ := hR.recog j h _ hu
  rw [hd₀] at hd
  cases hd
  rcases hg with ⟨o', ho', hp'⟩ | hr | ⟨_, _, hτ, _⟩
  · cases ho'; exact absurd hp' hp
  · exact ⟨g₀, hd₀, hr⟩
  · cases hτ

/-- **Genealogy.** Every relation to a physical object, present or absent, descends through
a chain of local recurrences from an *ostensive* relation to that object. The chain need
not collapse to a single similarity, since `sim` is not assumed transitive.
(Axiom used: Recognition.) -/
theorem genealogy (hR : Recognition S) (o : O) :
    ∀ t h, S.uptake t = some (h, .phys o) →
      ∃ s, s ≤ t ∧ Ostensive S s o ∧ Lineage S s t := by
  intro t
  induction t using strongInd with
  | step t ih =>
    intro h hu
    obtain ⟨a, g, hd, _, hg⟩ := hR.recog t h _ hu
    rcases hg with ⟨o', ho', hp⟩ | ⟨s, hs, a', g', h', hd', hu', hsim⟩ | ⟨_, _, hτ, _⟩
    · cases ho'
      exact ⟨t, Nat.le_refl t, ⟨h, hu, hp⟩, .refl t⟩
    · obtain ⟨s₀, hs₀, host, hlin⟩ := ih s hs h' hu'
      exact ⟨s₀, by omega, host, .echo hlin hs ⟨a, g, a', g', hd, hd', hsim⟩⟩
    · cases hτ

/-- **Symbolic reference originates in an originary declarative.** Every uptake of an act
as referent descends from a moment at which an *unsatisfied* failure was preserved
symbolically. (Axiom used: Recognition. Proof by strong induction.) -/
theorem declarative_origin (hR : Recognition S) :
    ∀ t h j, S.uptake t = some (h, .occ j) →
      ∃ k, j < k ∧ k ≤ t ∧ OriginaryDeclarative S j k := by
  intro t
  induction t using strongInd with
  | step t ih =>
    intro h j hu
    obtain ⟨a, g, hd, _, hg⟩ := hR.recog t h _ hu
    rcases hg with ⟨_, ho, _⟩ | ⟨s, hs, _, _, h', _, hu', _⟩ | ⟨j', hj', hτ, o, hopen⟩
    · cases ho
    · obtain ⟨k, h1, h2, h3⟩ := ih s hs h' j hu'
      exact ⟨k, h1, by omega, h3⟩
    · cases hτ
      exact ⟨t, hj', Nat.le_refl t, h, a, o, hopen, ⟨g, hd⟩, hu⟩

/-- **The Gansian order is derived, not stipulated.** Any declarative act presupposes an
originary declarative at `k`, which preserved a failed relation opened at `j`, which
descends from an ostensive at `s`, and `s < j < k ≤ t` strictly. (Axiom used: Recognition.) -/
theorem gansian_order (hR : Recognition S) {t : Nat} (hdecl : Declarative S t) :
    ∃ s j k o, s < j ∧ j < k ∧ k ≤ t ∧
      Ostensive S s o ∧ (∃ a h, Failure S j a h o) ∧ OriginaryDeclarative S j k := by
  obtain ⟨h, j, hu⟩ := hdecl
  obtain ⟨k, hjk, hkt, a, h', o, hopen, hpres⟩ := declarative_origin S hR t h j hu
  have hf := hopen.1
  obtain ⟨s, hsj, hos, _⟩ := genealogy S hR o j h' hf.2.1
  have hsj' : s < j := by
    rcases Nat.lt_or_eq_of_le hsj with hlt | heq
    · exact hlt
    · subst heq
      obtain ⟨_, _, hp⟩ := hos
      exact absurd hp hf.2.2
  exact ⟨s, j, k, o, hsj', hjk, hkt, hos, ⟨a, h', hf⟩, a, h', o, hopen, hpres⟩

/-- **Before the first declarative there are vertices but no graph.** If no originary
declarative has occurred before time `n`, every vertex is a physical object and there is no
arc between vertices. Contextual edges exist, but they connect no nodes.
(Axiom used: Recognition.) -/
theorem no_graph_before_declarative (hR : Recognition S) (n : Nat)
    (hnone : ∀ j k, k < n → ¬ OriginaryDeclarative S j k) :
    (∀ v, Vertex S n v → ¬ Symbolic v) ∧ (∀ v w, ¬ Arc S n v w) := by
  have key : ∀ t h j, t < n → S.uptake t ≠ some (h, .occ j) := by
    intro t h j htn hu
    obtain ⟨k, _, hkt, hk⟩ := declarative_origin S hR t h j hu
    exact hnone j k (by omega) hk
  constructor
  · rintro v ⟨t, h, htn, hu⟩ hsym
    cases v with
    | phys o => exact hsym o rfl
    | occ j => exact key t h j htn hu
  · rintro v w ⟨⟨t, h, htn, hu⟩, _, _, rfl, _, _⟩
    exact key t h _ htn hu

/-- **Persistent forcing guarantees resolution.** If forcing never lapses, a failure *must*
be resolved, by supply or by symbolic preservation. Consequently the clause "successful
preservation is not guaranteed" is consistent only if forcing can lapse.
(Axiom used: ForcedPreservation only.) -/
theorem resolution_of_persistent_forcing (hF : ForcedPreservation S)
    {j : Nat} {a h : P} {o : O} (hfail : Failure S j a h o)
    (hforce : ∀ t, j < t → S.forcing j t) :
    ∃ k, j ≤ k ∧ (Supplies S k h o ∨ Preserves S j k a h) := by
  obtain ⟨T, hT⟩ := hF.untenable j a h o hfail
  obtain ⟨t, hTt, hjt⟩ : ∃ t, T < t ∧ j < t := ⟨T + j + 1, by omega, by omega⟩
  have hnot := hT t hTt
  by_cases hop : Open S j t a h o
  · rcases hF.forced j t a h o hjt hop (hforce t hjt) with hd | ⟨g, hd⟩
    · by_cases hp : S.present (S.ctx (t+1)) o
      · exact ⟨t, by omega, Or.inl ⟨hd, hp⟩⟩
      · exact absurd ⟨hop, Or.inl ⟨hd, hp⟩⟩ hnot
    · by_cases hp : Preserves S j t a h
      · exact ⟨t, by omega, Or.inr hp⟩
      · exact absurd ⟨hop, Or.inr ⟨⟨g, hd⟩, hp⟩⟩ hnot
  · apply Classical.byContradiction
    intro hno
    exact hop ⟨hfail, fun k hk _ =>
      ⟨fun hs => hno ⟨k, hk, Or.inl hs⟩, fun hp => hno ⟨k, hk, Or.inr hp⟩⟩⟩

/-- **When supply is impossible, forcing entails the declarative.** If forcing persists and
the object never returns, the hearer's act is eventually taken up as being about the failed
act itself. (Axiom used: ForcedPreservation only. Whether such an uptake is *admissible* is
a separate question, answered by the next theorem.) -/
theorem declarative_of_forcing (hF : ForcedPreservation S)
    {j : Nat} {a h : P} {o : O} (hfail : Failure S j a h o)
    (hforce : ∀ t, j < t → S.forcing j t)
    (hunavail : ∀ t, j < t → ¬ S.present (S.ctx t) o) :
    ∃ k, j < k ∧ Preserves S j k a h := by
  obtain ⟨k, hk, hs | hp⟩ := resolution_of_persistent_forcing S hF hfail hforce
  · exact absurd hs.2 (hunavail (k+1) (by omega))
  · refine ⟨k, ?_, hp⟩
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact hlt
    · subst heq
      have := hp.2.symm.trans hfail.2.1
      simp at this

/-- **Without A5, the original axioms are inconsistent with persistent forcing on an
unavailable object.** Hence in any world without reflexive uptake, the forcing must lapse
and the relation collapses. The declarative is the *only* preserving exit.
(Axioms used: Recognition₀ and ForcedPreservation.) -/
theorem collapse_without_reflexivity (hA : Admissible₀ S)
    {j : Nat} {a h : P} {o : O} (hfail : Failure S j a h o)
    (hforce : ∀ t, j < t → S.forcing j t)
    (hunavail : ∀ t, j < t → ¬ S.present (S.ctx t) o) : False := by
  obtain ⟨k, _, _, hu⟩ := declarative_of_forcing S hA.2 hfail hforce hunavail
  obtain ⟨o', ho'⟩ := phys_only₀ S hA.1 k a _ hu
  cases ho'

/-- With A5, the preserving act of `declarative_of_forcing` yields a symbolic node with an
arc to the absent object. (Axioms used: all, including A5.) -/
theorem symbolic_node_of_forcing (hA : Admissible S)
    {j : Nat} {a h : P} {o : O} (hfail : Failure S j a h o)
    (hforce : ∀ t, j < t → S.forcing j t)
    (hunavail : ∀ t, j < t → ¬ S.present (S.ctx t) o) :
    ∃ k, j < k ∧ SymbolicNode S (k+1) (.occ j) ∧ Arc S (k+1) (.occ j) (.phys o) := by
  obtain ⟨k, hjk, _, hu⟩ := declarative_of_forcing S hA.2 hfail hforce hunavail
  have hv : Vertex S (k+1) (.occ j) := ⟨k, a, Nat.lt_succ_self k, hu⟩
  exact ⟨k, hjk, ⟨hv, fun _ h => by cases h⟩,
    hv, j, h, rfl, by omega, hfail.2.1⟩

end GA
