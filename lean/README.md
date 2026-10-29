# From ostension to symbolic nodes: a Lean 4 formalization

A machine-checked model of an idea drawn from Eric Gans's Generative Anthropology: the
ostensive → imperative → declarative sequence read as the emergence of graph structure.

* Lean 4.15.0, core library only (no Mathlib).
* No `sorry`, `admit` or custom `axiom`.
* `#print axioms`: the existence results depend only on `propext` and `Quot.sound`, so
  they are constructive. The forcing theorems also use `Classical.choice`.

```bash
lake build
```

```bash
lake env lean Check.lean
```

The first command builds the library. The second prints the axioms each theorem depends on.

| File | Contents |
|---|---|
| `GaEmergence/Basic.lean` | Definitions only: scenes, refined axioms, modes, graph |
| `GaEmergence/Theorems.lean` | General theorems, proved for **every** scene satisfying the axioms |
| `GaEmergence/Models.lean` | Three concrete models and the existence / non-inevitability results |
| `GaEmergence/Originary.lean` | Removing the ostensive from the axioms: it is derived from practical action (§7) |
| `GaEmergence/Polarity.lean` | The positive as the negation of a negation; partial universality (§19) |
| `GaEmergence/Roles.lean` | Relations with roles require order; firstness suffices (§18) |
| `GaEmergence/Graphs.lean` | Compound claims and the universality theorem for grounded graphs (§17) |
| `GaEmergence/Behaviour.lean` | Uptake defined as response, and restraint as exhaustion instead of catastrophe (§8) |

---

## 1. Critical evaluation of the proposed axioms

### Axiom 1 (Plurality): redundant once recognition is refined
On its own, plurality does nothing. What matters is that recognition is *other-directed*:
the hearer is not the author. Once that is part of Axiom 2, plurality follows from the
existence of any recognition at all (`GA.plurality`). So I state it as a theorem, not an axiom.

### Axiom 2 (Contextual recognition): needs a target and a ground
As stated, the axiom has two gaps.

1. **"Recognize as signifying" needs a target.** Without something the act is *about*,
   there is no relation, and hence no edge. Uptake is therefore modelled as a relation
   `hearer × target` attached to a deed.
2. **It allows meaning *ex nihilo*.** Nothing in the axiom stops a participant from
   recognizing a first-ever act as being about an absent object. Then the ostensive is not
   originary, and the imperative needs no ostensive before it. The refinement is a
   **grounding condition**: an uptake must rest on
   * *presence*: the target is a physical object present in the context (ostensive grounding), or
   * *recurrence*: the act is like an earlier act that was taken up as being about the same target.

   Grounding is what makes the genealogy theorems true. Without it, a model where the first
   uptake is about an absent hammer refutes them trivially.

"Need not be universal or reciprocal" is respected. Nothing requires an act to be taken
up, and the collapse model contains an act that no one takes up.

### Axiom 3 (Contextual recurrence): must not be an equivalence relation, and must carry the target
* If similarity were reflexive, symmetric and transitive, quotienting by it would yield
  abstract sign-types. Symbolic identity would then be smuggled in before the declarative.
  So `sim` is an arbitrary relation, and the emergence model makes it **non-transitive**
  (`Emergence.sim_not_transitive`). Descent is tracked by explicit chains of local
  similarities (`Lineage`), not by type membership.
* Recurrence of *form* alone produces no failure. For the absent-referent case to be a
  *failed relation*, the recurrent act must inherit the earlier act's target. This is part
  of the refined axiom. It uses only the identity of physical objects, which is allowed.

### Axiom 4 (Forced preservation): three clauses that interact
The axiom bundles three claims:
1. **compulsion**: while forced, the hearer must *attempt* preservation;
2. **untenability**: unsuccessful attempts cannot go on indefinitely;
3. **non-guarantee**: successful preservation is not assured.

Three problems follow.

* **Untenability needs unbounded time.** Over finite histories it is vacuous. Time is `Nat`,
  and untenability says that after some time `T` there are no more unsuccessful attempts.
* **The three clauses conflict unless forcing can lapse.** `resolution_of_persistent_forcing`
  shows that if forcing never lapses, compulsion and untenability together *entail* that the
  failure is resolved. So clause 3 can hold only in scenes where forcing switches off,
  meaning the relation is abandoned. The unspecified forcing function therefore has to
  allow lapse. The collapse model uses exactly this.
* **The axiom does not say what preservation is.** If the only way to preserve a relation
  is to make its object present, then an unavailable object makes preservation impossible.
  That gap is the most important missing assumption, A5 below.

---

## 2. Refined axiom system (as formalized)

A **scene** has participants `P`, physical objects `O`, contexts `C`, bodily forms `G`, a
presence relation, an arbitrary similarity `sim`, and one discrete-time history.
At each time it records:
* a deed: `sign p g`, `fetch p o` or `idle`;
* a context;
* an optional uptake `(hearer, target)`, where the target is `phys o` or `occ t` (the act at time `t`);
* an arbitrary forcing predicate `forcing j t`.

| # | Lean | Content |
|---|---|---|
| R | `Recognition₀` | Every uptake is of a produced form, by someone other than its author, and rests on presence or on recurrence (the target is inherited). |
| F1 | `ForcedPreservation.forced` | While the failure opened at `j` is unresolved and forcing is on, the hearer's deed is an attempt: fetching the object, or producing a form. |
| F2 | `ForcedPreservation.untenable` | For every failure there is a time after which no unsuccessful attempt occurs. |
| **A5** | `Recognition` (third clause `ReflGround`) | **Reflexive uptake.** An act by the hearer of a *still-open* failure can be taken up by that failure's author as being *about the failed act itself*. |
| N | `Nontrivial` | The existential clauses ("participants *can* ..."): two participants, an ostensive, a recurrence in absence, and forcing that actually applies to an open failure. |

`Admissible₀ = R ∧ F` (your axioms, refined). `Admissible = R + A5 ∧ F`.

### Additional assumptions, and why each is needed
1. **Physical presence and contexts** (`present`, `ctx`). Needed even to state that a referent is absent.
2. **Practical action** (`fetch`). The imperative has to be able to *do* something. Whether
   it succeeds is decided by the world (the next context).
3. **Grounding** (the refinement of Axiom 2). Needed for every genealogy result.
4. **Target inheritance under recurrence** (the refinement of Axiom 3). Needed for failure
   to exist at all.
5. **Unbounded time.** Needed for untenability to say anything.
6. **Forcing may lapse.** Needed for "success not guaranteed" to be consistent with persistent compulsion.
7. **A5, reflexive uptake.** *Necessary* for any symbolic node:
   * `phys_only₀`: without A5, everything ever taken up is physical, in every scene.
   * `collapse_without_reflexivity`: without A5, persistent forcing on an unavailable object
     is outright **inconsistent**. Forcing must lapse, and the relation collapses.

   A5 is restricted to *open* failures. That restriction is a substantive Gansian claim:
   attention to the sign as such arises only when its referent fails. If A5 allowed
   reference to *any* past act, symbolic reference could arise without a failed imperative,
   and `declarative_origin` / `gansian_order` would no longer hold.

**On "no symbolic nodes in advance".** A5 puts *events* into the space of possible targets,
and events have temporal identity. It does **not** put anything into the graph. Vertices
are only what has actually been taken up (`Vertex`). The theorems show that this set has
no non-physical members until a declarative occurs. A5 also says nothing about nodes, arcs,
re-presentation or independence. Those are defined over the history and then derived or
exhibited.

---

## 3. Modes and graph: what is defined

None of these are states of the system. Each is a pattern in the history.

| Concept | Definition (`Basic.lean`) |
|---|---|
| Ostensive | an uptake of a physical object that is present |
| Failure (dangling edge) | an uptake of a physical object that is absent |
| Imperative attempt | the hearer of an open failure fetches its object |
| Imperative satisfied | the fetch brings the object into the next context |
| Originary declarative | the hearer's act is taken up, by the original author, as being about the open failed act |
| Declarative act | any uptake whose target is an act |
| Vertex | anything actually taken up |
| Symbolic | not a physical object |
| Arc `v → w` | `v` is a vertex that is itself a recognized act, and `w` is what that act was about |
| Independent node | a symbolic vertex with an arc to an absent object, taken up in two distinct contexts with the object absent from both |

**A sharpening of your hypothesis.** Ostensive relations are *contextual incidences*. Each
one joins a momentary act to an object within one context, and the act end is not a vertex.
The first arc *between vertices* appears exactly when a relation becomes a referent. The
declarative therefore creates a node and an edge **together**: **the symbolic node is the
reified dangling edge.** This is like reification in graph theory, where an edge becomes a
vertex of a line graph, or a statement becomes a resource in RDF.

---

## 4. What is derived (theorems over all admissible scenes, `Theorems.lean`)

| Theorem | Statement | Uses |
|---|---|---|
| `plurality` | any recognition ⇒ ≥ 2 participants | R |
| `phys_only₀`, `no_symbolic_vertex₀` | without A5, no symbolic vertex ever | R (induction) |
| `failure_is_recurrence` | every failed relation rests on recurrence: the imperative presupposes repetition | R + A5 |
| `genealogy` | every relation to an object descends, through a `Lineage` of local similarities, from an **ostensive** of that object | R + A5 (induction) |
| `declarative_origin` | every symbolic reference descends from an **originary declarative** that preserved an *unsatisfied* failure | R + A5 (induction) |
| `gansian_order` | any declarative act at `t` implies an ostensive at `s`, a failure at `j` and an originary declarative at `k`, with **`s < j < k ≤ t`** | R + A5 |
| `no_graph_before_declarative` | before the first originary declarative, all vertices are physical and there are **no arcs** | R + A5 |
| `resolution_of_persistent_forcing` | persistent forcing ⇒ the failure is resolved (by supply or by preservation) | F only |
| `declarative_of_forcing` | persistent forcing + unavailable object ⇒ the hearer's act is eventually taken up as being about the failed act | F only |
| `collapse_without_reflexivity` | without A5, the previous hypotheses are inconsistent | R₀ + F |
| `symbolic_node_of_forcing` | with A5, they yield a symbolic node with an arc to the absent object | all |

The ostensive → imperative → declarative order is therefore **derived** (`gansian_order`),
not built into the definitions. It follows from grounding and the restriction of A5 to
open failures.

## 5. What is exhibited (models, `Models.lean`)

All three models use the same world: participants `a` and `b`, a hammer, contexts
`scene` / `absent` / `later`, and forms `g0`–`g3`.

**`Emergence`** (forcing always on):

| t | deed | context | uptake | mode |
|---|---|---|---|---|
| 0 | `a` makes g0 | scene (hammer present) | `b`: hammer | ostensive |
| 1 | `a` makes g1, which is like g0 | absent | `b`: hammer | failure (recurrence in absence) |
| 2, 3 | `b` fetches the hammer and fails | absent | none | imperative attempts |
| 4 | `b` makes g2 | absent | `a`: act at t1 | originary declarative |
| 5 | `a` makes g3, which is like g2 | later | `b`: act at t1 | declarative, re-presented by plain recurrence |

Proved:
* the model is admissible and nontrivial;
* `sim` is not transitive;
* by time 4 there is no graph;
* by time 6, `occ 1` is an **independent symbolic node**: it has an arc to the absent hammer
  and is taken up in two contexts by two different hearers.

The model also meets the hypotheses of `symbolic_node_of_forcing`, so this declarative is
entailed by the general theory, not only exhibited.

The re-presentation at t5 needs **no new assumption**. Once an act is a referent, ordinary
recurrence (Axiom 3) carries it into new contexts. That is where the node's independence
comes from.

**`Collapse`**: the same opening, then `b`'s symbolic attempt is taken up by no one, forcing
lapses, and the failure stays open forever. The model is admissible, *with A5 available*,
and nontrivial, yet **no symbolic vertex ever appears**.

**`Satisfied`**: the fetch succeeds, the imperative is satisfied, the ostensive is restored
at t3, and no symbolic vertex appears.

Headline theorems:
* `emergence_is_possible`: there is a nontrivial admissible scene with non-transitive
  similarity, an initial stretch with no graph, and then an independent symbolic node.
* `emergence_not_inevitable`: there is a nontrivial admissible scene, with A5 available,
  in which no symbolic node ever arises.

---

## 6. Limitations

* **No predication or negation.** The declarative is modelled only as its *topic*: a
  reified relation that stands for an absent object. Gans's declarative ("the hammer — not
  here") also has a comment, or predicate, and negation, and neither is modelled.
* **No originary scene.** The scene of mimetic crisis, the aborted gesture of
  appropriation and the central object are all absorbed into the unspecified `forcing`
  predicate, as you asked.
* **Dyadic interaction.** Uptake is dyadic, one hearer per act. Collective or joint
  attention would need set-valued uptake.
* **A5 is close to the phenomenon.** It is a permission for event-reference, restricted to
  open failures. The value of the formalization is not that A5 is surprising. It is that
  A5 is shown to be *necessary* (`phys_only₀`, `collapse_without_reflexivity`), *sufficient
  in context* (`symbolic_node_of_forcing`), and *not sufficient by itself*
  (`emergence_not_inevitable`). Everything graph-theoretic (vertices, arcs, the absence of
  a graph before the declarative, independent representability) is derived or exhibited.
  None of it is assumed.

---

## 7. Removing the ostensive from the axioms (`Originary.lean`)

Sections 1–6 **assume** the ostensive in four places:
* `OstGround` makes presence a primitive ground for taking an act as being about an object;
* `Nontrivial.ostension` requires that an ostensive occurs;
* `genealogy` traces everything back to an ostensive only because the ostensive is the induction's sole base case;
* `Deed` distinguishes signs from practical acts from the start.

`Originary.lean` replaces the ostensive ground with a practical layer that contains no
signs and no aboutness. This is Gans's minimal hypothesis, with the reason for restraint
left unspecified.

| Primitive | Lean | Content |
|---|---|---|
| directed movement | `aim`, `Practice.directed` | a movement can be physically aimed at an object, which must be present (geometry, not reference) |
| embodiment | `Practice.embodied` | an author's recorded movement is something the author's body does |
| appropriation | `grasps`, `Practice.completes` | one can grasp only what one has just reached for |
| mimetic symmetry | `MimeticCrisis.symmetric` | of two converging participants, neither completes unless the other does (no hierarchy) |
| restraint | `restraint`, `MimeticCrisis.restrained` | an unspecified forcing function under which a clash (two grasping one object) cannot occur |
| recognition without ostension | `RecognitionO` | an uptake rests on **joint deferral**, on recurrence, or (A5) on reflexivity |

**Derived (`JointDeferral`, the aborted gesture of appropriation).** Two participants
converge on an object and neither completes the grab. This is the only ground on which
an act can be taken as being about a present object.

| Theorem | Statement |
|---|---|
| `deferral_entailed` | convergence + symmetry + restraint ⇒ joint deferral (uses no axioms at all) |
| `ostensive_licensed` | an author and a hearer who converge under restraint have the originary ground for an ostensive uptake |
| `OrigGround.toOstGround` | the old ostensive ground is now a **theorem**: what is jointly deferred is present |
| `RecognitionO.toRecognition` | **bridge**: the ostensive-free axioms imply the old ones, so every result in §4 carries over |
| `genealogyO` | every relation to an object descends, through recurrence chains, from a joint deferral of a convergent reach for it |
| `no_signs_without_deferral` | if convergent appropriation is never jointly deferred, nothing is ever taken up as signifying anything |
| `emergence_from_practice` | a nontrivial model in which the only scene-setting condition is practical convergence under restraint; the deferral is entailed and leads, through failure and imperative attempts, to an independent symbolic node |
| `crisis_hypotheses_needed` | each half of the crisis is needed. **Hierarchy** (restraint, no symmetry): the dominant participant grasps and nothing is deferred. **Rivalry** (symmetry, no restraint): both grasp, there is a clash, and nothing is deferred |

In the full model, the "inappropriate ostensive" at t1 is **physically aimless**
(`aimless1`). The movement g1 is aimed at nothing, because the hammer isn't there. It
signifies only by recurrence.

**What still is assumed.** `uptake`, the *taking* of an act as signifying, is still a
primitive record. What has been removed is the claim that physical presence alone can
ground it. The next step would be to define uptake behaviourally, as mimetic response,
so that taking-as is itself a pattern of action. Directed movement (`aim`) is also
assumed. It is the raw material the ostensive is made from: reaching is directed at
*grasping*, not at *showing*. The difference between the two is exactly the deferral.

---

## 8. Uptake as response, restraint as exhaustion (`Behaviour.lean`)

This is a self-contained system that removes the two assumptions left over from §7.

### Taking-as is defined, not recorded
A `BScene` has **no uptake field**. It records only what each body does at each moment
(move, grasp, fetch, rest), where things are, what is aimed at what, and which forms feel
alike. *Taking an act as being about something* is the inductive predicate `Takes`. What
the act is about is read off what the response is directed at:

| `h`'s response to `a`'s movement | taken as being about |
|---|---|
| both reached for `o` and both refrained | `o` (ostensive) |
| the movement echoes one taken as about `o`; `h` fetches `o` | `o` (imperative) |
| `a`, who failed to supply what `h` asked for at `j`, echoes that act; `h` answers in kind | the act `j` (declarative) |
| the movement echoes one taken as about act `j`; `h` answers in kind | the act `j` (re-presentation) |

Answering in kind, when there is no object to reach for, is what makes the sign itself the target.

What used to be axioms about recognition are now properties of this definition:
* only movements are taken up, and only by someone other than the mover (`takes_mover`);
* every relation to an object descends from a joint deferral, and every relation to an
  act descends from an originary declarative (`takes_origin`, by induction on `Takes`);
* **taking a movement as being about an absent object consists in fetching it** (`failed_fetched`);
* the ostensive → failure → declarative order holds strictly (`gansian_order`);
* there are no symbolic vertices before the first declarative (`no_symbolic_before_declarative`);
* without joint deferral, nothing is taken as anything (`no_signs_without_deferral`).

A5 (reflexive uptake) has not disappeared. It has moved *into the definition*: the
`declare` clause says that an echo of a failed act, answered in kind, **is** taking that
act as a referent. What is still open is whether that is the right behavioural criterion.
It is no longer a separate capacity.

### Restraint by fatigue, not catastrophe
Clashes may happen, any number of times. The only assumption is `Exhausting`: clashes over
an object cannot recur indefinitely. This is your untenability clause applied to fighting.

| Theorem | Statement |
|---|---|
| `deferral_after_exhaustion` | once clashing is exhausted, a symmetric convergence is necessarily deferred |
| `ostensive_of_exhaustion` | symmetry + exhaustion + **persistent desire** ⇒ a joint deferral, with each participant taking the other's reach as being about the object |
| `fatigue_hypotheses_needed` | each ingredient is needed. **Brawl**: they fight forever (no exhaustion). **WalkAway**: they fight once and leave (desire fades). **Hierarchy**: one always wins (no symmetry). In each, nothing is ever taken as signifying anything |
| `emergence_by_response` | a model in which they fight twice, are exhausted, and defer. That deferral is the ostensive, and it is followed by an imperative (a fetch), its failure, an originary declarative, and re-presentation of an independent symbolic node |
| `declarative_of_forcing` | persistent forcing + an object that never returns ⇒ the failed party's movement is eventually answered in kind |

On this account the ostensive is not a response to catastrophe. It comes from **desire that
outlasts the capacity to fight**: they still want the hammer, cannot keep fighting over it,
and neither will let the other have it.

### What is still assumed
* Directed movement (`aim`), appropriation, and the physical constraints in `Practice`.
* Felt similarity (`sim`), which is arbitrary and not transitive.
* Mimetic symmetry, which is substantive and shown to be needed.
* The behavioural criteria in `Takes`, the real theoretical commitment of this layer.
  Each criterion is a hypothesis about what taking-as *consists in*.

---

## 9. The minimal theory

Sorted by which claim each assumption supports:

| Claim | Needs |
|---|---|
| **Possibility**: a symbolic node can emerge (`minimal_emergence`) | aiming requires presence |
| **Necessary order**: every sign descends from a joint deferral; ostensive < failure < declarative; no symbolic node before a declarative; no deferral ⇒ no signs | aiming requires presence, or nothing at all |
| **Conditional entailment**: persistent forcing on an object that never returns ⇒ declarative (`declarative_of_forcing`) | + forcing (Axiom 4) |
| **Likelihood / retention** (not formalized) | + repeated encounters with the object, and some carry-over (habit, association, reward, ...) |

Mimetic symmetry, exhaustion, restraint and the sparagmos are not needed for any of the
first three rows. They only make the deferral *entailed* rather than *possible*.

**Where the remaining weight sits.** With so few axioms, the substantive commitments are
in the *definition* of taking-as (`Takes`): joint deferral, fetching, and echo answered in
kind. A definition can smuggle in as much as an axiom, so these clauses need to be judged
as hypotheses about what taking-as consists in. The `declare` clause carries the former
A5. Possibility claims are cheap when behaviour is unconstrained. The informative results
are the necessity results, which hold in *every* scene.

---

## 10. Retention: what makes a movement worth repeating (`Retention.lean`)

The answer is deliberately unprescriptive and mirrors Axiom 4:

> **Retention.** Some unspecified retention function makes participants, under certain
> circumstances, produce again a movement like one they produced before, in a *similar*
> context. Its nature (habit, reward, salience, ...) is unspecified, and retention is not guaranteed.

Retention covers the speaker's side (why anyone makes the movement again). Forcing covers
the hearer's side (why anyone responds when it misfires). Because retention is keyed to
*similar* contexts, the repeated movement can happen where the object is absent. That is
the inappropriate ostensive, and it needs no extra association axiom.

| Theorem | Statement |
|---|---|
| `no_retention_only_ostensives` | if no movement ever resembles an earlier one, every taking-as is a joint deferral: no imperative, no declarative, no graph, whatever forcing does |
| `chain_from_one_chance` | one chance joint deferral + one retained echo + forcing + an object no longer available ⇒ failed fetch (imperative) and a symbolic node |
| `chain_hypotheses_consistent` | those hypotheses hold together (in `Fight`) |
| `Lone.retention_needed` | joint deferral, maximal forcing, object gone, but no retention: nothing beyond the ostensive ever happens |

The minimal theory, by role:

| Role | Assumption | Status |
|---|---|---|
| physics | one can aim only at what is present | axiom |
| origin | one joint deferral, for any reason | hypothesis (chance) |
| speaker | retention | unspecified function |
| hearer | forcing (supply, then preservation) | unspecified function |
| meaning | the four response-clauses of `Takes` | definitions |

---

## 11. The center (`Center.lean`)

* `joint_deferral_iff_shared_peaceful`: for two participants, joint deferral is **exactly**
  a shared (same relation) and peaceful (no clash between them) relation to a common
  center. It uses no axioms at all.
* `center_alternatives`: two participants directed at one center either defer jointly,
  or one takes it (an asymmetric relation, the start of hierarchy), or both take it (a clash).

**Limit.** `aim` is generic, so a joint *gaze* also counts. What is proved necessary is *a
shared, unappropriated center*. *Reaching and holding back* follows only under the extra
premise that the participants' directedness is appropriative.

---

## 12. The completion-based system (`Completion.lean`)

Self-contained. **Primitives:** movement forms (with onset-match `opens` and full match
`sim`), "would end in contact with" (`heads`), contact, reach (`within`), first-order
perception, a response window, and an unspecified retention predicate.

**Axioms:** heading requires reach and a movement; completion completes a heading;
perception is of another's actual movement; full match is a tolerance relation that
implies onset match; retention yields a later similar movement. **Kinematics** (an
added axiom, found during formalization): a movement that begins like one that headed for
`o`, made with `o` within reach, also heads for `o`.

**Definitions:**
* directedness = a pending completion (contact with an object, or a match with a movement);
* taking-as by the response principle;
* one notion of center for both kinds of target (ostensive = on an object,
  declarative = on a movement);
* the imperative = taken as about an object that is out of the mover's reach;
* content by lineage (`Descends`).

| Result | Kind |
|---|---|
| `completion_ends_aboutness`, `declarative_unfinished`, `plurality` | definitional |
| `aimless_in_absence`: a movement can't be directed at what is out of reach | derived (axiom 1) |
| `takes_object_within`: taking-as about an object needs a response where the object is | derived (axiom 1) |
| `unreachable_only_acts`: with nothing in reach, only movements can be targets | derived |
| `content_was_present`: whatever a sign stands for was once within someone's reach | derived (induction) |
| `salience`: pure attention to a gesture that descends from a reach for `o` requires `o` to be out of reach | derived (kinematics) |
| `no_recurrence_no_symbol`: without recurrence, no symbolic nodes | derived |
| `emergence`: ostensive, satisfied imperative, pure declarative standing for the absent hammer, non-transitive matching | model |
| `kinematics_needed`: without kinematics, a pure declarative can form with the object present | countermodel |
| `gaze_not_center`: joint looking, within reach, mutually perceived, is not an ostensive | model |

**No longer derivable here:** "every declarative presupposes a failed imperative". A
center can form on *any* earlier movement. What survives is `salience` (pure attention to
a gesture that descends from a reach requires absence) and `content_was_present`.

---

## 13. Direction of fit and the redirected interdiction (`Fit.lean`)

Gans's move: the hearer cannot bring the object, so "bring it" becomes "don't be present",
addressed to the object. This command is already fulfilled, so the declarative is an
imperative obeyed by the world as it is.

| Result | Statement | Kind |
|---|---|---|
| `imperative_unsatisfied_when_made`, `imperative_needs_change` | an imperative is unsatisfied when made; satisfying it requires the object to come into reach (world-to-sign fit) | definitional |
| `declarative_satisfied_when_made` | a pure declarative's "don't be present" is fulfilled when it is made (sign-to-world fit) | derived (kinematics) |
| `fit_needs_kinematics` | without kinematics, a pure declarative can be unfulfilled | countermodel |
| `interdiction_redirected` | ostensive: the object is in reach and the participants refrain. Declarative: the object is out of reach, i.e. it "refrains" | derived |
| `absent_only_through_sign` | an object out of reach can be addressed only by taking up a movement that descends from it (a node) | derived |
| `direction_of_fit` | model: imperative unsatisfied at t2, satisfied at t4; declarative satisfied when made at t6–t7 | model |

The emergence model now has the hammer brought within `a`'s reach at t4.

---

## 14. Falsehood requires drift (`Falsehood.lean`)

Under kinematics, a pure declarative whose gesture begins like a reach for `o` is always
fulfilled when made, so §13's system had no false declaratives.

* **False declarative:** a pure declarative on a movement standing for `o` by lineage,
  made while `o` is within reach (its "don't be present" is unfulfilled).
* **Coherence:** onset-matching survives full matching. Its failure is **drift**.

| Result | Statement |
|---|---|
| `lineage_root` | under coherence, beginning like a movement that descends from `o` means beginning like an earlier reach for `o` |
| `no_falsehood_without_drift` | with coherence and kinematics, **no declarative is false** |
| `false_requires_arbitrary` | a pure movement made with `o` in reach does not begin like any earlier reach for `o`: the sign has become arbitrary |
| `falsehood_from_drift` | a model satisfying all the axioms, kinematics included, where the lineage drifts (r2 ~ r1 ~ r0, not r2 ~ r0), coherence fails, and a declarative standing for the hammer is made with the hammer present |

So **falsehood becomes possible only when the sign has drifted from the reach it came from.**
That is a route to Saussurean arbitrariness: arbitrariness is not the starting point but
the precondition of falsehood.

---

## 15. Firstness (`Completion.lean`, revised)

A center now requires **firstness**: one participant is suspended first, and the other,
having perceived it, is suspended toward the same target **strictly later**, within the
window. No axiom changed; only the definition of the center (and of lineage) did.

| Result | Statement |
|---|---|
| `joint_iff_suspended_taking` | a center is exactly a taking-as whose response is suspended, plus the first participant perceiving that response. The center is no longer a separate notion |
| `center_takes` | in every center the second participant takes the first's movement as being about the target |
| `simultaneous_no_response`, `simultaneous_not_center` | a simultaneous joint stop contains no response and is not a center: coincidence is not a sign |

**Lineage** is now rooted only in the *first* movement of an ostensive (the sign; the
second is its uptake). In the emergence and drift models the t0 center is now sequential:
`a` holds back at t0 and `b` responds at t1. All earlier results still hold.

**Still open:** "in response to" means only "perceived, then a movement within the window",
so two stops that just happen in sequence still count. Registration as genuine dependence
remains to be done.

---

## 16. Dependent response: regularity with contrast (`Completion.lean`, revised)

"In response to" no longer means only "perceived, then a movement within the window". The
ostensive and the declarative now require a **dependent response**:

* **regularity:** another episode, at a different time, in which the first participant makes
  the same kind of movement and the second responds in the same way;
* **contrast:** a time at which the second participant had the opportunity (the object was
  within reach, or the target movement had already happened), the first made no movement of
  that kind, and the second did not respond.

No axiom changed. Retention now does more than make signs persist: without repetition
there is no dependence, so no sign at all.

| Result | Statement |
|---|---|
| `coincidence_not_dependent` | if there is only one episode, the response is not dependent: a one-off coincidence is not a sign |
| `indiscriminate_not_dependent` | if the second participant holds back toward the target whenever it can, regardless of the first, there is no contrast and no sign |

**Models rebuilt:**
* **emergence:** two ostensive episodes (t0–t1, t4–t5) with a contrast (t2–t3); an
  imperative (t6–t8); two declarative episodes on the t10 movement (t11–t12, t15–t16) with
  a contrast (t13–t14);
* **drift:** the same structure; the false declarative is now at t8–t9;
* **no-kinematics:** two declarative episodes with a contrast, all with the hammer present.

Every earlier result still holds. Movement tables are now lists with a lookup function
(`look`); large literal pattern matches made compilation time out.

---

## 17. From the originary declarative to arbitrary grounded graphs (`Graphs.lean`)

**Compound claims.** A claim is one center on two distinct targets at once, with a
dependent response for each. The claim-node is the first participant's movement, with two
"about" arcs. `claim_iff_two_declaratives`: a claim on two movements is exactly two
declaratives made by the same pair of movements, so the claim is generated, not added.

**Co-reach.** `Together t o1 o2`: someone has both objects within reach at `t`. It is defined
from reach; there is no new primitive. A claim's truth condition is "not together": the
originary "don't be present [with us]" with its second term made explicit.

| Result | Statement |
|---|---|
| `claim_iff_two_declaratives` | a claim on two movements = two declaratives made by the same movements |
| `claim_grounded` | whatever a claim is about was once within someone's reach |
| `universality` | for any `n` objects, any loop-free graph `G` on them and any arrangement `H` of which pairs are together, there is a history satisfying every axiom (kinematics included) in which every object has a grounded sign, every edge of `G` is a claim with arcs to exactly its endpoints' signs, each claim is true iff its objects are not together in `H`, and **there are no other claims** |
| `Univ.displaced` | at claim time neither speaker has any object within reach: the truth and falsehood are about elsewhere |
| example | three objects, claims "0 — 1" (false: they are together) and "1 — 2" (true) |

The construction gives each object an 8-step block (two ostensive episodes with a contrast,
then a sign made out of reach) and each edge an 8-step block (two claim episodes with a
contrast). Witness participants supply the arrangement `H`.

**Notes.**
* Claim forms begin like the signs they combine but not like the reaches those signs descend
  from, so coherence fails, as `Falsehood.lean` says it must for a claim to be false.
* Polarity is negative ("not together"). Since any graph's complement is also a graph,
  this costs no expressive power, but positive predication is not yet generated.
* Relations are symmetric co-reach only. Relations with roles ("on top of") are not yet generated.

---

## 18. Roles require order (`Roles.lean`)

A **reading** of claims assigns a proposition to each claim event. It is **faithful** to a
relation `R` if every claim about `o1, o2` is read as `R o1 o2`.

| Result | Statement |
|---|---|
| `claim_symm` | an (unordered) claim on two targets is the same event read either way round |
| `unordered_only_symmetric` | any faithful reading of unordered claims expresses a symmetric relation on every claimed pair |
| `no_asymmetric_unordered` | if a claimed pair stands in `R` one way but not the other, `R` has no faithful unordered reading |
| `Succ`, `succ_asymm` | **succession** (every presence of `o1` precedes every presence of `o2`): a relation with roles, defined from reach and time, and asymmetric |
| `succession_not_unordered` | in a concrete world (the universal construction: two objects, one edge), succession has no faithful unordered reading |
| `OClaim` | an **ordered claim**: a center on the first target, then a center on the second (firstness inside the claim) |
| `ordered_faithful` | if ordered claims determine what they are about, *every* relation, asymmetric ones included, has a faithful ordered reading |
| `succession_ordered` | in the `Ord` model (all axioms, kinematics included), succession has a faithful ordered reading under which "A then B" is true and "B then A" is false |
| `Ord.order_matters` | the claim at t16 is not the same claim with its targets swapped |

**Scope.** What is proved is that **some internal asymmetry is required** (unordered claims
cannot carry roles) and that **temporal order suffices**. That time is the *only* source of
order is argued from the primitives, not proved against every conceivable mechanism:
directedness has no role labels, so within one movement nothing distinguishes two targets.
Form-marking (case) would need a further primitive or a drifted contrast.

The `Ord` model also isolates the semantic role of form: a sign's object is fixed by its form
through lineage (`descends_obj`), and a held-back mark's target is fixed by its form
(`target_obj`), which is why ordered claims determine what they are about (`uniq`).

---

## 19. Polarity: the positive as the negation of a negation (`Polarity.lean`)

**One rule, applied recursively.** A center on something says "not that". A claim (a center on
two signs) says "not together". A center on a movement that says φ says "not φ". So a
center on a claim says "not (not together)", whose truth condition is "together".
Nothing new is added.

**Assertion.** A saying is *embedded* if a later center takes a movement of the same kind as
its target, and *asserted* otherwise. The claim inside "not (not together)" is embedded, so it
is not asserted.

| Result | Statement |
|---|---|
| `says_neg` | everything said is a negation: the originary "don't" is always outermost |
| `affirm` | a center on a claim says "not (not together)", which holds exactly when the objects are together |
| `no_contradiction` | a formula and its negation are never both true |
| `Univ2.says_inv` | in the construction, everything said is a claim on a listed pair or a denial of one |
| `partial_universality` | for any pairs `D` to deny, `A` to affirm (disjoint) and arrangement `H`, there is a history satisfying every axiom (kinematics included) in which exactly the pairs in `D` are asserted "not together" and exactly those in `A` are asserted "not (not together)", each true iff the arrangement agrees. Every other pair is **unsaid** |

This removes the closed-world assumption: affirmed, denied and unsaid are three distinct
states, so partial knowledge can be stated accurately. A pair may also be denied one way
round and affirmed the other (`(i, j) ∈ D`, `(j, i) ∈ A`), which represents a contradiction
between assertions; exactly one of them is true.

**Note on markedness.** Here the positive is the more complex form (two layers). Natural
languages mark negation instead. A bleaching story (the first-layer "not", always present,
stops being heard) could reconcile the two; that is a hypothesis, not a theorem.
