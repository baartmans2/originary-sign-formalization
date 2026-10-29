# Verifying the whitepaper

The whitepaper (`paper/whitepaper.tex`) is a work in progress. Parts of it were drafted
with AI assistance, and these parts must be checked against their sources before they
can be relied on.

## Convention

- **Cited** means the claim was checked against the source, at least at the level of the
  publisher's description, an abstract, or a review that reports its content.
- **Unverified** means the claim looks roughly right, but no one has yet checked it
  against the actual passage. Such a claim carries **no citation**. Instead it is marked
  with `\unverified{...}`, which prints an orange note in the margin saying what to look
  for.

To list every open item, run:

```bash
grep -n unverified paper/whitepaper.tex
```

To resolve an item:

1. Find the passage in the source.
2. Replace the `\unverified{...}` note with a proper `\cite{...}`, with a page or
   paragraph number where possible.
3. Add the source to the bibliography, if it isn't there already.
4. If the claim turns out to be wrong, correct or remove it.

## Open items in Section 1

| Claim | What is needed |
|---|---|
| Thought-priority objection to intention-based accounts | A citation. A candidate is Devitt, "Three Mistakes About Semantic Intentions". |
| The role of the dominance hierarchy in Gans's scene | The passage in Gans 1981 or 1993. |
| Imperative from the "inappropriate ostensive"; declarative from the negative ostensive | Check against Gans 1981; so far confirmed only through commentary. |
| Katz on the centre | Read Katz, "Generative Anthropology as the One Big Discipline", *Anthropoetics* XXIV, no. 2 (2019), or another source. |
| The sparagmos as discharge of deferred tension onto the object | A citable source; the *Anthropoetics* page used so far has an unconfirmed author. |
| Gans accepts the mimetic crisis but rejects the scapegoat mechanism as sufficient, and includes the sparagmos to incorporate Girard | A primary or scholarly source; so far confirmed only through an encyclopedia entry. |
| Sackeroff, "The Ends of Deferral" | Confirm the issue, *Anthropoetics* XX, no. 2; inferred from the URL. |
| Hawk–Dove: mutual restraint is not stable | The right citation; probably Maynard Smith, *Evolution and the Theory of Games* (1982). |
| Saussure's definition of the sign and of value | A citation to the *Course in General Linguistics*, with page. |
| Truth and falsity as a property of the end state | Possibly Hockett and Altmann on "prevarication"; check. |
| Declarative-first and other orderings | Name proponents, or rephrase as the author's conjecture. |

## Bibliography details to confirm

- Hockett 1960, "The origin of speech", *Scientific American*: volume, issue and pages.
- Peirce, *Collected Papers* 2.228: wording checked only against a secondary copy at
  cspeirce.com; confirm against the edition, and add the volume's editors and year.
- Morris 1938: series volume and number in the *International Encyclopedia of Unified
  Science*.
- Alexander, Skyrms and Zabell 2012: volume and pages.
- Lyons 1991: chapter pages, and the exact wording of the 1866 statute.
