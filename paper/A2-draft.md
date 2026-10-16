# The laws of counting: one criterion, two criteria, and a test

*Draft A2, October 2026. Not for circulation. Every theorem cited is
proved in Lean 4 in `EndToEnd/Encodings/` of this repository and checked
by CI (Appendix A). Statements marked **(argued, not formalized)** have
a proof in this text only. Statements marked **(reported)** are taken
from sources we have not been able to read. Literature claims are from
sources read for this project (`paper/A-literature.md`) unless marked
"not read".*

*Companion to Draft A1 (`paper/A1-draft.md`), whose full abstraction
theorem motivates this paper. A2 is written to stand alone: §2 restates
what it needs from A1.*

---

## Abstract

What sentences can observe of a count noun is its *counting function*:
for each property P, how many of the noun's things are P. We study these
functions directly. Our results:

1. **Representation.** The counting functions of nouns with one
   identity criterion are exactly the integer *coverage functions*, and
   each has unique units.
2. **Typology.** Two laws stated purely in terms of counts sort such
   nouns into four kinds. *Additivity* holds iff the noun never merges
   individuals; *singleness* holds iff it never splits one. Both hold
   iff the noun is a Montague noun. Never splitting is exactly the
   disjointness condition of Rothstein (2017) and Landman (2020).
3. **Submodularity.** All one-criterion counts satisfy count(P ∪ Q) +
   count(P ∩ Q) ≤ count(P) + count(Q). Copredicated counting by two
   criteria ("double distinctness") can break it.
4. **The structure of two criteria.** Counting by two criteria is
   exactly the least of a family of mixed single-criterion counts (by
   König's theorem). The class of such functions lies strictly between
   coverage functions and minima of coverage functions. It obeys
   subadditivity, a pairwise law, a claw law and an odd-cycle law for
   every odd length. The first two do not characterize it.
5. **An exact characterization.** When each individual is one thing,
   five laws characterize two-criteria counting exactly: singles, pair
   determination, the claw law, a diamond law and the odd-cycle laws.
   The proof is self-contained and machine-checked; it does not use the
   graph-theoretic results we could not check. The claw law is
   independent of the other four.
6. **A test.** Because submodularity holds for every one-criterion
   account at once, it gives a test of double distinctness that does
   not depend on which one-criterion account is right. We relate the
   test to the current debate (Gotham; Liebesman & Magidor; Sutton) and
   give a protocol, not yet run. The protocol must test each speaker in
   a fixed context, and its scenario must contain an anthology.

---

## 1. Introduction

### 1.1 From encodings to counting functions

Paper A1 shows that, for a fragment of English, whether nouns are types
or predicates makes no inferential difference once identity criteria
are accounted for. It also proves a full abstraction theorem: what
every sentence, in every context, can observe of a noun is its
multiset of *counting units*, equivalently its counting function. So
theories of individuation (types with criteria, setoids, predicates
with criteria, counting contexts, bases) differ observably only
through the counting functions they assign to nouns.

This paper asks which functions those are, and what laws they obey.
Laws of counting are what the theories predict about speakers'
judgments, independently of how each theory writes its meanings down.

### 1.2 Why this matters for copredication

"John picked up and mastered three books" is the central example of the
debate on copredication and counting.

- **Double distinctness.** Gotham (2017), Chatzikyriakidis & Luo (2015,
  2018) and Bahramian, Nematollahi & Sabry (2017) give it truth
  conditions requiring three books pairwise distinct both physically and
  informationally.
- **Property Versatility.** Liebesman & Magidor (2017, 2026) deny that
  the sentence has such a reading. On their account 'book' ranges, by
  contextual restriction, over physical or over informational books,
  and counting is ordinary.
- **QUD.** Sutton (2024) argues that double distinctness arises in
  neutral contexts and is suppressed when a more prominent question
  under discussion makes a modifier restrict the domain instead.

The disagreement is about judgments on single sentences in particular
scenarios, and those judgments are contested (Liebesman & Magidor 2026,
n. 38). We show that the accounts differ in a *law*, not just in
single counts. Every one-criterion account, whichever it is, makes the
counting function submodular, and double distinctness need not be. That
turns a dispute about intuitions into a question with a decidable
answer from a speaker's pattern of answers.

### 1.3 Contributions

| result | where |
|---|---|
| one-criterion counts = integer coverage functions, unique units | §3, `representation`, `units_unique` |
| additive ⟺ never merges; single ⟺ never splits; both ⟺ Montague | §4, `additive_iff`, `single_iff`, `montague_iff` |
| never splits ⟺ units pairwise disjoint (Rothstein, Landman) | §5, `noSplit_iff_disjoint` |
| submodularity of every one-criterion count | §6, `count_submod` |
| two criteria = least mixed single criterion (König) | §7, `count2_eq_min`, `copredication_is_min` |
| no single criterion yields some two-criteria counts | §7.4, `not_single` |
| coverage ⊊ two criteria ⊊ minima of coverage | §8, `isMinCov_of_isCount2`, `not_subadd_example`, `not_pairwise_example` |
| laws of two-criteria counts (subadditive, pairwise, claw, odd cycles of every length); the first two insufficient | §8, `count2_subadd`, `count2_pairwise`, `count2_claw`, `count2_oddCycle`, `two_laws_not_sufficient` |
| exact characterization with one thing per individual; the claw law independent | §9, `isCount2Self_iff`, `claw_independent` |
| the debate restated as hypotheses about laws | §10 |
| a protocol | §11 |

### 1.4 What is not claimed

- That double distinctness is the meaning of copredicated numerals.
  That is the hypothesis under test.
- That the fragment covers mass nouns, measure phrases, classifiers,
  or contextual shifts of criterion within a sentence.
- An exact characterization of two-criteria counting functions when
  individuals can own several things. It is open; the case of one thing
  per individual is settled (Theorem 9.2).
- Any experimental result. None has been run.

---

## 2. Setting

We restate what is needed from A1 (§11 there).

**Nouns with one criterion.** Fix a finite set A of individuals. A noun
is interpreted (`NounI`) by:

- a finite type T of its *things*;
- an embedding emb : T → A, which says which individual each thing is;
- a criterion crit : T → K, which says when two things count as one.

**Counting.** For P ⊆ A, count(P) is the number of distinct criterion
values among the things whose individual is in P (`NounI.count`):

> count(P) = |{crit(y) : y ∈ T, emb(y) ∈ P}|.

**Units.** Each criterion value k is a *unit*, covering the set
unit(k) = {emb(y) : crit(y) = k} of individuals (`NounI.unit`).
u(S) is the number of units covering exactly S (`NounI.units`). Then
(`count_meets`)

> count(P) = Σ_S u(S) · [S ∩ P ≠ ∅].

**Examples.**

| noun | things | individuals | criterion | units |
|---|---|---|---|---|
| "person" | people | people | identity | one singleton per person |
| "passenger" | journeys | people | journey | one unit {j} per journey of person j: three journeys, three units covering j |
| "book", counted as texts, two copies | copies | copies | text | one unit covering both copies |
| "book", counted as texts, two anthologies each holding texts X and Y | (volume, text) pairs | volumes | text | two units, each covering both volumes |

**Full abstraction** (A1, Theorem 11.1; `obsEq_iff`). Two
interpretations of a noun are indistinguishable by every sentence of
the fragment, in every context, iff they have the same units u. With
plurals (`obsEqP_iff`) and possible-worlds intensionality
(`obsEqW_iff`) this is unchanged. So the counting function, or
equivalently u, is all that sentences see.

**Nouns with several criteria.** A noun may have a nonempty family of
criteria (`NounM`). Then count(P) is the size of a largest set of
things over P that are pairwise distinct under *every* criterion
(`NounM.count`). With two criteria c1 (volume) and c2 (text), this is
`count2 c1 c2` (`TwoCriteria.count2`): the largest set of books no two
sharing a volume and no two sharing a text. Two interpretations of such
a noun are indistinguishable iff they have the same counting function
(`obsEqM_iff`).

---

## 3. Representation: count nouns are coverage functions

**Theorem 3.1 (`representation`).** A function f from properties of A
to ℕ is the counting function of some noun with one criterion iff
there is u : 𝒫(A) → ℕ with u(∅) = 0 and

> f(P) = Σ_S u(S) · [S ∩ P ≠ ∅] for all P.

**Theorem 3.2 (`units_unique`, `units_ofUnits`).** That u is unique,
and it is the noun's units.

*Proof.*

- (⇒) Take u to be the noun's units (`count_meets`).
- (⇐) Given u, build the noun `ofUnits u`. Its things are triples
  (S, i, x) with i < u(S) and x ∈ S, it embeds (S, i, x) to x, and its
  criterion is (S, i). Then it has u(S) units covering each S
  (`count_ofUnits`).
- Uniqueness (`eq_of_meets`): the counts of the sets that avoid S
  determine Σ_{R ⊆ S} u(R), and u(S) follows by strong induction
  on S. ∎

**Coverage functions.** In combinatorics, a function f(T) = w(∪_{i∈T}
A_i), the total weight of a union of sets, is a *coverage function*.
Equivalently f(P) = Σ_S w(S)·[S meets P] with w ≥ 0, where w is the
W-transform of f. Chakrabarty & Huang (2012; journal version 2015)
characterize coverage functions as those whose W-coefficients are
nonnegative, and the coefficients are unique (**reported**: from the
abstract and search results, as the paper could not be fetched here).

So Theorem 3.1 identifies count nouns with one criterion with the
*integer-valued* coverage functions, and Theorem 3.2 is their
uniqueness, reproved. What is new is the identification, and the
typology built on it below. No linguistic use of coverage, belief or
submodular functions for counting was found in a search, or in
Rothstein (2017) or Landman (2020).

**Reading.** A count noun with one criterion *is* a multiset of
nonempty sets of individuals: its units. Every account of one-criterion
individuation (types with criteria, setoids, predicates with criteria
over a richer domain, counting contexts, bases) is a way of presenting
such a multiset.

---

## 4. A typology by laws

### 4.1 Two laws

Both laws are stated in terms of counts alone.

- **Additive** (`Additive`): count(P ∪ Q) + count(P ∩ Q) = count(P) +
  count(Q), for all P, Q.
- **Single** (`Single`): count({x}) ≤ 1 for every individual x: no
  individual counts more than once.

### 4.2 Two structural properties

- **Never merges** (`NoMerge`): things counted as one are one
  individual. crit(y) = crit(y') → emb(y) = emb(y').
- **Never splits** (`NoSplit`): things that are one individual count as
  one. emb(y) = emb(y') → crit(y) = crit(y').

**Theorem 4.1 (`additive_iff`).** A noun is additive iff it never
merges.

**Theorem 4.2 (`single_iff`).** A noun is single iff it never splits.

*Proof sketches.*

- Never merging means every unit is a singleton. Counting is then
  counting individuals with multiplicity, and inclusion-exclusion is
  exact. Conversely, a unit covering two individuals x ≠ x' makes
  count({x}) + count({x'}) exceed count({x, x'}) + count(∅).
- Splitting means two units cover a common individual x, so
  count({x}) ≥ 2. ∎

### 4.3 The four kinds

**Theorem 4.3 (`cells_inhabited`).** With two distinct individuals,
every combination occurs, so the laws are independent.

| | never splits | splits |
|---|---|---|
| **never merges** | Montague nouns (count individuals) | passengers: one person, two journeys (`passengers`) |
| **merges** | copies counted as texts (`copies`) | anthologies counted as texts: two volumes, each holding the same two texts (`anthologies`) |

**Theorem 4.4 (`montague_iff`, `montague_obsEq`).** A noun obeys both
laws iff it counts as its extension does, iff it is indistinguishable
by every sentence from counting individuals. This is A1's
characterization theorem (`CModel.agree_iff_kernel`) restated as laws:
Luo's passengers and Gotham's books are the two ways to break them.

---

## 5. Disjointness: Rothstein, Landman, and the constraint on double counting

**Theorem 5.1 (`noSplit_iff_disjoint`).** A noun never splits iff its
units are pairwise disjoint.

With Theorem 4.2, the observable law count({x}) ≤ 1 is the same as
pairwise disjoint units.

### 5.1 Rothstein

Rothstein (2017, ch. 4) makes counting relative to a context k of
disjoint atoms:

- COUNT_k(N_root) = {⟨a, k⟩ : a ∈ N_root ∩ k} (36);
- "contextual disjointness is a condition on k" (p. 109);
- a numeral counts the k-atoms below a plurality, |π1(x)|_k = 3 (41,
  p. 112);
- what counts as one is context-dependent: four farmers' fencing is
  one, two or four fences (32, pp. 107-108).

Our criterion plays the role of her k, held fixed. Her disjointness is
never splitting. She does not discuss identity criteria in Geach's
sense, copredication or dot types; we searched the whole book.

### 5.2 Landman

Landman (2020) interprets an NP as an i-set ⟨body, base⟩, where the
base generates the body under sum (§5.1, p. 143).

- **Counting.** card_Z(x) = |(x] ∩ Z| "if Z is disjoint", undefined
  otherwise (§5.2, p. 144).
- **Count, neat, mass.** X is count iff base(X) is disjoint. It is neat
  iff base(X) is atomistic and its base-atoms are disjoint
  (§6.1.2, pp. 165-166). Mass is the rest.
- **The minimal assumption.** "The assumption of a disjoint base ... is
  the minimal assumption we have to make" (p. 160).

In our terms, base elements are units and card_Z is count. A disjoint
base is never splitting. A base element can be a sum of individuals
(his pottery example's teaset, p. 190), which is merging. So Landman's
count nouns are the never-splits column of the typology, with base
atoms as individuals.

Landman's neat mass nouns have overlapping bases. For counting and
count comparison, they use a disjoint set stuk_w(P) chosen in context
(§7.4.2, p. 208). For *pottery* there are three "maximally disjoint
subsets of base(POTTERY_w)" that are "naturally available" (p. 209):
the four pieces, {teapot, cup and saucer, fruit bowl}, and {teaset,
fruit bowl}. "Most pottery costs more than 5 euros" changes truth value
with that choice (p. 216). So a neat mass noun is a *family* of
never-splitting criteria, with *one member chosen per context*.

**Disjointness is an imperative.** Landman (§6.1.4, pp. 169-172) treats
disjointness as a default. Overlap is removed first by contextual
restriction, which is "pervasive" (p. 171), then by "pragmagic". His
§11.3 (pp. 350-361) describes two pragmagic repairs:

- *doppelgänger* (pp. 351-354), a local repair: two roads sharing a
  stretch are counted as two by pretending the shared part is two
  indiscernible parts;
- *indexing* (pp. 354-361), a global repair: each listed item gets its
  own index, and the indices are counted.

Indexing "is used precisely when we want to allow double counting"
(p. 358). It is what Rothstein and Mountain semantics build into every
count noun (p. 355), and it "comes with a processing cost" when it
changes lexical meanings (p. 360). His evidence is introspective:
"The Bordurians and the Szohôdians are two groups of Europeans" is
degraded when Szohôd is in Borduria (pp. 358-359), and counting cubes
that include sub-cubes needs pen and paper (p. 360). In our terms,
indexing makes overlapping items into disjoint atoms. That is the
Montague cell applied to a richer domain, which A1's translation
theorem says always exists.

### 5.3 Liebesman & Magidor's constraint on double counting

Liebesman & Magidor (2017, p. 4 of the version read) observe that
"Four colours are on the canvas" (three shades of red, and red) and
"Six wooden things are in the room" have no true reading. Their
explanation: "counting both a determinable and its determinate is ruled
out due to some restriction on double counting, as is counting both an
object and its parts". They leave open "what the content of the
constraint is" and "how it can be overridden" (n. 5). Their constraint
is the informal counterpart of never splitting. Theorem 4.2 says what
dropping it means observably, and Landman's indexing says what it
costs.

### 5.4 What none of them does

None of Rothstein, Landman or Liebesman & Magidor takes the *least*
count over a family of criteria. That is what double distinctness
amounts to (§7). Landman's neat mass nouns come closest: a family of
disjoint criteria, but with one *chosen* per context, not a minimum
taken over all of them.

---

## 6. Submodularity

**Theorem 6.1 (`count_submod`).** For every noun with one criterion and
all P, Q:

> count(P ∪ Q) + count(P ∩ Q) ≤ count(P) + count(Q).

*Proof.* count(P) is the size of img(P), the set of criterion values of
things over P. img(P ∪ Q) = img(P) ∪ img(Q) and img(P ∩ Q) ⊆ img(P) ∩
img(Q) (`img_or`, `img_and`). Inclusion-exclusion gives the inequality.
∎

Equality for all P, Q is additivity (§4), so submodularity is the part
of additivity that survives merging and splitting. Coverage functions
are submodular in general; Theorem 6.1 is that fact for integer ones.
It is what makes the law a test (§11): it holds for every one-criterion
noun, whatever the units.

---

## 7. Two criteria

### 7.1 Counting by two criteria

Let things have two criteria c1 : T → K1 (volume) and c2 : T → K2
(text). count2(Q) is the size of a largest set of Q-things that is
injective in c1 and in c2 (`count2`, `le_count2_iff`). Picture a
bipartite multigraph with volumes on one side and texts on the other,
and each book an edge from its volume to its text. Then count2 is the
size of a largest *matching* among the Q-edges.

This equals the count of A1's several-criteria semantics
(`countF_eq_count2`), which is Gotham's (2017) non-compressibility by
PHYS and INFO, and Chatzikyriakidis & Luo's (2018) `Three` over a
dot-setoid (A1, §13).

### 7.2 Mixed criteria

Choose a set S of texts. Count a thing by its *volume* if its text is
in S, and by its *text* otherwise (`mix c1 c2 S`). That is a single
criterion, with values in K2 ⊕ K1.

**Theorem 7.1 (`count2_le_mix`).** Every mixed criterion counts at least
as many: count2(Q) ≤ count_mix(S)(Q) for every S.

*Proof.* Things pairwise distinct in volume and in text are pairwise
distinct under any mixture. ∎

**Theorem 7.2 (`exists_mix_le`).** Some mixed criterion counts exactly
as many.

*Proof.* This is König's theorem, proved here from Hall's marriage
theorem in Mathlib. Take a set S₀ of texts of largest *deficiency*:
|S₀| minus the number of volumes holding them. Hall's condition then
holds for matching every text into its volumes plus deficiency-many
dummy volumes. The resulting matching has the size of the mixed count
for S₀. ∎

**Theorem 7.3 (`count2_eq_min`).** count2(Q) = min_S count_mix(S)(Q).

A mixed count is the size of a particular kind of *vertex cover*: the
volumes of the books whose text is in S, together with the texts not in
S. Theorem 7.3 is "maximum matching = minimum vertex cover" in this
form.

**Theorem 7.4 (`copredication_is_min`).** A noun with two criteria
counts as the pointwise least of the family of one-criterion nouns
(`mixNoun`) with the same things and embedding, one per S. The
minimizing S depends on the property counted.

By Theorem 3.1, each member of the family is a coverage function. So
**counting by two criteria is a minimum of coverage functions**
(`isMinCov_of_isCount2`).

### 7.3 Worked example

Three books: A = *Emma* in volume 1; B = *Emma* and C = *Persuasion*,
both in volume 2.

| S (texts counted by volume) | A | B | C | count of {A, B} | of {B, C} | of {A, B, C} | of {B} |
|---|---|---|---|---|---|---|---|
| ∅ (all by text) | Emma | Emma | Persuasion | **1** | 2 | **2** | **1** |
| {Emma} | vol 1 | vol 2 | Persuasion | 2 | 2 | 3 | 1 |
| {Persuasion} | Emma | Emma | vol 2 | **1** | 2 | **2** | **1** |
| {Emma, Persuasion} (all by volume) | vol 1 | vol 2 | vol 2 | 2 | **1** | **2** | **1** |
| **count2 = minimum** | | | | **1** | **1** | **2** | **1** |

The minimum for {A, B} is attained by counting by text, and the minimum
for {B, C} by counting by volume. No single row attains all four
minima. That is why the double-distinctness counts are not a
one-criterion count.

### 7.4 Not one criterion

**Theorem 7.5 (`not_single`, A1 Theorem 11.5).** The counting function
of §7.3 is indistinguishable from no noun with one criterion. It gives
count({A, B, C}) + count({B}) = 3 > 2 = count({A, B}) + count({B, C}),
which breaks Theorem 6.1. The individual facts are `books_union`,
`books_inter`, `books_01` and `books_12`.

### 7.5 What the counts hide

**Theorem 7.6 (`criteria_hidden`).** The counting function does not fix
what each criterion does alone. Two things at one individual, alike by
one criterion and distinct by the other, are indistinguishable from
one thing there. Only a fragment in which quantifiers count by
separately chosen criteria (A1, §8.3) sees the criteria separately.

### 7.6 The anthology is unavoidable

**Proposition 7.7.** If every volume holds one text, then double
distinctness is counting by text, a single criterion. Likewise if every
text has one copy, it is counting by volume.

*Proof.* If same volume implies same text, then "same volume or same
text" is "same text". It is transitive (`dotSame_trans_of`), so double
distinctness is counting by one equivalence relation
(`exists_setoid_iff`). The second case is symmetric (**argued, not
formalized**). ∎

So no scenario separates double distinctness from one criterion unless
it has both a text with two copies and a volume with two texts. This
constrains every test (§11).

---

## 8. The class of two-criteria counting functions

Let *IsCount2(f)* mean that f is the counting function of some noun
with two criteria. There must be a finite type of things T, an
embedding emb : T → A and criteria c1, c2 with f(P) = count2 over the
things whose individual is in P (`IsCount2`). Let *IsMinCov(f)* mean f
is the pointwise least of some family of integer coverage functions,
attained at every P (`IsMinCov`).

### 8.1 A strict hierarchy

> coverage (one criterion) ⊊ IsCount2 ⊊ IsMinCov.

- **First inclusion, strict.** One criterion is two equal criteria. The
  counting function of §7.3 is in IsCount2 and is not a coverage
  function (Theorem 7.5).
- **Second inclusion** (`isMinCov_of_isCount2`): by Theorem 7.4.
- **Second inclusion strict, twice:**
  - `not_subadd_example`. Take two individuals a and b. The minimum of
    "units meeting {a}" and "units meeting {b}" is 0 on each singleton
    and 1 on both. It is not subadditive, so not in IsCount2.
  - `not_pairwise_example`. Take three individuals. For each one,
    there is a coverage function with one unit covering the other two
    and one unit covering it. The minimum of the three, f3, is 1 on
    every pair and 2 on all three. It is subadditive (`f3_subadd`), so
    the failure is not only subadditivity. It breaks the pairwise law
    below.

### 8.2 Three laws

**Theorem 8.1 (subadditivity; `count2_subadd`, `IsCount2.subadd`).**
count2(P ∪ Q) ≤ count2(P) + count2(Q).

**Theorem 8.2 (pairwise law; `count2_pairwise`, `IsCount2.pairwise`).**
If count2(P ∪ Q), count2(Q ∪ R) and count2(P ∪ R) are each at most 1,
then so is count2(P ∪ Q ∪ R).

*Proof.* Two things distinct both ways would lie together in one of the
three unions. ∎

**Theorem 8.3 (odd-cycle law; `count2_cycle5`, `IsCount2.cycle5`).**
Let x₀, …, x₄ be five individuals in a cycle, each counted at least
once. Suppose every two neighbours count at most one together:
count2({x_i, x_{i+1}}) ≤ 1. Then some two non-neighbours also count at
most one together: count2({x_i, x_{i+2}}) ≤ 1 for some i.

*Proof.*

- *Hub lemma* (`hub_of_pairwise`, `le_one_iff_pairwise`). Things that
  pairwise share a volume or a text all share one volume or all share
  one text: a *hub*.
- Each individual's things lie on the hubs of both its pairs. So
  consecutive hubs are either equal or of different kinds (one a
  volume, one a text).
- Around an odd cycle the kinds cannot always alternate
  (`no_alternation`). So two consecutive hubs are equal, and the
  individuals at distance two through that hub count at most one
  together. ∎

**Theorem 8.3′ (odd-cycle laws of every length; `count2_oddCycle`,
`ForbiddenLaws.IsCount2.oddCycle`).** The same holds for 2m + 1
individuals in a cycle indexed by ZMod(2m + 1), for every m. If each is
counted at least once and every two neighbours count at most one
together, then for some i, the individuals i and i + 2 count at most
one together. The proof is the one above. If no two consecutive hubs
are equal, their kinds alternate, so after 2k steps a hub has the kind
it started with, and after 2m + 1 steps the opposite kind. That is
impossible, since step 2m + 1 returns to the start. For m = 1 the
conclusion concerns neighbours and is immediate. Even cycles have no
such law. In an even cycle of books whose neighbours share, in turn, a
volume and a text (b0 and b1 a volume, b1 and b2 a text, and so on),
the hypothesis holds, but every two books two apart count as two.

**Theorem 8.5 (the claw law; `count2_claw`, `ForbiddenLaws.IsCount2.claw`).**
Let X have something counted. If X counts at most one together with
each of Y, Z and W, then two of Y, Z, W count at most one together.

*Proof.* Each of X ∪ Y, X ∪ Z, X ∪ W has a hub, and all three pass
through one thing x of X. Two hubs through one thing are equal or of
different kinds, since a thing has one volume and one text
(`hub_step`). Of three hubs, two have the same kind, so they are equal,
and the corresponding two sets lie on one hub. ∎

The claw law holds when individuals own several things, not only for
one thing per individual.

### 8.3 The two laws are not sufficient

**Theorem 8.4 (`two_laws_not_sufficient`).** Let f5(P) be the size of a
largest subset of P ∩ {0, …, 4} with no two cyclic neighbours. Then:

- f5 is in IsMinCov. It is the minimum of five coverage functions, one
  per rotation r, each with a unit covering {r, r+1, r+4} and a unit
  covering {r+2, r+3, r+4} (`f5_isMinCov`).
- f5 is subadditive (`f5_subadd`) and obeys the pairwise law
  (`f5_pairwise`).
- f5 breaks the odd-cycle law, so it is not in IsCount2.

So the class IsCount2 is not characterized by subadditivity and the
pairwise law. Whether it has a finite set of laws characterizing it in
general is open (§9).

---

## 9. A graph-theoretic reading

This section separates what is proved, what is argued here, and what
is reported.

### 9.1 Matchings and line graphs (argued, not formalized)

Take the bipartite multigraph of §7.1: volumes and texts are vertices,
and things are edges. count2 of a set of things is the size of a
largest matching among them.

**One thing per individual.** Suppose emb is a bijection. Let H be the
*conflict graph* on things, with two things adjacent iff they share a
volume or a text. H is the line graph of the multigraph. Then count2(P)
is α(H[P]), the size of a largest set of pairwise non-adjacent vertices
of H inside P.

Conversely, every line graph of a bipartite multigraph arises this way,
with its two sides as the two criteria. Hence:

**Proposition 9.1.** With one thing per individual, f is in IsCount2
iff:

- **(a)** f is the independence number of the graph f defines on pairs
  (x, y adjacent iff f({x, y}) = 1, with f({x}) = 1 for each x),
  restricted to each P; and
- **(b)** that graph is the line graph of a bipartite multigraph.

### 9.2 Matching the laws to forbidden subgraphs (laws formalized; the correspondence argued)

- **The pairwise law is part of (a), not a forbidden subgraph.** A set
  whose pairs all count 1 is a clique, and α of a clique is 1, in every
  graph.
- **The odd-cycle laws exclude odd holes.** The odd-cycle law of
  length 2m + 1 (Theorem 8.3′, formalized for every m) excludes an
  induced odd cycle of that length. Indeed f5 is α of the 5-cycle.
- **The claw law excludes claws** (Theorem 8.5, formalized). Suppose a
  thing conflicts with three others. Then two of those three conflict
  with each other: by pigeonhole, two of them meet it at the same end
  (its volume or its text). So line graphs of bipartite multigraphs are
  claw-free.
- **Diamonds do occur**, from two copies of one text bound in one
  volume (parallel edges). Call two adjacent vertices *twins* if they
  have the same other neighbours. In the line graph of a bipartite
  multigraph, twins are either:
  - parallel edges; or
  - two edges uv and uw where every edge at v is parallel to uv and
    every edge at w is parallel to uw. An edge at v must meet uw, and v
    and w are on the same side.

  Merging each class of twins into one vertex gives the line graph of a
  *simple* bipartite graph. Conversely, blowing a vertex up into twins
  adds parallel edges. So (b) is equivalent to:

  **(b′)** after merging twins, the graph is the line graph of a simple
  bipartite graph.

### 9.3 What is reported, and what would follow

- **Reported (to check).** The line graphs of simple bipartite graphs
  are exactly the graphs with no claw, no diamond and no odd hole. This
  was attributed to Harary & Holzmann (1974), which we have not seen.
  A secondary source found by search attributes to them the
  characterization of line graphs of *triangle-free* graphs as the
  claw-free and diamond-free graphs. Adding "no odd hole" for bipartite
  graphs then follows by a short argument (**argued**). A shortest odd
  cycle of length ≥ 5 is chordless, so its edges induce an odd hole in
  the line graph. Conversely, an odd hole in the line graph gives an
  odd cycle.
- **Standard.** Line graphs of bipartite graphs are perfect (König's
  edge-colouring theorem).
- **Reported.** Trotter (1977), as summarized by search results: a
  graph is "line perfect" (its line graph is perfect) iff it has no odd
  cycle longer than 3. de Werra (1978) exists; its content was not
  found.

**Theorem 9.2 (characterization, one thing per individual;
`Count2Laws.isCount2Self_iff`).** Write pairLe(x, y) for f({x, y}) ≤ 1.
A function f counts individuals by two criteria (f = count2 c1 c2 for
some c1, c2 on the individuals) iff it obeys five laws:

1. **singles:** f({x}) = 1 for every x;
2. **pair determination:** f(P) is the size of a largest subset of P
   no two of whose members satisfy pairLe (`pairCount`);
3. **the claw law**, for individuals;
4. **the diamond law:** if pairLe(x, y), each of z and w is pairLe with
   both x and y, and not pairLe(z, w), then x and y are twins: for every
   u, pairLe(u, x) iff pairLe(u, y);
5. **the odd-cycle laws of every odd length**, for individuals.

The theorem is proved in full and does not rely on the reported
graph-theoretic result above. Its proof (`union_of_two_general`)
constructs the two criteria directly:

- **Twins.** Merge individuals that are pairLe with exactly the same
  individuals (`twinSetoid`). After merging, the diamond law says that
  the common neighbours of two distinct related individuals are
  pairwise related.
- **Lines.** A *line* is such a set of common neighbours (`IsLine`). A
  line is the line of any two of its distinct members
  (`line_common`), and two lines sharing two individuals are equal
  (`line_eq`).
- **At most two lines per individual** (`three_lines`), by the claw
  law.
- **Lines are two-colourable.** Two lines are adjacent if they share an
  individual (`lineAdj`). Mathlib's `two_colorable_iff_forall_loop_even`
  reduces this to excluding odd closed walks. Given one of length
  2m + 1, pick an individual where each consecutive pair of lines
  meets. That is an odd cycle of individuals, and the odd-cycle law
  gives i with individuals i and i + 2 related. Two cases:
  - All three individuals are distinct. Then they lie on one line, and
    two consecutive lines of the walk are equal, which is a
    contradiction.
  - Two of them coincide. Then the walk returns to a line two steps
    later, and removing those two steps gives a closed walk of length
    2m − 1 (`shorten`).

  By induction on m, no odd closed walk exists (`no_odd`).
- **The criteria.** For each colour b, "equal, or together on a line of
  colour b" is an equivalence relation (`SameCol`). pairLe is the union
  of the two (`union_of_two`). Pair determination then gives f =
  count2 (`count2_eq_pairCount`).

Necessity of the five laws is `isCount2Self_iff`'s other direction. The
claw and odd-cycle laws come from Theorems 8.3′ and 8.5. The diamond
law has a direct proof (`c_diamond`): if x and y share one criterion
but not the other, then z and w both share that criterion with x, so
they share it with each other.

**Theorem 9.3 (the claw law is independent; `Count2Laws.claw_independent`).**
Let fStar count the largest set of non-neighbours in a star with
centre 0 and leaves 1, 2, 3, with each individual counting one. Then
fStar obeys singles, pair determination, the diamond law and the
odd-cycle laws of every length, but breaks the claw law. So it does not
count individuals by two criteria, and by the set form of the claw law
(`IsCount2.claw`), not with several things per individual either
(`fStar_not_isCount2`).

- The diamond law holds by computation over the four individuals.
- The odd-cycle laws hold for a simple reason. If the cycle passes
  through the centre, the centre is related to everything two steps
  on. If not, consecutive leaves are equal, so the cycle is constant.

Whether the diamond law and the odd-cycle laws are also independent of
the rest is not shown here.

### 9.4 The general case is open

Theorem 9.2 covers one thing per individual. When one individual can
own several things, f(P) is the size of a
largest matching in the union of the edge groups of the individuals in
P. In matroid terms, it is the rank of a union of groups in the
intersection of two partition matroids. We found no characterization
of such functions in the literature. This is the natural setting for
copredicated plural individuals, and it is open.

---

## 10. The debate as hypotheses about laws

### 10.1 Double distinctness (DD)

**Gotham (2017).** Predicates contribute individuation relations, PHYS
and INFO. Determiners require the counted plurality to be
non-compressible under them (Definition 1, p. 339; pp. 341-353). PHYS
is not an equivalence relation, only transitive and symmetric (n. 7). "Picked up and
mastered three books" needs three books distinct both ways (pp. 334,
345, 351), and its entailments (122)-(123) to the single verbs hold.

**Chatzikyriakidis & Luo (2015).** Their Coq development derives double
distinctness from "picked up and mastered three books" with injectivity
axioms (A1, §4). They cite Gotham's evidence that the double
distinctness reading is not a cancellable implicature: "John picked up
and mastered three books, but he didn't pick up three books" and three
similar sentences, their (18)-(21), from Gotham (2012).

**Chatzikyriakidis & Luo (2018).** They obtain double distinctness from
a dot-setoid, whose relation is not transitive. No setoid works (A1,
§13).

**Bahramian, Nematollahi & Sabry (2017).** A noun is an identity type
between "prototypes" in homotopy type theory, formalized in Agda.
Their (24c) requires three books pairwise distinct qua physical and qua
informational (p. 17). Their §6.1 argues that "Fred has five books"
refutes each of four single criteria, given the verbs that follow.

On every DD account, the counting function is count2. It can break
submodularity (Theorem 7.5).

### 10.2 Property Versatility (PV)

Liebesman & Magidor (2017, 2026). 'Book' is univocal. By contextual
domain restriction (Stanley & Szabó 2000) it ranges over p-books or
over i-books, and properties like *by Tolstoy* and *memorized* are
"versatile", true of both kinds (2026, §3.1, pp. 22-26). Counting is
ordinary counting over the restricted domain (§3.2.3, pp. 32-36). Their
evidence against DD:

- **One sentence, two counts** (2026, pp. 19-20, (33)-(36)). "Alice
  picked up three books" can count i-books: a bookseller collecting 100
  copies each of four new titles says "I will pick up three books, and
  you can pick up the fourth one tomorrow". "Three books are by
  Tolstoy" can count volumes, when deciding whether a shelf needs
  reinforcing.
- **The counterexample** (2026, p. 21, (37); p. 34, (67)). Take ten
  wrinkled copies of *War and Peace* and two of *Wuthering Heights*.
  "# Exactly one wrinkled book is by Tolstoy" has, "to our ears", no
  true reading. Gotham's account predicts it true, since no two copies
  of *War and Peace* are distinct both ways. count2 gives 1 too.
- **Gotham's (2022) Granger example** (2026, p. 34, (68)). Gotham says
  "Granger memorized three yellow books" has no reading true of three
  copies of one text. Liebesman & Magidor answer that memorizing a
  p-book may require learning its text for the first time (p. 35), and
  in n. 38 they doubt the judgment.
- **Their methodological point** (p. 34). Discussions have asked how to
  generate double-distinctness truth conditions "without paying
  sufficient attention to the question of whether these sentences
  really have" them.

**Laws.** Under any fixed reading, PV counts by one criterion (volumes
or texts). So it predicts submodularity for each speaker in each
context. A violation could only arise from a reading switch between the
counts compared.

### 10.3 QUD (Sutton 2024)

A polysemous noun lexically introduces a question under discussion,
"How are we individuating books?", with answers physical,
informational or both (pp. 877, 879). Modifiers answer whichever QUD is
highest on the stack. A contextual QUD (which pile of books?) can take
priority, and then a modifier restricts the domain instead of the
criterion. Counting needs a quantized set relative to context (Sutton &
Filip 2020).

Her predictions (p. 877):

1. double distinctness in neutral contexts;
2. none when a more prominent QUD makes a modifier a domain restrictor;
3. further modifiers can bring it back: *memorised the first page of*
   does (ex. (10)), *tore out the first page of* does not (ex. (11);
   pp. 878, 890).

Word order matters too (p. 878). In the display-pile context, "three
damaged, insightful books" allows informational duplicates, while
"three damaged books are insightful", "three insightful, damaged
books" and "three damaged and insightful books" resist that reading
((6)-(9)). She also finds the anthology reading "at the very least
highly contextually restricted" (p. 877, n. 1).

**Laws.** Her lexical QUD selects the family of criteria: {volume},
{text}, or {volume, text}, the last being count2. So she predicts that
the law can fail in neutral contexts and holds under a prominent QUD:
**context switches the law on and off.**

### 10.4 Landman's cost

Landman (2020) does not discuss copredication, but his indexing repair
(§5.2) predicts that counting that needs overlapping items is costly.
Law-breaking answers, if they occur, should be slower or rated harder
than law-obeying ones. This prediction can hold alongside any of the
three accounts.

### 10.5 Do existing judgments already decide it?

**For or against DD as the meaning:** they bear on it, but they are
introspective and contested. The judgments go both ways: Gotham's
(2012) non-cancellability examples and Gotham's (2022) Granger example
for DD; Liebesman & Magidor's (37) against it, and their n. 38
against Gotham's.

**For or against the law:** no. The law constrains four counts by one
speaker in one context. Every published example gives one count. So
the law is untested.

---

## 11. The test

This is a draft protocol, not run. Running it needs human participants
and ethics approval.

### 11.1 The scenario

Three books on a desk, as in §7.3:

- volume 1: a copy of *Emma* (book A);
- volume 2: a two-novel omnibus with *Emma* (B) and *Persuasion* (C).

John picked up every volume and read every text. Two overlapping
groups:

- P = "the copies of *Emma*" = {A, B};
- Q = "the books in the omnibus" = {B, C}.

P ∩ Q = {B} and P ∪ Q = {A, B, C}.

By Proposition 7.7 the omnibus cannot be avoided. It is the reading
Sutton (n. 1) and Chatzikyriakidis & Luo (2018, n. 4) find marginal,
so the materials must make it salient: two title pages, "two novels in
one binding". A manipulation check (§11.5) asks how many books, not
volumes, the omnibus contains.

### 11.2 Questions and predictions

| books asked about | "picked up" (volume) | "mastered" (text) | "picked up and mastered" (count2) |
|---|---|---|---|
| A, B (P) | 2 | 1 | 1 |
| B, C (Q) | 1 | 2 | 1 |
| A, B, C (P ∪ Q) | 2 | 2 | 2 |
| B (P ∩ Q) | 1 | 1 | 1 |
| law: (P ∪ Q) + (P ∩ Q) ≤ P + Q | 3 ≤ 3 holds | 3 ≤ 3 holds | 3 ≤ 2 **fails** |

Predicted answers to the conjoined question:

- DD: the count2 column.
- PV: the volume column or the text column, whichever reading the
  context gives; never the count2 column.
- QUD: the count2 column in a neutral context; a single column under a
  prominent QUD.

**A weaker prediction**, shared by every account considered: the
conjoined answer never exceeds either single answer. By Theorem 7.1,
the all-text mixture (S = ∅) and the all-volume mixture (S = all texts)
both count at least count2. Answers above either would show a reading
this framework does not model.

### 11.3 Reading switches: the design must control them

Liebesman & Magidor's (33)-(36) show a speaker's criterion can change
from sentence to sentence. Hence:

1. **Never pool across speakers or questions.** Suppose text-readers
   give the modal answer to the P question (1) and volume-readers give
   the modal answer to the Q question (1), and both groups answer 2 and
   1 to the other two questions. The modal answers are then 1, 1, 2, 1,
   which break the law, though every speaker counted by one criterion.
   So the law is tested *per participant*. Each participant answers all
   four group questions for one verb, in one context. The analysis
   counts participants whose own four answers break the law.
2. **Fix the context across the four questions.** Keep one scenario and
   one framing throughout. After each answer, ask "which books did you
   count?", with the books pictured. Participants who switch criterion
   by their own report are analysed separately.

### 11.4 Conditions

- **Verb**, between participants: "picked up", "mastered", "picked up
  and mastered". The single verbs are controls, which every account
  predicts obey the law.
- **Context**, between participants (Sutton):
  - *neutral*: the scenario only;
  - *QUD*: a prior question making one criterion the point. For
    example, "John is weighing his luggage allowance" (volumes), or
    "John is preparing for an exam on separate novels" (texts).
- **Question order**, counterbalanced.

### 11.5 Further items and measures

- **Liebesman & Magidor's (37).** Ten wrinkled *War and Peace*, two
  wrinkled *Wuthering Heights*: true or false, "Exactly one wrinkled
  book is by Tolstoy"? DD (count2 = 1) predicts true; PV predicts false.
- **Sutton's modifier pair** ((10)-(11)), in her display-pile context:
  can "I memorised / tore out the first page of three damaged,
  insightful books" be true when two of them are copies of one text?
  She predicts no for *memorised* and yes for *tore out*.
- **Gotham's Granger item** ((68) in L&M 2026): "Granger memorized three
  yellow books", with three yellow copies of one text. DD predicts
  false.
- **Manipulation check**: how many books (not volumes) the omnibus
  contains. Participants who answer one reject the composite-book
  ontology. For them the law test is vacuous, and they are analysed
  separately.
- **Matching**: word order and structure kept identical across
  conditions, given Sutton's word-order effects.
- **Measures**: the number given, the "which books" report, a
  difficulty rating, and response time if run online (for Landman's
  prediction).
- **Elicitation without numbers**: a comparative version, "Who picked
  up and mastered more books, John or Mary?", modelled on Barner &
  Snedeker's (2005) "Who has more N?" task (reported by Rothstein 2017,
  ch. 5, pp. 117-121, and Landman 2020, pp. 197, 214). Each participant
  must still see all the comparisons the law needs.
- A power analysis is needed before running; none is attempted here.

### 11.6 What each outcome would show

- **Individual participants' four answers to the conjoined question
  break the law, with a stable criterion by their own report.** No
  one-criterion account can model these speakers, whatever it takes a
  book to be, so PV is refuted for this construction. DD is supported.
  If this happens only in the neutral condition, Sutton's QUD account
  is supported over DD as stated.
- **Answers obey the law.** DD is wrong for these speakers in this
  context, and a one-criterion account suffices, as PV says.
- **Law-breaking answers are slower or rated harder.** This fits
  Landman's indexing cost. If they are not, that counts against
  treating double counting as a repair.
- **Answers above a single-verb answer**: a reading outside this
  framework.

---

## 12. Related work

- **Counting and individuation in semantics.** Rothstein (2010, 2017):
  counting contexts, contextual and conceptual atomicity. Landman
  (2011, 2020): Iceberg semantics, disjoint bases, neat and mess mass
  nouns, pragmagic. Barner & Snedeker (2005), via Rothstein and
  Landman. Sutton & Filip (2016, 2020; not read): quantization and
  counting bases. The laws here are about counting functions, and they
  apply to any of these frameworks with the base, context or criterion
  held fixed.
- **Copredication.** Asher (2011); Gotham (2014 [not read], 2017, 2022
  [not read]); Chatzikyriakidis & Luo (2015, 2018); Bahramian et al.
  (2017); Liebesman & Magidor (2017, 2019 [not read], 2023 [not read],
  2025 [not read], 2026); Sutton (2024); Mery, Moot & Retoré (2019, not
  read). Liebesman & Magidor (2025, ch. 9 §4) discuss double
  distinctness at length and must be read before submission.
- **Combinatorics.**
  - Coverage functions and their W-transform: Chakrabarty & Huang
    (2012, 2015).
  - Matchings and vertex covers: König (1931); Hall (1935).
  - Line graphs: Harary & Holzmann (1974, not seen).
  - Perfection: Trotter (1977, reported); de Werra (1978, not seen).
  - Submodular functions in general: standard. We use only the
    elementary fact for integer coverage functions.

---

## 13. Limits and open problems

1. **The criterion is held fixed.** Rothstein's and Landman's central
   concern, how context sets the criterion, is modelled only as a
   family of criteria, not as a dynamics. Sutton's within-sentence
   effects are outside the fragment.
2. **count2 as meaning is a hypothesis.** The theorems say what it
   implies, not that it is right.
3. **No data.** The test has not been run.
4. **Open: exact laws for IsCount2 in general.** Theorem 9.2 settles
   the case of one thing per individual. The general case (§9.4) is
   open.
5. **Not formalized:** the twin analysis of §9.2, Proposition 7.7's
   symmetric half, and Proposition 9.1 (all superseded for the
   characterization by Theorem 9.2, which is formalized). Not shown:
   whether the diamond and odd-cycle laws are independent of the
   others; only the claw law's independence is proved (Theorem 9.3).
6. **Mass nouns.** Landman's neat mass nouns suggest a further class,
   choice from a family. Its counting functions, and how they relate to
   minima, are not studied here.
7. **More than two criteria.** Counting by k ≥ 3 criteria is matching in
   k-partite hypergraphs, where König's theorem fails. Nothing is
   claimed for that case.
8. **Not read:** Gotham (2022); Liebesman & Magidor (2019, 2023, 2025);
   Mery, Moot & Retoré (2019); Harary & Holzmann (1974); de Werra
   (1978); Chakrabarty & Huang beyond the abstract.

---

## 14. Conclusion

Count nouns with one identity criterion are integer coverage functions.
They fall into four kinds by two laws, never merging and never
splitting, and all of them are submodular. Never splitting is the
disjointness at the heart of Rothstein's and Landman's theories of
counting. Counting by two criteria at once, as proposed for
copredication, is the least of a family of such functions. It can break
submodularity. When each individual is one thing, five laws
characterize it exactly, and the claw law among them is independent. Because submodularity holds for every one-criterion account at
once, it turns the dispute over copredicated counting into a test on
each speaker's pattern of answers. The test is designed, and needs only
to be run.

---

## References

Items marked [not read] or [reported] must be checked before
submission.

- Asher, N. (2011). *Lexical Meaning in Context*. Cambridge University
  Press. (Ch. 5, pp. 146-159 read.)
- Bahramian, H., Nematollahi, N. & Sabry, A. (2017). Copredication in
  homotopy type theory. Manuscript (PDF dated 7 November 2017).
- Barner, D. & Snedeker, J. (2005). Quantity judgments and
  individuation: evidence that mass nouns count. *Cognition* 97:
  41-66. [reported via Rothstein 2017 and Landman 2020]
- Chakrabarty, D. & Huang, Z. (2012). Testing coverage functions. ICALP
  2012 (arXiv:1205.1587). Journal version: Recognizing coverage
  functions, *SIAM J. Discrete Math.* 29(3), 2015. [abstract only]
- Chatzikyriakidis, S. & Luo, Z. (2015). Individuation criteria,
  dot-types and copredication: a view from modern type theories.
  Proceedings of MoL 14: 39-50.
- Chatzikyriakidis, S. & Luo, Z. (2018). Identity criteria of common
  nouns and dot-types for copredication. *Oslo Studies in Language*
  10(2): 121-141.
- de Werra, D. (1978). On line perfect graphs. *Mathematical
  Programming* 15: 236-238, doi:10.1007/BF01609025. [not seen; title to
  check]
- Gotham, M. (2012). [cited by C&L 2015 for (18)-(21); not read]
- Gotham, M. (2017). Composing criteria of individuation in
  copredication. *Journal of Semantics* 34: 333-371.
- Gotham, M. (2022). Property inheritance, deferred reference and
  copredication. *Journal of Semantics* 39: 87-116. [not read]
- Hall, P. (1935). On representatives of subsets. *J. London Math. Soc.*
  10: 26-30. [cited for the theorem, via Mathlib]
- Harary, F. & Holzmann, C. (1974). Line graphs of bipartite graphs.
  *Revista de la Sociedad Matemática de Chile* 1: 19-22. [not seen]
- König, D. (1931). Gráfok és mátrixok. *Matematikai és Fizikai Lapok*
  38: 116-119. [cited for the theorem]
- Landman, F. (2011). Count nouns – mass nouns – neat nouns – mess
  nouns. *Baltic International Yearbook of Cognition, Logic and
  Communication* 6. [not read]
- Landman, F. (2020). *Iceberg Semantics for Mass Nouns and Count
  Nouns*. Springer, SLAP 105.
- Liebesman, D. & Magidor, O. (2017). Copredication and property
  inheritance. [venue to check]
- Liebesman, D. & Magidor, O. (2019). Copredication, counting, and
  criteria of individuation: a response to Gotham. *Journal of
  Semantics* 36(3): 549-561. [not read]
- Liebesman, D. & Magidor, O. (2023). Copredication and meaning
  transfer. *Journal of Semantics* 40: 69-91. [not read]
- Liebesman, D. & Magidor, O. (2025). *Property Versatility and
  Copredication*. Oxford University Press. [not read]
- Liebesman, D. & Magidor, O. (2026). What copredication can(not) teach
  us. *Theoretical Linguistics*, advance online,
  doi:10.1515/tl-2026-2002.
- Mery, B., Moot, R. & Retoré, C. (2019). Solving the individuation and
  counting puzzle with λ-DRT and MGL. [not read]
- Rothstein, S. (2010). Counting and the mass/count distinction.
  *Journal of Semantics* 27: 343-397. [reported via Landman 2020]
- Rothstein, S. (2017). *Semantics for Counting and Measuring*.
  Cambridge University Press.
- Stanley, J. & Szabó, Z. G. (2000). On quantifier domain restriction.
  *Mind & Language* 15: 219-261. [cited via L&M]
- Sutton, P. R. (2024). Individuation criteria and copredication:
  modification in context. *Proceedings of Sinn und Bedeutung* 28:
  876-894.
- Sutton, P. R. & Filip, H. (2016, 2020). [cited via Sutton 2024 and
  Landman 2020; not read]
- Trotter, L. E. (1977). Line perfect graphs. *Mathematical
  Programming* 12: 255-259. [reported]

---

## Appendix A. Theorems, files and CI runs

| result | Lean name | file | first CI run |
|---|---|---|---|
| full abstraction (§2) | `obsEq_iff`, `obsEqM_iff`, `obsEqP_iff`, `obsEqW_iff` | `FullAbstraction*.lean` | 38809883869, 38814363115, 38818866053, 38827684833 |
| Thm 3.1, 3.2 | `representation`, `units_unique`, `units_ofUnits` | `CountingLaws.lean` | 38832047031 |
| Thm 4.1-4.4 | `additive_iff`, `single_iff`, `cells_inhabited`, `montague_iff`, `montague_obsEq` | `CountingLaws.lean` | 38832047031 |
| Thm 5.1 | `noSplit_iff_disjoint` | `CountingLaws.lean` | 38840693113 (added with `TwoCriteria.lean`) |
| Thm 6.1 | `count_submod` | `CountingLaws.lean` | 38832047031 |
| Thm 7.1-7.4 | `count2_le_mix`, `exists_mix_le`, `count2_eq_min`, `copredication_is_min` | `TwoCriteria.lean` | 38840693113 |
| Thm 7.5, 7.6 | `not_single`, `criteria_hidden` | `FullAbstractionMulti.lean` | 38814363115 |
| Prop 7.7 (first half) | `dotSame_trans_of`, `exists_setoid_iff` | `Criteria.lean`, `DotSetoid.lean` | 38671403438, 38697690966 |
| §8.1 | `isMinCov_of_isCount2`, `not_subadd_example`, `not_pairwise_example` | `MinCoverage.lean` | 38843325962 |
| Thm 8.1, 8.2 | `count2_subadd`, `count2_pairwise` | `MinCoverage.lean` | 38843325962 |
| Thm 8.3, 8.4 | `count2_cycle5`, `IsCount2.cycle5`, `two_laws_not_sufficient` | `OddCycle.lean` | 38848341001 |
| Thm 8.3′, 8.5 | `count2_oddCycle`, `IsCount2.oddCycle`, `count2_claw`, `IsCount2.claw`, `hub_step` | `ForbiddenLaws.lean` | 38860685948 |
| Thm 9.2 | `isCount2Self_iff`, `union_of_two_general`, `union_of_two`, `no_odd`, `shorten`, `three_lines`, `count2_eq_pairCount`, `c_diamond` | `Count2Laws.lean` | 38865573037 |
| Thm 9.3 | `claw_independent`, `fStar_not_isCount2` | `Count2Laws.lean` | 38865573037 |

The main theorems carry `#guard_msgs` checks that they use only
`propext`, `Classical.choice` and `Quot.sound`, so the build fails if a
`sorry` gets in.

## Appendix B. Definitions to check

- `FullAbstraction`: `NounI`, `NounI.count`, `NounI.unit`,
  `NounI.units`, `meetsSum`, `ObsEq`.
- `FullAbstractionMulti`: `NounM`, `NounM.count`, `ObsEqM`, `books`.
- `CountingLaws`: `Additive`, `Single`, `NoMerge`, `NoSplit`, `ofUnits`,
  `passengers`, `copies`, `anthologies`.
- `TwoCriteria`: `count2`, `mix`, `mixNoun`.
- `MinCoverage`: `IsCount2`, `IsMinCov`, `f2`, `f3`.
- `OddCycle`: `onHub`, `U1`, `U2`, `g5`, `f5`.
- `Count2Laws`: `pairCount`, `pairLe`, `Singles`, `PairDet`, `ClawLaw`,
  `DiamondLaw`, `OddCycleLaw`, `IsCount2Self`, `twinSetoid`, `Hyp`,
  `IsLine`, `lineAdj`, `starRel`, `fStar`.

## Appendix C. Proof of the odd-cycle law, in prose

Let x₀, …, x₄ be individuals with things in a bipartite multigraph.
Each x_i has a thing. Each adjacent pair {x_i, x_{i+1}} has count2 ≤ 1,
so all things over that pair pairwise conflict. By the hub lemma they
share a common volume or a common text, the pair's hub h_i. The things
of x_{i+1} lie on h_i and on h_{i+1}.

- If h_i and h_{i+1} are both volumes, they must be equal, since a thing
  has one volume. Likewise if both are texts.
- So for each i, either h_i = h_{i+1}, or one is a volume and the other
  a text.
- If no two consecutive hubs were equal, the kinds would alternate
  around a cycle of odd length 5, which is impossible
  (`no_alternation`).
- So h_i = h_{i+1} for some i. Then all things of x_i, x_{i+1} and
  x_{i+2} lie on that one hub, so x_i and x_{i+2} have count2 ≤ 1
  together. ∎

The same argument works for every odd cycle (Theorem 8.3′,
`ForbiddenLaws.count2_oddCycle`).
