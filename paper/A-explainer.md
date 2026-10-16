# Paper A, explained

A plain-language guide to what Paper A is about, what it found, and what
is and is not new. It is written for you to learn the work well enough
to explain it yourself, without the code open. Section 9 says where each
claim lives in the repository.

---

## 1. The question, in one sentence

**When we write down the meaning of a sentence in logic, should a common
noun like "book" or "man" be a *predicate* (a property things can have)
or a *type* (a kind of thing)? And does the choice change which
inferences come out valid?**

---

## 2. The background you need

### Two ways to state "Every man walks"

**Nouns as predicates** (Montague's way, the standard one in formal
semantics). There is one big collection of things, the *individuals*.
"Man" and "walks" are both properties of individuals:

> for every individual x, if man(x) then walks(x)

**Nouns as types** (the Modern Type Theory or MTT way, from Ranta, Luo
and Chatzikyriakidis). "Man" is a *type*, a kind of thing in its own
right, and the quantifier ranges over that type directly:

> for every x of type Man, walks(x)

Verbs and adjectives stay properties in both. Only nouns change.

### Why anyone thinks the choice matters

MTT people argue that nouns are special. A noun tells you how to
*count* its things, and a verb doesn't. Philosophers call this the
noun's **identity criterion** (Geach). Their standard example:

> "EasyJet transported 1 million **passengers** in 2010" does **not**
> mean "EasyJet transported 1 million **persons**."

One person on three flights is three passengers but one person. So
"passenger" and "person" count the same people differently. Types,
they argue, are the natural way to give each noun its own way of
counting.

### Two more terms

- **Valid entailment.** "Premises ⇒ conclusion" is *valid* if the
  conclusion is true in every situation (every *model*) where the
  premises are true. Comparing the two encodings means asking whether
  they make the same entailments valid.
- **FraCaS.** A standard test suite of 346 short inference problems
  (premises, a hypothesis, and an answer: yes, no or unknown), built in
  the 1990s to test semantic theories. FraCaS problem 55: "Some Irish
  delegates finished the survey on time" ⇒ "Some delegates finished
  the survey on time"? Answer: yes.

### What Lean is doing here

Lean is a *proof assistant*: a program that checks mathematical proofs
step by step. Every theorem in this project is checked by Lean's
kernel, so a result that builds is a real proof, not a test run on a
few examples. That is why the results are trustworthy even though an
AI wrote much of the code. Proofs checked by a machine don't depend on
trusting whoever wrote them. *What* was proved still needs a human to
check that the statements say the right thing, which is what a
professor can help with.

---

## 3. The main result: the equivalence theorem

### The intuition

Take any situation described with nouns as types. Turn each type into
the predicate "is one of the things of that type", and you get a
situation described with predicates. Going the other way, turn each
predicate into the type "the things that have it". These two
translations go back and forth.

Does the translation preserve truth? For "every", "some" and "no",
always. For **counting** words ("at least three", "most", "exactly
two"), only if counting means the same thing on both sides.

### Where counting can go wrong

With types, "three books" counts *things of type Book*. With
predicates, it counts *individuals that are books*. These come apart
if two things of type Book can be **the same individual**. In
mathematical terms, if the map from the type to the individuals is not
*injective* (not one-to-one).

### The two theorems

1. **`valid_iff` (in `Equivalence.lean`):** if each type maps
   one-to-one onto individuals, nouns as types and nouns as predicates
   make exactly the same entailments valid.
2. **`validI_iff` (in `Counting.lean`), the stronger one:** if
   counting words count *individuals* rather than elements of the type,
   the two make exactly the same entailments valid with **no condition
   at all**.

Both hold for a whole *fragment*: every, some, no, most, both, neither,
at least / at most / exactly *k*, "more ... than", and the connectives.
They are not checked one example at a time.

They also hold with **two-place verbs** (`Relational.lean`). There,
quantifiers can sit inside each other, as in "every student read some
book", which is the first gap a reviewer would point to. Nothing new
was needed for the proofs: a quantifier over the type Book still hands
its verb an individual, so the same counting lemmas apply.

### The converse: the characterization theorem

`validI_iff` says: count by individuals, and the two views agree. The
**characterization theorem** (`CModel.agree_iff_kernel`, in
`Characterization.lean`) adds the other direction. Give each noun *any*
rule for when two of its things count as one (its identity criterion).
Then the two views agree on every sentence of the fragment, whatever the
verbs mean, **if and only if** that rule says "same" exactly when the
two things are the same individual.

The proof of the "only if" half is the useful part, because it says
*how* a criterion can go wrong, and which sentence catches it:

- **It splits one individual into several.** One person on two flights
  is two passengers. Then "at most one passenger is v" (with v true of
  that person only) is true with predicates and false with types.
- **It merges several individuals into one.** Two copies of one novel
  are one book, counted as texts. Then "at least two books are v" (with
  v true of the two copies only) is true with predicates and false with
  types.

These are exactly Luo's passengers and Gotham's books. So those two
famous examples are not just examples: they are the *only two ways* the
views can come apart in this fragment.

**In one line:** in this fragment, nouns as types make a logical
difference exactly when, and only when, a noun counts by an identity
criterion that differs from counting individuals.

### And even that difference goes away: the translation theorem

Predicate accounts can count by criteria too. Gotham (2017) does it by
putting more things in the domain (copies, texts, the composite books
made of both) and counting by relations like "same text". The
**translation theorem** (`validC_iff`, in `Translation.lean`) proves
that this is enough, in general, for the fragment.

Translate a sentence word by word: every word stays the same except
"is" (identity), which becomes "is the same individual as". Then the
sentence is valid with nouns as types and identity criteria exactly
when its translation is valid with nouns as predicates, over a domain
with an identity relation and criteria.

The theorem also holds when a noun counts by several criteria at
once (`validM_iff`, in `TranslationMulti.lean`). That is the
copredication case: "picked up and mastered three books" needs three
books distinct both as volumes and as texts. Counting by two criteria
means finding the largest set of books that differ both ways. (It is a
matching problem: volumes on one side, texts on the other, each book a
line between its volume and its text.)

So nouns being *types* never matters for which inferences are valid in
the fragment. What matters is the **ontology**, meaning what the domain
contains and how things are counted. That ties every earlier result
together:

| claimed advantage | what actually delivers it |
|---|---|
| quantifiers and counting | nothing: the two views are equivalent |
| identity criteria | a richer domain plus criteria, with predicates |
| anaphora | dependent types, with predicates |
| selectional restrictions | sorts, with predicates |
| copredication counting | two criteria at once, with predicates; one setoid can't do it |
| "heavy book" (C&L 2017) | sorts, with the adjective said of the noun's variable |
| subsective adjectives (FraCaS 29) | a subsectivity postulate, the same stipulation as the type |
| the verb choosing how a noun counts | carries over to predicates unchanged |
| the "both" view makes type checking undecidable (C&L 2017) | only if (*) is a typing rule; with the link proved about models, type checking is decidable |
| MTT's entailment is derivability, not model-theoretic validity | the equivalence also holds as derivability, provable with no axioms at all |
| "competent" (FraCaS 215) | noun-relative adjectives, with predicates too; extensional adjectives fail with types too |

### Why: what a noun means, as far as inference can tell

The **full abstraction theorem** (`obsEq_iff`, in
`FullAbstraction.lean`) explains why the translation theorem holds. It
asks which part of a noun's interpretation sentences can see at all.

Think of a noun as a list of **counting units**. Each unit is one thing
you would count, together with the individuals it covers. Some examples:
- One person on three journeys is three passenger units, each covering
  the same person.
- Two copies of one novel, counted as texts, are one unit covering both
  copies.

The theorem says this. Take two interpretations of a noun. No sentence
of the fragment tells them apart, whatever the other words mean,
exactly when they have the same units the same number of times.
"Every", "some" and "no" see only which individuals are covered.
"Exactly three N are P" sees how many units touch P, and those numbers
pin the units down.

For a noun that counts individuals, the units are just the individuals,
so all that matters is the noun's extension, as Montague had it
(`obsEq_byInd_iff`).

So, for inference, a count noun means a collection of units. Types with
criteria and predicates with criteria are two ways of writing that
collection down.

For nouns that count in two ways at once (copredication), the same holds
with the counts themselves in place of the units (`obsEqM_iff`). And
here something new appears (`not_single`). Take three books: the first
two are copies of one text, and the last two are two texts bound in one
volume. Counting books distinct both as volumes and as texts:
- the first two are one book;
- the last two are one book;
- all three are two books (the first and the third).
No noun with a single criterion, of any kind, gives those numbers. With
one criterion, "how many among X or Y" plus "how many among X and Y" can
never exceed "how many among X" plus "how many among Y", and here it is
2 + 1 against 1 + 1. So copredication really is two criteria at once,
not one criterion in disguise, and that is visible from sentences
alone.

**Plurals don't change the answer** (`obsEqP_iff`, in
`FullAbstractionPlural.lean`). Add plural sentences: "three passengers
gathered", "the books are heavy together", "each of them read one". Let
a plurality of passengers be a collection of the noun's own things (here
journeys), as nouns as types would have it. Then three journeys by one
person form a group of three passengers, or two, or one. That looks like
it could reveal more of a noun than singular sentences do. It doesn't:
two interpretations are still indistinguishable exactly when they have
the same units. A group of k passengers covering exactly some people
exists exactly when some k units each touch those people and together
cover them, and that depends only on the units.

**Intensional contexts don't change it either** (`obsEqW_iff`, in
`FullAbstractionIntensional.lean`). Add possible worlds, "necessarily",
and "John believes that ...". Now a noun can mean different things in
different worlds. What sentences see is the units in each world, and
nothing else. For nouns that count individuals, that is Montague's
intension: the extension in each world.

A natural hope is that types give finer meanings than predicates, so
that "John believes every equilateral triangle is equilateral" could be
true while "John believes every equiangular triangle is equilateral" is
false. Possible-worlds belief can't make that distinction, with types or
with predicates (`believes_same`). An attitude that relates people to
sentences can (`thinks_distinguishes`), but it does so by looking at
which word is used. It would tell apart two nouns with exactly the same
meaning. So finer-grained belief comes from the attitude, not from
whether nouns are types.

### From diagnosis to theory: laws of counting

Everything so far compares two encodings. `CountingLaws.lean` says what
a count noun *is*, using only how it counts: for each property P, how
many of the noun's things are P.

**Two laws.** A noun is *additive* if counting P-or-Q plus counting
P-and-Q gives the same as counting P plus counting Q. It is *single* if
it never counts one individual twice. Each law matches something about
the noun:
- additive exactly when it **never merges**: things counted as one are
  one individual;
- single exactly when it **never splits**: things that are one
  individual count as one.

That gives four kinds of noun, and all four exist:

| | never splits | splits |
|---|---|---|
| never merges | ordinary nouns ("dog") | passengers |
| merges | books counted as texts | anthologies counted as texts |

The nouns that obey both laws are exactly the ones that behave like
Montague's sets of individuals (`montague_iff`). The literature's two
famous problems, Luo's passengers and Gotham's books, are exactly the
two ways of breaking the laws.

**A third law, and a prediction.** Every noun with one criterion obeys
a weaker law: P-or-Q plus P-and-Q is *at most* P plus Q. Copredicated
nouns can break it (the three books). So: if a noun's counts break that
law, it must count in more than one way at once. That is a claim about
language, which a diagnosis cannot make.

**The mathematics already exists.** A function is how some noun counts
exactly when it is what combinatorics calls a *coverage function*
(`representation`), and the noun's units are its coefficients, which
are unique. That characterization is a known theorem (Chakrabarty &
Huang 2012). Paper A cites it; what is new is that count nouns are
exactly these functions, and the typology built on it.

**How the counting literature fits.** Rothstein (2017) and Landman
(2020) both require the things a count noun counts to be *disjoint*: no
part shared between two. That is exactly our "never splits" law
(`noSplit_iff_disjoint`). So passengers (one person, several
passengers) and copredicated books break their condition when the
individuals are people or books; those theories must count other
entities instead, such as journeys.

**What counting by two criteria is.** Take the copredicated books.
Divide the texts into two groups. Count books whose text is in the first
group by volume, and the rest by text. That is an ordinary single
criterion. The number of books distinct both ways is exactly the
*smallest* count you can get by choosing the groups well
(`count2_eq_min`; the proof is König's theorem). So double distinctness
is not one way of counting, but the most conservative of a family of
ordinary ways. Each of those is a coverage function, so counting by two
criteria is a minimum of coverage functions.

The converse is false (`MinCoverage.lean`). Counting by criteria obeys
two laws that a minimum of coverage functions need not:
- the count of P-or-Q is at most the count of P plus the count of Q;
- if every pair among three groups holds at most one countable thing,
  so do all three together.
Three individuals give a minimum of coverage functions that counts 1 on
every pair and 2 on all three: no noun with criteria counts like that.
So nouns with two criteria sit strictly between ordinary nouns and
minima of coverage functions.

Those two laws are not the whole story (`OddCycle.lean`). Put five
individuals in a ring and count the largest group with no two
neighbours. That obeys both laws, but no noun counted by volume and text
counts like it. The reason is a third law: in a ring of five where
neighbours always "clash" (count as one together), some non-neighbours
must clash too. Things that clash pairwise all share one volume or one
text, and around a ring of odd length the shared volumes and texts
cannot alternate. The full list of laws is still open.

**The prediction, as an experiment.** `paper/A-prediction.md` drafts a
test: three books (two copies of *Emma*, one of them bound with
*Persuasion*), and questions about overlapping groups of them. Counting
by volume or by text alone obeys the law; "picked up and mastered", if
it is double distinctness, breaks it. The test separates every
one-criterion account from copredication at once.

---

## 4. Where they really do differ: identity criteria

Each of these cases comes from the published literature, and each is
proved in Lean (`Copredication.lean`, `Counting.lean`, `Criteria.lean`).

**The books (Gotham 2017; Asher 2011).** A book is both a physical
object and a text.

> John picked up three books. John mastered every book.
> ⇒ John mastered three books?

Not necessarily: he might have picked up three copies of the same
novel. "Picked up" counts physical objects; "mastered" counts texts.
- With nouns as predicates over one domain, this inference comes out
  **valid**, which is the wrong answer.
- With types where each verb counts by its own aspect (Asher 2011;
  Chatzikyriakidis & Luo 2018), it comes out **not valid**, the right
  answer. The countermodel is three copies of one text.

**The anthology (Asher 2011).** The mirror image: one volume holding
several texts. "Mastered three books" doesn't give "picked up three
books".

**Passengers (Luo 2012)** and **judges (Asher 2011):** five judgeships
held by four people, because one person holds two. "Five judges" is
true and "five people" false.

**"Picked up and mastered three books."** This needs three books that
are distinct *both* physically and as texts (Gotham; Chatzikyriakidis &
Luo 2018). Lean proves this entails "picked up three" and "mastered
three".

---

## 5. What FraCaS shows: almost no difference

The project also compared the encodings on the FraCaS problems. On
those, the choice almost never matters:

- **Phase 2:** with counting by individuals, every problem the pipeline
  reaches gets the same answers either way.
- **Phase 3:** 8 problems needed an extra fact like "an Irish delegate
  is a delegate". In 7, any encoding that builds "Irish delegate" from
  "Irish" and "delegate" supplies it, predicates included. Only one,
  FraCaS 29 ("leading businessmen"), needs more, because "leading" is
  a *subsective* adjective: a leading businessman is a businessman, but
  not necessarily a leading person. Types build this in; predicates
  need a postulate that "leading" is subsective. `Modifiers.lean`
  proves these are the same stipulation in two places. With it, both
  get 29; without it, neither does.
- **Phase 1a, FraCaS 215:**
  > All legal authorities are law lecturers. All law lecturers are
  > legal authorities. ⇒ All competent legal authorities are competent
  > law lecturers?

  The answer is unknown: being competent depends on *as what*. With
  predicates as plain sets ("extensional"), the two nouns have the same
  members, so "competent" can't tell them apart and the inference
  wrongly comes out valid. Types, or intensional predicates, avoid
  this.
- **Phase 1b, Section 3 (pronouns and possessives),** for example
  FraCaS 138: "Every report has a cover page. R-95-103 is a report.
  Smith signed the cover page. ⇒ Smith signed the cover page of
  R-95-103." The type encoding needed no invented helper functions,
  where the pipeline needed one per possessive. But Dependent Type
  Semantics (Bekki 2014) does the same with nouns as predicates, and
  the project checked this in Lean. An encoding "D", with nouns as
  predicates and dependent types, also needs no helper functions, and
  its automatic prover found more answers than the type encoding's (9
  of 11 against 7). So the credit goes to *dependent types*, not to
  nouns as types.

**So:** on FraCaS, the encoding matters mainly for one subsective
adjective (29) and one adjective that depends on its noun (215). The
interesting differences are outside FraCaS: the identity-criterion
cases in section 4.

**Selectional restrictions: well-formedness, not validity.** MTT's
other selling point is that "#the television ate the cake" is a *type
error*: "eat" wants something animate, and a television isn't. With
predicates over one domain the sentence is fine and simply false (or
true). This is about which sentences are *well formed*, so the project
compared typing rules, not inferences (`Selection.lean`), and proved
three things:

1. Whether a sentence type-checks depends on a noun's type only through
   *which verb slots it fits*. Two lexicons that agree on that accept
   exactly the same sentences.
2. So a **many-sorted** predicate lexicon accepts exactly the same
   sentences. It has a few sorts (human, physical, ...), with nouns as
   predicates over their sort. "Man" and "woman" can share a sort; they
   needn't be separate types. This is Asher's and Retoré's kind of
   system.
3. For sentences that *do* type-check, typing changes no truth value:
   what a verb does outside its domain never matters.

So selectional restrictions separate MTT from *one-domain* predicates,
but not from *many-sorted* predicates. Once again the credit goes to
the type structure around the nouns (typed verb slots), not to nouns
being types.

**The one real cost of types is automation.** Generic automatic provers
find fewer proofs when nouns are types. The proofs exist; the provers
just search less well. The D encoding shows the cost comes from nouns
being types, not from dependent types.

---

## 6. Two findings about published papers

Handle these carefully and politely. Have an expert check them before
telling the authors.

1. **Chatzikyriakidis & Luo (2015).** To get "picked up and mastered
   three books" right in Coq, they added an axiom: different books are
   different physical objects and different texts. Their own footnote
   says this holds only if the map is injective. By `valid_iff`, that
   axiom is *exactly* the condition under which their account says the
   same as predicates. That explains Gotham's (2017) objection that
   their system validates the books inference.
2. **Chatzikyriakidis & Luo (2018).** For copredication they define two
   books as "the same" if they share a volume *or* a text, and say this
   is an equivalence relation. It isn't transitive:
   - Copy 1 of *Crime and Punishment* and copy 2 share a text.
   - Copy 2 is bound together with a different novel, so they share a
     volume.
   - Copy 1 and that other novel share neither.

   Their numerals compare books in pairs, so their predictions come out
   right. But the problem is deeper than one wrong word. The project
   proved (`DotSetoid.lean`) that **no** equivalence relation works in
   that library. Whatever relation you pick, some "picked up and
   mastered two books" sentence gets miscounted: it counts one book
   where there are two, or two where there is one. A relation that
   works exists exactly when "same volume or same text" happens to be
   transitive. Their own footnote 4 accepts libraries like this one.
   So their setoid framework, in which every count comes from one
   equivalence relation, cannot express the counting they want.
   Gotham's account uses two separate relations (physical and
   informational), and the theorem says you can't merge them into one.

---

## 7. What is new, and what is not

| Not ours (cite it) | Ours |
|---|---|
| Nouns as types (Ranta 1994; Luo 2012) | The fragment-wide equivalence theorems, `valid_iff` and `validI_iff` |
| The passengers and books examples, as examples | The characterization theorem: those two kinds of example are the only ways the views come apart in the fragment |
| Identity criteria for nouns (Geach; Luo 2012) | Showing that the 2015 axiom is exactly the equivalence condition |
| The books argument (Gotham 2017, ex. 100) | The proof that no single equivalence relation (no setoid) gives the 2018 paper's copredication counting in libraries it accepts |
| Verbs choosing the counting criterion (Asher 2011; Chatzikyriakidis & Luo 2018) | The FraCaS-scale comparison (Phases 1–3) |
| The anthology and judges cases (Asher 2011); passengers (Luo 2012) | Machine-checked versions of all of the above |
| Recognising predicates for types (Retoré 2013), who leaves open how a type relates to its predicate | An answer to that open question, for the fragment |
| Selectional restrictions as type errors (Chatzikyriakidis & Luo 2017); many-sorted alternatives (Asher 2011; Retoré 2013) | The proof that well-formedness depends only on which verb slots a noun fits, so many-sorted predicates accept exactly what MTT accepts |
| Quantifier scope ("every student read some book") | The equivalence and characterization extended to two-place verbs |
| Predicate accounts with criteria (Gotham 2017; Asher 2011) | The translation theorem: nouns as types with criteria are a word-by-word notational variant of them, for the fragment |
| Montague's nouns as sets of individuals | Full abstraction: what sentences see of a noun is exactly its counting units, and for nouns that count individuals, exactly its extension |
| Copredication needs two criteria (Gotham 2017; C&L 2018), and a setoid can't do it (ours, `DotSetoid.lean`) | No single criterion of any kind is indistinguishable by sentences from some copredicated nouns |
| Coverage functions and their unique coefficients (Chakrabarty & Huang 2012) | Count nouns with one criterion are exactly the integer coverage functions; the typology of nouns by laws of counting |

The honest framing: Paper A *mechanizes and sharpens* an existing
debate. It proves exactly where the two views agree, and it pinpoints
where they differ. It does not discover that identity criteria matter;
that is the literature's point.

---

## 8. Saying it yourself

**In 30 seconds:**
> "Formal semanticists disagree about whether nouns should be predicates
> or types. I proved, with Lean checking every step, that for a large
> fragment of English quantifiers the two give exactly the same valid
> inferences, as long as you count by individuals. They differ exactly when
> a noun brings its own way of counting, like 'mastered three books'
> counting texts while 'picked up three books' counts copies. And even
> then, I proved that a word-by-word translation into predicates over a
> richer domain gives back exactly the same valid inferences. So the
> real choice is about ontology, not about types."

**Questions a professor may ask, with honest answers:**

- *"Isn't that obvious?"* For "every" and "some", nearly. The content is
  in counting: exactly which condition makes them agree, proved for a
  whole fragment, and showing that a published axiom is that condition.
- *"What's the fragment missing?"* "Many" and "few", anaphora across
  sentences, adjectives like "former" or "competent" that depend on the
  noun, and coercions (the mechanism behind "John began the book").
  Two-place verbs ("every student read some book") *are* in it now.
- *"What about selectional restrictions?"* Typing the verbs' argument
  slots is what does the work, and many-sorted predicate systems do
  that too. The project proves they accept exactly the same sentences.
- *"Why Lean?"* So the claims are proofs, not arguments, and anyone can
  re-check them.
- *"How much did you do yourself?"* Say it straight: an AI assistant
  wrote most of the code and proofs, and you directed the project and
  are now learning it in depth. Then ask what they'd want you to do to
  own it fully.
- *"Who else works on this?"* Chatzikyriakidis and Luo (MTT), Gotham
  (copredication and counting), Asher (dot objects), Retoré (many-sorted
  lexicon), Bekki (Dependent Type Semantics).

---

## 9. Where things are

- Main results: `EndToEnd/Encodings/README.md`, read from "The
  equivalence theorem" onwards.
- Literature notes with page numbers: `paper/A-literature.md`.
- Proofs:
  - `EndToEnd/Encodings/Equivalence.lean`: `valid_iff`.
  - `Counting.lean`: `validI_iff`, and the books for any number.
  - `Characterization.lean`: the characterization theorem,
    `CModel.agree_iff_kernel`.
  - `Relational.lean`: everything above, with two-place verbs.
  - `Selection.lean`: selectional restrictions.
  - `Translation.lean`: the translation theorem, `validC_iff`.
  - `Modifiers.lean`: the "heavy book" argument and subsectivity.
  - `TypeCheck.lean`: a type checker proved correct.
  - `Constructive.lean`: the equivalence as derivability, with no axioms.
  - `FullAbstraction.lean`: what sentences see of a noun, `obsEq_iff`.
  - `FullAbstractionMulti.lean`: the same with several criteria, and
    three books no single criterion counts, `not_single`.
  - `FullAbstractionPlural.lean`: the same with plurals and collective
    verbs, `obsEqP_iff`.
  - `FullAbstractionIntensional.lean`: the same with possible worlds,
    belief and a hyperintensional attitude, `obsEqW_iff`.
  - `CountingLaws.lean`: laws of counting, the typology, and the
    representation theorem.
  - `TwoCriteria.lean`: counting by two criteria as the least mixed
    count, `count2_eq_min`.
  - `VerbCriteria.lean`: one entry for "book", with the verb choosing
    how it counts.
  - `TranslationMulti.lean`: the same with several criteria per noun
    (copredication), `validM_iff`.
  - `Copredication.lean`: the books for two.
  - `Criteria.lean`: Gotham's examples, passengers, double
    distinctness, and transitivity.
  - `DotSetoid.lean`: no setoid counts copredicated books.

## 10. Glossary

- **Predicate:** a property of individuals, such as man(x).
- **Type:** a kind of thing; "x : Man" says x is of type Man.
- **Model:** one possible situation, with its individuals and which
  properties hold of them.
- **Valid:** true in every model where the premises are true.
- **Countermodel:** a model where the premises hold and the conclusion
  fails. One countermodel shows an inference is not valid.
- **Injective:** one-to-one; different inputs go to different outputs.
- **Identity criterion:** a noun's rule for when two things count as the
  same.
- **Copredication:** two predicates on one noun that need different
  aspects, as in "picked up (physical) and mastered (text) the book".
- **Dot type:** an MTT type for nouns with two aspects, such as
  Physical • Informational.
- **Subsective adjective:** a "leading N" is an N, but not necessarily a
  leading anything else.
- **Fragment:** the precisely defined part of language a theorem covers.
