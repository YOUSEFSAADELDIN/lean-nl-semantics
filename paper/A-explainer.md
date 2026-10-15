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

**In one line:** in this fragment, nouns as types make a logical
difference only when a noun counts by its own identity criterion rather
than by individuals.

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
  FraCaS 29 ("leading businessmen"), needs nouns as types, because
  "leading" is a *subsective* adjective: a leading businessman is a
  businessman, but not necessarily a leading person.
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
  where the pipeline needed one per possessive. Dependent Type Semantics
  (Bekki 2014) does the same with nouns as predicates, so the credit
  goes to *dependent types*, not to nouns as types. The project is now
  checking this in Lean (the "D" encoding); the build was being fixed
  when this guide was written.

**So:** on FraCaS, the encoding matters mainly for one subsective
adjective (29) and one adjective that depends on its noun (215). The
interesting differences are outside FraCaS: the identity-criterion
cases in section 4.

**The one real cost of types is automation.** Generic automatic provers
find fewer proofs when nouns are types. The proofs exist; the provers
just search less well.

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

   Their counting only compares books in pairs, so their predictions
   are unaffected. The finding is real but small.

---

## 7. What is new, and what is not

| Not ours (cite it) | Ours |
|---|---|
| Nouns as types (Ranta 1994; Luo 2012) | The fragment-wide equivalence theorems, `valid_iff` and `validI_iff` |
| Identity criteria for nouns (Geach; Luo 2012) | Showing that the 2015 axiom is exactly the equivalence condition |
| The books argument (Gotham 2017, ex. 100) | The transitivity observation about the 2018 paper |
| Verbs choosing the counting criterion (Asher 2011; Chatzikyriakidis & Luo 2018) | The FraCaS-scale comparison (Phases 1–3) |
| The anthology and judges cases (Asher 2011); passengers (Luo 2012) | Machine-checked versions of all of the above |
| Recognising predicates for types (Retoré 2013), who leaves open how a type relates to its predicate | An answer to that open question, for the fragment |

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
> inferences, as long as you count by individuals. They differ only when
> a noun brings its own way of counting, like 'mastered three books'
> counting texts while 'picked up three books' counts copies. On the
> FraCaS benchmark that almost never comes up."

**Questions a professor may ask, with honest answers:**

- *"Isn't that obvious?"* For "every" and "some", nearly. The content is
  in counting: exactly which condition makes them agree, proved for a
  whole fragment, and showing that a published axiom is that condition.
- *"What's the fragment missing?"* Relations between two quantified
  nouns ("every student read some book"), "many" and "few", anaphora
  across sentences, and adjectives like "former" or "competent" that
  depend on the noun.
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
  - `Copredication.lean`: the books for two.
  - `Criteria.lean`: Gotham's examples, passengers, double
    distinctness, and transitivity.

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
