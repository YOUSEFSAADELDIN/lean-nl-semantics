# Paper A: literature notes

What the papers read so far say that bears on Paper A (nouns as types
against nouns as predicates), with page or example numbers, and how each
relates to the repository's results (`EndToEnd/Encodings/README.md`).
Read in full: the papers below unless an entry says otherwise; of
books, the chapters and pages each entry names.

## Gotham (2017), "Composing criteria of individuation in copredication", Journal of Semantics 34: 333-371

- **The data.** "Three books are heavy" counts physically, "three books
  are informative" informationally, and copredication ("three
  informative books are heavy", "John picked up and mastered three
  books") needs books distinct both ways (pp. 334, 345, 351).
- **His account.** Predicates contribute individuation relations (PHYS,
  INFO), and determiners use them to require the counted plurality to
  be non-compressible (Definition 1, p. 339; pp. 341-353). PHYS is not
  an equivalence relation, only transitive and symmetric (n. 7).
- **The argument we use as I1** (§3.3.2, ex. 100, p. 353): "John picked
  up three books. John mastered every book. ⇒ John mastered three
  books" is *invalid* (three copies of *The Language Instinct*). (103)
  is the control: "...defaced every book ⇒ defaced three books" is
  *valid*, since both verbs individuate physically. Ex. (105): "John
  read every book" is ambiguous, which he treats as two verbs.
- **Asher (2011), via Gotham §4.1** (pp. 355-361). Dot objects are
  counted relative to one constituent type, and the domain of
  quantification is relativized to a criterion (Asher 2011: 157-9).
  The anthology case is a single volume containing several novellas
  (Asher 2011: 146-7; Gotham's Figs. 1, 3 and 5). Gotham argues TCL is
  too permissive for "picked up and mastered three books" (pp. 359-361).
- **Against Chatzikyriakidis & Luo (2015)** (§4.3, pp. 366-369, n. 34).
  Their system counts elements of the type `Book`, so it makes (100)
  valid, and with the extra axioms of their Appendix A it also makes
  (160) ("...⇒ John mastered three informational objects") valid. Both
  are wrong. Gotham notes their entailments (122)-(123) for
  copredication are right, but only because double distinctness is
  predicted everywhere.

## Chatzikyriakidis & Luo (2015), "Individuation criteria, dot-types and copredication: a view from modern type theories", MoL 14: 39-50

- "John picked up three books" counts physical objects, "mastered" counts
  informational ones, and "picked up and mastered three books" needs
  both (p. 39, exx. 2-4).
- Their Coq check (p. 45, Appendix A, p. 49): `Three A P` is three
  pairwise distinct elements of `A`. To derive "three physical
  objects" and "three informational objects" from "three books" they
  add the axioms `forall x y : Book, x <> y -> x <> y :> Phy` (and the
  same for `Info`). Footnote 9 notes these hold only "if c is
  injective".
- **Relation to our results.** That axiom is the injectivity of the
  embeddings `Book → Phy` and `Book → Info`. `Equivalence.lean`'s
  `valid_iff` shows that with injective embeddings, nouns as types
  validate exactly what nouns as predicates do, and
  `not_valid_without_injectivity` shows that without it they part. So
  the axiom that gives Chatzikyriakidis & Luo double distinctness is the
  condition under which their account collapses to the predicate one,
  and with it Gotham's (160).
- They cite Gotham's evidence that double distinctness is not a
  cancellable implicature: "John picked up and mastered three books,
  but he didn't pick up three books" and three similar sentences, their
  (18)-(21), from Gotham (2012). These are the judgments Liebesman &
  Magidor (2026, below) dispute for related sentences.
- n. 9 justifies the axiom: "For the atomic types like Book and PHY, the
  equality on a subtype coincides with that of the supertype". They add
  the same axiom for `Info`. Both together say two distinct books are
  never two copies of one text and never two texts in one volume, so the
  scenarios that separate the criteria cannot arise.
- §4 (newspaper, linear dot-types) is not relevant to Paper A.
- Rechecked against the 12-page PDF supplied (October 2026): the points
  above stand.

## Chatzikyriakidis & Luo (2018), "Identity criteria of common nouns and dot-types for copredication", Oslo Studies in Language 10(2): 121-141

- **Their answer to the above.** Common nouns are setoids (A, =): a type
  with an identity criterion (pp. 124, 127-128, ex. 10). n. 1 says the
  2015 paper "did not realise the necessity of considering identity
  criteria".
- **In usual cases criteria are inherited and can be ignored**
  (Man ≤ Human with =_M the restriction of =_H; "sub-setoid", p. 130).
  Counting then agrees (ex. 24). This is the informal counterpart of
  `validI_iff` (counting by the individuals' identity, types and
  predicates agree) and of `countBy_of_injective`.
- **The verb's domain sets the criterion** (pp. 131-133, exx. 37-43):
  `Three(Book, Phy, pick up)` counts by =_p, `Three(Book, Info, master)`
  by =_i. That is our M encoding (`Copredication.lean`, `Counting.lean`).
  With one lexical entry and the verb choosing (`VerbCriteria.lean`),
  the translation theorem still holds (`validV_iff`). Adjectives have a
  say too ((48)-(54)), and "how the identity criteria are decided are a
  little bit more complicated" (p. 136). They give no general rule; our
  reconstruction (the aspects at which the variable is used in
  restrictor and scope) gives each of their examples.
- **Dot-setoids for copredication** (§4.2, p. 134): ⟨a1,b1⟩ = ⟨a2,b2⟩ iff
  a1 =_A a2 ∨ b1 =_B b2, so `Three` over it gives double distinctness
  (ex. 47). p. 135 says "Our definition does result in an equivalence
  relation". **Checked: it does not** (`Criteria.lean`,
  `dotSame_not_transitive`). With x = (volume 1, C&P), y = (volume 2,
  C&P) and z = (volume 2, NfU), x and y agree informationally, y and z
  physically, and x and z in neither. It is transitive if each volume
  has one text (`dotSame_trans_of`). Their `Three` uses only pairwise
  distinctness, which is exactly distinctness in both (`atLeastDot_iff`),
  so their predictions are those of double distinctness.
- **No equivalence relation would do** (`DotSetoid.lean`). Some
  equivalence relation gives double distinctness by their (32) exactly
  when "same volume or same text" is transitive on the books at hand
  (`exists_setoid_iff`). In the library above none does (`no_setoid`).
  So, given n. 4, p. 135's "as long as it is an equivalence relation,
  it would do" cannot be met. Gotham (2017: 338-339, (11), (14)) uses
  two relations, PHYS and INFO, "transitive and symmetric" each, and
  never claims their union is an equivalence.
- **The anthology case** (n. 4, p. 123): they adopt Asher's and Gotham's
  view that physically identical books can be informationally
  different, while saying they "incline to believe" otherwise. That
  inclination is our `OneTextPerVolume` postulate, under which I2
  becomes valid (`M_I2_valid_of`).
- Modified CNs as Σ-types inherit the criterion (exx. 51-59).

## Luo (2012), "Common nouns as types", LACL 2012, LNCS 7351: 173-185

- **Why CNs are types:** CNs have criteria of identity (Geach), and in
  constructive mathematics a type comes with its own equality (§3,
  pp. 176-180).
- **The passenger example** (Gupta), p. 177: "EasyJet has transported 1
  million passengers in 2010" does not imply "...1 million persons",
  because one person on several journeys is several passengers.
  `Passenger[T] = Σp:Person. Journey[T](p)` (p. 178). This is a
  non-injective embedding of a noun's type into the individuals
  (passengers into persons), counted by the type's own equality. It is
  a second individuation case besides books, not yet in the repository.
- **Proof irrelevance** is needed for Σ-types to give modified CNs the
  inherited criterion (§4, pp. 180-181). Lean's `Prop` is
  proof-irrelevant, so our subtypes `{x // P x}` have it.
- GQs in MTT have type ΠA:CN.(A → Prop) → Prop, unlike the symmetric
  Montague GQ (p. 183). Our typed determiners keep a restrictor `C` on
  the type, so they cover both.

## Chatzikyriakidis & Luo (2017), "On the interpretation of common nouns: types versus predicates", in Modern Perspectives in Type-Theoretical Semantics, Springer SLAP 98: 43-70

- **Their survey** (§2.2) covers four options: CNs as predicates
  (Montague), as types (MTT), as predicates in a dependent type theory
  (DTS: Bekki; Tanaka et al.), and as both (Retoré).
- **Their argument against predicates** (pp. 47-48): with subtypes Phy
  and Info of e and `book : Phy•Info → t`, "heavy book" needs Phy ≤
  Phy•Info, the wrong direction. **Checked** (`Modifiers.lean`): the
  argument types `heavy : (Phy → t) → (Phy → t)` as a modifier of the
  noun predicate. Said of the noun's variable instead, as MTT's
  `Σx : Book. heavy(x)` does, the sorted encoding needs only
  Phy•Info ≤ Phy, which MTT assumes, and accepts "John picked up and
  mastered every heavy book" (`wt_sorts_heavy_book`). Our P avoids this by having no sorts
  at all, one domain. The cost is that it cannot state selectional
  restrictions ("#the television ate the cake", p. 49). Phase 5
  (`Selection.lean`) tests it: well-formedness depends only on which
  argument types a noun's type fits, so a many-sorted predicate
  lexicon (Retoré's option (2)) accepts exactly the sentences a
  type-per-noun lexicon accepts. The argument holds against one-domain
  predicates only.
- **Their argument against "both"** (p. 51): it needs (*) "x : Man iff
  man(x)", which cannot be stipulated without making type checking
  undecidable. `IsA` and `Equivalence.lean`'s `shadow`/`lift` relate the
  two readings in the metatheory, as a theorem about models, not as a
  rule of the object theory, so this objection does not apply to them.
  **Checked** (`TypeCheck.lean`): type checking in the fragment is
  decidable, by a checker proved correct (`check_iff`), and (*) holds
  between models (`both_shadow`, `both_lift`). Their claim that (*) as
  a typing rule makes typing undecidable is not checked.
- **Predicational forms** `p_A`, `NOT`, `P_A` for "John is (not) a man"
  (§3, Coq in §4). Our `IsA e x` is a predicational form of the
  judgement x : A, defined through the embedding.
- **Proof irrelevance** again (pp. 49-50). Indexed types for gradable and
  temporal nouns (§5) are not relevant to Paper A.

## Asher (2011), *Lexical Meaning in Context: A Web of Words*, CUP, ch. 5 (pp. 146-159 read)

- **Relative identity for books** (p. 147, ex. 5.37): two copies of one
  text are b1 =_i b2 and b1 ≠_p b2. Read mereologically, they would be
  two absolutely distinct objects. That gives ten books for a shelf of
  Jane Austen's works, which he rejects.
- **Aspects, not parts** (pp. 149-150). We count "thick individuals",
  objects under an aspect. "Several physically distinct books [can]
  have the same informational aspect" (p. 149). When counting objects of
  • type "we must choose one of these to guide counting and
  individuation. Thus, predication is constitutive of the domain of
  quantification" (p. 150). That is the verb-selects-the-criterion view
  our M encodes, earlier than Chatzikyriakidis & Luo (2018).
- **One criterion at a time** (p. 157). "We can count books either as
  informational or as physical objects (though not coherently as
  both)." Gotham (2017) argues this is too weak for "picked up and
  mastered three books", which needs both. Our `AtLeastBoth`
  (`Criteria.lean`) is Gotham's and Chatzikyriakidis & Luo's double
  distinctness, not Asher's.
- **The anthology** (p. 157, Figs. 5.6-5.7): one volume holding Jane
  Austen's seven novels, plus three copies of the Bible, gives four
  books by the physical criterion and eight by the informational one.
  That is our I2 countermodel. (5.44) "*The Best of Thomas Hardy* is
  three books in one" (p. 159) is the same case in one sentence.
  Footnote 9 (p. 146) says physically identical books "of course" have
  the same informational content. Read with p. 157, that has to mean a
  volume's whole content (the collected works) counted as one
  informational object, so it is not our `OneTextPerVolume`.
- **Mid-discourse switching** (p. 159, ex. 5.43): "...thus there are ten
  books on the shelf. Fred has read Emma, the Bible, and Formal
  Philosophy, that is, three books. Yet Fred has read all of the books
  on the shelf."
- **Judges** (p. 159): five judgeships, filled by four people because
  John fills two. "There are five judges" is true, "five people" false.
  That is another non-injective case, like Luo's passengers.

## Bekki (2014), "Representing anaphora with dependent types", LACL 2014, LNCS 8535: 14-29

- **Dependent Type Semantics (DTS)** is Martin-Löf type theory with Π, Σ,
  equality and ℕ, plus an @-operator for anaphora and presupposition
  triggers (§3). Nouns are *predicates* over one type of entities `e`:
  "a man entered" is `(Σu:(Σx:e)M(x))E(π₁u)` (n. 8, ex. 12). The other
  style, `(Σx:M)L(x)` with the noun as a type, is set aside to avoid
  making nominal modifiers polymorphic (n. 8, citing Fox & Lappin).
- **Anaphora resolution is proof search** (Definition 2): an @-term is
  replaced by a proof term built from the context, for example
  `π₁π₁π₂(c)` for the donkey (§4, ex. 18).
- **Relation to Paper A.** This is the third option of Chatzikyriakidis &
  Luo's (2017) survey: nouns as predicates in a dependent type theory.
  It matters for Phase 1b. Our M avoids F's stipulated functions by
  projecting Σ-typed premises, and DTS does the same with nouns as
  predicates. So the Section 3 saving is owed to dependent types, not
  to nouns as types (corrected in `EndToEnd/Encodings/README.md`).
  Chatzikyriakidis & Luo (2017: 50-51) argue DTS keeps the predicate
  view's trouble with subtyping (Phy, Info and "heavy book"). Paper A
  does not test subtyping between sorts.

## Tanaka, Mineshima & Bekki (2015), "Resolving modal anaphora in Dependent Type Semantics", JSAI-isAI 2014 Workshops, LNAI 9067: 83-98

- DTS extended with explicit quantification over worlds for modal
  subordination ("A wolf might enter. It would growl.").
- Nouns are again predicates, now world-indexed (`wolf_w x`, entities
  `E_w`; §4).
- **Bridging** (ex. 12): "John has a house. The door is blue." The axiom
  `f : Πx:E. house x → Σy:E. door y ∧ have(x,y)` is projected to find the
  door. That is the same pattern as Phase 1b's "every report has a cover
  page" in M, here with predicates.
- Modality was outside Paper A's fragment until
  `FullAbstractionIntensional.lean`, which, like DTS here, indexes nouns
  by worlds (there with types and criteria per world).

## Retoré (2013), "A type theoretical framework for natural language semantics: the Montagovian generative lexicon", HAL hal-00779214v2 (preprint); published as "The Montagovian generative lexicon ΛTyn", TYPES 2013, LIPIcs 26 (2014)

The paper Chatzikyriakidis & Luo (2017) cite for the view that nouns are
both types and predicates. Page numbers below are the preprint's.

- **ΛTyn** (§2.3, pp. 8-9) is a many-sorted higher-order logic in Girard's
  system F. It has base types e₁, ..., eₙ for sorts, plus t. Each word
  has a principal λ-term and optional λ-terms, each marked rigid or
  flexible, which do the coercions (§2.4, Fig. 3).
- **Five options for the base types** (§2.2, p. 7): (1) one type e;
  (2) a small ontology (Asher's position); (3) classifiers (Mery &
  Retoré); (4) a type per common noun (Luo); (5) a type per formula. For
  each type τ "there should be a corresponding predicate τ̂ : e → t
  which recognises τ entities among entities of a larger type"
  (pp. 7-8), with the presupposition P(ι(P)), or ι(τ̂) : τ (n. 10).
- **That is the "both" view**, and it is our construction. τ̂ over a top
  type e is our `IsA e` over the individuals. Reading a typed model as
  its predicates (`TModel.shadow`) and a predicate as its type
  (`PModel.lift`) are the two directions Retoré needs. §5.3 (p. 20)
  leaves open "the relation ... between type judgements x : T that, as
  linguistic presuppositions, cannot be denied and predicates T̂(x)
  that can be denied". `valid_iff` and `validI_iff` answer it for a
  fragment, as a theorem about models: stating a noun by its type or
  by its recognising predicate validates the same entailments, provided
  counting is by the individuals.
- **Copredication** (Term 1, p. 9; §3.1) is a polymorphic AND applying P
  and Q to f(x) and g(x) for optional terms f : ξ → α and g : ξ → β
  ("Liverpool is vast and voted"). Rigid terms block infelicitous
  copredication ("#Liverpool voted and won").
- **Counting** (§4.2, p. 18): a cardinality operator ||_|| : Πα.(α → t) →
  ℕ counts at whatever type it is given. With coercions f : ξ → α,
  counting a property at ξ or at α can differ. That is the individuation
  question, but the paper does not raise it, and its copredication
  examples do not count.
- **Determiners** are Hilbert ε, τ (and ι, η) terms, generic elements
  rather than generalized quantifiers (§4.1). Outside Paper A's fragment.
- **Comparison** (§5.2, pp. 19-20): Asher's, Luo's and Retoré's logical
  forms "are quite similar". The differences are in the metalogic and
  in whether coercions are word-driven or type-driven.

## Mery & Retoré (2013), "Semantic types, lexical sorts and classifiers", arXiv:1312.3168 (preprint)

- **Not the paper Chatzikyriakidis & Luo (2017) cite** for "both types and
  predicates". That is Retoré (2013), above.
- **A many-sorted Montague semantics** (TY_n) with lexical modifiers:
  coercions such as `t₃ : T → Pl` turning a town into a place, attached
  to words, for selection restrictions and copredication ("Birmingham
  is a huge place and voted Labour", ex. 5, with a polymorphic
  conjunction).
- **The paper's question is which sorts to use.** Its answer is the
  classifier systems of classifier languages (Japanese, Chinese, sign
  languages), which are used for counting (§3).
- **Relation to Paper A.** It is a fourth kind of encoding: nouns as
  predicates over many sorts, with coercions, which our P (one sort)
  and M (types with embeddings) bracket but do not test. Classifiers as
  counting units connect to Luo's (2012, §5) proposal that a classifier
  or measure word supplies the identity criterion.

## Chakrabarty & Huang (2012), "Testing coverage functions", ICALP 2012 (arXiv:1205.1587); journal version "Recognizing coverage functions", SIAM J. Discrete Math. 29(3), 2015

Not read in full: the PDF could not be fetched from this environment.
What follows is from the abstract and search results, and must be
checked against the paper before citing.

- A coverage function gives each set T of indices the total weight of
  the union of sets A_i, i ∈ T. Equivalently f(T) = Σ w(S) over S that
  meet T, where w is the W-transform of f.
- Theorem 1.1 (as cited): f is a coverage function iff all its
  W-coefficients are nonnegative; the W-coefficients are unique.
- For Paper A: a noun's counting function is exactly such an f, with
  the individuals as indices and the units as the weighted sets
  (`CountingLaws.representation`). Our uniqueness proof (`eq_of_meets`)
  reproves their uniqueness in our setting. Cite them for both.

## Rothstein (2017), *Semantics for Counting and Measuring*, Cambridge University Press (Key Topics in Semantics and Pragmatics)

Read: ch. 4 in full (pp. 82-116); ch. 5, pp. 117-122. Searched the
whole book for identity criteria, passengers, copredication, dot types
and Gupta: none are discussed.

- **Counting is relative to a context k of disjoint atoms** (§4.4).
  Count nouns are `COUNT_k(N_root) = {<a,k> : a ∈ N_root ∩ k}` (36),
  "contextual disjointness is a condition on k" (p. 109), and a
  numeral counts the k-atoms below a plurality, `|π1(x)|_k = 3` (41,
  p. 112).
- **What counts as one is context-dependent**: four farmers' fencing is
  one, two or four fences (32, pp. 107-108); the places you visited
  (p. 108).
- **Landman (2011a, 2016), as reported** (p. 113): count predicates have
  a disjoint base, mass predicates an overlapping one; "neat" mass nouns
  like *furniture* overlap vertically (a table, six chairs and the
  suite each count as one item). Now read directly: see the Landman
  entry below.
- **Bale & Barner (2009), as reported** (ch. 5, pp. 120-121): count nouns
  and object mass nouns denote "individuated" semi-lattices, generated
  by non-overlapping individuals, and are compared by cardinality.

For Paper A:

- The shared disjointness condition is our "never splits" law
  (`CountingLaws.noSplit_iff_disjoint`, with `single_iff`): units
  pairwise disjoint iff no individual is counted twice.
- Luo's passengers and copredicated books break it when the
  individuals are people or books, so on these theories the atoms must
  be other entities (journeys, or Gotham's composite books). Our
  translation theorems say such a richer domain always exists.
- Double distinctness is not counting in any one context k over the
  books (it is not even submodular, `not_single`), but it is the least
  count over a family of contexts, each with disjoint atoms
  (`TwoCriteria.count2_eq_min`).
- Our criterion plays the role of her context k; we hold it fixed, she
  studies how it varies (fences). Combining the two is open.
- The method she reports (Barner & Snedeker's "Who has more N?") is a
  model for testing our prediction (`paper/A-prediction.md`).

## Landman (2020), *Iceberg Semantics for Mass Nouns and Count Nouns: A New Framework for Boolean Semantics*, Springer (Studies in Linguistics and Philosophy 105)

Read from the book (chapter PDFs supplied October 2026): ch. 5 in full
(pp. 141-160); §6.1 (pp. 161-172); ch. 7, pp. 189-200 and 205-216;
§11.3 (pp. 350-361). Page numbers are the book's printed ones, checked
against the running heads. Searched the whole book for copredication,
Gotham, Liebesman, dot types, identity criteria, individuation and
passengers: none are discussed (only "individuation" in titles in the
references). This entry replaces earlier secondhand notes taken from a
third-party formalization. Those notes were right on the definitions
but had the section numbers slightly off.

- **I-sets** (§5.1, p. 143): an NP denotes a pair ⟨body, base⟩ with
  body ⊆ *base (the base generates the body under sum). For count
  nouns, "the base is the distribution set, a disjoint set in terms of
  which the body is counted" (ch. 5 abstract, p. 141).
- **Cardinality** (§5.2, p. 144): D_Z(x) = (x] ∩ Z "if Z is disjoint",
  undefined otherwise; card_Z(x) = |D_Z(x)|, "the cardinality of the set
  of Z-parts of x". Counting relative to an overlapping set is a
  presupposition failure (p. 145).
- **Head principle** (§5.3, pp. 145-146): base(NP) = (body(NP)] ∩
  base(head), so a disjoint head base stays disjoint (lemma, p. 146) and
  complex NPs inherit count/mass from their head. Numerals, adjectives
  and *most* then count by the base (§§5.4-5.5, pp. 147-160). "The
  assumption of a disjoint base ... is the minimal assumption we have to
  make" (p. 160).
- **Count, mass, neat, mess** (§6.1.2, pp. 165-167): X is count iff
  base(X) is disjoint; mass iff (non-null and) not count; neat iff
  base(X) is atomistic and its set of atoms is disjoint; mess otherwise.
  "Count i-sets are atomistic i-sets whose base is disjoint; neat i-sets
  are atomistic i-sets whose set of base-atoms is disjoint" (p. 166).
  The distinction is "horizontal": it concerns overlap among base
  elements, not atoms below them (p. 164).
- **Disjointness is an imperative, not a law** (§6.1.4, pp. 169-172).
  Count nouns are interpreted at "internal" indices, where the base is
  disjoint. Overlap is first removed by contextual restriction, which
  is "pervasive" (p. 171). In "a context of counting" where restriction
  fails, speakers resort to "pragmagic" (p. 171), changing the ontology.
  Overlapping bases in counting (body parts, p. 172) are "a puzzler".
- **Conceptually vs contextually disjoint** (§6.1.4, p. 169; §7.2,
  pp. 196-200, after Sutton & Filip 2016 and Rothstein 2010). A noun is
  conceptually disjoint if the union of its bases over all internal
  indices is disjoint (*cat*), and contextually disjoint otherwise
  (*fence*). He argues *furniture*, *pottery* and *jewelry* are only
  contextually disjoint, against Rothstein (pp. 198-200).
- **Neat mass nouns count by a contextual choice of disjoint set**
  (§7.1, pp. 189-190; §7.4.2, pp. 208-209; §7.4.3, pp. 214-216). The
  pottery example has base {teapot, cup, saucer, fruit bowl, cup and
  saucer, teaset}: overlapping, so mass, but its atoms are disjoint, so
  neat. The classifier *stuk(s)* and count comparison use stuk_w(P), a
  disjoint set chosen in context (p. 208). For *pottery*, three
  "maximally disjoint subsets of base(POTTERY_w)" are "naturally
  available": the four pieces, {teapot, cup and saucer, fruit bowl}, or
  {teaset, fruit bowl} (p. 209). "Most pottery costs more than 5 euros"
  changes truth value with that choice (p. 216).
- **Double counting via indexing, at a cost** (§11.3, pp. 350-361).
  *Doppelgänger* (pp. 351-354) is a local repair: two roads sharing a
  stretch are counted as two by pretending the shared part is two
  indiscernible parts. *Indexing* (pp. 354-361) pairs each listed item
  with its own index and counts the indices. It "is used precisely when
  we want to allow double counting" (p. 358), it is what Rothstein and
  Mountain semantics build into every count noun (p. 355), and it "comes
  with a processing cost" when it changes lexical meanings (p. 360).
  Evidence cited: "The Bordurians and the Szohôdians are two groups of
  Europeans" is degraded when Szohôd is inside Borduria (pp. 358-359),
  and so is counting cubes that include sub-cubes (p. 360). No
  experimental data are reported.

For Paper A:

- Base elements are our units and card_Z is our count for a single
  criterion. A disjoint base is our "never splits"
  (`CountingLaws.noSplit_iff_disjoint`). A base element can be a sum of
  several individuals (the teaset), which is our "merges". So Landman's
  count nouns (disjoint base) are the never-splits column of the
  typology, with the base atoms as individuals. Neat mass nouns have
  overlapping bases, but each count uses one maximal disjoint subset
  (p. 209): one never-splitting criterion per context, chosen from a
  family.
- Copredicated counting (`TwoCriteria.count2_eq_min`) also involves a
  family of never-splitting criteria, the mixtures, but takes the
  *least* count over the family, not one contextual choice. Landman's
  framework has no counterpart of taking a minimum. Rothstein's doesn't
  either.
- The submodularity law (`count_submod`) holds for every count in his
  framework with a fixed disjoint base, and also for each choice of
  stuk_w, since each is one criterion. It can fail only where the
  choice varies between the counts compared. That is his pragmagic or
  contextual shift, and the protocol must hold it fixed
  (`A-prediction.md`).
- Indexing makes overlapping items into disjoint atoms. This is our
  Montague cell (units = individuals) applied to a richer domain, which
  our translation theorems say always exists. His claim that it is
  costly gives the experiment a second measure (difficulty or response
  time) besides the count.

## Liebesman & Magidor (2026), "What copredication can(not) teach us", *Theoretical Linguistics* (advance online), doi:10.1515/tl-2026-2002

Read: §§2.3-2.3.1, 3.1 and 3.2.3 (pp. 14-36 of the advance version).

- **Target.** "Dual Nature" accounts (Asher 2011, Gotham 2017, and in
  n. 23 Chatzikyriakidis & Luo), which give 'book' one reading and let
  predicates supply criteria of individuation.
- **One sentence, two counts** (pp. 19-20, exx. (33)-(36)). "Alice
  picked up three books" can count *i-books*: a bookseller collecting
  100 copies each of four new titles says "I will pick up three books,
  and you can pick up the fourth one tomorrow". "Three books are by
  Tolstoy" can count volumes: whether a shelf needs reinforcing. On
  their view the predicate does not fix the criterion; context can
  override it.
- **The counterexample** (p. 21, ex. (37); repeated p. 34, (67)). The
  bookstore holds ten wrinkled copies of *War and Peace* and two of
  *Wuthering Heights*. "# Exactly one wrinkled book is by Tolstoy" has,
  "to our ears", no true reading. Asher and Gotham predict it true:
  Gotham because no two of the ten copies are distinct in both ways.
- **Property Versatility** (§3.1, pp. 22-26): 'book' is univocal and
  ranges, by contextual domain restriction, over p-books or over
  i-books. Properties like *by Tolstoy* or *memorized* are "versatile",
  true of both kinds. Counting is ordinary counting over the restricted
  domain (§3.2.3, pp. 32-36). Each reading of (37) is false: ten
  p-books, or zero wrinkled i-books.
- **Gotham's (2022) reply** (p. 34, ex. (68)): "Granger memorized three
  yellow books" has, Gotham says, no reading true of three copies of
  one text. They answer that memorizing a p-book may require learning
  its text for the first time (p. 35), and n. 38 doubts the judgment.
- **Their overall claim** (p. 34): discussions have asked how to
  generate double-distinctness truth conditions "without paying
  sufficient attention to the question of whether these sentences
  really have" them.

For Paper A:

- **Do their cases already count as evidence?** For or against
  `count2` as the meaning of copredicated numerals: yes, as
  introspective judgments, contested by Gotham (2022) and accepted by
  Sutton (2024, below) for neutral contexts. `count2` gives (37) the
  count 1, so if their judgment is right, double distinctness is wrong
  for modifier-plus-predicate copredication. For or against our law:
  no. The law is about four counts by one speaker in one context, and
  their examples give one count each. Their bookstore cases show
  something the protocol must control: the criterion can switch from
  one sentence to the next, and pooled answers from switching speakers
  can break the law even when each speaker counts by one criterion
  (`A-prediction.md`, "Reading switches").
- **Should the protocol test Property Versatility?** Yes, as the main
  alternative. With a fixed reading, PV counts by one criterion (volumes
  or texts), so it obeys the law (`count_submod`). It predicts that each
  speaker's four answers fit the volume column or the text column of the
  table, never the "both" column. Their (37) also goes in as a separate
  item, because there `count2` and PV disagree on a single count.
- The theorems are unaffected: they are claims about what each account
  predicts, not about which is right. What is at stake is the
  linguistic reading of `count2` (`TwoCriteria.lean`) as the meaning of
  "picked up and mastered three books". The paper should present it as
  the Gotham / C&L hypothesis under test.

## Liebesman & Magidor (2017), "Copredication and property inheritance"

Read: the PDF supplied (a pre-publication version; page numbers below
are that version's), pp. 1-6. The published venue is probably
*Philosophical Issues* 27 (2017), from memory, not from the PDF: check it
before citing.

- 'book' is univocal. Its p-book and i-book readings come from
  contextual domain restriction (Stanley & Szabó 2000), not ambiguity
  (pp. 2-4).
- **A constraint on double counting** (p. 4): "Four colours are on the
  canvas" (three shades of red, plus red) and "Six wooden things are in
  the room" have no true reading. "Counting both a determinable and its
  determinate is ruled out due to some restriction on double counting,
  as is counting both an object and its parts". They leave open "what
  the content of the constraint is" and "how it can be overridden"
  (n. 5 cites Kratzer and Liebesman).
- For Paper A: their constraint is the informal counterpart of
  disjointness, our "never splits". Landman (2020, above) gives a
  formal version: disjointness is the default, and double counting
  needs costly indexing. Paper A's typology says what follows when the
  constraint is dropped (splitting nouns, `CountingLaws.single_iff`).

## Liebesman & Magidor (2019), "Copredication, counting, and criteria of individuation: a response to Gotham", *Journal of Semantics* 36(3): 549-561

Not read: no copy available. To be cited as the start of the exchange
that Gotham (2022) answers and Liebesman & Magidor (2026, above)
continues.

## Sutton (2024), "Individuation criteria and copredication: modification in context", *Proceedings of Sinn und Bedeutung* 28: 876-894

- **Main question** (p. 877): what mechanisms "underpin when
  double-distinctness readings arise, and when they do not?"
- **Account** (pp. 877, 879): a polysemous noun lexically introduces a
  QUD, "How are we individuating books?", with answers physical,
  informational, or both. Modifiers answer whichever QUD is highest on
  the stack. A contextual QUD (which pile of books?) can take priority,
  and then a modifier restricts the domain instead of the criterion.
  Counting needs a quantized set relative to context (Sutton & Filip
  2020; p. 879).
- **Predictions** (p. 877): (1) double distinctness in neutral contexts;
  (2) not when a more prominent QUD makes a modifier a domain
  restrictor; (3) further modifiers can bring it back. *Memorised the
  first page of* brings it back (ex. (10)); *tore out the first page
  of* does not (ex. (11); pp. 878, 890).
- **Word order matters** (p. 878): in the display-pile context, "three
  damaged, insightful books" allows informational duplicates, but
  "three damaged books are insightful", "three insightful, damaged
  books" and "three damaged and insightful books" resist that reading
  (exx. (6)-(9)).
- She also finds the anthology reading (two texts in one volume) "at the
  very least highly contextually restricted" (p. 877, n. 1), siding
  with Chatzikyriakidis & Luo (2018, n. 4).

For Paper A (relevant to the experiment's design):

- In our terms, her lexical QUD picks the family of criteria: {volume},
  {text}, or {volume, text} (`count2`). Her prediction 1 says neutral
  contexts give the two-criteria family, which breaks the law in our
  scenario. Her prediction 2 says a prominent QUD gives one criterion,
  which obeys it. So her account predicts that context *switches the
  law on and off*. That is a sharper test than a single count. The
  protocol gets a neutral and a QUD condition.
- Her word-order and modifier effects mean every item must be matched
  in structure across conditions. Her *memorise* / *tear out* pair
  gives a within-item manipulation of the predicted criterion.
- Her n. 1 bears on our scenario, which relies on the anthology (B and
  C are two books in one volume). The protocol already records which
  reading participants report.

## Bahramian, Nematollahi & Sabry (2017), "Copredication in homotopy type theory", manuscript (PDF dated 7 November 2017; the acknowledgements mention TYPES post-proceedings reviewers)

- **Model** (§6.4, pp. 13-16): a count noun is an identity type between
  "prototypes", ⟦Book⟧ = (BookPrototype = PhysicalPrototype) =
  (BookPrototype = InformationalPrototype). A book's physical and
  informational aspects ("b qua physical", "b qua informational") are
  composite paths, (21)-(22). Formalized in Agda.
- **Counting** (§6.4, p. 17): "picked up and mastered three books" ((24c))
  requires three books pairwise distinct qua physical *and* pairwise
  distinct qua informational: double distinctness, with distinctness
  taken in each aspect type.
- **Their puzzle** (§6.1, pp. 11-12): "Fred has five books" refutes each
  of the four single criteria (physical; informational; distinct in
  either; distinct in both), given the verbs that follow.
- They claim (§6.6, p. 19) that C&L (2015) and Bekki & Asher (2012) are
  equally adequate once existential closure is added. The advantage
  claimed is conceptual, with no subtyping.
- For Paper A: their predictions on counting are those of double
  distinctness, so `count2` models them and `not_single` and the
  submodularity law apply unchanged. Like Gotham, they never put one
  identity relation on Book, so our setoid impossibility
  (`DotSetoid.no_setoid`) does not bear on them. It bears on C&L (2018)
  only. A third proof-assistant formalization of copredication (after
  C&L's Coq and ours in Lean), worth citing as such.

## Graph theory: matchings and line graphs (the "matching function" check)

Not read in the original: Harary & Holzmann (1974), Trotter (1977) and
de Werra (1978) could not be fetched here. What follows separates what
is proved in this repository, what follows by short arguments given
here (not formalized), and what is only reported.

- **Proved here.** `count2` (`TwoCriteria.lean`) counts the largest set
  of things no two of which share a volume or a text. Take each thing
  as an edge from its volume to its text, in a bipartite multigraph.
  Then `count2` of a set of things is the size of a largest matching
  among them (by definition). The laws proved are subadditivity, the
  pairwise law (`MinCoverage.lean`) and the odd-cycle law
  (`OddCycle.lean`).
- **A short argument (not formalized).** When each individual has
  exactly one thing (`emb` a bijection), `count2(P)` is α(H[P]): the
  size of a largest set of pairwise non-adjacent vertices in the
  subgraph of H on P. Here H is the conflict graph (two things are
  adjacent if they share a volume or a text), which is the line graph
  of that multigraph. Conversely, every line graph of a bipartite
  multigraph arises this way: its two sides are the two criteria. So,
  in that case, a set function f is a `count2` function iff (a) f is
  α of the graph that f itself defines on pairs (x, y adjacent iff
  f({x, y}) = 1), and (b) that graph is the line graph of a bipartite
  multigraph.
- **Matching the laws to forbidden subgraphs.** The pairwise law (a set
  whose pairs all count 1 counts 1) holds for α of *every* graph. It is
  part of (a), not a counterpart of a forbidden subgraph. The odd-cycle
  laws exclude induced odd cycles of every length (`count2_cycle5`, f5
  is α of C5; every length in `ForbiddenLaws.count2_oddCycle`).
  Claw-freeness is a further law: if a thing conflicts with three
  others, two of those three conflict (`ForbiddenLaws.count2_claw`,
  from the hub argument). Diamonds *do*
  occur, from two copies of one text bound in one volume (parallel
  edges). Call two adjacent vertices *twins* if they have the same
  other neighbours. In the line graph of a bipartite multigraph, twins
  are either parallel edges, or two edges uv, uw where every edge at v
  is parallel to uv and every edge at w is parallel to uw (an edge at v
  must meet uw, and v, w are on the same side). Merging each class of
  twins into one vertex therefore gives the line graph of a simple
  bipartite graph. Conversely, blowing a vertex of a line graph up
  into twins is adding parallel edges. So (b) is equivalent to (b'):
  after merging twins, the graph is the line graph of a simple
  bipartite graph.
- **Reported, to check.** The line graphs of simple bipartite graphs
  are exactly the claw-free, diamond-free, odd-hole-free graphs
  (Harary & Holzmann 1974, as stated by you; not seen here). A
  secondary source found by search attributes to them the
  characterization of line graphs of *triangle-free* graphs as the
  claw- and diamond-free graphs. Adding "odd-hole-free" for bipartite
  graphs then follows by a short argument: a shortest odd cycle of
  length ≥ 5 is chordless, and its edges induce an odd hole in the line
  graph; conversely an odd hole in the line graph gives an odd cycle.
  Line graphs of bipartite graphs are perfect (König's edge-colouring
  theorem; standard). Trotter (1977, *Mathematical Programming* 12:
  255-259), as summarized by search results: a graph is "line perfect"
  (its line graph is perfect) iff it has no odd cycle longer than 3.
  de Werra (1978, *Mathematical Programming* 15: 236-238,
  doi:10.1007/BF01609025) exists; its content was not found.
- **What would follow.** If the Harary & Holzmann statement holds,
  `count2` functions with one thing per individual would be exactly the
  set functions satisfying (a) and (b'). By the points above, (b')
  means: no claw, no odd hole, and no diamond except from merged pairs.
  That would be an exact law-based characterization of this case. Its
  laws (claw, all odd holes) are now proved; the converse is not. The
  general
  case, where one individual can own several things (a plurality of
  copies counted as one individual), is a "matching number of a union
  of edge groups". In matroid terms that is the rank, in the
  intersection of two partition matroids, of a union of groups of
  elements. It remains open, and no source on it was found.

## What this means for Paper A

- I1 is Gotham's (100). M is Chatzikyriakidis & Luo's (2018) account. I2
  is Asher's anthology case. Credited in `EndToEnd/Encodings/README.md`
  and `Copredication.lean`.
- **Apparently new**, relative to the papers above:
  - `valid_iff` and `validI_iff`: a fragment-wide equivalence, with the
    exact condition.
  - `validC_iff` (`Translation.lean`): nouns as types with identity
    criteria (C&L 2018, one criterion per noun) and nouns as predicates
    over a domain with an identity relation and criteria (the shape of
    Gotham's and Asher's accounts) validate the same entailments, by a
    word-by-word translation that sends identity to "same individual".
    `validM_iff` (`TranslationMulti.lean`) extends it to nouns with
    several criteria, which covers copredicated numerals: with two
    criteria "at least n" is Gotham's non-compressibility by PHYS and by
    INFO. Other determiners under two criteria are our extension.
    Neither Gotham nor C&L state such a correspondence; Gotham's
    critique of C&L (2015) and C&L's (2018) reply compare them on
    examples.
  - `wt_iff_of_sameFit` and `wt_sorts_iff` (`Selection.lean`):
    well-formedness sees only which argument types a noun fits, so
    sorted predicates accept what MTT accepts. Retoré (2013, §5.2)
    calls Asher's, Luo's and his logical forms "quite similar"; this
    makes the point exact for selection, in the fragment.
  - The characterization (`CModel.agree_iff_kernel`): for nouns counting
    by any identity criterion, the encodings agree under all verb
    interpretations iff each criterion is the individuals' identity.
    Its two failure modes, splitting an individual and merging
    individuals, are Luo's passengers and Gotham's books. C&L (2018)'s
    "sub-setoid" remark (p. 130) is the informal sufficiency half; the
    necessity half is in none of the papers read here.
  - Full abstraction (`obsEq_iff`, `FullAbstraction.lean`): two
    interpretations of a noun with one criterion are indistinguishable
    by every sentence of the fragment in every context iff they have the
    same counting units with the same multiplicities; for nouns counting
    individuals, iff their extensions agree. None of these papers states
    what sentences can observe of a noun. With several criteria
    (`obsEqM_iff`, `FullAbstractionMulti.lean`), indistinguishable iff
    the same counts; and three books (two copies of one text, two texts
    in one volume) are counted as no single criterion of any kind can
    count them (`not_single`), since one-criterion counts are
    submodular. Gotham (2017) and C&L (2018) argue copredication needs
    both criteria from examples; this proves no single criterion can
    stand in for them, judged by sentences alone. With plurals
    (`obsEqP_iff`, `FullAbstractionPlural.lean`): collective numerals,
    definite plurals, collective verbs and "one of them", with a
    plurality of `N`s a set of the noun's own things counted by its
    criterion; indistinguishable still iff the same units. In
    intensional contexts (`obsEqW_iff`, `FullAbstractionIntensional.lean`):
    necessity and possible-worlds belief, with world-varying types and
    criteria; indistinguishable iff the same units at every world. A
    hyperintensional attitude separates necessarily coextensive nouns
    only by their symbol (`thinks_distinguishes`). Not checked against
    any MTT treatment of attitudes or hyperintensionality; none has
    been read for this project.
  - Laws of counting (`CountingLaws.lean`): count nouns with one
    criterion are exactly the integer coverage functions (the
    representation is Chakrabarty & Huang's, above); additive iff never
    merging, single iff never splitting, both iff Montague; a
    submodularity law that copredicated nouns can break. No linguistic
    use of coverage, belief or submodular functions for counting turned
    up in a search, nor in Rothstein (2017, above), which also does not
    discuss identity criteria or copredication. Neither does Landman
    (2020, searched in full). Their disjointness condition is our
    "never splits" law. Counting by two criteria is the least of the
    mixed single-criterion counts (`TwoCriteria.count2_eq_min`, König's
    theorem). Neither Rothstein nor Landman takes a least count over a
    family of criteria. Landman's neat mass nouns choose one member of
    such a family per context (p. 209).
    Not every minimum of coverage functions arises that way
    (`MinCoverage.not_pairwise_example`), and the two laws do not
    characterize the class (`OddCycle.two_laws_not_sufficient`). With
    one thing per individual, the class is the independence numbers of
    line graphs of bipartite multigraphs. That reduces it to a known
    graph class, if the Harary & Holzmann statement checks out (graph
    theory entry above). The general case is open.
  - The diagnosis that the injectivity axiom Chatzikyriakidis & Luo
    (2015) add is exactly that condition.
  - The FraCaS-scale comparison (Phases 1-3).
  - The transitivity problem above (checked), and its strengthening:
    no equivalence relation gives the dot-setoid counting once a text
    has two copies and a volume two texts (`exists_setoid_iff`,
    `no_setoid`). Their predictions survive; the claim that a setoid
    delivers them does not.
- **Added** (`Criteria.lean`): Gotham's (100) and (103) in his wording;
  Luo's passengers; double distinctness, shown to coincide with
  Chatzikyriakidis & Luo's dot-setoid `Three`; and the transitivity
  check.
- **Correction from the DTS papers, checked.** Phase 1b's saving (no
  stipulated functions) is owed to dependent types. D, the 11 Section 3
  problems with nouns as predicates and Σ-typed premises, needs no
  stipulated functions either, and the generic prover finds 9/11 of its
  answers against M's 7/11 (`EndToEnd/Encodings/README.md`, Phase 1b).
- **Retoré's open question is answered for the fragment.** He leaves
  open how type judgements x : T relate to their recognising predicates
  T̂(x) (§5.3). Paper A's equivalence theorems answer it for the
  fragment, so the paper can present them as that answer.
- **The empirical premise is contested.** Every novelty claim above
  about copredication is a claim about what accounts predict, and
  stands. Whether "picked up and mastered three books" has double
  distinctness truth conditions at all is disputed. Liebesman & Magidor
  (2017, 2019, 2026) say no, Gotham (2017, 2022) says yes, and Sutton
  (2024) says it depends on the QUD. The paper should present
  `count2` as the hypothesis the law tests, not as established
  meaning. The protocol (`A-prediction.md`) is designed to decide
  between these three positions.
- **Not yet read:** Gupta (1980); Cooper (2011), "Copredication,
  quantification and frames", LACL 2011, LNCS 6736: 64-79 (the PDF
  supplied was Chatzikyriakidis & Luo 2015 again). Of Asher (2011), only
  ch. 5, pp. 146-159. Also, cited by Liebesman & Magidor (2026):
  Gotham (2022), "Property inheritance, deferred reference and
  copredication", *Journal of Semantics* 39: 87-116; Liebesman &
  Magidor (2019, above); (2023), "Copredication and meaning transfer",
  *Journal of Semantics* 40: 69-91; (2025), *Property Versatility and
  Copredication*, OUP (ch. 9 §4 on double distinctness); Mery, Moot &
  Retoré (2019), "Solving the individuation and counting puzzle with
  λ-DRT and MGL". Graph theory: Harary & Holzmann (1974), Trotter
  (1977), de Werra (1978) (entry above).
