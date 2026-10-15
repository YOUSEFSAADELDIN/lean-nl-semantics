# Paper A: literature notes

What the papers read so far say that bears on Paper A (nouns as types
against nouns as predicates), with page or example numbers, and how each
relates to the repository's results (`EndToEnd/Encodings/README.md`).
Read in full: the nine papers below, and the relevant pages of Asher
(2011).

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
- §4 (newspaper, linear dot-types) is not relevant to Paper A.

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
  The paper should say so.
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
- Modality itself is outside Paper A's fragment.

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

## What this means for Paper A

- I1 is Gotham's (100). M is Chatzikyriakidis & Luo's (2018) account. I2
  is Asher's anthology case. Credited in `EndToEnd/Encodings/README.md`
  and `Copredication.lean`.
- **Apparently new**, relative to these five papers:
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
- **Not yet read:** Gupta (1980); Cooper (2011), "Copredication,
  quantification and frames", LACL 2011, LNCS 6736: 64-79 (the PDF
  supplied was Chatzikyriakidis & Luo 2015 again). Of Asher (2011), only
  ch. 5, pp. 146-159.
