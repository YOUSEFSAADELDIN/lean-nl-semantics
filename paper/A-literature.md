# Paper A: literature notes

What the papers read so far say that bears on Paper A (nouns as types
against nouns as predicates), with page or example numbers, and how each
relates to the repository's results (`EndToEnd/Encodings/README.md`).
Read in full: the five papers below. Cited only through them: Asher
(2011), whose relevant pages Gotham gives.

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
  relation". **To check:** a disjunction of two equivalence relations is
  not transitive in general. With x = (volume 1, C&P), y = (volume 2,
  C&P) and z = (volume 2, NfU), x and y agree informationally, y and z
  physically, and x and z in neither. Their `Three` only uses pairwise
  distinctness, so its predictions may not depend on transitivity.
  Not yet checked in Lean.
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
  Phy•Info, the wrong direction. Our P avoids this by having no sorts
  at all, one domain. The cost is that it cannot state selectional
  restrictions ("#the television ate the cake", p. 49), which Paper A
  does not test.
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

## What this means for Paper A

- I1 is Gotham's (100). M is Chatzikyriakidis & Luo's (2018) account. I2
  is Asher's anthology case. Credited in `EndToEnd/Encodings/README.md`
  and `Copredication.lean`.
- **Apparently new**, relative to these five papers:
  - `valid_iff` and `validI_iff`: a fragment-wide equivalence, with the
    exact condition.
  - The diagnosis that the injectivity axiom Chatzikyriakidis & Luo
    (2015) add is exactly that condition.
  - The FraCaS-scale comparison (Phases 1-3).
  - Possibly the transitivity problem above, if it checks out.
- **To add:** Gotham's (103) as a control; Luo's passenger example;
  double distinctness for "picked up and mastered three books"; the
  transitivity check.
- **Not yet read:** Asher (2011) itself, Gupta (1980), Retoré (2013),
  Bekki (2014) and Tanaka et al. (2015) on DTS, Cooper (2011) on TTR
  copredication.
