# The lexical-premise audit

The project's founding idea is that nouns are types (Chatzikyriakidis
and Luo's modern type theories) rather than predicates. The corpus, like
FraCoq, states nouns as predicates. This audit asks a narrow, countable
question of the 342 hand-written problems: **how much of what they prove
rests on knowledge the formalization supplies rather than FraCaS
states, and which of that knowledge nouns-as-types would supply
instead?** It is the first step of the nouns-as-types comparison
(`EndToEnd/Encodings/README.md` holds the rest), and replaces an earlier
rough count ("about 21 of 236 theorems take a noun-to-noun fact") with
an exact one.

## How it was done

`scripts/lexical_audit.py` reads, for every problem, the statement the
corpus proves or evaluates: the main theorem `fracas_NNN` of each of the
236 yes/no problems, and the generic claim `fracas_NNN_claim` of each of
the 106 unknown/undef ones (`BlindEvalUnknown*.lean`). It splits each into
premises and conclusion: 499 premises in all.

Every premise was then read beside the FraCaS sentences and tagged by
hand. The tags are in `lexical_audit.tsv`, one row per premise or
theorem recorded:

- **added**: a premise that translates no FraCaS sentence, tagged by
  what it supplies;
- **stated_noun**: a premise that translates a FraCaS sentence relating
  two nouns ("Every Swede is a Scandinavian");
- **in_translation**: a yes/no theorem whose conclusion is literally one
  of its premises, or a conjunct of one. There the step from premises
  to hypothesis was taken when the English was translated, not by the
  proof. Tagged by what kind of step it was.

A premise not recorded translates a FraCaS sentence. That includes
sentences merged into one premise, and translations that pick a reading.

The script checks that the file still matches the corpus. Each recorded
premise must be the premise at that position of that problem's
statement. The `in_translation` records must be exactly the theorems
whose conclusion is one of their premises, which the script computes
itself. It runs in CI (the `build` job), so a change to the corpus that
the audit does not account for fails the build.

## Results

**Added premises: 46, in 46 problems** (one each).

| what it supplies | premises | problems |
|---|---|---|
| a modified noun is a kind of the noun ("an Irish delegate is a delegate") | 8 | 29, 55, 57, 59, 63, 70, 76, 80 |
| the same, for a verb's object ("won the contract from APCOM" ⇒ "won a contract") | 3 | 17, 24, 328 |
| a verb phrase with a modifier or quantity removed ("finished on time" ⇒ "finished") | 6 | 23, 25, 31, 38, 46, 48 |
| adjective and degree knowledge (contraries, comparatives, "former") | 13 | 198, 204, 205, 208, 209, 210, 211, 212, 220, 223, 224, 227, 229 |
| what a verb entails ("know", "manage", "see"; "build" ⇒ "finish") | 7 | 320, 322, 325, 326, 334, 336, 342 |
| two predicates exclude each other ("unemployed", "employed") | 1 | 316 |
| calendar and event-time facts | 6 | 258, 259, 284, 307, 315, 318 |
| a definite plural's restrictor is not empty | 2 | 5, 100 |

**Noun-to-noun premises FraCaS states: 27, in 26 problems**: 18–21,
26–28, 34–37, 42–44, 49–53, 65–69, 202 and 214 (two). Most are Section
1's "Every European is a person" and "Every Canadian resident is a
resident of the North American continent" families. 215 states the same
two relations as 214, but its generic claim is an opaque proposition,
so it is not counted.

**Concluded in translation: 90 of the 236 yes/no theorems.**

| step taken in translation | theorems | problems |
|---|---|---|
| ellipsis or anaphora resolved | 51 | 121, 122, 128, 133, 138, 142, 144–155, 157, 159, 160, 162–166, 168–172, 175, 176, 178, 180, 182, 183, 185–187, 189–191, 193, 195, 196, 236, 237, 244, 245, 311 |
| the English differs only in form (coordination, "there are", "it is true that") | 15 | 1, 7, 11, 81, 82, 87, 114, 139, 249, 331, 332, 338, 339, 345, 346 |
| a reading chosen ("many" and "several" as "some", "or" as "and") | 9 | 8, 9, 90, 92, 93, 96, 97, 112, 250 |
| a temporal or aspectual modifier dropped ("in two hours") | 8 | 251, 288, 290, 294, 297, 300, 302, 306 |
| an adjective's class or comparison class settled | 4 | 199, 203, 216, 218 |
| a possessive's presupposition written into the premise | 2 | 115, 116 |
| reflexive and passive given one translation | 1 | 140 |

(The script prints these tables; the ranges above abbreviate its lists.)

## What nouns-as-types would change

Each class above, against the comparison's encodings
(`EndToEnd/Encodings/README.md`: P extensional Montague, W intensional,
M nouns as types).

- **The 8 noun premises: supplied by building the noun phrase from its
  parts, and only one of them by the types.** In 7 (55, 57, 59, 63, 70,
  76, 80) the adjective is intersective (Irish, Portuguese, Scandinavian,
  female), so "an Irish delegate is a delegate" follows in any encoding
  that states "Irish delegate" as "Irish" and "delegate": P and W as
  much as M. The premise is needed only because the corpus and the
  pipeline fuse the phrase into one name. In 29 ("leading
  businessmen") the adjective is subsective: P and W need a postulate,
  and M has it in its types. This is Phase 1a's subsectivity result (35
  postulates in M against 53 in P and 65 in W, Section 5) on one Section
  1 problem. Phase 3 of the encoding comparison
  (`EndToEnd/Encodings/README.md`) checks all 8 in Lean. An earlier
  version of this audit credited all 8 to nouns as types.
- **Supplied only with a compositional verb phrase: the 3 object
  premises.** The corpus fuses verb and object (`wonNobelLit`), and under
  a fused name nothing supplies them. With the object stated
  compositionally, under a verb upward monotone in it, the same split
  applies. In 17 ("the Nobel prize for literature") and 328 ("the
  contract from APCOM") a restrictive prepositional phrase is dropped,
  which any compositional encoding allows. In 24 ("interesting
  results"), "interesting" is subsective in the shared lexicon
  (`EndToEnd/background.py`), so only M supplies it without a
  postulate. This is argued, not checked: Phase 3 keeps the verb
  phrases fused.
- **Restated, not removed: the 27 stated noun relations.** FraCaS
  states these, so every encoding must assume them. In M they become
  declared coercions between types instead of premises; the knowledge
  is the same.
- **Needed in every encoding, but stated per noun in M: the 13
  adjective premises.** Privativity and the degree lexicon are
  postulates in all four encodings (Phase 1a). What M changes is where
  they can be stated: "small" can take the noun as an argument. The
  corpus gets the same effect with fused names (`smallAnimal`,
  `largeMouse` in 210–212). Here too, extensional predicates make 215's
  wrong answer valid (`extensional_forces_215`, `MTT/Intensionality.lean`).
  This is the one verdict-level difference the comparison has found.
- **Untouched by the noun encoding: 22 premises.** These are the 6 verb
  phrase, 7 verb, 6 time, 1 antonym and 2 existence premises. The
  existence ones are not supplied by types either: a type, like a
  predicate, may be empty.
- **Steps taken in translation.** Only the 4 adjective steps bear on
  nouns. 199 ("a successful former university student") is read with
  "successful" intersective. 203 reads "four-legged animal"
  intersectively. 216 ("a fatter politician than Bill") and 218 ("a
  clever person") are read with the comparison class left out, which
  217 and 219 show is not generally sound. These are the steps a
  noun-indexed adjective in M makes explicit. The other 86 do not
  depend on how nouns are stated. The discourse steps overlap Phase 1b
  only in Section 3 (121, 122, 128, 133, 138), where M states anaphora
  as projections. The rest are Section 4 ellipsis, which no noun
  encoding resolves.

**In sum**, on FraCaS the noun encoding touches:

- 1 of the 46 added premises (29's), and 1 more (24's) with
  compositional verb phrases. The other 9 noun and object-noun premises
  follow from any compositional noun phrase;
- the 27 noun relations FraCaS states;
- the 13 adjective premises and 4 adjective steps of Section 5, where
  it changes how they are stated and, at 215, what is valid.

None of the rest depends on it. That fixes the size of the "FraCaS half"
of the comparison: the effect is concentrated in Section 5's adjectives.
In Section 1 it comes down to one subsective adjective. The rest of
Section 1's modified nouns need only a compositional noun phrase, in any
encoding.

## Limits

- The tags are one reading of each premise, made by hand; the file
  gives each added premise a one-line reason, so each can be checked.
- "Stated" is judged against FraCaS's sentence, not against a faithful
  translation of it. A premise that translates its sentence loosely
  still counts as stated. One does so wrongly: 69's premise says
  "have the right to live in Europe" where FraCaS says "can travel
  freely", which is FraCaS's own slip (`EndToEnd/README.md`).
- Premises a theorem drops are not counted. Examples: a distractor
  sentence, or 325's first premise, which its translation replaces with
  an added one.
- The unknown/undef claims abstract their predicates (`P`, `Q`), so
  they show few lexical premises by construction; none was added.
