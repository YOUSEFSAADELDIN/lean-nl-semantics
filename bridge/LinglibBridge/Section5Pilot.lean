import LinglibBridge
import LeanNLSemantics.MTT.Adjectives

/-!
# A real fragment: Section 5's mammal/animal/four-legged/former-student pilot

`LinglibBridge.lean`'s own closing note flagged `toyLexicon` as "not a
real fragment's lexicon" — this file is the first real one, built over
three of `LeanNLSemantics/FraCaS/Section5`'s own actual problems
(`fracas_198`, `fracas_202` from `Batch1.lean`; `fracas_210` from
`Batch2.lean`) rather than `CN.lean`'s standalone toy model.

Four things are demonstrated:

1. **`fracas_202` re-derived through the bridge's `CN'`.** The
   predicate-style proof in `Batch1.lean` takes `∀ x, mammal x →
   animal x` as an explicit premise. Here, `.mammal ≤ .animal` is a
   `decide`-checked fact about this fragment's own tag lattice instead
   — no premise needed — and the conclusion follows via `CN'.widen`
   plus `Adjectives.lean`'s *already-proved* `Intersective`/
   `intersective_every_iff`/`inter_noun_drop`/`inter_adj_drop`, reused
   completely unchanged at `A := CN' section5Lexicon .mammal`. Zero new
   proof content for the "adjective passes through a subtyping step"
   part of the inference — four of `Adjectives.lean`'s own theorems
   transfer, not just one.

2. **Coherence survives the generalization.** `CN.lean`'s own closing
   example checks that widening `john` from `Man` to `Thing` agrees
   whether taken directly or via `Human` — the payoff of basing
   subtyping on a `Prop`-valued (hence proof-irrelevant) `≤`.
   Generalizing `Lexicon`/`CN'` away from `CN.lean`'s own hardcoded tag
   type (earlier in this file's history) could have silently lost that;
   a `rfl`-checked example re-runs the identical check — widening
   `mammal → thing` directly vs. via `animal` — over `section5Lexicon`'s
   real `S5Tag` lattice, confirming it didn't.

3. **`fracas_198`'s privativity, encoded a third way.** This project
   already has two treatments of "a former university student is not a
   university student": `Batch1.lean`'s own `fracas_198`, which takes it
   as an assumed premise (`∀ x, formerUnivStudent x → ¬ univStudent x`),
   and `Adjectives.lean`'s general `Gun`/`realGun`/`fakeGun` sum-type
   construction, which *proves* disjointness from a sum type's own
   `noConfusion` — still predicate-style underneath (a theorem about
   predicates on a sum type), not something the CN lattice itself rules
   out structurally. The tag lattice below adds a third option:
   `.former` has no ancestor edge to `.univStudent` at all, so the
   *only* obligation `CN'.widen` ever asks a fragment author to
   discharge — the `≤` proof — is false by `decide`, with nothing to
   prove and nothing assumed. `fracas_198_bridge` strengthens this from
   one missing coercion to the full entailment `fracas_198` itself
   needs (`∀ x, formerUnivStudent x → ¬ univStudent x`), proved rather
   than assumed, for every individual the fragment could ever have.

4. **`fracas_210`'s lattice boundary, made explicit.** `Batch2.lean`'s
   own premise 1 ("all mice are small animals") bundles a subtyping
   fact (`mouse x → animal x`) together with a separate lexical fact
   (`mouse x → smallAnimal x`, which isn't tag subtyping at all —
   `smallAnimal` is the comparison-class-relative judgment
   `Section5/Adjectives.lean`'s own header explains this section
   deliberately keeps out of the subtype machinery). `Batch2.lean`'s own
   proof computes the subtyping half and then discards it, never using
   it. Through the bridge, with a second `.mouse` tag added alongside
   `.mammal` under `.animal`, that half simply isn't a premise any more
   — it's `CN'.widen`, free — while the genuinely lexical half stays
   exactly as assumed as it is in `Batch2.lean`. This is the clearest
   statement in this file of what the tag lattice actually buys:
   subtyping, not lexical content.
-/

namespace MTT.LinglibBridge

/-! ## The tag lattice -/

/-- Six tags: a shared root, two independent branches under `.animal`
(`.mammal` for `fracas_202`, `.mouse` for `fracas_210`'s own "all mice
are small animals"), and the `univStudent`/`former` pair `fracas_198`
needs — kept deliberately disconnected from each other (see
`S5Tag.ancestors`). -/
inductive S5Tag where
  | thing
  | animal
  | mammal
  | mouse
  | univStudent
  | former
  deriving DecidableEq, Repr

/-- Written by hand rather than `deriving Fintype`, matching `CN.lean`'s
own `CNTag` instance and for the same reason: a derived completeness
proof is the fragile part on this toolchain, not the case analysis
itself. -/
instance : Fintype S5Tag where
  elems := {.thing, .animal, .mammal, .mouse, .univStudent, .former}
  complete x := by cases x <;> decide

/-- Each tag's ancestors, itself first — same shape as `CN.lean`'s
`CNTag.ancestors`. `.mammal` and `.mouse` are independent siblings under
`.animal` (two branches of the same root, not nested in each other);
`.former` and `.univStudent` are siblings under `.thing` only: no edge
between them, on purpose. -/
def S5Tag.ancestors : S5Tag → List S5Tag
  | .thing => [.thing]
  | .animal => [.animal, .thing]
  | .mammal => [.mammal, .animal, .thing]
  | .mouse => [.mouse, .animal, .thing]
  | .univStudent => [.univStudent, .thing]
  | .former => [.former, .thing]

instance : PartialOrder S5Tag where
  le a b := b ∈ a.ancestors
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := S5Tag) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (b ∈ a.ancestors))

/-- The edge `fracas_202` needs, checked rather than assumed. -/
example : S5Tag.mammal ≤ .animal := by decide

/-- The missing edge `fracas_198`'s privativity turns into, once stated
in the tag lattice instead of as a predicate premise: `CN'.widen`'s only
proof obligation for a `.former → .univStudent` coercion is false,
checked over this finite order rather than assumed or derived from a
sum type's disjointness. -/
example : ¬ (S5Tag.former ≤ .univStudent) := by decide

/-! ## A minimal entity domain -/

/-- Same shape as `CN.lean`'s own `Individual`: every individual carries
its most specific tag. -/
structure S5Individual where
  kind : S5Tag
  name : String
  deriving DecidableEq, Repr

/-- FraCaS's own "Dumbo" (`fracas_203`'s subject), reused here rather
than invented fresh. -/
def dumbo : S5Individual := ⟨.mammal, "dumbo"⟩

/-- The real lexicon: `embed_mono` is exactly `CN.lean`'s own
`le_trans` argument, discharged here against `S5Tag` instead of
`MTT.CNTag`. -/
def section5Lexicon : Lexicon S5Tag S5Individual where
  embed t x := x.kind ≤ t
  embed_mono h _ hx := le_trans hx h

/-! ## `fracas_202`, re-derived -/

/-- The bridge's own `fracas_202`. Compare `Batch1.lean`'s proof term
`fun h x ⟨hm, hf⟩ => ⟨h x hm, hf⟩`, which takes the mammal-animal
entailment `h` as a hypothesis: here the identical move (keep the
`fourLegged` witness, widen the rest) needs no `h` argument at all,
because `CN'.widen`'s own proof obligation is discharged by `decide`
against `section5Lexicon`'s tag lattice instead. -/
def fracas_202_bridge (fourLegged : S5Individual → Prop) :
    MTT.Intersective (CN' section5Lexicon .mammal) (fun z => fourLegged z.1) →
      MTT.Intersective (CN' section5Lexicon .animal) (fun z => fourLegged z.1) :=
  fun ⟨x, hx⟩ => ⟨CN'.widen section5Lexicon (by decide) x, hx⟩

/-- The quantified reading of the same fact, obtained by invoking
`Adjectives.lean`'s `intersective_every_iff` unchanged at
`A := CN' section5Lexicon .mammal` — no new proof, just instantiation. -/
example (fourLegged isAnimal : S5Individual → Prop) :
    MTT.Every
        (MTT.Intersective (CN' section5Lexicon .mammal) (fun z => fourLegged z.1))
        (fun z => isAnimal z.forget.1) ↔
      MTT.Every (CN' section5Lexicon .mammal)
        (fun x => fourLegged x.1 → isAnimal x.1) :=
  MTT.intersective_every_iff (A := CN' section5Lexicon .mammal)
    (fun z => fourLegged z.1) (fun x => isAnimal x.1)

/-- Two more of `Adjectives.lean`'s intersective theorems, reused the
same way: "some four-legged mammal is Q" entails both "some mammal is
Q" (`inter_noun_drop`, the existential form of `fracas_202`'s own move)
and "some mammal is four-legged" (`inter_adj_drop`, recovering the
adjective itself). Neither needs a new proof — both are `Adjectives.lean`
applied at `A := CN' section5Lexicon .mammal`, exactly like
`intersective_every_iff` above. -/
example (fourLegged isAnimal : S5Individual → Prop) :
    MTT.Some' (MTT.Intersective (CN' section5Lexicon .mammal) (fun z => fourLegged z.1))
        (fun z => isAnimal z.forget.1) →
      MTT.Some' (CN' section5Lexicon .mammal) (fun x => isAnimal x.1) :=
  MTT.inter_noun_drop (A := CN' section5Lexicon .mammal)
    (fun z => fourLegged z.1) (fun x => isAnimal x.1)

example (fourLegged isAnimal : S5Individual → Prop) :
    MTT.Some' (MTT.Intersective (CN' section5Lexicon .mammal) (fun z => fourLegged z.1))
        (fun z => isAnimal z.forget.1) →
      MTT.Some' (CN' section5Lexicon .mammal) (fun x => fourLegged x.1) :=
  MTT.inter_adj_drop (A := CN' section5Lexicon .mammal)
    (fun z => fourLegged z.1) (fun x => isAnimal x.1)

/-! ## Coherence survives the generalization -/

/-- `CN.lean`'s own closing example checks that widening `john` from
`Man` to `Thing` agrees whether taken directly or via `Human` — the
payoff of basing subtyping on a `Prop`-valued (hence proof-irrelevant)
`≤`. Generalizing `Lexicon`/`CN'` to an arbitrary tag type earlier in
this file could have silently lost that: this is the same check, over
`section5Lexicon`'s real `S5Tag` lattice instead of `CN.lean`'s own
`CNTag` toy model, confirming it didn't. -/
example (x : CN' section5Lexicon .mammal) :
    CN'.widen section5Lexicon (a := .animal) (b := .thing) (by decide)
        (CN'.widen section5Lexicon (a := .mammal) (b := .animal) (by decide) x)
      = CN'.widen section5Lexicon (a := .mammal) (b := .thing) (by decide) x :=
  rfl

/-! ## `fracas_198`, strengthened -/

/-- A concrete former-university-student individual, the `.former`-side
counterpart to `dumbo` above. -/
def pat : S5Individual := ⟨.former, "pat"⟩

/-- `pat` is not, under this lexicon, a university student — the
concrete instance of the missing-edge fact above, the same payoff
`CN.lean`'s own `decide`-checked examples give for its toy model.
Stated over `pat.kind ≤ .univStudent` directly rather than through
`section5Lexicon.embed`: `decide` needs a `Decidable` instance found by
typeclass search, and a structure field like `embed` doesn't unfold for
that search the way a plain `def` does, even though the two are
definitionally equal (as `fracas_198_bridge`'s own proof below relies
on, via defeq-checking a supplied term rather than synthesizing one). -/
example : ¬ (pat.kind ≤ S5Tag.univStudent) := by decide

/-- The missing edge, generalized from one pair of tags to *every* tag
this fragment has: no tag is ever both `.former`-typed and
`.univStudent`-typed. Proved by cases over the whole (finite) tag set
at once, the same move `S5Tag`'s own `Fintype`/`PartialOrder` instances
above already use — not assumed per-pair, derived once for the lattice
as a whole. -/
theorem former_univStudent_tags_disjoint :
    ∀ t : S5Tag, ¬ (t ≤ S5Tag.former ∧ t ≤ .univStudent) := by
  intro t
  cases t <;> decide

/-- The real, fully spelled-out form of `fracas_198`'s own premise
(`∀ x, formerUnivStudent x → ¬ univStudent x`) — except here it is a
**proved theorem**, holding for every individual this fragment could
ever have (not just the one FraCaS names), derived from
`former_univStudent_tags_disjoint` rather than assumed as a hypothesis
or derived from a sum type's `noConfusion`. This is the bridge's actual
payoff over the single missing-edge fact above: that fact only rules
out one *coercion*; this theorem rules out the entailment itself, for
every individual, the same strength `fracas_198`'s own premise is
stipulated to have. -/
theorem fracas_198_bridge (x : S5Individual) :
    section5Lexicon.embed .former x → ¬ section5Lexicon.embed .univStudent x :=
  fun h1 h2 => former_univStudent_tags_disjoint x.kind ⟨h1, h2⟩

/-! ## `fracas_210`, split into its free and assumed parts -/

/-- FraCaS's own "Mickey" (`fracas_210`'s subject), a mouse. -/
def mickey : S5Individual := ⟨.mouse, "mickey"⟩

/-- `Batch2.lean`'s own `fracas_210` premise 1 ("all mice are small
animals") bundles two separate things into one conjunction: `mouse x →
animal x` (a subtyping fact) and `mouse x → smallAnimal x` (a lexical
fact about mice specifically — `smallAnimal` is not a CN tag at all,
it's the comparison-class-relative adjectival judgment
`Section5/Adjectives.lean`'s own header explains this section
deliberately does NOT route through subtype machinery). `Batch2.lean`'s
own proof computes the `animal` half and then discards it
(`(h1 mickey hmouse).2`, never using `.1`) — a sign that half of the
premise was never doing any work for *this* conclusion. Through the
bridge, that half isn't a premise to discard: it's free, via
`CN'.widen`, with nothing to assume or throw away. -/
example : CN' section5Lexicon .animal :=
  CN'.widen section5Lexicon (by decide)
    (⟨mickey, (by decide : mickey.kind ≤ S5Tag.mouse)⟩ : CN' section5Lexicon .mouse)

/-- The real `fracas_210` entailment, through the bridge: the exact same
two genuinely-needed hypotheses `Batch2.lean`'s own proof uses
(contrariety, and "mice are small animals" restricted to its only
non-discardable half) — the subtyping half is gone from the premise
list entirely, not merely satisfied automatically, because it was never
needed to state the theorem in the first place. This is the tag
lattice's real boundary: it makes subtyping free, it does not make
`smallAnimal`/`largeAnimal`'s own contrariety or "mice are small"
disappear — those stay exactly as assumed as they are in `Batch2.lean`. -/
theorem fracas_210_bridge
    (smallAnimal largeAnimal : S5Individual → Prop)
    (hcontrary : ∀ x, smallAnimal x → ¬ largeAnimal x)
    (hMouseSmall : ∀ x : CN' section5Lexicon .mouse, smallAnimal x.1) :
    ¬ largeAnimal mickey :=
  hcontrary mickey (hMouseSmall ⟨mickey, (by decide : mickey.kind ≤ S5Tag.mouse)⟩)

end MTT.LinglibBridge
