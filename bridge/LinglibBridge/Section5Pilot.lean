import LinglibBridge
import LeanNLSemantics.MTT.Adjectives

/-!
# A real fragment: Section 5's mammal/animal/four-legged/former-student pilot

`LinglibBridge.lean`'s own closing note flagged `toyLexicon` as "not a
real fragment's lexicon" — this file is the first real one, built over
two of `LeanNLSemantics/FraCaS/Section5/Batch1.lean`'s own actual
problems (`fracas_198`, `fracas_202`) rather than `CN.lean`'s standalone
toy model.

Two things are demonstrated:

1. **`fracas_202` re-derived through the bridge's `CN'`.** The
   predicate-style proof in `Batch1.lean` takes `∀ x, mammal x →
   animal x` as an explicit premise. Here, `.mammal ≤ .animal` is a
   `decide`-checked fact about this fragment's own tag lattice instead
   — no premise needed — and the conclusion follows via `CN'.widen`
   plus `Adjectives.lean`'s *already-proved* `Intersective`/
   `intersective_every_iff`, reused completely unchanged at
   `A := CN' section5Lexicon .mammal`. Zero new proof content for the
   "adjective passes through a subtyping step" part of the inference.

2. **`fracas_198`'s privativity, encoded a third way.** This project
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
   prove and nothing assumed.
-/

namespace MTT.LinglibBridge

/-! ## The tag lattice -/

/-- Five tags: a shared root, the `animal`/`mammal` edge `fracas_202`
needs, and the `univStudent`/`former` pair `fracas_198` needs — kept
deliberately disconnected from each other (see `S5Tag.ancestors`). -/
inductive S5Tag where
  | thing
  | animal
  | mammal
  | univStudent
  | former
  deriving DecidableEq, Repr

/-- Written by hand rather than `deriving Fintype`, matching `CN.lean`'s
own `CNTag` instance and for the same reason: a derived completeness
proof is the fragile part on this toolchain, not the case analysis
itself. -/
instance : Fintype S5Tag where
  elems := {.thing, .animal, .mammal, .univStudent, .former}
  complete x := by cases x <;> decide

/-- Each tag's ancestors, itself first — same shape as `CN.lean`'s
`CNTag.ancestors`. `.former` and `.univStudent` are siblings under
`.thing` only: no edge between them, on purpose. -/
def S5Tag.ancestors : S5Tag → List S5Tag
  | .thing => [.thing]
  | .animal => [.animal, .thing]
  | .mammal => [.mammal, .animal, .thing]
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

end MTT.LinglibBridge
