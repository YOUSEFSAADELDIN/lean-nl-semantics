import Mathlib

/-!
# Generalized quantifiers for FraCaS Section 1

FraCaS Section 1 (Generalized Quantifiers) tests inference patterns
between determiners (every/some/most/few/at least three/both/...), not
the CN-subtyping machinery `MTT/Quantifiers.lean` is built around. A
single FraCaS sentence like "Most great tenors are Italian" has an
explicit **restrictor** (`great tenor`) and **scope** (`Italian`) as two
separate predicates over one flat domain — not a CN-typed quantifier
`Every (CN .man) P` the way `MTT.lean` encodes "every man walks". So this
file defines the classic two-predicate `Det(A)(restrictor)(scope)` shape
(Barwise & Cooper 1981) instead of reusing `MTT.Every`/`Some'`/`No'`,
and lives under `FraCaS.Section1` rather than `MTT` to keep that
distinction visible. `MTT`'s quantifiers and this file's are two
different, deliberately non-unified encodings of natural-language
determiners — see the README roadmap for why unifying them is future
work, not assumed here.

Every definition below takes its own `{A : Type*}`/`[Fintype A]`
explicitly rather than relying on a shared `variable` block: a `Fintype
A` instance used only in a `def`'s *body* (as `Finset.univ` is here)
isn't auto-included from a section `variable` the way one mentioned in
the stated type is — the same "`variable` only scans the type, not the
proof" gotcha `NLIExamples.lean`'s `include john in` documents, and it
bites `def` bodies exactly the same way it bit that theorem's proof
term.
-/

namespace FraCaS.Section1

/-- The cardinality of a decidable predicate's extension, restricted to
a `Fintype` domain — the one piece of machinery the plain `∀`/`∃`
quantifiers below don't need, since "most"/"few"/"at least n" genuinely
count. `abbrev`, not `def`: `decide` on the concrete countermodels in
`Batch1.lean` (problems 12/16) needs to unfold through `card`/`Most`/
`AtLeast`/`AtMost` during instance search, the same `def`-is-opaque
gotcha `CN.lean`'s `Fintype` instance hit first. -/
abbrev card {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] : Nat :=
  (Finset.univ.filter P).card

/-- "Every/all/each/both P are Q" (treating `both` as `every` restricted
to a 2-element P, and ignoring that cardinality presupposition where it
isn't needed for the inference — see `Batch1.lean`'s problem 13). -/
def Every {A : Type*} (P Q : A → Prop) : Prop := ∀ x, P x → Q x

/-- "Some/an/a/many/several/a few P are Q" — all of these differ only in
an implicated *approximate size*, not in the truth-conditional entailment
pattern FraCaS Section 1 actually tests (problems 1–11 all just ask
whether the determiner licenses "there exist P who are Q"), so one
existential covers all of them here; see each problem's comment in
`Batch1.lean` for the source determiner. -/
def Some {A : Type*} (P Q : A → Prop) : Prop := ∃ x, P x ∧ Q x

/-- "No/neither P is Q" (`neither` again treated as `no` restricted to a
2-element P). -/
def No {A : Type*} (P Q : A → Prop) : Prop := ∀ x, P x → ¬ Q x

/-- "Most P are Q": strictly more than half of the `P`s are also `Q`. -/
abbrev Most {A : Type*} [Fintype A] (P Q : A → Prop)
    [DecidablePred P] [DecidablePred fun x => P x ∧ Q x] : Prop :=
  2 * card (fun x => P x ∧ Q x) > card P

/-- "At least n P are Q". -/
abbrev AtLeast {A : Type*} [Fintype A] (n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] : Prop :=
  card (fun x => P x ∧ Q x) ≥ n

/-- "At most n P are Q". -/
abbrev AtMost {A : Type*} [Fintype A] (n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] : Prop :=
  card (fun x => P x ∧ Q x) ≤ n

/-! ## Composition lemmas

Reusable across many Section 1 problems, the same way `Subtyping.lean`'s
`every_anti`/`some_mono`/`no_anti` were reused across `NLIExamples.lean`
— most of Section 1's "does the conclusion follow" problems are one of
these shapes applied to differently-named predicates. -/

/-- Combining two `Every`-shaped facts that share a restrictor into one
fact about their conjunction — `Every` *is* this file's entailment
relation (`Monotonicity/Signature.lean`'s file comment), so this is
exactly "P entails Q, P entails R, therefore P entails Q ∧ R," with no
reference to any particular quantifier. Every one of `every_trans`/
`every_mp`/`some_trans`/`atMost_trans` below combines two premises this
same way before feeding the result into a quantifier-specific rule —
this lemma is the piece those four proofs share, pulled out so
`Monotonicity/Tactic.lean`'s Phase-2 extension can apply it directly
instead of re-deriving it once per rule name. -/
theorem entails_and {A : Type*} (P Q R : A → Prop) :
    Every P Q → Every P R → Every P (fun x => Q x ∧ R x) :=
  fun hq hr x hx => ⟨hq x hx, hr x hx⟩

/-- Every predicate entails itself — the trivial `Every` fact `every_mp`'s
own shape needs (`Every P Q → Every (P ∧ Q) R → Every P R`: combining this
with the first premise via `entails_and` gives exactly the `Every P (P ∧
Q)` fact `every_mp`'s second premise's restrictor names). -/
theorem entails_refl {A : Type*} (P : A → Prop) : Every P P :=
  fun _ hx => hx

/-- `entails_and`'s mixed-quantifier sibling: `Some P Q` plus a fact
holding everywhere on `P` (`Every P R`) gives `Some P (fun x => R x ∧ Q
x)` - the witness `Some P Q` already supplies satisfies `R` too, since it
satisfies `P`. This is the one new piece `some_trans`'s own recipe needs
beyond what `every_trans`'s Phase-2 reconstruction already has: `Some P R
→ Every P S → Every (fun x => S x ∧ R x) Q → Some P Q` (problem 27's "a
few committee members are from Sweden; all committee members are people;
all people from Sweden are from Scandinavia ⊢ some committee members are
from Scandinavia") reduces to `some_mono_scope P (fun x => S x ∧ R x) Q
(some_entails_and P R S h1 h2) h3` - `some_mono_scope` (already in
`Signature.lean`'s table) doing the actual substitution, exactly as
`every_trans` reduces to `entails_and` feeding `every_mono_scope`. -/
theorem some_entails_and {A : Type*} (P Q R : A → Prop) :
    Some P Q → Every P R → Some P (fun x => R x ∧ Q x) :=
  fun ⟨x, hx, hqx⟩ h => ⟨x, hx, h x hx, hqx⟩

/-- Narrowing a fact's own restrictor along a known entailment: `P
entails S` lets any fact conditioned on `S x ∧ X x` be re-conditioned on
the (possibly smaller) `P x ∧ X x` instead - `S`/`X` never separately
interact with anything else, so `P x → S x` is all `entails_and`-style
composition needs to make the swap.

This is the general schema `atMost_trans` (below) and `every_mp` (its
`Every`-quantifier instance) both already reduce to, once each is looked
at as "one Entails fact conditioned on an *outer* restrictor via a
second Entails fact" rather than as a hand-written proof in its own
right - not a rule invented to fit either: `every_mp`'s own proof (`fun
h1 h2 x hx => h2 x ⟨hx, h1 x hx⟩`) already *is* `entails_narrow`
specialized to `P = S` (taking the first premise's own `Every P Q` as
both the "P entails S" step and the outer restrictor at once - see
`Monotonicity/Tactic.lean`'s `atMost_mono_scope_conditioned` search for
where the general form gets used for real, on a genuinely different
outer/inner restrictor pair).

`Monotonicity/Tactic.lean`'s Phase 2 `entails_and`/`entails_refl` combine
step targets a different axis entirely - decomposing `needTo` into two
conjuncts sharing `needFrom` as a common restrictor - so this doesn't
overlap or duplicate that search; the two combine into the two premises
`atMost_trans` actually needs (`Every P S`, `Every (fun x => S x ∧ Q x)
R`), narrowed here into the one conditioned fact `atMost_mono_scope_
conditioned` consumes. -/
theorem entails_narrow {A : Type*} (P S X Y : A → Prop) :
    Every P S → Every (fun x => S x ∧ X x) Y → Every (fun x => P x ∧ X x) Y :=
  fun hPS hSXY x hx => hSXY x ⟨hPS x hx.1, hx.2⟩

/-- `Every P Q` plus a witness that `P` holds of something (recovered here
from a second premise `Some P R`, not assumed outright) gives `Some P Q` —
problems 2/3/4's "every X wants Y; some X are Z ⊢ some X want Y" shape.

The real principle this instantiates is existential transfer through a
universal: *any* fact establishing `P` nonempty, combined with `Every P
Q`, gives `Some P Q` - `R` above is discarded entirely (only the witness
`x` and `P x` are used), so a second `Some`-headed premise is one
possible *source* of that witness, not part of the principle itself. See
`some_of_nonempty` immediately below for the same principle stated over
a bare nonemptiness fact, the other source `Monotonicity/Existential.lean`
finds this witness from (e.g. problem 5's explicit `∃ x, ambitious x`
premise, no second `Some` in sight). -/
theorem every_some {A : Type*} (P Q R : A → Prop) :
    Every P Q → Some P R → Some P Q :=
  fun h ⟨x, hx, _⟩ => ⟨x, hx, h x hx⟩

/-- The same existential-transfer principle as `every_some`, stated over
a bare nonemptiness witness instead of a second `Some`-headed premise -
not a new principle, just this file's own two-line proof of it, kept
separate from `every_some` (rather than deriving one from the other)
since both are already relied on directly, unchanged, by existing
`Batch1.lean` proofs. -/
theorem some_of_nonempty {A : Type*} (P Q : A → Prop) :
    (∃ x, P x) → Every P Q → Some P Q :=
  fun ⟨x, hx⟩ h => ⟨x, hx, h x hx⟩

/-- Three-premise universal transitivity: `Every P R`, `Every P S`, and
`Every (fun x => S x ∧ R x) Q` (i.e. "every P that is both R and S is Q")
together give `Every P Q` — problems 18–21's "every European has the
right; every European is a person; every person with the right can
travel ⊢ every European can travel" shape. -/
theorem every_trans {A : Type*} (P R S Q : A → Prop) :
    Every P R → Every P S → Every (fun x => S x ∧ R x) Q → Every P Q :=
  fun h1 h2 h3 x hx => h3 x ⟨h2 x hx, h1 x hx⟩

/-- Two-premise universal modus ponens: `Every P Q`, `Every (fun x => P x
∧ Q x) R` ⊢ `Every P R` — problem 13's "both leading tenors are
excellent; leading tenors who are excellent are indispensable ⊢ both
leading tenors are indispensable" shape. -/
theorem every_mp {A : Type*} (P Q R : A → Prop) :
    Every P Q → Every (fun x => P x ∧ Q x) R → Every P R :=
  fun h1 h2 x hx => h2 x ⟨hx, h1 x hx⟩

/-- `No P Q` is exactly the negation of `Some P Q` — problem 6's "no
really great tenors are modest ⊢ ¬∃ such a tenor" shape (same
`∀`-vs-`¬∃` pattern as `MTT.nli_no_iff`, restated here in two-predicate
form since that's what Section 1 sentences need). -/
theorem no_iff_not_some {A : Type*} (P Q : A → Prop) :
    No P Q ↔ ¬ Some P Q :=
  ⟨fun h ⟨x, hx, hqx⟩ => h x hx hqx, fun h x hx hqx => h ⟨x, hx, hqx⟩⟩

/-- `AtLeast n P Q` for `n ≥ 1` gives `Some P Q` — problem 15's "at least
three tenors will take part ⊢ there are tenors who will take part"
shape. -/
theorem atLeast_some {A : Type*} [Fintype A] (n : Nat) (P Q : A → Prop)
    [DecidablePred fun x => P x ∧ Q x]
    (hn : n ≥ 1) (h : AtLeast n P Q) : Some P Q := by
  have hpos : 0 < card (fun x => P x ∧ Q x) := lt_of_lt_of_le hn h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter] at hx
  exact ⟨x, hx.2⟩

/-- `Most P Q` gives `Some P Q`: a strict majority of `P ∩ Q` over `P`
forces `P ∩ Q` nonempty, since `P ∩ Q ⊆ P` already bounds
`card (P ∩ Q) ≤ card P` — problem 10's "most great tenors are Italian ⊢
there are great tenors who are Italian" shape (also reused for problem
26). -/
theorem most_some {A : Type*} [Fintype A] (P Q : A → Prop)
    [DecidablePred P] [DecidablePred fun x => P x ∧ Q x]
    (h : Most P Q) : Some P Q := by
  have hsub : (Finset.univ.filter fun x => P x ∧ Q x) ⊆ Finset.univ.filter P := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1
  have hle : card (fun x => P x ∧ Q x) ≤ card P := Finset.card_le_card hsub
  have hpos : 0 < card (fun x => P x ∧ Q x) := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter] at hx
  exact ⟨x, hx.2⟩

/-- Weakening the scope predicate under `Some` — problem 17's "an
Irishman won the Nobel prize for literature ⊢ an Irishman won a Nobel
prize" shape (also reused for problems 23/25's "on time"/"published in
major newspapers" premise-detail-dropping pattern). -/
theorem some_mono_scope {A : Type*} (P Q R : A → Prop) :
    Some P Q → (∀ x, Q x → R x) → Some P R :=
  fun ⟨x, hx, hq⟩ h => ⟨x, hx, h x hq⟩

/-- Weakening the scope predicate under `Every` — problem 29's "both
commissioners used to be leading businessmen ⊢ both used to be
businessmen" shape (dual of `some_mono_scope`). -/
theorem every_mono_scope {A : Type*} (P Q R : A → Prop) :
    Every P Q → (∀ x, Q x → R x) → Every P R :=
  fun h hqr x hx => hqr x (h x hx)

/-- Weakening the scope predicate under `AtLeast` — problem 31's "at
least three commissioners spend a lot of time at home ⊢ at least three
spend time at home" shape: widening the scope predicate can only grow
the qualifying set, so the same lower bound still holds. -/
theorem atLeast_mono_scope {A : Type*} [Fintype A] (n : Nat) (P Q R : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] [DecidablePred fun x => P x ∧ R x] :
    AtLeast n P Q → (∀ x, Q x → R x) → AtLeast n P R := by
  intro h hqr
  have hsub : (Finset.univ.filter fun x => P x ∧ Q x) ⊆ Finset.univ.filter fun x => P x ∧ R x := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, hqr x hx.2⟩
  have hle : card (fun x => P x ∧ Q x) ≤ card (fun x => P x ∧ R x) := Finset.card_le_card hsub
  omega

/-- `Some P R` plus two universal facts (`Every P S`, and "every `S` that
is also `R` is `Q`") gives `Some P Q` — problem 27's "a few committee
members are from Sweden; all committee members are people; all people
from Sweden are from Scandinavia ⊢ some committee members are from
Scandinavia" shape (the `Some`-headed analogue of `every_trans`). -/
theorem some_trans {A : Type*} (P R S Q : A → Prop) :
    Some P R → Every P S → Every (fun x => S x ∧ R x) Q → Some P Q :=
  fun ⟨x, hx, hr⟩ h2 h3 => ⟨x, hx, h3 x ⟨h2 x hx, hr⟩⟩

/-- `Most P R` plus two universal facts (`Every P S`, and "every `S` that
is also `R` is `Q`") gives `Most P Q`: the majority witnessing `Most P R`
is a subset of `P ∩ Q` (since every `P ∩ R` element is `S ∧ R`, hence
`Q`), so it's at least as big — problem 26's "most Europeans are
resident; all Europeans are people; all resident people can travel ⊢
most Europeans can travel" shape (the `Most`-headed analogue of
`every_trans`). -/
theorem most_trans {A : Type*} [Fintype A] (P R S Q : A → Prop)
    [DecidablePred P] [DecidablePred fun x => P x ∧ R x] [DecidablePred fun x => P x ∧ Q x]
    (h1 : Most P R) (h2 : Every P S) (h3 : Every (fun x => S x ∧ R x) Q) : Most P Q := by
  have hsub : (Finset.univ.filter fun x => P x ∧ R x) ⊆ Finset.univ.filter fun x => P x ∧ Q x := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, h3 x ⟨h2 x hx.1, hx.2⟩⟩
  have hle : card (fun x => P x ∧ R x) ≤ card (fun x => P x ∧ Q x) := Finset.card_le_card hsub
  omega

/-- `AtMost n P R` plus two universal facts (`Every P S`, and "every `S`
that is also `Q` is `R`") gives `AtMost n P Q`: every `P ∩ Q` element is
forced into `P ∩ R` (since `S` always holds on `P`, so `S ∧ Q` does too,
giving `R`), so `P ∩ Q` is no bigger than the already-bounded `P ∩ R` —
problem 44's "few committee members are from southern Europe; all
committee members are people; all people from Portugal are from
southern Europe ⊢ few committee members are from Portugal" shape (the
`AtMost`-headed analogue of `every_trans`/`some_trans`/`most_trans`,
and the mirror image of `atLeast_mono_scope`: there the scope widens
along a known implication, here the *restrictor* narrows along one). -/
theorem atMost_trans {A : Type*} [Fintype A] (n : Nat) (P Q S R : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] [DecidablePred fun x => P x ∧ R x]
    (h1 : AtMost n P R) (h2 : Every P S) (h3 : Every (fun x => S x ∧ Q x) R) : AtMost n P Q := by
  have hsub : (Finset.univ.filter fun x => P x ∧ Q x) ⊆ Finset.univ.filter fun x => P x ∧ R x := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, h3 x ⟨h2 x hx.1, hx.2⟩⟩
  have hle : card (fun x => P x ∧ Q x) ≤ card (fun x => P x ∧ R x) := Finset.card_le_card hsub
  omega

/-- Weakening the scope predicate under `AtMost`, in the direction that
*narrows* it (dual of `atLeast_mono_scope`, which widens): if at most `n`
`P`s are `Q`, and `R` implies `Q`, then at most `n` `P`s are `R` too,
since `P ∩ R ⊆ P ∩ Q` — problem 48's "at most ten commissioners spend
time at home ⊢ at most ten spend a lot of time at home" shape (spending
"a lot" implies spending *some*, so the narrower set can only be
smaller). -/
theorem atMost_mono_scope {A : Type*} [Fintype A] (n : Nat) (P Q R : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] [DecidablePred fun x => P x ∧ R x] :
    AtMost n P Q → (∀ x, R x → Q x) → AtMost n P R := by
  intro h hrq
  have hsub : (Finset.univ.filter fun x => P x ∧ R x) ⊆ Finset.univ.filter fun x => P x ∧ Q x := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, hrq x hx.2⟩
  have hle : card (fun x => P x ∧ R x) ≤ card (fun x => P x ∧ Q x) := Finset.card_le_card hsub
  omega

/-- `atMost_mono_scope`'s conditioned generalization: the licensing
implication only has to hold *within* `P` (`Every (fun x => P x ∧ R x)
Q`, i.e. `∀ x, P x → R x → Q x`) rather than everywhere, since the proof
only ever applies it to an `x` already known to satisfy `P` (`hx.1`
below - exactly the same reason the flat `atMost_mono_scope` proof above
still goes through when its own `hrq` is weakened this way: every use
site already has `hx.1 : P x` sitting right there). This is the general
schema's `AtMost`-scope instance - see `entails_narrow`'s doc comment for
the schema itself and why `every_mp` is independent evidence it isn't
invented for `atMost_trans` alone. `atMost_trans` itself is now exactly
`entails_narrow` feeding this: `atMost_mono_scope_conditioned n P R Q h1
(entails_narrow P S Q R h2 h3)`. -/
theorem atMost_mono_scope_conditioned {A : Type*} [Fintype A] (n : Nat) (P Q R : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] [DecidablePred fun x => P x ∧ R x] :
    AtMost n P Q → Every (fun x => P x ∧ R x) Q → AtMost n P R := by
  intro h hcond
  have hsub : (Finset.univ.filter fun x => P x ∧ R x) ⊆ Finset.univ.filter fun x => P x ∧ Q x := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, hcond x hx⟩
  have hle : card (fun x => P x ∧ R x) ≤ card (fun x => P x ∧ Q x) := Finset.card_le_card hsub
  omega

/-- `Some P Q` plus `Every P R` gives `Some R Q`: the witness for `P` is
also `R`, so it witnesses `Some R Q` too — problem 49's "a Swede won a
Nobel prize; every Swede is a Scandinavian ⊢ a Scandinavian won a Nobel
prize" shape (also reused, with `R` the plain superset predicate, for
problems 55/57/59's "some Irish/Portuguese/female-committee X ⊢ some X"
restrictor-dropping pattern). -/
theorem some_restrict {A : Type*} (P Q R : A → Prop) :
    Some P Q → Every P R → Some R Q :=
  fun ⟨x, hx, hq⟩ h => ⟨x, h x hx, hq⟩

/-- `Every R Q` plus `Every P R` gives `Every P Q` (plain transitivity of
`Every`, restricting a universal from a superset down to a known
subset) — problems 66–69/77's "every North American resident can
travel; every Canadian resident is a North American resident ⊢ every
Canadian resident can travel" shape: unlike 50–53's *converse* (which
tried to go from the subset's universal to the superset's, and fails),
this direction always holds. -/
theorem every_restrict {A : Type*} (P Q R : A → Prop) :
    Every R Q → Every P R → Every P Q :=
  fun hRQ hPR x hx => hRQ x (hPR x hx)

/-- `AtLeast n P Q` plus `Every P R` gives `AtLeast n R Q`: `P`'s
witnesses for the bound are already `R`-witnesses too, since `P ⊆ R` —
problem 63's "at least three female commissioners spend time at home ⊢
at least three commissioners do" shape (a lower bound on a subset always
transfers up to any superset). -/
theorem atLeast_restrict {A : Type*} [Fintype A] (n : Nat) (P Q R : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] [DecidablePred fun x => R x ∧ Q x]
    (h : AtLeast n P Q) (hPR : Every P R) : AtLeast n R Q := by
  have hsub : (Finset.univ.filter fun x => P x ∧ Q x) ⊆ Finset.univ.filter fun x => R x ∧ Q x := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hPR x hx.1, hx.2⟩
  have hle : card (fun x => P x ∧ Q x) ≤ card (fun x => R x ∧ Q x) := Finset.card_le_card hsub
  omega

/-- `AtMost n P Q` plus `Every R P` gives `AtMost n R Q`: any `R`-witness
is already a `P`-witness, since `R ⊆ P`, so `R`'s count can't exceed the
bound already holding for the bigger set `P` — problem 76's "few
committee members are from southern Europe ⊢ few female committee
members are" shape (an upper bound on a superset always transfers down
to any subset; the mirror image of `atLeast_restrict`). -/
theorem atMost_restrict {A : Type*} [Fintype A] (n : Nat) (P Q R : A → Prop)
    [DecidablePred fun x => P x ∧ Q x] [DecidablePred fun x => R x ∧ Q x]
    (h : AtMost n P Q) (hRP : Every R P) : AtMost n R Q := by
  have hsub : (Finset.univ.filter fun x => R x ∧ Q x) ⊆ Finset.univ.filter fun x => P x ∧ Q x := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hRP x hx.1, hx.2⟩
  have hle : card (fun x => R x ∧ Q x) ≤ card (fun x => P x ∧ Q x) := Finset.card_le_card hsub
  omega

end FraCaS.Section1
