import EndToEnd.Encodings.FullAbstraction

/-!
# Full abstraction with plurals

`FullAbstraction.lean` shows that what the fragment's sentences see of a
noun with one identity criterion is its counting units. Its fragment is
singular: verbs are true of individuals. This file adds plurals and
asks whether collective predication sees more.

**The plural fragment (`PForm`).** Everything in `Relational.Form`, plus
plural variables, bound separately from the individual ones, and:

- `coll d n φ`, "`d` `n`s together are such that `φ`": `d` is "exactly
  `k`" or "at least `k`", and `φ` speaks of the plurality as plural
  variable `0`;
- `the n φ`, "the `n`s are such that `φ`";
- `pverb p k`, a collective verb ("gathered", "lifted the piano") true of
  plurality `k`;
- `among t k`, "`t` is one of them": with the singular quantifiers this
  gives distributive readings ("each of them").

**Pluralities are pluralities of the noun's own things.** A plurality of
`N`s is a set `Y` of elements of `N`'s type. A collective verb is true or
false of the individuals `Y` embeds to, and `Y` counts as as many `N`s as
the criterion has values on it (`NounI.pl`). This is the reading closest
to nouns as types: three journeys by one person are a plurality of
three passengers, or of two, or of one. So plural sentences could, in
principle, see more of a noun than singular ones: which sets of
individuals its units can jointly cover, with how many units.

**`obsEqP_iff`.** They do not. Two interpretations of a noun are
indistinguishable by every formula of the plural fragment, in every
context, exactly when they have the same counting units with the same
multiplicities, as in the singular fragment.

How. Singular sentences already fix the units (`FullAbstraction`). The
other way, a plurality of `k` `N`s covering exactly `X` exists exactly
when some `k` units, counted with multiplicity, each meet `X` and
together cover it (`pl_iff_keys`, `pl_iff_m`). That depends only on the
units.

The domain is finite, as in the singular result.
-/

namespace FraCaS.Encodings.FullAbstractionPlural
open FraCaS.Encodings.Typed FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence
open FraCaS.Encodings.Relational
open FraCaS.Encodings.FullAbstraction (NounI detBy_obs count_meets ext_iff_count eq_of_meets
  units_empty count_congr)
open Classical

/-! ## The plural fragment -/

/-- Collective determiners: "exactly `k`" and "at least `k`". -/
inductive CDet where
  | exactly (k : Nat)
  | atLeast (k : Nat)

inductive PForm (Noun Verb Rel PVerb Name : Type) where
  | verb : Verb → Term Name → PForm Noun Verb Rel PVerb Name
  | rel : Rel → Term Name → Term Name → PForm Noun Verb Rel PVerb Name
  | isA : Noun → Term Name → PForm Noun Verb Rel PVerb Name
  | eq : Term Name → Term Name → PForm Noun Verb Rel PVerb Name
  | top : PForm Noun Verb Rel PVerb Name
  | not : PForm Noun Verb Rel PVerb Name → PForm Noun Verb Rel PVerb Name
  | and : PForm Noun Verb Rel PVerb Name → PForm Noun Verb Rel PVerb Name →
      PForm Noun Verb Rel PVerb Name
  | or : PForm Noun Verb Rel PVerb Name → PForm Noun Verb Rel PVerb Name →
      PForm Noun Verb Rel PVerb Name
  | imp : PForm Noun Verb Rel PVerb Name → PForm Noun Verb Rel PVerb Name →
      PForm Noun Verb Rel PVerb Name
  /-- `d` noun `n` that `C` are `Q`: binds individual variable `0` -/
  | quant : Det → Noun → PForm Noun Verb Rel PVerb Name → PForm Noun Verb Rel PVerb Name →
      PForm Noun Verb Rel PVerb Name
  | more : Noun → PForm Noun Verb Rel PVerb Name → PForm Noun Verb Rel PVerb Name →
      PForm Noun Verb Rel PVerb Name → PForm Noun Verb Rel PVerb Name
  /-- a collective verb, of plural variable `k` -/
  | pverb : PVerb → Nat → PForm Noun Verb Rel PVerb Name
  /-- "`t` is one of them": `t` is among plural variable `k` -/
  | among : Term Name → Nat → PForm Noun Verb Rel PVerb Name
  /-- "`d` `n`s together are such that `φ`": binds plural variable `0` -/
  | coll : CDet → Noun → PForm Noun Verb Rel PVerb Name → PForm Noun Verb Rel PVerb Name
  /-- "the `n`s are such that `φ`": binds plural variable `0` -/
  | the : Noun → PForm Noun Verb Rel PVerb Name → PForm Noun Verb Rel PVerb Name

variable {Noun Verb Rel PVerb Name A : Type}

/-- `Y` is a plurality of `k` of the noun's things covering exactly `X`. -/
def _root_.FraCaS.Encodings.FullAbstraction.NounI.pl (I : NounI A) (k : Nat) (X : Finset A) : Prop :=
  ∃ Y : Finset I.T, Y.image I.emb = X ∧ (Y.image I.crit).card = k

/-- The individuals of all the noun's things: "the `N`s". -/
noncomputable def _root_.FraCaS.Encodings.FullAbstraction.NounI.all (I : NounI A) : Finset A := Finset.univ.image I.emb

theorem _root_.FraCaS.Encodings.FullAbstraction.NounI.mem_all (I : NounI A) (x : A) :
    x ∈ I.all ↔ I.ext x := by
  constructor
  · intro h
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hy⟩

structure PCtx (Noun Verb Rel PVerb Name A : Type) where
  noun : Noun → NounI A
  verb : Verb → A → Prop
  rel : Rel → A → A → Prop
  pverb : PVerb → Finset A → Prop
  name : Name → A

/-- Evaluation, with an assignment `ρ` to individual variables and `σ`
to plural ones. -/
noncomputable def PCtx.eval (M : PCtx Noun Verb Rel PVerb Name A) :
    PForm Noun Verb Rel PVerb Name → (Nat → A) → (Nat → Finset A) → Prop
  | .verb v t, ρ, _ => M.verb v (t.eval M.name ρ)
  | .rel r t u, ρ, _ => M.rel r (t.eval M.name ρ) (u.eval M.name ρ)
  | .isA n t, ρ, _ => (M.noun n).ext (t.eval M.name ρ)
  | .eq t u, ρ, _ => t.eval M.name ρ = u.eval M.name ρ
  | .top, _, _ => True
  | .not φ, ρ, σ => ¬ M.eval φ ρ σ
  | .and φ ψ, ρ, σ => M.eval φ ρ σ ∧ M.eval ψ ρ σ
  | .or φ ψ, ρ, σ => M.eval φ ρ σ ∨ M.eval ψ ρ σ
  | .imp φ ψ, ρ, σ => M.eval φ ρ σ → M.eval ψ ρ σ
  | .quant d n C Q, ρ, σ =>
    detBy (M.noun n).count (M.noun n).emb d (fun x => M.eval C (push x ρ) σ)
      (fun x => M.eval Q (push x ρ) σ)
  | .more n C Q S, ρ, σ =>
    (M.noun n).count (fun x => M.eval C (push x ρ) σ ∧ M.eval Q (push x ρ) σ) >
      (M.noun n).count (fun x => M.eval C (push x ρ) σ ∧ M.eval S (push x ρ) σ)
  | .pverb p k, _, σ => M.pverb p (σ k)
  | .among t k, ρ, σ => t.eval M.name ρ ∈ σ k
  | .coll (.exactly k) n φ, ρ, σ => ∃ X, (M.noun n).pl k X ∧ M.eval φ ρ (push X σ)
  | .coll (.atLeast k) n φ, ρ, σ =>
    ∃ j X, k ≤ j ∧ (M.noun n).pl j X ∧ M.eval φ ρ (push X σ)
  | .the n φ, ρ, σ => M.eval φ ρ (push (M.noun n).all σ)

noncomputable def PCtx.set (M : PCtx Noun Verb Rel PVerb Name A) (n0 : Noun) (I : NounI A) :
    PCtx Noun Verb Rel PVerb Name A :=
  { M with noun := fun n => if n = n0 then I else M.noun n }

theorem PCtx.set_self (M : PCtx Noun Verb Rel PVerb Name A) (n0 : Noun) (I : NounI A) :
    (M.set n0 I).noun n0 = I := if_pos rfl

theorem PCtx.set_ne (M : PCtx Noun Verb Rel PVerb Name A) {n n0 : Noun} (I : NounI A)
    (h : n ≠ n0) : (M.set n0 I).noun n = M.noun n := if_neg h

/-- Two interpretations of `n0` are indistinguishable by plural
sentences too. -/
def ObsEqP (n0 : Noun) (I I' : NounI A) : Prop :=
  ∀ (M : PCtx Noun Verb Rel PVerb Name A) (φ : PForm Noun Verb Rel PVerb Name) (ρ : Nat → A)
    (σ : Nat → Finset A), (M.set n0 I).eval φ ρ σ ↔ (M.set n0 I').eval φ ρ σ

/-! ## Agreement -/

/-- Nouns that no sentence can tell apart by what it reads off them. -/
structure NEq (J J' : NounI A) : Prop where
  ext : ∀ x, J.ext x ↔ J'.ext x
  count : ∀ P, J.count P = J'.count P
  pl : ∀ k X, J.pl k X ↔ J'.pl k X

theorem all_eq {J J' : NounI A} (hE : ∀ x, J.ext x ↔ J'.ext x) : J.all = J'.all :=
  Finset.ext fun x => by rw [J.mem_all, J'.mem_all]; exact hE x

theorem detBy_congr {T : Type} (cnt : (A → Prop) → Nat) (e : T → A) (d : Det)
    {C C' Q Q' : A → Prop} (hC : ∀ x, C x ↔ C' x) (hQ : ∀ x, Q x ↔ Q' x) :
    detBy cnt e d C Q ↔ detBy cnt e d C' Q' := by
  obtain rfl : C = C' := funext fun x => propext (hC x)
  obtain rfl : Q = Q' := funext fun x => propext (hQ x)
  exact Iff.rfl

section
variable {M M' : PCtx Noun Verb Rel PVerb Name A} (hv : M.verb = M'.verb) (hr : M.rel = M'.rel)
  (hp : M.pverb = M'.pverb) (hn : M.name = M'.name) (hN : ∀ n, NEq (M.noun n) (M'.noun n))
include hv hr hp hn hN

/-- Contexts that agree on everything but nouns, with nouns that agree
on extension, counts and pluralities, agree on every formula. -/
theorem eval_congr : ∀ (φ : PForm Noun Verb Rel PVerb Name) (ρ : Nat → A) (σ : Nat → Finset A),
    M.eval φ ρ σ ↔ M'.eval φ ρ σ
  | .verb v t, ρ, σ => by
    show M.verb v (t.eval M.name ρ) ↔ M'.verb v (t.eval M'.name ρ)
    rw [hv, hn]
  | .rel r t u, ρ, σ => by
    show M.rel r (t.eval M.name ρ) (u.eval M.name ρ) ↔ M'.rel r (t.eval M'.name ρ) (u.eval M'.name ρ)
    rw [hr, hn]
  | .isA n t, ρ, σ => by
    show (M.noun n).ext (t.eval M.name ρ) ↔ (M'.noun n).ext (t.eval M'.name ρ)
    rw [hn]
    exact (hN n).ext _
  | .eq t u, ρ, σ => by
    show t.eval M.name ρ = u.eval M.name ρ ↔ t.eval M'.name ρ = u.eval M'.name ρ
    rw [hn]
  | .top, _, _ => Iff.rfl
  | .not φ, ρ, σ => not_congr (eval_congr φ ρ σ)
  | .and φ ψ, ρ, σ => and_congr (eval_congr φ ρ σ) (eval_congr ψ ρ σ)
  | .or φ ψ, ρ, σ => or_congr (eval_congr φ ρ σ) (eval_congr ψ ρ σ)
  | .imp φ ψ, ρ, σ => imp_congr (eval_congr φ ρ σ) (eval_congr ψ ρ σ)
  | .quant d n C Q, ρ, σ => by
    show detBy (M.noun n).count (M.noun n).emb d (fun x => M.eval C (push x ρ) σ)
        (fun x => M.eval Q (push x ρ) σ) ↔
      detBy (M'.noun n).count (M'.noun n).emb d (fun x => M'.eval C (push x ρ) σ)
        (fun x => M'.eval Q (push x ρ) σ)
    exact (detBy_congr _ _ d (fun x => eval_congr C (push x ρ) σ)
      (fun x => eval_congr Q (push x ρ) σ)).trans
      (detBy_obs _ _ (hN n).ext (hN n).count d _ _)
  | .more n C Q S, ρ, σ => by
    show (M.noun n).count (fun x => M.eval C (push x ρ) σ ∧ M.eval Q (push x ρ) σ) >
        (M.noun n).count (fun x => M.eval C (push x ρ) σ ∧ M.eval S (push x ρ) σ) ↔
      (M'.noun n).count (fun x => M'.eval C (push x ρ) σ ∧ M'.eval Q (push x ρ) σ) >
        (M'.noun n).count (fun x => M'.eval C (push x ρ) σ ∧ M'.eval S (push x ρ) σ)
    have e1 : (M.noun n).count (fun x => M.eval C (push x ρ) σ ∧ M.eval Q (push x ρ) σ) =
        (M'.noun n).count (fun x => M'.eval C (push x ρ) σ ∧ M'.eval Q (push x ρ) σ) :=
      (count_congr (M.noun n) (fun x => and_congr (eval_congr C (push x ρ) σ)
        (eval_congr Q (push x ρ) σ))).trans ((hN n).count _)
    have e2 : (M.noun n).count (fun x => M.eval C (push x ρ) σ ∧ M.eval S (push x ρ) σ) =
        (M'.noun n).count (fun x => M'.eval C (push x ρ) σ ∧ M'.eval S (push x ρ) σ) :=
      (count_congr (M.noun n) (fun x => and_congr (eval_congr C (push x ρ) σ)
        (eval_congr S (push x ρ) σ))).trans ((hN n).count _)
    rw [e1, e2]
  | .pverb q k, _, σ => by
    show M.pverb q (σ k) ↔ M'.pverb q (σ k)
    rw [hp]
  | .among t k, ρ, σ => by
    show t.eval M.name ρ ∈ σ k ↔ t.eval M'.name ρ ∈ σ k
    rw [hn]
  | .coll (.exactly k) n φ, ρ, σ =>
    exists_congr fun X => and_congr ((hN n).pl k X) (eval_congr φ ρ (push X σ))
  | .coll (.atLeast k) n φ, ρ, σ =>
    exists_congr fun j => exists_congr fun X =>
      and_congr Iff.rfl (and_congr ((hN n).pl j X) (eval_congr φ ρ (push X σ)))
  | .the n φ, ρ, σ => by
    show M.eval φ ρ (push (M.noun n).all σ) ↔ M'.eval φ ρ (push (M'.noun n).all σ)
    rw [all_eq (hN n).ext]
    exact eval_congr φ ρ _

end

theorem nEq_set (M : PCtx Noun Verb Rel PVerb Name A) (n0 : Noun) {I I' : NounI A}
    (h : NEq I I') (n : Noun) : NEq ((M.set n0 I).noun n) ((M.set n0 I').noun n) := by
  by_cases hn : n = n0
  · subst hn
    rw [M.set_self, M.set_self]
    exact h
  · rw [M.set_ne I hn, M.set_ne I' hn]
    exact ⟨fun _ => Iff.rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩

/-! ## Pluralities, through the units -/

/-- A plurality of `k` things covering exactly `X` is `k` units, each
meeting `X`, that together cover `X`. -/
theorem pl_iff_keys (I : NounI A) (k : Nat) (X : Finset A) :
    I.pl k X ↔ ∃ K' ⊆ I.keys, K'.card = k ∧ (∀ c ∈ K', ∃ x ∈ I.unit c, x ∈ X) ∧
      ∀ x ∈ X, ∃ c ∈ K', x ∈ I.unit c := by
  constructor
  · rintro ⟨Y, hY, hk⟩
    refine ⟨Y.image I.crit, fun c hc => ?_, hk, fun c hc => ?_, fun x hx => ?_⟩
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
      refine ⟨I.emb y, (I.mem_unit _ _).mpr ⟨y, rfl, rfl⟩, ?_⟩
      rw [← hY]
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    · rw [← hY] at hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨I.crit y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, (I.mem_unit _ _).mpr ⟨y, rfl, rfl⟩⟩
  · rintro ⟨K', -, hk, h1, h2⟩
    refine ⟨Finset.univ.filter (fun y => I.crit y ∈ K' ∧ I.emb y ∈ X), ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hy).2.2
      · intro hx
        obtain ⟨c, hc, hxc⟩ := h2 x hx
        obtain ⟨y, hyc, rfl⟩ := (I.mem_unit _ _).mp hxc
        exact Finset.mem_image.mpr
          ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hyc]; exact hc, hx⟩, rfl⟩
    · rw [← hk]
      congr 1
      ext c
      constructor
      · intro hc
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
        exact (Finset.mem_filter.mp hy).2.1
      · intro hc
        obtain ⟨x, hxu, hxX⟩ := h1 c hc
        obtain ⟨y, hyc, rfl⟩ := (I.mem_unit _ _).mp hxu
        exact Finset.mem_image.mpr
          ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hyc]; exact hc, hxX⟩, hyc⟩

/-- `k` units, as a sub-multiset `m` of the units `u`, each meeting `X`,
together covering `X`. -/
def PlM [Fintype A] (u : Finset A → Nat) (k : Nat) (X : Finset A) : Prop :=
  ∃ m : Finset A → Nat, (∀ S, m S ≤ u S) ∧ ∑ S, m S = k ∧ (∀ S, 0 < m S → ∃ x ∈ S, x ∈ X) ∧
    ∀ x ∈ X, ∃ S, 0 < m S ∧ x ∈ S

/-- **Pluralities depend only on the units.** -/
theorem pl_iff_m [Fintype A] (I : NounI A) (k : Nat) (X : Finset A) :
    I.pl k X ↔ PlM I.units k X := by
  rw [pl_iff_keys]
  constructor
  · rintro ⟨K', hK, hk, h1, h2⟩
    refine ⟨fun S => (K'.filter (fun c => I.unit c = S)).card, fun S => ?_, ?_,
      fun S hS => ?_, fun x hx => ?_⟩
    · exact Finset.card_le_card (Finset.filter_subset_filter _ hK)
    · exact (Finset.card_eq_sum_card_fiberwise (f := I.unit) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)).symm.trans hk
    · obtain ⟨c, hc⟩ := Finset.card_pos.mp hS
      obtain ⟨hcK, rfl⟩ := Finset.mem_filter.mp hc
      exact h1 c hcK
    · obtain ⟨c, hc, hxc⟩ := h2 x hx
      exact ⟨I.unit c, Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, rfl⟩⟩, hxc⟩
  · rintro ⟨m, hm, hs, h1, h2⟩
    have hex : ∀ S, ∃ t ⊆ I.keys.filter (fun c => I.unit c = S), t.card = m S :=
      fun S => Finset.exists_subset_card_eq (hm S)
    choose t ht htc using hex
    have hunit : ∀ S c, c ∈ t S → I.unit c = S ∧ c ∈ I.keys := fun S c hc =>
      ⟨(Finset.mem_filter.mp (ht S hc)).2, (Finset.mem_filter.mp (ht S hc)).1⟩
    refine ⟨Finset.univ.biUnion t, fun c hc => ?_, ?_, fun c hc => ?_, fun x hx => ?_⟩
    · obtain ⟨S, -, hcS⟩ := Finset.mem_biUnion.mp hc
      exact (hunit S c hcS).2
    · calc (Finset.univ.biUnion t).card = ∑ S, (t S).card :=
            Finset.card_biUnion (by
              intro S _ S' _ hne
              exact Finset.disjoint_left.mpr fun c h1 h2 =>
                hne ((hunit S c h1).1.symm.trans (hunit S' c h2).1))
        _ = ∑ S, m S := Finset.sum_congr rfl fun S _ => htc S
        _ = k := hs
    · obtain ⟨S, -, hcS⟩ := Finset.mem_biUnion.mp hc
      have hpos : 0 < m S := by
        rw [← htc S]
        exact Finset.card_pos.mpr ⟨c, hcS⟩
      rw [(hunit S c hcS).1]
      exact h1 S hpos
    · obtain ⟨S, hS, hxS⟩ := h2 x hx
      rw [← htc S] at hS
      obtain ⟨c, hc⟩ := Finset.card_pos.mp hS
      refine ⟨c, Finset.mem_biUnion.mpr ⟨S, Finset.mem_univ _, hc⟩, ?_⟩
      rw [(hunit S c hc).1]
      exact hxS

/-! ## Full abstraction -/

/-- Indistinguishable interpretations have the same counts: the singular
sentence "exactly `j` `n0`s are `v`", with `v` true of `P`. -/
theorem count_of_obs (v : Verb) {n0 : Noun} {I I' : NounI A}
    (h : ObsEqP (Verb := Verb) (Rel := Rel) (PVerb := PVerb) (Name := Name) n0 I I')
    (P : A → Prop) : I.count P = I'.count P := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a⟩⟩
  · rw [FullAbstraction.count_empty I hA, FullAbstraction.count_empty I' hA]
  · let M : PCtx Noun Verb Rel PVerb Name A :=
      ⟨fun _ => I, fun _ => P, fun _ _ _ => False, fun _ _ => False, fun _ => a⟩
    have key : ∀ (J : NounI A) (j : Nat),
        (M.set n0 J).eval (.quant (.exactly j) n0 (.verb v (.var 0)) .top)
          (fun _ => a) (fun _ => ∅) ↔ J.count (fun z => P z ∧ True) = j := by
      intro J j
      show ((M.set n0 J).noun n0).count (fun z => P z ∧ True) = j ↔
        J.count (fun z => P z ∧ True) = j
      rw [M.set_self]
    have h1 := (key I' (I.count (fun z => P z ∧ True))).mp ((h M _ _ _).mp ((key I _).mpr rfl))
    have hPI := count_congr I (P := fun z => P z ∧ True) (P' := P)
      (fun z => ⟨fun hz => hz.1, fun hz => ⟨hz, trivial⟩⟩)
    have hPI' := count_congr I' (P := fun z => P z ∧ True) (P' := P)
      (fun z => ⟨fun hz => hz.1, fun hz => ⟨hz, trivial⟩⟩)
    omega

/-- **Full abstraction with plurals.** Two interpretations of a noun are
indistinguishable by every formula of the plural fragment in every
context exactly when they have the same counting units, with the same
multiplicities. -/
theorem obsEqP_iff [Fintype A] (v : Verb) (n0 : Noun) (I I' : NounI A) :
    ObsEqP (Verb := Verb) (Rel := Rel) (PVerb := PVerb) (Name := Name) n0 I I' ↔
      ∀ S, I.units S = I'.units S := by
  constructor
  · intro h
    have hc := count_of_obs v h
    exact eq_of_meets (by rw [units_empty, units_empty])
      (fun P => (count_meets I P).symm.trans ((hc P).trans (count_meets I' P)))
  · intro hu M φ ρ σ
    have hm : I.units = I'.units := funext hu
    have hc : ∀ P, I.count P = I'.count P := fun P => by
      rw [count_meets, count_meets, hm]
    have hE : ∀ x, I.ext x ↔ I'.ext x := fun x => by
      rw [ext_iff_count, ext_iff_count, hc]
    have hp : ∀ k X, I.pl k X ↔ I'.pl k X := fun k X => by
      rw [pl_iff_m, pl_iff_m, hm]
    exact eval_congr (M := M.set n0 I) (M' := M.set n0 I') rfl rfl rfl rfl (nEq_set M n0 ⟨hE, hc, hp⟩) φ ρ σ

end FraCaS.Encodings.FullAbstractionPlural
