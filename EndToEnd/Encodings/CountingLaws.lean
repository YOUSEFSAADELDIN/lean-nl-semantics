import EndToEnd.Encodings.FullAbstraction

/-!
# Laws of counting: what count nouns are

The files so far compare encodings. This one states what a count noun
with one identity criterion is, by laws on how it counts, and proves
that the encodings are representations of it.

A noun's **counting function** says, for each property `P`, how many of
the noun's things are `P` (`NounI.count`). By full abstraction
(`FullAbstraction.obsEq_iff`) it is all that sentences see of the noun.

**Representation (`representation`, `units_unique`).** A function `f`
is the counting function of some noun with one criterion exactly when
`f P = ∑_S u S · [S meets P]` for some `u` assigning each nonempty set of
individuals a number of units; `u` is then unique (and is the noun's
`units`). In combinatorics such `f` are *coverage functions*, and `u`
their W-coefficients: Chakrabarty & Huang (2012, "Testing coverage
functions", ICALP, Thm 1.1) characterize them as the functions whose
W-coefficients are nonnegative. So representation and uniqueness are
known mathematics; what is new here is that count nouns are exactly the
integer coverage functions.

**A typology by laws.** Two laws, each stated only in terms of counts:

- **additive**: `count (P ∪ Q) + count (P ∩ Q) = count P + count Q`;
- **single**: no individual is counted more than once,
  `count {x} ≤ 1`.

Each matches a property of the noun's structure:

- additive exactly when the noun **never merges** individuals: things
  counted as one are one individual (`additive_iff`);
- single exactly when it **never splits** an individual: things that are
  one individual count as one (`single_iff`).

| | never splits | splits |
|---|---|---|
| never merges | Montague nouns | passengers (`passengers`) |
| merges | copies counted as texts (`copies`) | anthologies counted as texts (`anthologies`) |

- **Montague nouns** obey both laws, and are exactly the nouns that count
  as their extension does (`montague_iff`), indistinguishable from
  counting individuals (`montague_obsEq`). This is the characterization
  theorem (`Characterization.lean`), restated as laws of counting.
- Every noun with one criterion obeys the weaker law
  `count (P ∪ Q) + count (P ∩ Q) ≤ count P + count Q` (`count_submod`).
  Copredicated nouns, counted by two criteria at once, can break it
  (`FullAbstractionMulti.not_single`): that law separates one criterion
  from several.

All four cells are inhabited, with two distinct individuals
(`cells_inhabited`), so the laws are independent.
-/

namespace FraCaS.Encodings.CountingLaws
open FraCaS.Encodings.Typed FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence
open FraCaS.Encodings.FullAbstraction (NounI count_meets meetsSum eq_of_meets units_empty
  obsEq_iff)
open Classical

variable {A : Type}

/-! ## Laws and structure -/

/-- Counts add up: `count (P ∪ Q) + count (P ∩ Q) = count P + count Q`. -/
def Additive (I : NounI A) : Prop :=
  ∀ P Q : A → Prop,
    I.count (fun x => P x ∨ Q x) + I.count (fun x => P x ∧ Q x) = I.count P + I.count Q

/-- No individual is counted more than once. -/
def Single (I : NounI A) : Prop := ∀ x : A, I.count (fun z => z = x) ≤ 1

/-- Things counted as one are one individual. -/
def NoMerge (I : NounI A) : Prop := ∀ y y', I.crit y = I.crit y' → I.emb y = I.emb y'

/-- Things that are one individual count as one. -/
def NoSplit (I : NounI A) : Prop := ∀ y y', I.emb y = I.emb y' → I.crit y = I.crit y'

/-- The criterion's values on the `P`s. -/
noncomputable def img (I : NounI A) (P : A → Prop) : Finset I.K :=
  (Finset.univ.filter (fun y => P (I.emb y))).image I.crit

theorem count_img (I : NounI A) (P : A → Prop) : I.count P = (img I P).card := rfl

theorem mem_img (I : NounI A) (P : A → Prop) (k : I.K) :
    k ∈ img I P ↔ ∃ y, P (I.emb y) ∧ I.crit y = k := by
  unfold img
  constructor
  · intro hk
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨y, (Finset.mem_filter.mp hy).2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩

theorem img_or (I : NounI A) (P Q : A → Prop) :
    img I (fun x => P x ∨ Q x) = img I P ∪ img I Q := by
  ext k
  rw [mem_img, Finset.mem_union, mem_img, mem_img]
  constructor
  · rintro ⟨y, h | h, rfl⟩
    · exact Or.inl ⟨y, h, rfl⟩
    · exact Or.inr ⟨y, h, rfl⟩
  · rintro (⟨y, h, rfl⟩ | ⟨y, h, rfl⟩)
    · exact ⟨y, Or.inl h, rfl⟩
    · exact ⟨y, Or.inr h, rfl⟩

theorem img_and (I : NounI A) (P Q : A → Prop) :
    img I (fun x => P x ∧ Q x) ⊆ img I P ∩ img I Q := by
  intro k hk
  obtain ⟨y, ⟨h1, h2⟩, rfl⟩ := (mem_img I _ k).mp hk
  exact Finset.mem_inter.mpr ⟨(mem_img I P _).mpr ⟨y, h1, rfl⟩, (mem_img I Q _).mpr ⟨y, h2, rfl⟩⟩

/-- **Every noun with one criterion counts submodularly.** -/
theorem count_submod (I : NounI A) (P Q : A → Prop) :
    I.count (fun x => P x ∨ Q x) + I.count (fun x => P x ∧ Q x) ≤ I.count P + I.count Q := by
  rw [count_img, count_img, count_img, count_img, img_or]
  have e := Finset.card_union_add_card_inter (img I P) (img I Q)
  have l := Finset.card_le_card (img_and I P Q)
  omega

/-! ## Each law is a property of the structure -/

/-- **Additive exactly when the noun never merges individuals.** -/
theorem additive_iff (I : NounI A) : Additive I ↔ NoMerge I := by
  constructor
  · intro h y y' hc
    by_contra hne
    have e := h (fun z => z = I.emb y) (fun z => z = I.emb y')
    have h0 : (img I (fun z => z = I.emb y ∧ z = I.emb y')).card = 0 := by
      by_contra h0
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
      obtain ⟨z, ⟨h1, h2⟩, -⟩ := (mem_img I _ k).mp hk
      exact hne (h1.symm.trans h2)
    rw [count_img, count_img, count_img, count_img, img_or, h0] at e
    have e2 := Finset.card_union_add_card_inter (img I (fun z => z = I.emb y))
      (img I (fun z => z = I.emb y'))
    have hin : I.crit y ∈ img I (fun z => z = I.emb y) ∩ img I (fun z => z = I.emb y') :=
      Finset.mem_inter.mpr ⟨(mem_img I _ _).mpr ⟨y, rfl, rfl⟩, (mem_img I _ _).mpr ⟨y', rfl, hc.symm⟩⟩
    have hpos := Finset.card_pos.mpr ⟨_, hin⟩
    omega
  · intro h P Q
    rw [count_img, count_img, count_img, count_img, img_or]
    have heq : img I (fun x => P x ∧ Q x) = img I P ∩ img I Q := by
      refine Finset.Subset.antisymm (img_and I P Q) fun k hk => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hk
      obtain ⟨y, hy, rfl⟩ := (mem_img I P k).mp h1
      obtain ⟨y', hy', hc⟩ := (mem_img I Q _).mp h2
      exact (mem_img I _ _).mpr ⟨y, ⟨hy, h y' y hc ▸ hy'⟩, rfl⟩
    rw [heq]
    exact Finset.card_union_add_card_inter _ _

/-- **Single exactly when the noun never splits an individual.** -/
theorem single_iff (I : NounI A) : Single I ↔ NoSplit I := by
  constructor
  · intro h y y' he
    by_contra hne
    have hlt : 1 < I.count (fun z => z = I.emb y) :=
      one_lt_countBy_of (f := I.crit) (x := y) (y := y') rfl he.symm hne
    exact absurd (h (I.emb y)) (not_le.mpr hlt)
  · intro h x
    exact countBy_le_one_of fun y y' hy hy' => h y y' (hy.trans hy'.symm)

/-! ## Montague nouns -/

theorem byInd_noMerge (I : NounI A) : NoMerge I.byInd := fun _ _ h => h

theorem byInd_noSplit (I : NounI A) : NoSplit I.byInd := fun _ _ h => h

/-- **Montague nouns are the nouns that obey both laws**: they count
exactly as their extension does. -/
theorem montague_iff (I : NounI A) :
    (NoMerge I ∧ NoSplit I) ↔ ∀ P, I.count P = I.byInd.count P := by
  constructor
  · rintro ⟨h1, h2⟩ P
    unfold NounI.count
    exact countBy_eq_of_kernel fun y y' _ _ => ⟨h1 y y', h2 y y'⟩
  · intro h
    have hA : Additive I := by
      intro P Q
      rw [h, h, h, h]
      exact (additive_iff I.byInd).mpr (byInd_noMerge I) P Q
    have hS : Single I := fun x => by
      rw [h]
      exact (single_iff I.byInd).mpr (byInd_noSplit I) x
    exact ⟨(additive_iff I).mp hA, (single_iff I).mp hS⟩

/-- ... and so exactly the nouns no sentence tells apart from counting
individuals. -/
theorem montague_obsEq [Fintype A] {Noun Verb Rel Name : Type} (v : Verb) (n0 : Noun)
    (I : NounI A) :
    (NoMerge I ∧ NoSplit I) ↔
      FullAbstraction.ObsEq (Verb := Verb) (Rel := Rel) (Name := Name) n0 I I.byInd := by
  rw [montague_iff, obsEq_iff v n0]
  constructor
  · intro h
    exact eq_of_meets (by rw [units_empty, units_empty])
      (fun P => (count_meets I P).symm.trans ((h P).trans (count_meets I.byInd P)))
  · intro hu P
    rw [count_meets, count_meets, funext hu]

/-! ## The four cells -/

/-- One person on two journeys: splits, never merges. -/
def passengers (j : A) : NounI A := ⟨Bool, inferInstance, fun _ => j, Bool, id⟩

/-- Two copies of one text, counted as texts: merges, never splits. -/
def copies (a c : A) : NounI A := ⟨Bool, inferInstance, fun b => cond b a c, Unit, fun _ => ()⟩

/-- Two volumes, each holding the same two texts, counted as texts:
merges and splits. -/
def anthologies (a c : A) : NounI A :=
  ⟨Bool × Bool, inferInstance, fun p => cond p.1 a c, Bool, fun p => p.2⟩

theorem passengers_cell (j : A) : NoMerge (passengers j) ∧ ¬ NoSplit (passengers j) :=
  ⟨fun _ _ _ => rfl, fun h => Bool.false_ne_true (h false true rfl)⟩

theorem copies_cell {a c : A} (hac : a ≠ c) : ¬ NoMerge (copies a c) ∧ NoSplit (copies a c) :=
  ⟨fun h => hac (h true false rfl), fun _ _ _ => rfl⟩

theorem anthologies_cell {a c : A} (hac : a ≠ c) :
    ¬ NoMerge (anthologies a c) ∧ ¬ NoSplit (anthologies a c) :=
  ⟨fun h => hac (h (true, true) (false, true) rfl),
   fun h => Bool.false_ne_true (h (true, false) (true, true) rfl)⟩

/-- **The laws are independent**: with two individuals, every cell of the
table is inhabited. -/
theorem cells_inhabited {a c : A} (hac : a ≠ c) :
    (∃ I : NounI A, NoMerge I ∧ NoSplit I) ∧ (∃ I : NounI A, NoMerge I ∧ ¬ NoSplit I) ∧
      (∃ I : NounI A, ¬ NoMerge I ∧ NoSplit I) ∧ (∃ I : NounI A, ¬ NoMerge I ∧ ¬ NoSplit I) :=
  ⟨⟨(passengers a).byInd, byInd_noMerge _, byInd_noSplit _⟩, ⟨_, passengers_cell a⟩,
   ⟨_, copies_cell hac⟩, ⟨_, anthologies_cell hac⟩⟩

/-! ## Representation -/

/-- The noun with `u S` units covering each set `S`. -/
noncomputable def ofUnits [Fintype A] (u : Finset A → Nat) : NounI A :=
  ⟨(S : Finset A) × (Fin (u S) × {x // x ∈ S}), inferInstance, fun t => t.2.2.1,
    (S : Finset A) × Fin (u S), fun t => ⟨t.1, t.2.1⟩⟩

theorem count_ofUnits [Fintype A] (u : Finset A → Nat) (P : A → Prop) :
    (ofUnits u).count P = meetsSum u P := by
  have himg : img (ofUnits u) P =
      ((Finset.univ.filter (fun R : Finset A => ∃ x ∈ R, P x)).sigma
        (fun R => (Finset.univ : Finset (Fin (u R)))) : Finset ((S : Finset A) × Fin (u S))) := by
    ext ⟨R, i⟩
    constructor
    · intro h
      obtain ⟨⟨R', i', x⟩, hP, he⟩ := (mem_img (ofUnits u) P _).mp h
      obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp he
      exact Finset.mem_sigma.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.1, x.2, hP⟩, Finset.mem_univ _⟩
    · intro h
      obtain ⟨hR, -⟩ := Finset.mem_sigma.mp h
      obtain ⟨x, hx, hP⟩ := (Finset.mem_filter.mp hR).2
      exact (mem_img (ofUnits u) P _).mpr ⟨⟨R, i, ⟨x, hx⟩⟩, hP, rfl⟩
  calc (ofUnits u).count P = (img (ofUnits u) P).card := count_img _ _
    _ = ((Finset.univ.filter (fun R : Finset A => ∃ x ∈ R, P x)).sigma
          (fun R => (Finset.univ : Finset (Fin (u R))))).card := congrArg Finset.card himg
    _ = ∑ R ∈ Finset.univ.filter (fun R : Finset A => ∃ x ∈ R, P x),
          (Finset.univ : Finset (Fin (u R))).card := Finset.card_sigma _ _
    _ = meetsSum u P := by
      rw [Finset.sum_filter]
      unfold meetsSum
      refine Finset.sum_congr rfl fun R _ => ?_
      split_ifs <;> simp

/-- **Representation.** A counting function comes from a noun with one
criterion exactly when it is `P ↦ ∑_S u S · [S meets P]` for some `u`:
an integer coverage function. -/
theorem representation [Fintype A] (f : (A → Prop) → Nat) :
    (∃ I : NounI A, ∀ P, I.count P = f P) ↔
      ∃ u : Finset A → Nat, u ∅ = 0 ∧ ∀ P, f P = meetsSum u P := by
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨I.units, units_empty I, fun P => (hI P).symm.trans (count_meets I P)⟩
  · rintro ⟨u, -, hu⟩
    exact ⟨ofUnits u, fun P => (count_ofUnits u P).trans (hu P).symm⟩

/-- **Uniqueness.** The units are determined by the counting function. -/
theorem units_unique [Fintype A] {u u' : Finset A → Nat} (h0 : u ∅ = 0) (h0' : u' ∅ = 0)
    (h : ∀ P, meetsSum u P = meetsSum u' P) : u = u' :=
  funext (eq_of_meets (h0.trans h0'.symm) h)

/-- The noun built from `u` has exactly `u`'s units. -/
theorem units_ofUnits [Fintype A] (u : Finset A → Nat) (h0 : u ∅ = 0) : (ofUnits u).units = u :=
  units_unique (units_empty _) h0 fun P => (count_meets _ P).symm.trans (count_ofUnits u P)

end FraCaS.Encodings.CountingLaws

/-- info: 'FraCaS.Encodings.CountingLaws.representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.CountingLaws.representation

/-- info: 'FraCaS.Encodings.CountingLaws.montague_obsEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.CountingLaws.montague_obsEq
