import EndToEnd.Encodings.FullAbstraction

/-!
# Full abstraction in intensional contexts

`FullAbstraction.lean` shows that what the fragment's sentences see of a
noun with one identity criterion is its counting units. That fragment is
extensional. This file adds possible worlds and intensional operators,
and asks whether they see more.

**The fragment (`IForm`).** Everything in `Relational.Form`, plus:

- `nec φ`, "necessarily `φ`": `φ` at every accessible world;
- `believes t φ`, "`t` believes that `φ`": `φ` at every world compatible
  with what `t` believes there. `t` may be a bound variable, so "every
  student believes that some book is long" has its de re and de dicto
  readings by scope;
- `thinks t φ`, a **hyperintensional** attitude: a relation between `t`,
  the world, and the sentence `φ` itself (with its assignment), not the
  set of worlds where `φ` is true.

A context (`ICtx`) gives each noun an interpretation at each world (a
type, an embedding and a criterion, which may vary from world to world),
verbs and relations at each world, rigid names, an accessibility
relation, belief accessibility for each individual, and what each
individual `thinks` at each world.

**`obsEqW_iff`.** Two world-indexed interpretations of a noun are
indistinguishable by every formula, in every context and at every world,
exactly when at every world they have the same counting units with the
same multiplicities. So in intensional contexts a count noun means a
function from worlds to multisets of units, and nothing more.

**`obsEqW_byInd_iff` (Montague's intensions, recovered).** For nouns that
count individuals, two interpretations are indistinguishable exactly
when their extensions agree at every world: the noun means its
intension, a property.

**Hyperintensionality is in the attitude, not the noun.**
- Possible-worlds belief cannot tell apart two nouns with the same
  interpretation at every world (`believes_same`).
- The hyperintensional attitude can (`thinks_distinguishes`), but it
  sees the noun's *symbol*: two different nouns with literally the same
  interpretation are told apart. So it gives finer distinctions whatever
  nouns denote, types or predicates; and it does not see the
  interpretation, so full abstraction is unchanged.

Worlds can be any type; the domain is finite and the same at every world.
-/

namespace FraCaS.Encodings.FullAbstractionIntensional
open FraCaS.Encodings.Typed FraCaS.Encodings.Counting FraCaS.Encodings.Equivalence
open FraCaS.Encodings.Relational
open FraCaS.Encodings.FullAbstraction (NounI detBy_obs count_meets ext_iff_count eq_of_meets
  units_empty count_congr count_byInd)
open Classical

/-! ## The intensional fragment -/

inductive IForm (Noun Verb Rel Name : Type) where
  | verb : Verb → Term Name → IForm Noun Verb Rel Name
  | rel : Rel → Term Name → Term Name → IForm Noun Verb Rel Name
  | isA : Noun → Term Name → IForm Noun Verb Rel Name
  | eq : Term Name → Term Name → IForm Noun Verb Rel Name
  | top : IForm Noun Verb Rel Name
  | not : IForm Noun Verb Rel Name → IForm Noun Verb Rel Name
  | and : IForm Noun Verb Rel Name → IForm Noun Verb Rel Name → IForm Noun Verb Rel Name
  | or : IForm Noun Verb Rel Name → IForm Noun Verb Rel Name → IForm Noun Verb Rel Name
  | imp : IForm Noun Verb Rel Name → IForm Noun Verb Rel Name → IForm Noun Verb Rel Name
  /-- `d` noun `n` that `C` are `Q`: binds variable `0` -/
  | quant : Det → Noun → IForm Noun Verb Rel Name → IForm Noun Verb Rel Name →
      IForm Noun Verb Rel Name
  | more : Noun → IForm Noun Verb Rel Name → IForm Noun Verb Rel Name →
      IForm Noun Verb Rel Name → IForm Noun Verb Rel Name
  /-- "necessarily `φ`" -/
  | nec : IForm Noun Verb Rel Name → IForm Noun Verb Rel Name
  /-- "`t` believes that `φ`", over possible worlds -/
  | believes : Term Name → IForm Noun Verb Rel Name → IForm Noun Verb Rel Name
  /-- "`t` thinks that `φ`", a relation to the sentence itself -/
  | thinks : Term Name → IForm Noun Verb Rel Name → IForm Noun Verb Rel Name

variable {Noun Verb Rel Name W A : Type}

structure ICtx (Noun Verb Rel Name W A : Type) where
  noun : Noun → W → NounI A
  verb : Verb → W → A → Prop
  rel : Rel → W → A → A → Prop
  name : Name → A
  acc : W → W → Prop
  dox : A → W → W → Prop
  thought : A → W → IForm Noun Verb Rel Name → (Nat → A) → Prop

noncomputable def ICtx.eval (M : ICtx Noun Verb Rel Name W A) :
    IForm Noun Verb Rel Name → W → (Nat → A) → Prop
  | .verb v t, w, ρ => M.verb v w (t.eval M.name ρ)
  | .rel r t u, w, ρ => M.rel r w (t.eval M.name ρ) (u.eval M.name ρ)
  | .isA n t, w, ρ => (M.noun n w).ext (t.eval M.name ρ)
  | .eq t u, _, ρ => t.eval M.name ρ = u.eval M.name ρ
  | .top, _, _ => True
  | .not φ, w, ρ => ¬ M.eval φ w ρ
  | .and φ ψ, w, ρ => M.eval φ w ρ ∧ M.eval ψ w ρ
  | .or φ ψ, w, ρ => M.eval φ w ρ ∨ M.eval ψ w ρ
  | .imp φ ψ, w, ρ => M.eval φ w ρ → M.eval ψ w ρ
  | .quant d n C Q, w, ρ =>
    detBy (M.noun n w).count (M.noun n w).emb d (fun x => M.eval C w (push x ρ))
      (fun x => M.eval Q w (push x ρ))
  | .more n C Q S, w, ρ =>
    (M.noun n w).count (fun x => M.eval C w (push x ρ) ∧ M.eval Q w (push x ρ)) >
      (M.noun n w).count (fun x => M.eval C w (push x ρ) ∧ M.eval S w (push x ρ))
  | .nec φ, w, ρ => ∀ w', M.acc w w' → M.eval φ w' ρ
  | .believes t φ, w, ρ => ∀ w', M.dox (t.eval M.name ρ) w w' → M.eval φ w' ρ
  | .thinks t φ, w, ρ => M.thought (t.eval M.name ρ) w φ ρ

noncomputable def ICtx.set (M : ICtx Noun Verb Rel Name W A) (n0 : Noun) (I : W → NounI A) :
    ICtx Noun Verb Rel Name W A :=
  { M with noun := fun n => if n = n0 then I else M.noun n }

theorem ICtx.set_self (M : ICtx Noun Verb Rel Name W A) (n0 : Noun) (I : W → NounI A) :
    (M.set n0 I).noun n0 = I := if_pos rfl

theorem ICtx.set_ne (M : ICtx Noun Verb Rel Name W A) {n n0 : Noun} (I : W → NounI A)
    (h : n ≠ n0) : (M.set n0 I).noun n = M.noun n := if_neg h

/-- Two world-indexed interpretations of `n0` are indistinguishable: no
formula, in no context, at no world, tells them apart. -/
def ObsEqW (n0 : Noun) (I I' : W → NounI A) : Prop :=
  ∀ (M : ICtx Noun Verb Rel Name W A) (φ : IForm Noun Verb Rel Name) (w : W) (ρ : Nat → A),
    (M.set n0 I).eval φ w ρ ↔ (M.set n0 I').eval φ w ρ

/-! ## Agreement -/

/-- Nouns that agree on extension and counts. -/
structure NEq (J J' : NounI A) : Prop where
  ext : ∀ x, J.ext x ↔ J'.ext x
  count : ∀ P, J.count P = J'.count P

theorem detBy_congr {T : Type} (cnt : (A → Prop) → Nat) (e : T → A) (d : Det)
    {C C' Q Q' : A → Prop} (hC : ∀ x, C x ↔ C' x) (hQ : ∀ x, Q x ↔ Q' x) :
    detBy cnt e d C Q ↔ detBy cnt e d C' Q' := by
  obtain rfl : C = C' := funext fun x => propext (hC x)
  obtain rfl : Q = Q' := funext fun x => propext (hQ x)
  exact Iff.rfl

section
variable {M M' : ICtx Noun Verb Rel Name W A} (hv : M.verb = M'.verb) (hr : M.rel = M'.rel)
  (hn : M.name = M'.name) (ha : M.acc = M'.acc) (hd : M.dox = M'.dox)
  (ht : M.thought = M'.thought) (hN : ∀ n w, NEq (M.noun n w) (M'.noun n w))
include hv hr hn ha hd ht hN

/-- Contexts that agree on everything but nouns, with nouns that agree
on extension and counts at every world, agree on every formula at every
world. -/
theorem eval_congr : ∀ (φ : IForm Noun Verb Rel Name) (w : W) (ρ : Nat → A),
    M.eval φ w ρ ↔ M'.eval φ w ρ
  | .verb v t, w, ρ => by
    show M.verb v w (t.eval M.name ρ) ↔ M'.verb v w (t.eval M'.name ρ)
    rw [hv, hn]
  | .rel r t u, w, ρ => by
    show M.rel r w (t.eval M.name ρ) (u.eval M.name ρ) ↔
      M'.rel r w (t.eval M'.name ρ) (u.eval M'.name ρ)
    rw [hr, hn]
  | .isA n t, w, ρ => by
    show (M.noun n w).ext (t.eval M.name ρ) ↔ (M'.noun n w).ext (t.eval M'.name ρ)
    rw [hn]
    exact (hN n w).ext _
  | .eq t u, w, ρ => by
    show t.eval M.name ρ = u.eval M.name ρ ↔ t.eval M'.name ρ = u.eval M'.name ρ
    rw [hn]
  | .top, _, _ => Iff.rfl
  | .not φ, w, ρ => not_congr (eval_congr φ w ρ)
  | .and φ ψ, w, ρ => and_congr (eval_congr φ w ρ) (eval_congr ψ w ρ)
  | .or φ ψ, w, ρ => or_congr (eval_congr φ w ρ) (eval_congr ψ w ρ)
  | .imp φ ψ, w, ρ => imp_congr (eval_congr φ w ρ) (eval_congr ψ w ρ)
  | .quant d n C Q, w, ρ => by
    show detBy (M.noun n w).count (M.noun n w).emb d (fun x => M.eval C w (push x ρ))
        (fun x => M.eval Q w (push x ρ)) ↔
      detBy (M'.noun n w).count (M'.noun n w).emb d (fun x => M'.eval C w (push x ρ))
        (fun x => M'.eval Q w (push x ρ))
    exact (detBy_congr _ _ d (fun x => eval_congr C w (push x ρ))
      (fun x => eval_congr Q w (push x ρ))).trans
      (detBy_obs _ _ (hN n w).ext (hN n w).count d _ _)
  | .more n C Q S, w, ρ => by
    show (M.noun n w).count (fun x => M.eval C w (push x ρ) ∧ M.eval Q w (push x ρ)) >
        (M.noun n w).count (fun x => M.eval C w (push x ρ) ∧ M.eval S w (push x ρ)) ↔
      (M'.noun n w).count (fun x => M'.eval C w (push x ρ) ∧ M'.eval Q w (push x ρ)) >
        (M'.noun n w).count (fun x => M'.eval C w (push x ρ) ∧ M'.eval S w (push x ρ))
    have e1 : (M.noun n w).count (fun x => M.eval C w (push x ρ) ∧ M.eval Q w (push x ρ)) =
        (M'.noun n w).count (fun x => M'.eval C w (push x ρ) ∧ M'.eval Q w (push x ρ)) :=
      (count_congr (M.noun n w) (fun x => and_congr (eval_congr C w (push x ρ))
        (eval_congr Q w (push x ρ)))).trans ((hN n w).count _)
    have e2 : (M.noun n w).count (fun x => M.eval C w (push x ρ) ∧ M.eval S w (push x ρ)) =
        (M'.noun n w).count (fun x => M'.eval C w (push x ρ) ∧ M'.eval S w (push x ρ)) :=
      (count_congr (M.noun n w) (fun x => and_congr (eval_congr C w (push x ρ))
        (eval_congr S w (push x ρ)))).trans ((hN n w).count _)
    rw [e1, e2]
  | .nec φ, w, ρ => by
    show (∀ w', M.acc w w' → M.eval φ w' ρ) ↔ (∀ w', M'.acc w w' → M'.eval φ w' ρ)
    rw [ha]
    exact forall_congr' fun w' => imp_congr Iff.rfl (eval_congr φ w' ρ)
  | .believes t φ, w, ρ => by
    show (∀ w', M.dox (t.eval M.name ρ) w w' → M.eval φ w' ρ) ↔
      (∀ w', M'.dox (t.eval M'.name ρ) w w' → M'.eval φ w' ρ)
    rw [hd, hn]
    exact forall_congr' fun w' => imp_congr Iff.rfl (eval_congr φ w' ρ)
  | .thinks t φ, w, ρ => by
    show M.thought (t.eval M.name ρ) w φ ρ ↔ M'.thought (t.eval M'.name ρ) w φ ρ
    rw [ht, hn]

end

theorem nEq_set (M : ICtx Noun Verb Rel Name W A) (n0 : Noun) {I I' : W → NounI A}
    (h : ∀ w, NEq (I w) (I' w)) (n : Noun) (w : W) :
    NEq ((M.set n0 I).noun n w) ((M.set n0 I').noun n w) := by
  by_cases hn : n = n0
  · subst hn
    rw [M.set_self, M.set_self]
    exact h w
  · rw [M.set_ne I hn, M.set_ne I' hn]
    exact ⟨fun _ => Iff.rfl, fun _ => rfl⟩

/-! ## Reading off counts and extensions at a world -/

/-- A context that interprets every noun by `I`, the verbs by `V`, and
nothing else. -/
noncomputable def ctxOf (I : W → NounI A) (V : W → A → Prop) (a : A) :
    ICtx Noun Verb Rel Name W A :=
  ⟨fun _ => I, fun _ => V, fun _ _ _ _ => False, fun _ => a, fun _ _ => False,
    fun _ _ _ => False, fun _ _ _ _ => False⟩

/-- Indistinguishable interpretations have the same counts at every
world: "exactly `j` `n0`s are `v`", evaluated there. -/
theorem count_of_obs (v : Verb) {n0 : Noun} {I I' : W → NounI A}
    (h : ObsEqW (Verb := Verb) (Rel := Rel) (Name := Name) n0 I I') (w : W) (P : A → Prop) :
    (I w).count P = (I' w).count P := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a⟩⟩
  · rw [FullAbstraction.count_empty (I w) hA, FullAbstraction.count_empty (I' w) hA]
  · let M : ICtx Noun Verb Rel Name W A := ctxOf I (fun _ => P) a
    have key : ∀ (J : W → NounI A) (j : Nat),
        (M.set n0 J).eval (.quant (.exactly j) n0 (.verb v (.var 0)) .top) w (fun _ => a) ↔
          (J w).count (fun z => P z ∧ True) = j := by
      intro J j
      show ((M.set n0 J).noun n0 w).count (fun z => P z ∧ True) = j ↔
        (J w).count (fun z => P z ∧ True) = j
      rw [M.set_self]
    have h1 := (key I' ((I w).count (fun z => P z ∧ True))).mp
      ((h M _ _ _).mp ((key I _).mpr rfl))
    have hPI := count_congr (I w) (P := fun z => P z ∧ True) (P' := P)
      (fun z => ⟨fun hz => hz.1, fun hz => ⟨hz, trivial⟩⟩)
    have hPI' := count_congr (I' w) (P := fun z => P z ∧ True) (P' := P)
      (fun z => ⟨fun hz => hz.1, fun hz => ⟨hz, trivial⟩⟩)
    omega

/-- Indistinguishable interpretations have the same extension at every
world: "some `n0` is `v`", with `v` true of one individual. -/
theorem ext_of_obs (v : Verb) {n0 : Noun} {I I' : W → NounI A}
    (h : ObsEqW (Verb := Verb) (Rel := Rel) (Name := Name) n0 I I') (w : W) (x : A) :
    (I w).ext x ↔ (I' w).ext x := by
  let M : ICtx Noun Verb Rel Name W A := ctxOf I (fun _ y => y = x) x
  have key : ∀ J : W → NounI A,
      (M.set n0 J).eval (.quant .some n0 (.verb v (.var 0)) .top) w (fun _ => x) ↔
        (J w).ext x := by
    intro J
    show SomeT ((M.set n0 J).noun n0 w).emb (fun y => y = x) (fun _ => True) ↔ (J w).ext x
    rw [M.set_self]
    exact ⟨fun ⟨y, hy, _⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy, trivial⟩⟩
  exact (key I).symm.trans ((h M _ _ _).trans (key I'))

/-! ## Full abstraction -/

/-- **Full abstraction in intensional contexts.** Two world-indexed
interpretations of a noun are indistinguishable by every formula, in
every context, at every world, exactly when at every world they have the
same counting units with the same multiplicities. -/
theorem obsEqW_iff [Fintype A] (v : Verb) (n0 : Noun) (I I' : W → NounI A) :
    ObsEqW (Verb := Verb) (Rel := Rel) (Name := Name) n0 I I' ↔
      ∀ w S, (I w).units S = (I' w).units S := by
  constructor
  · intro h w
    exact eq_of_meets (by rw [units_empty, units_empty])
      (fun P => (count_meets (I w) P).symm.trans
        ((count_of_obs v h w P).trans (count_meets (I' w) P)))
  · intro hu M φ w ρ
    have hN : ∀ w, NEq (I w) (I' w) := fun w => by
      have hm : (I w).units = (I' w).units := funext (hu w)
      have hc : ∀ P, (I w).count P = (I' w).count P := fun P => by
        rw [count_meets, count_meets, hm]
      exact ⟨fun x => by rw [ext_iff_count, ext_iff_count, hc], hc⟩
    exact eval_congr (M := M.set n0 I) (M' := M.set n0 I') rfl rfl rfl rfl rfl rfl
      (nEq_set M n0 hN) φ w ρ

/-- **Montague's intensions, recovered.** For nouns that count
individuals, two interpretations are indistinguishable exactly when
their extensions agree at every world. -/
theorem obsEqW_byInd_iff [Fintype A] (v : Verb) (n0 : Noun) (I J : W → NounI A) :
    ObsEqW (Verb := Verb) (Rel := Rel) (Name := Name) n0
        (fun w => (I w).byInd) (fun w => (J w).byInd) ↔
      ∀ w x, (I w).ext x ↔ (J w).ext x := by
  constructor
  · intro h w x
    exact ext_of_obs v h w x
  · intro hE M φ w ρ
    have hN : ∀ w, NEq (I w).byInd (J w).byInd := fun w =>
      ⟨fun x => hE w x, fun P => by
        rw [count_byInd, count_byInd]
        congr 1
        exact Finset.filter_congr (fun x _ => and_congr (hE w x) Iff.rfl)⟩
    exact eval_congr (M := M.set n0 (fun w => (I w).byInd)) (M' := M.set n0 (fun w => (J w).byInd))
      rfl rfl rfl rfl rfl rfl (nEq_set M n0 hN) φ w ρ

/-! ## Hyperintensionality is in the attitude -/

/-- "Every `k` is an `n1`". -/
def everyIs (k n1 : Noun) : IForm Noun Verb Rel Name := .quant .every k .top (.isA n1 (.var 0))

/-- **Possible-worlds belief does not tell apart nouns with the same
interpretation at every world.** -/
theorem believes_same (M : ICtx Noun Verb Rel Name W A) {n1 n2 : Noun}
    (h : M.noun n1 = M.noun n2) (t : Term Name) (w : W) (ρ : Nat → A) :
    M.eval (.believes t (everyIs n1 n1)) w ρ ↔ M.eval (.believes t (everyIs n2 n1)) w ρ := by
  simp only [ICtx.eval, everyIs, h]

/-- **The hyperintensional attitude does**, even when the two nouns have
literally the same interpretation: it sees which noun the sentence
uses. -/
theorem thinks_distinguishes {n1 n2 : Noun} (hne : n1 ≠ n2) (I : W → NounI A) (a : A)
    (V : Verb → W → A → Prop) (R : Rel → W → A → A → Prop) (w : W) :
    ∃ M : ICtx Noun Verb Rel Name W A, M.noun n1 = I ∧ M.noun n2 = I ∧
      M.eval (.thinks (.var 0) (everyIs n1 n1)) w (fun _ => a) ∧
      ¬ M.eval (.thinks (.var 0) (everyIs n2 n1)) w (fun _ => a) := by
  refine ⟨⟨fun _ => I, V, R, fun _ => a, fun _ _ => False, fun _ _ _ => False,
    fun _ _ φ _ => φ = everyIs n1 n1⟩, rfl, rfl, ?_, ?_⟩
  · show everyIs n1 n1 = everyIs n1 n1
    rfl
  · show ¬ (everyIs n2 n1 = everyIs n1 n1)
    intro he
    exact hne (IForm.quant.inj he).2.1.symm

end FraCaS.Encodings.FullAbstractionIntensional

/-- info: 'FraCaS.Encodings.FullAbstractionIntensional.obsEqW_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.FullAbstractionIntensional.obsEqW_iff

/-- info: 'FraCaS.Encodings.FullAbstractionIntensional.obsEqW_byInd_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FraCaS.Encodings.FullAbstractionIntensional.obsEqW_byInd_iff
