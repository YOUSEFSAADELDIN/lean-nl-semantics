import EndToEnd.Encodings.Section5
import EndToEnd.Encodings.Section3

/-!
# What each encoding commits to on FraCaS 215

A prover's "unknown" can mean the claim is false in the encoding or that
the prover did not find a proof. For FraCaS 215 ("All competent legal
authorities are competent law lecturers", gold unknown) this file settles
which, for the generated claims themselves:

- in P (extensional Montague) the "yes" claim is *valid*: coextensive
  nouns are equal predicates (`funext`, `propext`), so every adjective
  treats them alike (`MTT/Intensionality.lean`'s `extensional_forces_215`,
  here for the generated claim). P commits to the wrong answer, whatever
  a prover finds.
- in W (intensional Montague) and M (MTT) it is *not* valid: each has a
  countermodel, so "unknown" is the encoding's own answer.

It also proves valid the M claims the generic prover misses: in Section
5 (202, 210, 211, 212, 214): each needs identity reasoning across the embeddings
(`eAnimal a = eMouse m`), which `aesop` and `grind` do not find; in Section 3 (118, 131, 132),
which need a Σ-typed proof object in the context projected or a
conjunction taken apart under one. So M's lower scores with that prover
are a cost of automation, not of what M entails.

These are checked by `lake build`, so a change to the generated claims
that broke them would fail the build.
-/

namespace FraCaS.Encodings.Commitments

/-- P makes 215's wrong "yes" valid. -/
theorem p_215_valid : P.fracas_215_yes := by
  intro E authority lawLecturer legal competent _ _ h₁ h₂
  have h : legal authority = lawLecturer := funext fun x => propext ⟨h₁ x, h₂ x⟩
  intro e he
  rw [← h]
  exact he

/-- W does not: at the actual world the two nouns are coextensive, but
"competent" looks at another world, where they differ. -/
theorem w_215_not_valid : ¬ W.fracas_215_yes := by
  intro h
  have := @h Unit Bool true (fun _ _ => True) (fun w _ => w = true)
    (fun c w e => c w e) (fun c w e => c false e ∧ c w e)
    (fun _ _ _ h => h) (fun _ _ _ h => h.2) (fun _ _ => rfl) (fun _ _ => trivial)
    () ⟨trivial, trivial⟩
  have h' : (false = true) ∧ (true = true) := this
  exact Bool.false_ne_true h'.1

/-- Nor does M: the two nouns are different types with the same members,
and "competent" is indexed by the type (here: whether it has at most one
element). -/
theorem m_215_not_valid : ¬ M.fracas_215_yes := by
  intro h
  obtain ⟨_, hb, _⟩ := @h Unit Unit (fun _ => ()) Bool (fun _ => ())
    (fun _ _ => True) (fun X _ => Subsingleton X)
    (fun _ _ => ⟨true, rfl⟩) (fun _ => ⟨(), trivial, rfl⟩)
    () trivial ⟨fun _ _ => Subtype.ext rfl⟩
  have hb' : Subsingleton Bool := hb
  exact absurd (hb'.elim true false) (by decide)

/-! ## M's claims the generic prover misses, proved by hand -/

theorem m_202 : M.fracas_202_yes := by
  intro E Mammal eM Animal eA fl h x hx
  obtain ⟨a, ha⟩ := h x
  exact ⟨a, by rw [ha]; exact hx, ha⟩

theorem m_210 : M.fracas_210_no := by
  intro E Mouse eM Animal eA small large mickey _ _ hc h1 ⟨m, _, hm⟩ ⟨a, ha, ha'⟩
  obtain ⟨a', hs, ha''⟩ := h1 m
  have h : eA a' = eA a := by rw [ha'', hm, ha']
  exact hc Animal (eA a) (h ▸ hs) ha

theorem m_211 : M.fracas_211_no := by
  intro E Elephant eEl Animal eA large small dumbo _ _ hc h1 ⟨el, _, hel⟩ ⟨a, ha, ha'⟩
  obtain ⟨a', hl, ha''⟩ := h1 el
  have h : eA a' = eA a := by rw [ha'', hel, ha']
  exact hc Animal (eA a) ha (h ▸ hl)

theorem m_212 : M.fracas_212_yes := by
  intro E Mouse eM Animal eA Elephant eEl small large largeThan mickey dumbo _ _ _ _ _ hcomp _ h1 h2
    ⟨m, _, hm⟩ ⟨el, _, hel⟩
  obtain ⟨a, hs, ha⟩ := h1 m
  obtain ⟨b, hl, hb⟩ := h2 el
  have hs' : small Animal mickey := by rw [← hm, ← ha]; exact hs
  have hl' : large Animal dumbo := by rw [← hel, ← hb]; exact hl
  exact hcomp Animal mickey dumbo hs' hl'

theorem m_214 : M.fracas_214_yes := by
  intro E Authority eAu LawLecturer eLL legal fat ext _ p1 p2 x hx hfat
  have hco : ∀ e, (∃ y : Authority, legal Authority (eAu y) ∧ eAu y = e) ↔
      (∃ z : LawLecturer, eLL z = e) := by
    intro e
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact p1 y hy
    · rintro ⟨z, rfl⟩
      exact p2 z
  obtain ⟨z, hz⟩ := p1 x hx
  refine ⟨z, ?_, hz⟩
  rw [hz]
  exact ext hco _ hfat

/-! ## Section 3: M's claims the generic prover misses, proved by hand -/

theorem m_118 : S3.fracas_118_yes := by
  intro E Student eS Workstation eW female use haveV mary dep is _
  exact ⟨(dep is.1).1, by rw [← is.2]; exact (dep is.1).2.2⟩

theorem m_131 : S3.fracas_131_yes := by
  intro E Department eD Line eL dedicated haveV rent fromP bt _ h x
  obtain ⟨y, _, hf, hr⟩ := h x
  exact ⟨y, hf, hr⟩

theorem m_132 : S3.fracas_132_yes := by
  intro E Department eD Line eL SalesDepartment eSD dedicated haveV rent fromP bt _ h x
  obtain ⟨y, _, hf, hr⟩ := h x
  exact ⟨y, hf, hr⟩

end FraCaS.Encodings.Commitments
