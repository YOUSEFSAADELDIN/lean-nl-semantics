import EndToEnd.Encodings.Section5

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

end FraCaS.Encodings.Commitments
