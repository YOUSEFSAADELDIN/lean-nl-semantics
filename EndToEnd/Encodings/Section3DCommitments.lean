import EndToEnd.Encodings.Section3D

/-!
# FraCaS Section 3 in D: the valid answers, proved by hand

D (`Section3D.lean`) states the Section 3 problems with nouns as
predicates over one type of entities, as Dependent Type Semantics does,
and keeps M's Σ-typed premises. Each claim below whose gold answer is
"yes" is proved here, so D's valid answers are settled whatever the
generic prover finds. The proofs project the premises' proof objects
just as M's do (`Commitments.lean`): no stipulated function is needed
with nouns as predicates either.

119 (gold "no") is left open, as in M and in the pipeline: Mary may
have used someone else's workstation.
-/

namespace FraCaS.Encodings.S3D

theorem d_114 : fracas_114_yes := by
  unfold fracas_114_yes
  intro _ _ _ _ _ mary _ _ h
  exact ⟨mary, h⟩

theorem d_115 : fracas_115_yes := by
  unfold fracas_115_yes
  intro _ _ _ _ _ _ acc1 _ _
  exact ⟨acc1.1, acc1.2⟩

theorem d_116 : fracas_116_yes := by
  unfold fracas_116_yes
  intro _ _ _ _ _ _ _ h _
  exact h

theorem d_117 : fracas_117_yes := by
  unfold fracas_117_yes
  intro _ _ _ _ _ _ _ _ is3 h
  obtain ⟨x, hx, rfl⟩ := is3
  exact h x hx

theorem d_118 : fracas_118_yes := by
  unfold fracas_118_yes
  intro _ _ _ _ _ _ _ dep2 is3 _
  obtain ⟨x, hx, rfl⟩ := is3
  obtain ⟨y, -, hw, hh⟩ := dep2 x hx
  exact ⟨y, hw, hh⟩

theorem d_120 : fracas_120_yes := by
  unfold fracas_120_yes
  intro _ _ _ _ _ ev1 h
  exact ⟨ev1.1, ev1.2.1, h⟩

theorem d_131 : fracas_131_yes := by
  unfold fracas_131_yes
  intro _ _ _ _ _ _ _ _ _ h x hx
  obtain ⟨y, hl, -, hf, hr⟩ := h x hx
  exact ⟨y, hl, hf, hr⟩

theorem d_132 : fracas_132_yes := by
  unfold fracas_132_yes
  intro _ _ _ _ _ _ _ _ _ _ h x hx
  obtain ⟨y, hl, -, hf, hr⟩ := h x hx
  exact ⟨y, hl, hf, hr⟩

theorem d_133 : fracas_133_yes := by
  unfold fracas_133_yes
  intro _ _ _ _ _ _ _ _ _ h
  exact h

theorem d_138 : fracas_138_yes := by
  unfold fracas_138_yes
  intro _ _ _ _ _ _ _ _ h
  exact h

end FraCaS.Encodings.S3D
