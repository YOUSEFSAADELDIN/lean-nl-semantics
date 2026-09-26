import Mathlib

/-!
# NLI automation (skeleton)

Chatzikyriakidis & Luo's JoLLI 2014 automation for FraCaS goals was a
custom tactic unfolding definitions and then calling `intuition`,
`congruence` and `jauto` (TLC's `LibTactics`, Coq). `tauto` here is
Mathlib's; this has not been exercised against a real FraCaS goal yet,
since this environment cannot fetch a Lean/Mathlib toolchain (see the
repo README's "Network limitations" section) to compile-check it.
-/
namespace MTT

macro "nli" : tactic => `(tactic| (dsimp only; tauto))

end MTT
