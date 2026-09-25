/-!
# FraCaS problem representation

Structures for FraCaS-style NLI problems (Cooper et al. 1996, as
transcribed by MacCartney into `fracas.xml`). No problems are vendored
here yet: this environment's network policy blocks `nlp.stanford.edu`
(see the repo README). Once reachable, transcribe problems into
`FraCaS/Data/SectionN.lean` files, one `Problem` per FraCaS id, with a
`fracas_NNN` theorem per Phase 2 of the README's roadmap.
-/
namespace FraCaS

inductive Answer
  | yes | no | unknown
  deriving Repr, DecidableEq

/-- One FraCaS problem: numbered premises, an optional question, a
hypothesis, and the gold answer. Four problems in MacCartney's XML
(276, 305, 309, 310) have no hypothesis/question and should be skipped
rather than force-fit into this shape. -/
structure Problem where
  id : Nat
  premises : List String
  hypothesis : String
  answer : Answer

end FraCaS
