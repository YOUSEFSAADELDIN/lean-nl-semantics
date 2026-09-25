/-!
# Tense (skeleton)

A minimal event/time model, enough to state past/future reference. CoqLACL
(`MainCoq.v`) treats tense alongside quantifiers and adjectives; extend
this once FraCaS's temporal-reference problems (see the IWCS 2021 "Applied
Temporal Analysis" line in the README) are being ported.
-/
namespace MTT

axiom Event : Type
axiom Time : Type
axiom runtime : Event → Time
axiom utteranceTime : Time
axiom before : Time → Time → Prop

def Past (e : Event) : Prop := before (runtime e) utteranceTime
def Future (e : Event) : Prop := before utteranceTime (runtime e)

end MTT
