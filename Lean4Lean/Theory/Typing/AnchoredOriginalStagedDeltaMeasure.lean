import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaPacket

/-! Compatibility module for the retired declaration-history rich delta
constructor. Operative delta queries use the canonical packet and shared
`RichObs.canonicalDelta`; plain legacy `Obs.delta` remains supported. -/
