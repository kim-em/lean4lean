import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParallelBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedBetaLevelJoin

/-! # Raw beta joins modulo structural universe conversion

Parallel developments give raw beta confluence. This makes joinability modulo
universe variation transitive, including paths containing reverse beta steps.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean

private theorem parallel_map (F : ProofShape → ProofShape)
    (H : ∀ {a b}, BetaPar a b → BetaPar (F a) (F b))
    (R : ReflTransGen BetaPar a b) : ReflTransGen BetaPar (F a) (F b) := by
  induction R with
  | rfl => exact .rfl
  | tail _ R ih => exact ih.tail (H R)

private theorem parallel_pair (F : ProofShape → ProofShape → ProofShape)
    (H : ∀ {a b c d}, BetaPar a b → BetaPar c d → BetaPar (F a c) (F b d))
    (R : ReflTransGen BetaPar a b) (S : ReflTransGen BetaPar c d) :
    ReflTransGen BetaPar (F a c) (F b d) :=
  (parallel_map (fun x => F x c) (fun R => H R (.refl _)) R).trans
    (parallel_map (F b) (fun S => H (.refl _) S) S)

private theorem BetaRed.toParallel (R : BetaRed a b) : ReflTransGen BetaPar a b := by
  induction R with
  | refl => exact .rfl
  | trans _ _ ihR ihS => exact ihR.trans ihS
  | beta => exact .tail .rfl (.beta (.refl _) (.refl _))
  | app _ _ ihR ihS => exact parallel_pair .app (fun R S => .app R S) ihR ihS
  | lam _ _ ihR ihS => exact parallel_pair .lam (fun R S => .lam R S) ihR ihS
  | forallE _ _ ihR ihS => exact parallel_pair .forallE (fun R S => .forallE R S) ihR ihS
  | proj _ ih => exact parallel_map _ (fun R => .proj R) ih

private theorem parallel_toBeta (R : ReflTransGen BetaPar a b) : BetaRed a b := by
  induction R with
  | rfl => exact .refl
  | tail _ R ih => exact ih.trans R.toBeta

private theorem parallel_strip (R : BetaPar a b) (S : ReflTransGen BetaPar a c) :
    ∃ out, ReflTransGen BetaPar b out ∧ BetaPar c out := by
  induction S with
  | rfl => exact ⟨b, .rfl, R⟩
  | tail _ S ih =>
    obtain ⟨d, BD, CD⟩ := ih
    obtain ⟨out, SO, DO⟩ := S.diamond CD
    exact ⟨out, BD.tail DO, SO⟩

private theorem parallel_confluent
    (R : ReflTransGen BetaPar a b) (S : ReflTransGen BetaPar a c) :
    ∃ out, ReflTransGen BetaPar b out ∧ ReflTransGen BetaPar c out := by
  induction R with
  | rfl => exact ⟨c, S, .rfl⟩
  | tail _ R ih =>
    obtain ⟨d, BD, CD⟩ := ih
    obtain ⟨out, BO, DO⟩ := parallel_strip R BD
    exact ⟨out, BO, CD.tail DO⟩

/-- Raw annotated beta reduction is confluent, with no typing or normalization
hypothesis. Retained lambda domains are developed along with their bodies. -/
theorem BetaRed.raw_confluent (R : BetaRed a b) (S : BetaRed a c) :
    ∃ out, BetaRed b out ∧ BetaRed c out := by
  obtain ⟨out, BO, CO⟩ := parallel_confluent R.toParallel S.toParallel
  exact ⟨out, parallel_toBeta BO, parallel_toBeta CO⟩

/-- A pair of beta reducts differing only by equivalent universe annotations.
This raw certificate does not assert a typed universe-conversion path. -/
def BetaLevelJoin (a b : ProofShape) : Prop :=
  ∃ a' b', BetaRed a a' ∧ BetaRed b b' ∧ StructuralVariant a' b'

/-- Reflexivity of the raw join certificate. -/
theorem BetaLevelJoin.refl : BetaLevelJoin a a := ⟨a, a, .refl, .refl, .refl⟩

/-- A join certificate can be reversed. -/
theorem BetaLevelJoin.symm (H : BetaLevelJoin a b) : BetaLevelJoin b a := by
  obtain ⟨a', b', RA, RB, V⟩ := H
  exact ⟨b', a', RB, RA, V.symm⟩

/-- Raw beta confluence and structural simulation compose join certificates. -/
theorem BetaLevelJoin.trans (H : BetaLevelJoin a b) (K : BetaLevelJoin b c) :
    BetaLevelJoin a c := by
  obtain ⟨a', b', RA, RB, V⟩ := H
  obtain ⟨b'', c', SB, SC, W⟩ := K
  obtain ⟨d, BD, B'D⟩ := RB.raw_confluent SB
  obtain ⟨a'', AA, VA⟩ := BD.variant V.symm
  obtain ⟨c'', CC, VC⟩ := B'D.variant W
  exact ⟨a'', c'', RA.trans AA, SC.trans CC, VA.symm.trans VC⟩

/-- A forward beta path supplies a join certificate. -/
theorem BetaLevelJoin.beta (R : BetaRed a b) : BetaLevelJoin a b :=
  ⟨b, b, R, .refl, .refl⟩

/-- Equivalent universe annotations supply a join certificate. -/
theorem BetaLevelJoin.variant (V : StructuralVariant a b) : BetaLevelJoin a b :=
  ⟨a, b, .refl, .refl, V⟩

/-- Join certificates are compatible with application. -/
theorem BetaLevelJoin.app (H : BetaLevelJoin f g) (K : BetaLevelJoin a b) :
    BetaLevelJoin (.app f a) (.app g b) := by
  obtain ⟨f', g', RF, RG, V⟩ := H
  obtain ⟨a', b', RA, RB, W⟩ := K
  exact ⟨_, _, .app RF RA, .app RG RB, .app V W⟩

/-- Join certificates are compatible with retained lambda annotations. -/
theorem BetaLevelJoin.lam (H : BetaLevelJoin A A') (K : BetaLevelJoin b b') :
    BetaLevelJoin (.lam A b) (.lam A' b') := by
  obtain ⟨_, _, RA, RA', V⟩ := H
  obtain ⟨_, _, RB, RB', W⟩ := K
  exact ⟨_, _, .lam RA RB, .lam RA' RB', .lam V W⟩

/-- Join certificates are compatible with Pi domains and bodies. -/
theorem BetaLevelJoin.forallE (H : BetaLevelJoin A A') (K : BetaLevelJoin B B') :
    BetaLevelJoin (.forallE A B) (.forallE A' B') := by
  obtain ⟨_, _, RA, RA', V⟩ := H
  obtain ⟨_, _, RB, RB', W⟩ := K
  exact ⟨_, _, .forallE RA RB, .forallE RA' RB', .forallE V W⟩

/-- Join certificates are compatible with projections. -/
theorem BetaLevelJoin.proj (H : BetaLevelJoin a b) :
    BetaLevelJoin (.proj s i a) (.proj s i b) := by
  obtain ⟨_, _, RA, RB, V⟩ := H
  exact ⟨_, _, .proj RA, .proj RB, .proj V⟩

end Lean4Lean.VEnv.Strengthening.ProofShape
