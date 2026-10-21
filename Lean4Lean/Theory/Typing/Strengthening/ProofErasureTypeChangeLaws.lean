import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecursiveNeutral

/-! # Local laws sufficient for typed recovery and checking transport

These are explicit requirements on a depth-indexed relation on erased types.
They describe syntax, selected projection recipes and typed computation. They
do not assume recovery transport, carrier transport or comparison transport.
Satisfying them does not establish that the relation covers all type equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Local structural laws for a proposed type-conversion relation. Record
families, universe instances and arities stay fixed; parameters may change if
all actual closed field recipes remain related. The computation law only
concerns erased, actually equal types. General record coverage and these laws
must be proved for each proposed relation; none is asserted universally. -/
structure TypeChangeLaws
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Rel : Nat → ProofShape → ProofShape → Prop) : Prop where
  /-- Identical type syntax is allowed at every protected depth. -/
  refl : ∀ {k A}, Rel k A A
  /-- Inserting one binder protects all previously changed neutral positions. -/
  shift : ∀ {k A B}, Rel k A B → Rel (k + 1) (A.liftN 1) (B.liftN 1)
  /-- Applying a recovered function instantiates both related result types. -/
  inst : ∀ {k A B x}, Rel (k + 1) A B → Rel k (A.inst x) (B.inst x)
  /-- Lambda recovery constructs a related Pi from related domain and body. -/
  pi : ∀ {k A B A' B'}, Rel k A A' → Rel (k + 1) B B' →
    Rel k (.forallE A B) (.forallE A' B')
  /-- A displayed Pi exposes related domains and bodies on the target side. -/
  pi_inv : ∀ {k A B T}, Rel k (.forallE A B) T →
    ∃ A' B', T = .forallE A' B' ∧ Rel k A A' ∧ Rel (k + 1) B B'
  /-- Recovery's universe outputs retain their exact levels. -/
  sort_inv : ∀ {k u T}, Rel k (.sort u) T → T = .sort u
  /-- Registered rigid carriers keep their heads, levels and arity. -/
  record : ∀ {k c info ls ps T}, env.projections c info →
    Rel k (ProofShape.mkApps (.const c ls) ps) T →
    ∃ ps', T = ProofShape.mkApps (.const c ls) ps' ∧ ps'.length = ps.length
  /-- Related parameters give related instantiated closed field recipes,
  including dependencies on earlier projections of the same major. -/
  field : ∀ {k c info ls doms result ps ps'}, env.projections c info →
    ProjTele env univs c info ls doms result →
    Rel k (ProofShape.mkApps (.const c ls) ps) (ProofShape.mkApps (.const c ls) ps') →
    ∀ j (hj : info.nparams + j < doms.length) major,
      Rel k (projectionType c info doms j hj ps major)
        (projectionType c info doms j hj ps' major)
  /-- Structural subsingleton certificates survive the type change. -/
  subsingleton : ∀ {k A B}, Rel k A B → SubsingletonCarrier A → SubsingletonCarrier B
  /-- Every computation of an actually typed source type has a related target
  computation. This does not require the two types to have a common reduct. -/
  compute : ∀ {k Γ A B u a b out}, Rel k a b → OnCtx Γ (env.IsType univs) →
    env.IsDefEq univs Γ A B (.sort u) → proofErase Γ A = a → proofErase Γ B = b →
    ScopedCompute Step (proofEraseCtx Γ) a out →
    ∃ out', ScopedCompute Step (proofEraseCtx Γ) b out' ∧ Rel k out out'

end Lean4Lean.VEnv.Strengthening
