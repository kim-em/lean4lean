import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProofIndexFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationSingletonEquation

/-! # Generated singleton equations with propositional index telescopes -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}

/-- Every generated prefix of a registered singleton with propositional
indices has a typed chain. All fixed code certificates come from registration
and generation; its family guard is proved by exact erasure equality. -/
theorem TypedComputationEq.generated_proof_indices_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hreg : recursorData data.name = some data) (H : RecursorRegistered env data)
    (hl : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hS : data.singletonLayout env levels = some S)
    (hindices : PropTelescope env univs (data.propParams levels).reverse S.indices)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : env.HasType univs Γ (mkApps (.const data.name levels) args) T) :
    TypedComputationEq D Γ (mkApps (.const data.name levels) args) program.rhs T := by
  obtain ⟨recType, hrec⟩ := H.recursorType_exists
  obtain ⟨_, _, hlv, hlen, heqn, hbody, _⟩ :=
    InductiveSignature.RecursorData.singletonUnfolding_spec hg
  rw [hlv] at hlen
  have hnlevels := hlen.trans (InductiveSignature.RecursorData.singletonEquation_uvars heqn)
  obtain ⟨index, howner, _⟩ := VEnv.RecursorData.singletonEquation_eq heqn
  obtain ⟨S', E, hS', hE, _⟩ := InductiveSignature.RecursorData.propElim_wf
    henv H hl hz hw hnlevels ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  let C : SingletonPrefixCode := ⟨data, levels, args.length, recType,
    program.equation, program.equationBody, S, E⟩
  have V : C.Valid := ⟨hreg, H, hl, hz, hw, hrec, heqn, hbody, hS, hE, args, program, rfl, hg⟩
  exact TypedComputationEq.proof_indices_prefix heq hs V hindices hΓ rfl hg ht

/-- The full lambda-wrapped singleton equation has a typed computation chain
when every declared index is a proposition. The index telescope may depend on
parameters and earlier index proofs. No guard coverage or joining premise remains. -/
theorem TypedComputationEq.proof_indices_singleton_equation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hlookup : recursorData data.name = some data)
    (H : RecursorRegistered env data)
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some equation) (hpe : env.PatEquation equation)
    (hlT : env.HasType equation.uvars [] equation.lhs equation.type)
    (hrT : env.HasType equation.uvars [] equation.rhs equation.type)
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = equation.uvars)
    (hlarge : data.largeTarget = true)
    (hS : data.singletonLayout env levels = some S)
    (hindices : PropTelescope env univs (data.propParams levels).reverse S.indices)
    (hzero : (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero) :
    TypedComputationEq D Γ (equation.lhs.instL levels) (equation.rhs.instL levels)
      (equation.type.instL levels) := by
  apply TypedComputationEq.singleton_equation_of_prefix heq hs hΓ hlookup H howner hgen hpe
    hlT hrT hw hl hlarge hzero
  intro Δ args rhs HP T hΔ ht
  cases HP with
  | intro hreg hr _ hl hw hz hg _ =>
    cases Option.some.inj (hreg.symm.trans hlookup)
    exact TypedComputationEq.generated_proof_indices_prefix heq hs hΔ hlookup hr hl hz hw hS hindices hg ht

end Lean4Lean.VEnv.Strengthening
