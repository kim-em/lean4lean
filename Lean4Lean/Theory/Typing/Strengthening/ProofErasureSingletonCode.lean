import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixArguments
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonTemplates
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonPrefixBody

/-! # Raw code for a general singleton prefix

Declaration metadata and supplied arity are fixed independently of any original
input representative. Raw supply reconstructs the residual telescope, context
opening supplies the providers, and fixed templates determine guard and output.
Validity includes generation at one arbitrary prefix of the given arity; it
does not require that prefix to represent the actual raw inputs or be typed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim

/-- Fixed declaration code and arity for a singleton prefix. -/
structure SingletonPrefixCode where
  data : RecursorData
  levels : List VLevel
  arity : Nat
  recType : VExpr
  equation : VDefEq
  body : RecursorSchema.EquationBody
  layout : SingletonLayout
  elim : PropElim

variable [Params]

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}
/-- Code validity depends only on the registered declaration and arity.
The generation witness certifies structural feasibility, not a source typing,
family conversion, or an unfolding check. -/
structure Valid (C : SingletonPrefixCode) : Prop where
  lookup : recursorData C.data.name = some C.data
  registered : RecursorRegistered env C.data
  large : C.data.largeTarget = true
  zero : C.data.sourceLevel C.levels ≈ .zero
  levels_wf : ∀ l ∈ C.levels, l.WF univs
  recType_eq : C.data.recursorType = some C.recType
  equation_eq : C.data.singletonEquation = some C.equation
  body_eq : RecursorSchema.EquationBody.extract C.equation.lhs C.equation.rhs
    C.equation.type = some C.body
  layout_eq : C.data.singletonLayout env C.levels = some C.layout
  elim_eq : C.data.propElim C.levels = some C.elim
  generation : ∃ args program, args.length = C.arity ∧
    C.data.singletonUnfolding env univs C.levels args = some program

/-- Raw residual telescope computed from a fixed closed declaration instance. -/
noncomputable def telescope (C : SingletonPrefixCode) (args : List ProofShape) :
    Option (List ProofShape × ProofShape) :=
  ProofShape.residualTelescope (C.data.majorOffset + 1 - args.length) args
    (proofErase [] (C.recType.instL C.levels))

/-- Fixed raw family guard at the reconstructed residual context and providers. -/
def guard (C : SingletonPrefixCode)
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ domains args : List ProofShape) : Prop :=
  let all := ProofShape.openPrefixArguments Δ domains args
  ScopedSingletonFamilyGuard Step (domains.reverse ++ Δ) C.layout
    (C.data.propParams C.levels) C.elim (all.take C.data.numParams)
    ((all.drop C.data.indexOffset).take C.data.numIndices)

/-- Exact raw lambda output, including all retained domains and selected slots. -/
noncomputable def output (C : SingletonPrefixCode) (Δ domains args : List ProofShape) : ProofShape :=
  let all := ProofShape.openPrefixArguments Δ domains args
  ProofShape.wrapLams domains
    ((proofErase (C.body.domains.map (·.instL C.levels)).reverse
      (C.body.rhs.instL C.levels)).instOuter
        (all.take C.data.indexOffset ++ ProofShape.singletonSlots C.layout.slot C.layout.fields.length
          ((all.drop C.data.indexOffset).take C.data.numIndices)))

/-- A valid code generates a program for every original argument list of its
arity, without requiring a guard or typing for that list. -/
theorem Valid.generate (V : C.Valid) (ha : args.length = C.arity) :
    ∃ program, C.data.singletonUnfolding env univs C.levels args = some program := by
  obtain ⟨seed, program, hs, hg⟩ := V.generation
  exact RecursorData.singletonUnfolding_sameArity hg (ha.trans hs.symm)

/-- Every generated program uses the code's fixed universe list and body. -/
theorem Valid.program_metadata (V : C.Valid)
    (hg : C.data.singletonUnfolding env univs C.levels args = some program) :
    program.levels = C.levels ∧ program.equationBody = C.body := by
  obtain ⟨_, _, hl, _, he, hb, _⟩ := RecursorData.singletonUnfolding_spec hg
  have heq := Option.some.inj (he.symm.trans V.equation_eq)
  rw [heq] at hb
  exact ⟨hl, Option.some.inj (hb.symm.trans V.body_eq)⟩

/-- Raw code supply computes the exact telescope of every typed realization. -/
theorem Valid.telescope_eq (V : C.Valid) (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args)) :
    C.telescope (args.map (proofErase Γ)) =
      some (proofEraseDomains Γ program.domains,
        proofErase (program.domains.reverse ++ Γ) program.result) := by
  simpa only [telescope, List.length_map] using
    proofErase_singleton_prefix_telescope hΓ V.registered V.levels_wf V.recType_eq hg ht

/-- The code's raw guard agrees with the actual generated family guard at any
typed realization, before either guard is assumed true. -/
theorem Valid.guard_iff (V : C.Valid) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args)) :
    C.guard Step (proofEraseCtx Γ) (proofEraseDomains Γ program.domains)
      (args.map (proofErase Γ)) ↔
    GuardedSingleton.FamilyGuard (GuardedSingleton.ScopedFamilyComparison Step)
      Γ C.data C.levels args program C.layout C.elim := by
  have hh := scoped_singleton_prefix_template_iff (Step := Step) heq hΓ V.registered
    V.large V.zero V.levels_wf V.layout_eq V.elim_eq hg ht
  dsimp only at hh
  rw [proofErase_singleton_prefix_arguments hΓ V.registered V.levels_wf hg ht] at hh
  exact hh.symm

/-- Under its actual check, the non-proof generated output is precisely the
code's raw output, independent of the original source representative. -/
theorem Valid.output_eq (V : C.Valid) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (HC : UnfoldingCheck env univs Γ (mkApps (.const C.data.name C.levels) args) program)
    (hn : ¬ IsProof Γ (mkApps (.const C.data.name C.levels) args)) :
    proofErase Γ program.rhs = C.output (proofEraseCtx Γ)
      (proofEraseDomains Γ program.domains) (args.map (proofErase Γ)) := by
  have hh := proofErase_singleton_prefix_output heq hΓ V.registered V.large V.zero
    V.levels_wf V.layout_eq V.elim_eq hg HC hn
  dsimp only at hh
  obtain ⟨hl, hb⟩ := V.program_metadata hg
  rw [proofErase_singleton_prefix_arguments hΓ V.registered V.levels_wf hg
    ⟨_, HC.source_typed⟩, hl, hb] at hh
  exact hh

end SingletonPrefixCode
end Lean4Lean.VEnv.Strengthening
