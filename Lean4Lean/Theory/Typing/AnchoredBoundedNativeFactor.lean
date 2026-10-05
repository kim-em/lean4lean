import Lean4Lean.Theory.Typing.AnchoredBoundedFactorization
import Lean4Lean.Theory.Typing.AnchoredNativeResultCertificate

/-! The native result-template factor keeps its original native-depth fuel,
including every removed source operand. This is the finite ledger used by
initial native support construction; it does not assert that old field-copy
requirements already cover the newly factored result-index requirements. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

inductive BoundedParamsFootprint (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) :
    List VExpr → Footprint → Footprint → Type where
  | nil (footprint : Footprint) :
      BoundedParamsFootprint current fuel env U registry target locals σ [] footprint footprint
  | cons
      (tail : BoundedParamsFootprint current fuel env U registry target locals σ arguments before middle)
      (head : BoundedInstFootprint current fuel env U registry target locals σ argument
        arguments.length middle after) :
      BoundedParamsFootprint current fuel env U registry target locals σ
        (argument :: arguments) before after

/-- The unbounded client receives exactly the same actual cuts. -/
noncomputable def BoundedParamsFootprint.forget
    {target : List VExpr}
    (ledger : BoundedParamsFootprint current fuel env U registry target locals σ arguments before after) :
    ParamsFootprint env U registry target locals σ arguments before after := by
  induction ledger with
  | nil footprint => exact .nil footprint
  | cons tail head ih => exact .cons ih head.forget

private theorem ofList_tail (arguments : List VExpr) (σ : Subst) :
    Subst.lift_l (.skipN .refl arguments.length) ((Subst.ofList arguments).comp σ) = σ := by
  funext i
  simp only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.comp, Subst.ofList]
  rw [dif_neg (by omega)]
  simp only [Nat.add_sub_cancel, subst_bvar]

private theorem ofList_cons (argument : VExpr) (arguments : List VExpr) (σ : Subst) :
    ((Subst.one argument).liftN arguments.length).comp ((Subst.ofList arguments).comp σ) =
      (Subst.ofList (argument :: arguments)).comp σ := by
  funext i
  have h := instOuter_eq_subst (.bvar i) (argument :: arguments)
  change ((VExpr.bvar i).inst argument arguments.length).instOuter arguments = _ at h
  rw [instOuter_eq_subst, instN_eq, subst_subst] at h
  simpa only [subst_bvar, Subst.comp, subst_subst] using
    congrArg (fun expression => expression.subst σ) h

/-- Only the supplied certificate is structurally traversed. Repeated cuts
and their reconstructed certificates keep the same fuel; their size is never
used as a well-founded argument for the semantic predecessor theorem. -/
theorem CodeCert.factorParamsBounded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {σ : Subst} {template : VExpr} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ
      (template.instOuter arguments) demand footprint)
    (newLocals : List Nat) (bounded : certificate.nativeDepth current ≤ fuel) :
    ∃ required, ∃ result : CodeCert env U registry target newLocals
      ((Subst.ofList arguments).comp σ) template demand required,
      Nonempty (BoundedParamsFootprint current fuel env U registry target locals σ
        arguments footprint required) ∧ result.nativeDepth current ≤ fuel := by
  induction arguments generalizing template footprint with
  | nil =>
    have identity : (Subst.ofList []).comp σ = σ := by
      funext i
      simp [Subst.ofList, Subst.comp]
    rw [identity]
    let result := certificate.renameSource .refl σ rfl newLocals
    have resultBound := certificate.nativeDepth_renameSource current .refl σ rfl newLocals
    have fixed : ∃ result : CodeCert env U registry target newLocals σ
        ((template.instOuter []).lift' .refl) demand (footprint.sourceLift .refl),
        result.nativeDepth current ≤ fuel :=
      ⟨result, by simpa only [result, CodeCert.nativeDepth_renameSource] using bounded⟩
    have exprIdentity : (template.instOuter []).lift' .refl = template := by
      simp only [VExpr.instOuter, VExpr.lift'_refl]
    have footIdentity : footprint.sourceLift .refl = footprint := by
      change List.map (fun entry => entry) footprint = footprint
      exact List.map_id _
    rw [exprIdentity, footIdentity] at fixed
    obtain ⟨result, resultBound⟩ := fixed
    exact ⟨footprint, result, ⟨.nil footprint⟩, resultBound⟩
  | cons argument arguments ih =>
    obtain ⟨middle, factored, ⟨tail⟩, factoredBound⟩ := ih certificate bounded
    have next := factored.factorInstBounded template argument arguments.length rfl σ
      (ofList_tail arguments σ) locals newLocals factoredBound
    rw [ofList_cons] at next
    obtain ⟨required, result, ⟨head⟩, resultBound⟩ := next
    exact ⟨required, result, ⟨.cons tail head⟩, resultBound⟩

/-- Scope changes only the unused realization tail. Every actual native
child, including its whole registered-type certificate, is unchanged. -/
theorem CodeCert.factorNativeTemplateBounded
    {current : Name → Bool} {fuel : Nat}
    (certificate : CodeCert env U registry Γ locals σ
      (template.instOuter arguments) demand footprint)
    (scope : template.ClosedN arguments.length) (newLocals : List Nat)
    (bounded : certificate.nativeDepth current ≤ fuel) :
    ∃ required, ∃ result : CodeCert env U registry Γ newLocals
      (nativeCaptureSubst (arguments.map (·.subst σ))) template demand required,
      Nonempty (BoundedParamsFootprint current fuel env U registry Γ locals σ
        arguments footprint required) ∧ result.nativeDepth current ≤ fuel := by
  obtain ⟨required, factored, ledger, factoredBound⟩ :=
    certificate.factorParamsBounded newLocals bounded
  have agree : ∀ i < arguments.length,
      ((Subst.ofList arguments).comp σ) i =
        nativeCaptureSubst (arguments.map (·.subst σ)) i := by
    intro i hi
    simp only [Subst.comp, Subst.ofList, nativeCaptureSubst, List.length_map]
    rw [dif_pos hi, dif_pos hi]
    simp only [List.getElem_map]
  exact ⟨required, factored.realizePrefix scope _ agree, ledger, by
    simpa only [CodeCert.nativeDepth_realizePrefix] using factoredBound⟩

/-- The original declared-result certificate supplies a generic residual
certificate and bounded genuine operand cuts, at exactly its input support.
New result-index requirements remain explicit and must be packed by the
initial native producer. -/
theorem CodeCert.nativeResultTemplateBounded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst}
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (signature : NativeConstantSignature data program.levels)
    (registered : NativeRecursorRegistered env data)
    (selected : data.saturatedProgram program.levels arguments = some program)
    (closed : signature.type.Closed)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ
      (program.equationBody.type.instL program.levels) support footprint)
    (bounded : certificate.nativeDepth current ≤ fuel) :
    ∃ required, ∃ result : CodeCert env U registry target (List.range signature.domains.length)
      (nativeCaptureSubst ((program.equationBody.lhs.instL program.levels).getAppFnArgs.2.map
        (·.subst σ))) signature.result support required,
      Nonempty (BoundedParamsFootprint current fuel env U registry target locals σ
        (program.equationBody.lhs.instL program.levels).getAppFnArgs.2 footprint required) ∧
      result.nativeDepth current ≤ fuel := by
  have resultScope := signature.resultScoped closed
  have length := nativeEquationArguments_length (witnesses := []) selected
  simp only [nativeEquationArguments, List.length_map] at length
  rw [← length] at resultScope
  have bridge := signature.equationResult_template registered selected
  have input : ∃ input : CodeCert env U registry target locals σ
      (signature.result.instOuter (program.equationBody.lhs.instL program.levels).getAppFnArgs.2)
      support footprint, input.nativeDepth current ≤ fuel := by
    rw [bridge]
    exact ⟨certificate, bounded⟩
  obtain ⟨input, bound⟩ := input
  exact input.factorNativeTemplateBounded resultScope (List.range signature.domains.length) bound

end Lean4Lean.AnchoredSource.Adapted
