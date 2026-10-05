import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedApplication
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedConversion
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty

/-! The full original-child application constructor includes all enclosing
source observation closures. Its reverse direction converts the actual
instantiated result certificate using the original appDF result-type child. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

section
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  (henv : env.Ordered) (hscoped : registry.Scoped)
  {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
  {available : Valuation} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
  (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
  (originalBody : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
  (originalFunction : GradedJoint env U registry source f g (.forallE A B))
  (originalArgument : GradedJoint env U registry source a b A)
  (originalResult : GradedJoint env U registry source (B.inst a) (B.inst b) (.sort bodyLevel))
  (formedA : env.HasType U source A (.sort domainLevel))
  (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
  (rawArgument : env.IsDefEq U source a b A)
  (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (fits : PairedFits env U registry source target locals σ τ available)

include henv hscoped originalDomain originalBody originalFunction originalArgument originalResult
  formedA formedB rawArgument closed hTarget substitutions fits in
 theorem Obs.graded_application
    (observation : Obs env U registry target locals σ (.app f a) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .app fn arg arguments admitted =>
    exact Obs.graded_app_transfer henv hscoped originalDomain originalBody originalFunction
      originalArgument originalResult formedA formedB rawArgument closed hTarget substitutions fits
      fn arg arguments admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := left.graded_application
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := right.graded_application
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨value⟩ := source.graded_application resources
    exact ⟨value.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨value⟩ := source.graded_application resources
    exact ⟨value.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨value⟩ := source.graded_application resources
    exact ⟨value.unpad⟩
  | .rowShift source =>
    obtain ⟨value⟩ := source.graded_application resources
    exact ⟨(value.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩
termination_by sizeOf observation

include henv hscoped originalDomain originalBody originalFunction originalArgument originalResult
  formedA formedB rawArgument closed hTarget substitutions fits in
 theorem GradedTransfer.appDF :
    GradedTransfer env U registry target locals σ τ available (.app f a) (.app g b) (B.inst a) := by
  intro n demand footprint observation resources
  exact observation.graded_application henv hscoped originalDomain originalBody originalFunction
    originalArgument originalResult formedA formedB rawArgument closed hTarget substitutions fits resources

end

/-- Both endpoint transfers and sort correctness are consequences of the
original five semantic children of appDF, with no added typing premise. -/
theorem GradedJoint.appDF
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
    (originalBody : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (originalFunction : GradedJoint env U registry source f g (.forallE A B))
    (originalArgument : GradedJoint env U registry source a b A)
    (originalResult : GradedJoint env U registry source (B.inst a) (B.inst b) (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A) :
    GradedJoint env U registry source (.app f a) (.app g b) (B.inst a) := by
  apply GradedJoint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  have forward : GradedTransfer env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) := GradedTransfer.appDF henv hscoped originalDomain originalBody originalFunction
    originalArgument originalResult formedA formedB rawArgument closed hTarget substitutions fits
  have backward : GradedTransfer env U registry target locals σ τ available
      (.app g b) (.app f a) (B.inst b) :=
    GradedTransfer.appDF henv hscoped originalDomain originalBody originalFunction.symm
      originalArgument.symm originalResult.symm formedA formedB rawArgument.symm
      closed hTarget substitutions fits
  exact ⟨forward, GradedTransfer.convert henv hscoped originalResult.symm closed hTarget
    substitutions fits backward⟩

end Lean4Lean.AnchoredSource.Adapted
