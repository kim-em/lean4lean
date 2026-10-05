import Lean4Lean.Theory.Typing.AnchoredNativeArgumentCuts
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode
import Lean4Lean.Theory.Typing.AnchoredNativeTemplateRealization

/-! Produce an initial native input from its actual finite source cuts and the
original argument theorem. The generated domain certificate may introduce
additional earlier-argument demands; its exact factor ledger is retained.
The resulting key is provisional and can be raised after the finite backward
pass has collected all grades. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem realized_template {template : VExpr} {arguments : List VExpr}
    (scope : template.ClosedN arguments.length) (σ : Subst) :
    (template.instOuter arguments).subst σ =
      template.subst (nativeCaptureSubst (arguments.map (·.subst σ))) := by
  rw [instOuter_eq_subst, subst_subst]
  apply subst_congr_closedN scope
  intro i hi
  simp only [Subst.comp, Subst.ofList, nativeCaptureSubst, List.length_map]
  rw [dif_pos hi, dif_pos hi]
  simp only [List.getElem_map]

structure NativeBinderInput (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (argument template : VExpr) (prefixArguments : List VExpr)
    (required : Footprint) (minimum : Nat) where
  packed : NativeArgumentPack env U registry target locals σ available argument required minimum
  support : Profile packed.rank
  originalTypeFootprint : Footprint
  originalTypeResources : originalTypeFootprint.Available available
  domainFootprint : Footprint
  domainCertificate : CodeCert env U registry target (List.range prefixArguments.length)
    (nativeCaptureSubst (prefixArguments.map (·.subst σ))) template support domainFootprint
  domainCuts : ParamsFootprint env U registry target locals σ prefixArguments
    originalTypeFootprint domainFootprint
  guard : LambdaGuard env U registry target (nativeCaptureSubst (prefixArguments.map (·.subst σ)))
    template ⟨template.subst (nativeCaptureSubst (prefixArguments.map (·.subst σ))),
      argument.subst σ, packed.input⟩ support

/-- Interpolate only the actual aggregate source argument observation. Its
requested-grade certificate gives the exact domain guard; factorization then
exposes every new preceding-argument requirement instead of assuming coverage. -/
theorem NativeArgumentPack.formInput
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {argument template : VExpr} {prefixArguments : List VExpr}
    {required : Footprint} {minimum : Nat}
    (packed : NativeArgumentPack env U registry target locals σ available argument required minimum)
    (scope : template.ClosedN prefixArguments.length)
    (originalArgument : GradedJoint env U registry source argument argument
      (template.instOuter prefixArguments))
    (rawArgument : env.HasType U source argument (template.instOuter prefixArguments))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available) :
    Nonempty (NativeBinderInput env U registry target locals σ available argument template
      prefixArguments required minimum) := by
  obtain ⟨value⟩ := (originalArgument target locals σ σ available closed hTarget substitutions fits).1
    packed.observation packed.resources
  have certificate := value.requestedCertificate
  obtain ⟨domainFootprint, ⟨domainCertificate⟩, ⟨cuts⟩⟩ :=
    certificate.factorNativeTemplate scope (List.range prefixArguments.length)
  have raw := rawArgument.substDF henv substitutions.wf hTarget substitutions
  have related := value.requestedRelated henv hTarget
  have code := TypeRelated.lower henv value.bound value.typeCode
  rw [realized_template scope σ] at raw related code
  refine ⟨{
    packed := packed
    support := lowerProfile packed.rank value.bound value.support
    originalTypeFootprint := value.typeFootprint
    originalTypeResources := value.typeAvailable
    domainFootprint := domainFootprint
    domainCertificate := domainCertificate
    domainCuts := cuts
    guard := {
      inputTyped := value.requestedTyped
      formed := certificate.formed
      path := .refl
      domains := code
      anchor := ⟨raw, raw, _, value.requestedTyped, certificate.formed, code, related, related⟩ } }⟩

/-- Raising the provisional input leaves every source cut and all remaining
prefix requirements intact. No original typing theorem is queried again. -/
noncomputable def NativeArgumentPack.raise
    (packed : NativeArgumentPack env U registry target locals σ available argument required minimum)
    (bound : packed.rank ≤ N) :
    NativeArgumentPack env U registry target locals σ available argument required minimum where
  rank := N
  bound := Nat.le_trans packed.bound bound
  input := raiseProfile N bound packed.input
  argumentFootprint := packed.argumentFootprint
  observation := packed.observation.raise bound
  resources := packed.resources
  outside := packed.outside
  pack := packed.pack.raise bound

noncomputable def NativeBinderInput.raise
    (henv : env.Ordered)
    (input : NativeBinderInput env U registry target locals σ available argument template
      prefixArguments required minimum) (bound : input.packed.rank ≤ N) :
    NativeBinderInput env U registry target locals σ available argument template
      prefixArguments required minimum where
  packed := input.packed.raise bound
  support := raiseProfile N bound input.support
  originalTypeFootprint := input.originalTypeFootprint
  originalTypeResources := input.originalTypeResources
  domainFootprint := input.domainFootprint
  domainCertificate := input.domainCertificate.raise bound
  domainCuts := input.domainCuts
  guard := by
    simpa only [raiseKey, NativeArgumentPack.raise] using input.guard.raise henv bound

end Lean4Lean.AnchoredSource.Adapted
