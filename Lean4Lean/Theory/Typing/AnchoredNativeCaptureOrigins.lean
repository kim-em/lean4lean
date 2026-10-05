import Lean4Lean.Theory.Typing.AnchoredNativeSelectedRouting

/-! The finite original-origin chain for initial native capture routing.
The chain stores declared-field provenance and literal generator occurrences.
Registered natural domains come from the actual full application spine,
including its conversions, rather than a raw syntactic type equality.
The backward pass constructs each actual field seed and guard, propagates its
declared-domain cuts first, and retains the natural-domain cuts in the final
native argument ledger. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

/-- Raw provenance for the selected generated capture instructions. This
does not assert program selection or manufacture constructor typing: callers
must obtain these exact occurrences from the original generated equation. -/
inductive NativeCaptureOrigins (sourceEnv : VEnv) (U : Nat) (source : List VExpr)
    {data : NativeRecursorData} (program : SaturatedProgram data)
    (nativeArguments captureArguments : List VExpr) : Nat → Type where
  | prefix
      (same : captureArguments.take data.indexOffset = nativeArguments.take data.indexOffset)
      (bound : data.indexOffset ≤ nativeArguments.length) :
      NativeCaptureOrigins sourceEnv U source program nativeArguments captureArguments 0
  | index {templates : NativeIndexTemplates program} {index : Nat}
      {declared : VExpr}
      (nativeOccurrence : nativeArguments[data.indexOffset + templates.slot]? = some (.bvar index))
      (captureOccurrence : captureArguments[data.indexOffset + templates.field]? = some (.bvar index))
      (lookup : Lookup source index declared)
      (declaredOrigin : declared = templates.declaredDomain.instOuter
        (captureArguments.take (data.indexOffset + templates.field)))
      (declaredScope : templates.declaredDomain.ClosedN
        (captureArguments.take (data.indexOffset + templates.field)).length)
      (previous : NativeCaptureOrigins sourceEnv U source program nativeArguments captureArguments templates.field) :
      NativeCaptureOrigins sourceEnv U source program nativeArguments captureArguments (templates.field + 1)
  | proof {field : Nat} {argument proposition domain : VExpr}
      (instruction : program.instructions[field]? = some (.proof domain))
      (captureOccurrence : captureArguments[data.indexOffset + field]? = some argument)
      (originalProposition : sourceEnv.IsDefEqStrong U source proposition proposition (.sort .zero))
      (originalArgument : sourceEnv.IsDefEqStrong U source argument argument proposition)
      (sourceProof : sourceEnv.IsDefEqStrong U
        (((program.equationBody.domains.take (data.indexOffset + field)).map
          (·.instL program.levels)).reverse) domain domain (.sort .zero))
      (propositionOrigin : proposition = domain.instOuter
        (captureArguments.take (data.indexOffset + field)))
      (domainScope : domain.ClosedN (captureArguments.take (data.indexOffset + field)).length)
      (previous : NativeCaptureOrigins sourceEnv U source program nativeArguments captureArguments field) :
      NativeCaptureOrigins sourceEnv U source program nativeArguments captureArguments (field + 1)

/-- The original-origin chain is interpreted backward in the finite capture
list. Every newly exposed type cut is routed before an earlier key is frozen.
The only semantic induction hypothesis is the existing predecessor-stage
theorem, applied to the raw original children retained in this chain. -/
theorem NativeCaptureOrigins.route
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (registered : NativeRecursorRegistered env data)
    {recursorType : VExpr} (headerType : data.recursorType = some recursorType)
    (typeClosed : recursorType.Closed)
    (formation : OriginalTypePayload sourceEnv env U registry []
      (recursorType.instL program.levels) (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) []
      (recursorType.instL program.levels))
    {expression assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const data.name program.levels)
    {captureArguments witnesses : List VExpr}
    (nativeValues : program.prefixArgs = expression.getAppFnArgs.2.map (·.subst σ))
    (capturedValues : witnesses = captureArguments.map (·.subst σ))
    {fields : Nat}
    (origins : NativeCaptureOrigins sourceEnv U source program expression.getAppFnArgs.2 captureArguments fields)
    {required : Footprint}
    (ledger : NativeArgumentLedger env U registry target locals σ available
      (captureArguments.take (data.indexOffset + fields)) required)
    (minimum : Nat) :
    Nonempty (InitialNativeCaptureRoute env U registry target program witnesses locals σ available
      expression.getAppFnArgs.2 fields required) := by
  match origins with
  | .prefix same bound => exact ⟨InitialNativeCaptureRoute.prefix nativeValues same bound ledger⟩
  | .index (templates := templates) nativeOccurrence captureOccurrence lookup
      declaredOrigin declaredScope previous =>
    have typeEq : templates.recursorType = recursorType :=
      Option.some.inj (templates.registeredType.symm.trans headerType)
    have templateClosed : templates.recursorType.Closed := typeEq ▸ typeClosed
    have templateFormation : OriginalTypePayload sourceEnv env U registry []
        (templates.recursorType.instL program.levels) (.sort level) := by
      rw [typeEq]
      exact formation
    have templateHeader : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) []
        (templates.recursorType.instL program.levels) := by
      rw [typeEq]
      exact header
    obtain ⟨prepared⟩ := ledger.prepareRegisteredIndex henv hscoped hle earlier
      closed hTarget substitutions fits templates registered templateClosed templateFormation
      templateHeader original head nativeOccurrence captureOccurrence lookup
      declaredOrigin declaredScope minimum
    obtain ⟨routed⟩ := previous.route henv hscoped hle earlier closed hTarget substitutions fits
      registered headerType typeClosed formation header original head
      nativeValues capturedValues prepared.previous minimum
    exact ⟨prepared.finish nativeValues capturedValues routed⟩
  | .proof instruction captureOccurrence originalProposition originalArgument sourceProof
      propositionOrigin domainScope previous =>
    obtain ⟨prepared⟩ := ledger.prepareProof henv hle closed hTarget substitutions fits instruction
      captureOccurrence capturedValues ⟨originalProposition, (earlier originalProposition).joint⟩
      ⟨originalArgument, (earlier originalArgument).joint⟩ sourceProof propositionOrigin domainScope minimum
    obtain ⟨routed⟩ := previous.route henv hscoped hle earlier closed hTarget substitutions fits
      registered headerType typeClosed formation header original head
      nativeValues capturedValues prepared.previous minimum
    exact ⟨prepared.finish routed⟩
termination_by sizeOf origins

end Lean4Lean.AnchoredSource.Adapted
