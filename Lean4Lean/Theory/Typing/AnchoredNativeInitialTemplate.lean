import Lean4Lean.Theory.Typing.AnchoredNativeInitialGuard
import Lean4Lean.Theory.Typing.AnchoredNativeTemplateRealization

/-! The initial guarded copy from the actual constructor argument typing.
Both endpoint certificates are factored into the registered literal templates;
the finite cut ledgers retain every source argument used to support them. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private def requirements (footprint : Footprint) : Valuation :=
  fun index => (footprint.filter (fun entry => entry.1 == index)).map Prod.snd

private theorem requirements_available (footprint : Footprint) :
    footprint.Available (requirements footprint) := by
  intro index need member
  exact List.mem_map.mpr ⟨(index, need), List.mem_filter.mpr ⟨member, by simp⟩, rfl⟩

private theorem realized_template {template : VExpr} {arguments : List VExpr} (scope : template.ClosedN arguments.length) (σ : Subst) :
    (template.instOuter arguments).subst σ =
      template.subst (nativeCaptureSubst (arguments.map (·.subst σ))) := by
  rw [instOuter_eq_subst, subst_subst]
  apply subst_congr_closedN scope
  intro i hi
  simp only [Subst.comp, Subst.ofList, nativeCaptureSubst, List.length_map]
  rw [dif_pos hi, dif_pos hi]
  simp only [List.getElem_map]

/-- The abstract valuations here are the exact finite template demands.
They are accompanied by literal argument-cut ledgers back to the original
constructor valuation, rather than assumed to have fitting substitutions. -/
structure InitialNativeTemplateGuard
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) {data : NativeRecursorData}
    {program : NativeRecursorData.SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (locals naturalLocals captureLocals : List Nat) (σ : Subst) (available : Valuation)
    (naturalArguments declaredArguments : List VExpr) (input : Profile n) where
  naturalOriginalFootprint : Footprint
  naturalOriginalResources : naturalOriginalFootprint.Available available
  declaredOriginalFootprint : Footprint
  declaredOriginalResources : declaredOriginalFootprint.Available available
  naturalFootprint : Footprint
  declaredFootprint : Footprint
  naturalCuts : ParamsFootprint env U registry target locals σ naturalArguments
    naturalOriginalFootprint naturalFootprint
  declaredCuts : ParamsFootprint env U registry target locals σ declaredArguments
    declaredOriginalFootprint declaredFootprint
  guard : NativeIndexGuard (env := env) (U := U) (registry := registry) (target := target)
    templates naturalLocals captureLocals
    (nativeCaptureSubst (naturalArguments.map (·.subst σ)))
    (nativeCaptureSubst (declaredArguments.map (·.subst σ)))
    (requirements naturalFootprint) (requirements declaredFootprint) input
  naturalFootprint_eq : guard.naturalFootprint = naturalFootprint
  declaredFootprint_eq : guard.declaredFootprint = declaredFootprint

/-- No new semantic producer is assumed: the only semantic induction
premise is the preceding declaration stage, applied to retained children of
the actual original variable argument typing. In particular the proof does
not strengthen away the current field or assume an arbitrary major replay. -/
theorem HasTypeStrong.initialTemplateGuard
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A B level}, sourceEnv.IsDefEqStrong U Γ A B (.sort level) →
      GradedJoint env U registry Γ A B (.sort level))
    {source target : List VExpr} {index : Nat} {declared natural : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source (.bvar index) natural structural)
    (lookup : Lookup source index declared)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : NativeRecursorData.SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (naturalArguments declaredArguments : List VExpr)
    (naturalOrigin : natural = templates.naturalDomain.instOuter naturalArguments)
    (declaredOrigin : declared = templates.declaredDomain.instOuter declaredArguments)
    (naturalScope : templates.naturalDomain.ClosedN naturalArguments.length)
    (declaredScope : templates.declaredDomain.ClosedN declaredArguments.length)
    (naturalLocals captureLocals : List Nat)
    {input : Profile n} (needed : (⟨n, input⟩ : Need) ∈ available index) :
    Nonempty (InitialNativeTemplateGuard env U registry target templates locals
      naturalLocals captureLocals σ available naturalArguments declaredArguments input) := by
  obtain ⟨entry⟩ := fits.forward.entry index ⟨n, input⟩ needed declared lookup
  obtain ⟨alignment⟩ := HasTypeStrong.initialNativeAlignment henv hscoped hle earlier
    original rfl lookup closed hTarget substitutions fits entry.certificate entry.available
  have naturalCertificate := Eq.mp (congrArg
    (fun e => CodeCert env U registry target locals σ e entry.support alignment.footprint)
    naturalOrigin) alignment.naturalCertificate
  have declaredCertificate := Eq.mp (congrArg
    (fun e => CodeCert env U registry target locals σ e entry.support entry.footprint)
    declaredOrigin) entry.certificate
  obtain ⟨naturalFoot, ⟨naturalCode⟩, ⟨naturalCuts⟩⟩ :=
    naturalCertificate.factorNativeTemplate naturalScope naturalLocals
  obtain ⟨declaredFoot, ⟨declaredCode⟩, ⟨declaredCuts⟩⟩ :=
    declaredCertificate.factorNativeTemplate declaredScope captureLocals
  have naturalRealized := realized_template naturalScope σ
  have declaredRealized := realized_template declaredScope σ
  rw [← naturalOrigin] at naturalRealized
  rw [← declaredOrigin] at declaredRealized
  exact ⟨{
    naturalOriginalFootprint := alignment.footprint
    naturalOriginalResources := alignment.resources
    declaredOriginalFootprint := entry.footprint
    declaredOriginalResources := entry.available
    naturalFootprint := naturalFoot
    declaredFootprint := declaredFoot
    naturalCuts := naturalCuts
    declaredCuts := declaredCuts
    guard := {
      naturalSupport := entry.support
      declaredSupport := entry.support
      naturalFootprint := naturalFoot
      naturalCertificate := naturalCode
      naturalResources := requirements_available _
      declaredFootprint := declaredFoot
      declaredCertificate := declaredCode
      declaredResources := requirements_available _
      naturalTyped := entry.typed
      declaredTyped := entry.typed
      alignment := naturalRealized ▸ declaredRealized ▸
        DomainChain.step alignment.path entry.typed declaredCertificate.formed
          alignment.related (.refl _)
      declaredCode := declaredRealized ▸
        (alignment.related.symm henv entry.typed.wf_type).left_diagonal }
    naturalFootprint_eq := rfl
    declaredFootprint_eq := rfl }⟩

end Lean4Lean.AnchoredSource.Adapted
