import Lean4Lean.Theory.Typing.AnchoredNativeRetelescope
import Lean4Lean.Theory.Typing.AnchoredNativeTypeCertificate
import Lean4Lean.Theory.Typing.AnchoredNativeSpineObservation

/-! A computational skeleton and its actual registered header certificate
produce the genuine native source observer. Registered binder guards are
constructed by retelescoping, and the inverse finite view restores the exact
original computational demand before the application spine is replayed. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
open private telescope_eq from Lean4Lean.Theory.Inductive.NativeCommonPrefix
set_option backward.isDefEq.respectTransparency false

private theorem telescopeContext {env : VEnv} {U : Nat} {Γ domains : List VExpr}
    {result : VExpr} (henv : env.Ordered)
    (formed : OnCtx Γ (env.IsType U))
    (type : env.IsType U Γ (wrapForalls domains result)) :
    OnCtx (domains.reverse ++ Γ) (env.IsType U) := by
  induction domains generalizing Γ with
  | nil => exact formed
  | cons domain domains ih =>
    obtain ⟨domainType, bodyType⟩ := IsType.forallE_inv henv type
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih (Γ := domain :: Γ) ⟨formed, domainType⟩ bodyType

theorem NativeRetelescopeSkeleton.source
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    (registered : NativeRecursorRegistered env data)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (typeClosed : signature.type.Closed)
    (formation : sourceEnv.IsDefEqStrong U [] (signature.type.instL levels)
      (signature.type.instL levels) (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry)
      [] (signature.type.instL levels))
    {atom : Atom n} (skeleton : NativeRetelescopeSkeleton env U registry target signature [] atom [])
    {support : Profile n} {typeLocals : List Nat} {typeRealization : Subst}
    (certificate : CodeCert env U registry target typeLocals typeRealization
      (signature.type.instL levels) support [])
    (typed : (Profile.singleton atom).HasType support)
    (locals : List Nat) (σ : Subst) :
    Nonempty (Obs env U registry target locals σ (.const data.name levels) (.singleton atom) []) := by
  have closed : Valuation.AtomClosed (fun _ => []) := by intro _ _ h; cases h
  have literal := telescope_eq signature.telescope
  have certificate' : CodeCert env U registry target [] (nativeCaptureSubst [])
      (wrapForalls signature.domains signature.result) support [] := by
    rw [← literal]
    exact certificate.closedSource typeClosed.instL [] (nativeCaptureSubst [])
  obtain ⟨result⟩ := skeleton.build henv hscoped hle hTarget
    (by simpa only [List.length_nil, List.take_zero, List.reverse_nil, List.drop_zero, ← literal] using header)
    closed .nil .nil (by intro _ _ h; cases h)
    (by simpa only [List.length_nil, List.range_zero, List.drop_zero] using certificate')
    (by intro _ _ h; cases h) typed
  have footprintEmpty : result.footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    exact nomatch result.resources index need member
  have tree : NativeInitialTree env U registry target signature [] (.singleton result.output) [] :=
    footprintEmpty ▸ result.tree
  have whole : CodeCert env U registry target [] typeRealization (signature.type.instL levels)
      (result.view.mapType support) [] :=
    result.certificate (certificate.closedSource typeClosed.instL [] typeRealization)
  have raw : env.HasType U [] (wrapForalls signature.domains signature.result) (.sort level) := by
    rw [← literal]
    exact (formation.defeq.mono hle).hasType.1
  have domains := telescopeContext (Γ := []) henv trivial ⟨_, raw⟩
  have native := tree.source henv levelsWF lookup notDefinition rfl registered
    (by simpa only [List.append_nil] using domains) whole (result.typed typed) locals σ
  exact ⟨.view native (result.view.inverse henv)⟩

end Lean4Lean.AnchoredSource.Adapted
