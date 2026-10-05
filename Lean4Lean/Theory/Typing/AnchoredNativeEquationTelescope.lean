import Lean4Lean.Theory.Typing.AnchoredNativePairedLambda

/-! Reconstruct and compare the shared original equation telescope. At every
binder the two original natural types are retained separately; their concrete
source certificates and finite semantic bridge are passed to the body. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure NativeEquationResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (left right rightType : VExpr) (demand support : Profile n) where
  footprint : Footprint
  observation : Obs env U registry target locals σ left demand footprint
  resources : footprint.Available available
  related : Related env U registry target (right.subst σ) (left.subst σ)
    (rightType.subst σ) demand support

/-- Internal telescope motive. Its eventual leaf is the concrete native
terminal interpretation, including its actual registered argument valuation. -/
def NativeEquationComparison (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source : List VExpr) (left right : VExpr) : Prop :=
  ∀ {leftType rightType leftStructural rightStructural},
    sourceEnv.HasTypeStrong U source left leftType leftStructural →
    sourceEnv.HasTypeStrong U source right rightType rightStructural →
    ∀ {target locals σ available}, available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ σ source →
    PairedFits env U registry source target locals σ σ available →
    ∀ {n} {demand support : Profile n} {footprint leftFootprint rightFootprint},
    Obs env U registry target locals σ right demand footprint → footprint.Available available →
    CodeCert env U registry target locals σ leftType support leftFootprint →
    CodeCert env U registry target locals σ rightType support rightFootprint →
    leftFootprint.Available available → rightFootprint.Available available →
    TypeRelated env U registry target (leftType.subst σ) (rightType.subst σ) support →
    demand.HasType support →
    Nonempty (NativeEquationResult env U registry target locals σ available left right rightType demand support)

private theorem pack_append {p q : Profile n}
    (first : BinderPack n p before outside)
    (second : BinderPack n q after other) :
    BinderPack n (p.union q) (before ++ after) (outside ++ other) := by
  induction first with
  | nil => exact second
  | «local» need bound tail ih =>
    simpa only [Profile.union, Profile.atoms, Profile.mk, List.append_assoc, List.cons_append] using
      BinderPack.local need bound ih
  | external index need tail ih => exact .external index need ih

private theorem typed_subset {p q d : Profile n}
    (subset : ∀ atom ∈ p.atoms, atom ∈ q.atoms) (typed : q.HasType d) : p.HasType d := by
  cases n with
  | zero => exact fun atom hm => typed atom (subset atom hm)
  | succ n => exact ⟨fun atom hm => typed.1 atom (subset atom hm), typed.2.1,
      fun atom hm => typed.2.2 atom (subset atom hm)⟩

private theorem compare_lambda
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {source : List VExpr} {A left right : VExpr}
    (next : NativeEquationComparison sourceEnv env U registry (A :: source) left right)
    {leftType rightType leftStructural rightStructural}
    (originalLeft : sourceEnv.HasTypeStrong U source (.lam A left) leftType leftStructural)
    (originalRight : sourceEnv.HasTypeStrong U source (.lam A right) rightType rightStructural)
    {target locals σ available} (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {n} {demand support : Profile n} {footprint leftFootprint rightFootprint}
    (observation : Obs env U registry target locals σ (.lam A right) demand footprint)
    (resources : footprint.Available available)
    (leftCertificate : CodeCert env U registry target locals σ leftType support leftFootprint)
    (rightCertificate : CodeCert env U registry target locals σ rightType support rightFootprint)
    (leftResources : leftFootprint.Available available)
    (rightResources : rightFootprint.Available available)
    (bridge : TypeRelated env U registry target (leftType.subst σ) (rightType.subst σ) support)
    (typed : demand.HasType support) :
    Nonempty (NativeEquationResult env U registry target locals σ available
      (.lam A left) (.lam A right) rightType demand support) := by
  revert support
  match hobs : observation with
  | .empty =>
    intro support leftCertificate rightCertificate bridge typed
    exact ⟨{
      footprint := []
      observation := .empty
      resources := by intro _ _ h; cases h
      related := by cases n <;> intro _ h <;> cases h }⟩
  | .lam (key := key) (bodyFootprint := bodyFootprint) (externalFootprint := oldOutside)
      (domainFootprint := domainFootprint) domain guard body pack covered =>
    intro support leftCertificate rightCertificate bridge typed
    obtain ⟨leftOrigin⟩ := HasTypeStrong.originalLambdaOrigin earlier originalLeft rfl
    obtain ⟨rightOrigin⟩ := HasTypeStrong.originalLambdaOrigin earlier originalRight rfl
    obtain ⟨row⟩ := leftOrigin.pairedRow henv hscoped hle rightOrigin closed hTarget
      substitutions fits leftCertificate rightCertificate leftResources rightResources bridge typed
    have domainAvailable := fun i need hm => resources i need (List.mem_append_left _ hm)
    have outsideAvailable := fun i need hm => resources i need (List.mem_append_right _ hm)
    have rowsPack := pack_append row.left.pack row.right.pack
    have rowsCovered := fun atom hm => (List.mem_append.mp hm).elim
      (row.left.covered atom) (row.right.covered atom)
    have joinedPack := pack_append pack rowsPack
    have joinedCovered := fun atom hm => (List.mem_append.mp hm).elim
      (covered atom) (rowsCovered atom)
    have joinedOutside : (oldOutside ++ (row.left.outside ++ row.right.outside)).Available available := by
      intro i need hm
      rcases List.mem_append.mp hm with hm | hm
      · exact outsideAvailable i need hm
      · exact (List.mem_append.mp hm).elim (row.left.outsideAvailable i need)
          (row.right.outsideAvailable i need)
    let required := bodyFootprint ++ (row.left.bodyFootprint ++ row.right.bodyFootprint)
    let head := required.localNeeds ++ required.localNeeds.flatMap Need.singletons
    have localClosed := Valuation.push_atomized_closed closed required.localNeeds
    obtain ⟨raw, _, _, _, _, _, _, anchor⟩ := guard.anchor
    have arguments := Related.convert henv guard.inputTyped guard.domains anchor
    have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons key.anchor) (A :: source) :=
      .cons substitutions (rightOrigin.domainStrong.defeq.mono hle) (guard.path.cast raw)
    have localFits := fits.pushDiagonal henv hTarget domain domainAvailable guard.inputTyped arguments
      head (fun need hm => (joinedPack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => joinedCovered atom ((joinedPack.atomized_localNeeds need hm).2 atom ha))
    have allResources := joinedPack.available_atomized_localNeeds joinedOutside
    obtain ⟨child⟩ := next leftOrigin.bodyTyping rightOrigin.bodyTyping localClosed hTarget paired
      localFits body (fun i need hm => allResources i need (List.mem_append_left _ hm))
      row.left.body row.right.body
      (fun i need hm => allResources i need (List.mem_append_right _ (List.mem_append_left _ hm)))
      (fun i need hm => allResources i need (List.mem_append_right _ (List.mem_append_right _ hm)))
      row.related row.typed
    obtain ⟨newPacked, outside, newPack, newCovered, newOutsideAvailable⟩ :=
      Footprint.pack_available child.resources
        (fun need hm => (joinedPack.atomized_localNeeds need hm).1)
        (fun need hm atom ha => joinedCovered atom ((joinedPack.atomized_localNeeds need hm).2 atom ha))
    let changed := Obs.lam domain guard child.observation newPack newCovered
    have changedAvailable : (domainFootprint ++ outside).Available available := fun i need hm =>
      (List.mem_append.mp hm).elim (domainAvailable i need) (newOutsideAvailable i need)
    obtain ⟨leftSelf⟩ := (earlier originalLeft.refl target locals σ σ available closed hTarget
      substitutions fits).1 changed changedAvailable
    obtain ⟨rightSelf⟩ := (earlier originalRight.refl target locals σ σ available closed hTarget
      substitutions fits).1 (.lam domain guard body pack covered) resources
    exact ⟨⟨_, changed, changedAvailable, row.close henv hscoped typed hTarget substitutions
      (rightOrigin.domainStrong.defeq.mono hle) (leftOrigin.bodyStrong.defeq.mono hle)
      (rightOrigin.bodyStrong.defeq.mono hle) (leftSelf.requestedRelated henv hTarget)
      (rightSelf.requestedRelated henv hTarget) child.related⟩⟩
  | .union first second =>
    intro support leftCertificate rightCertificate bridge typed
    obtain ⟨a⟩ := compare_lambda henv hscoped hle earlier next originalLeft originalRight
      closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      leftCertificate rightCertificate leftResources rightResources bridge
      (typed_subset (fun _ hm => List.mem_append_left _ hm) typed)
    obtain ⟨b⟩ := compare_lambda henv hscoped hle earlier next originalLeft originalRight
      closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
      leftCertificate rightCertificate leftResources rightResources bridge
      (typed_subset (fun _ hm => List.mem_append_right _ hm) typed)
    exact ⟨⟨_, .union a.observation b.observation,
      fun i need hm => (List.mem_append.mp hm).elim (a.resources i need) (b.resources i need),
      a.related.union b.related⟩⟩
  | .view child change =>
    intro support leftCertificate rightCertificate bridge typed
    let inverse := change.inverse henv
    obtain ⟨a⟩ := compare_lambda henv hscoped hle earlier next originalLeft originalRight
      closed hTarget substitutions fits child resources (.map inverse leftCertificate)
      (.map inverse rightCertificate) leftResources rightResources
      (inverse.codeMap henv hscoped bridge) (inverse.mapType_typed typed)
    exact ⟨⟨_, .view a.observation change, a.resources,
      (change.termMap henv hscoped hTarget a.related).retag henv typed
        (bridge.symm henv typed.wf_type).left_diagonal⟩⟩
  | .pad child =>
    intro support leftCertificate rightCertificate bridge typed
    obtain ⟨a⟩ := compare_lambda henv hscoped hle earlier next originalLeft originalRight
      closed hTarget substitutions fits child resources (.down leftCertificate) (.down rightCertificate)
      leftResources rightResources (bridge.down henv) typed.pad_inv
    exact ⟨⟨_, .pad a.observation, a.resources, (a.related.pad henv).retag henv typed
      (bridge.symm henv typed.wf_type).left_diagonal⟩⟩
  | .unpad child =>
    intro support leftCertificate rightCertificate bridge typed
    obtain ⟨a⟩ := compare_lambda henv hscoped hle earlier next originalLeft originalRight
      closed hTarget substitutions fits child resources (.pad leftCertificate) (.pad rightCertificate)
      leftResources rightResources (bridge.pad henv) typed.pad
    exact ⟨⟨_, .unpad a.observation, a.resources, (a.related.unpad henv hTarget).retag henv typed
      (bridge.symm henv typed.wf_type).left_diagonal⟩⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ child =>
    intro support leftCertificate rightCertificate bridge typed
    let inverse := AtomView.uncommutePadFn (env := env) (U := U) (registry := registry)
      (Γ := target) key output
    have oldTyped : (Profile.fn key output).HasType (inverse.mapType support).down := by
      apply Profile.HasType.pad_inv
      simpa only [Profile.fn, Profile.pad_singleton] using inverse.mapType_typed typed
    obtain ⟨a⟩ := compare_lambda henv hscoped hle earlier next originalLeft originalRight
      closed hTarget substitutions fits child resources (.down (.map inverse leftCertificate))
      (.down (.map inverse rightCertificate)) leftResources rightResources
      ((inverse.codeMap henv hscoped bridge).down henv) oldTyped
    have padded := a.related.pad henv
    simp only [Profile.fn, Profile.pad_singleton] at padded
    have changed := (AtomView.commutePadFn key output).termMap henv hscoped hTarget padded
    exact ⟨⟨_, .rowShift a.observation, a.resources, changed.retag henv typed
      (bridge.symm henv typed.wf_type).left_diagonal⟩⟩
termination_by sizeOf observation
decreasing_by all_goals subst_vars; simp_wf; omega

/-- Lift the concrete open comparison through every literal original lambda.
Every observation closure and every original outer type conversion is covered. -/
theorem NativeEquationComparison.underTelescope
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    (domains : List VExpr) {source : List VExpr} {left right : VExpr}
    (terminal : NativeEquationComparison sourceEnv env U registry
      (domains.reverse ++ source) left right) :
    NativeEquationComparison sourceEnv env U registry source
      (wrapLams domains left) (wrapLams domains right) := by
  induction domains generalizing source with
  | nil => exact terminal
  | cons A domains ih =>
    apply compare_lambda henv hscoped hle earlier
    apply ih
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at terminal
    exact terminal

end Lean4Lean.AnchoredSource.Adapted
