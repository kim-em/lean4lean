import Lean4Lean.Theory.Typing.AnchoredBoundedPiExtraction
import Lean4Lean.Theory.Typing.AnchoredDomainChainView
import Lean4Lean.Theory.Typing.AnchoredEtaAnnotation
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty

/-! Reverse eta expands actual raw function observations at the right
realization. Their assigned-type certificates remain at the left realization. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

structure EtaExpansionResult (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (A B f : VExpr) (demand : Profile n) where
  rawDemand : Profile n
  footprint : Footprint
  observation : Obs env U registry target locals τ (.lam A (.app f.lift (.bvar 0))) rawDemand footprint
  resultAvailable : footprint.Available available
  adapter : NormalProfileAdapter env U registry target rawDemand demand
  support : Profile n
  typeFootprint : Footprint
  certificate : CodeCert env U registry target locals σ (.forallE A B) support typeFootprint
  typeAvailable : typeFootprint.Available available
  typed : demand.HasType support
  rawTyped : rawDemand.HasType support
  code : TypeRelated env U registry target ((VExpr.forallE A B).subst σ) ((VExpr.forallE A B).subst σ) support
  related : Related env U registry target (f.subst τ)
    ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ)
    ((VExpr.forallE A B).subst σ) demand support
  rawRelated : Related env U registry target
    ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ)
    ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ)
    ((VExpr.forallE A B).subst σ) rawDemand support
  observationBound : observation.nativeDepth current ≤ fuel
  certificateBound : certificate.nativeDepth current ≤ fuel

private theorem eta_subst (A f : VExpr) (τ : Subst) :
    (VExpr.lam A (.app f.lift (.bvar 0))).subst τ =
      .lam (A.subst τ) (.app (f.subst τ).lift (.bvar 0)) := by
  show VExpr.lam (A.subst τ) (.app (f.lift.subst τ.lift) ((VExpr.bvar 0).subst τ.lift)) = _
  rw [lift_subst_lift]
  rfl

private theorem etaPack (input : Profile n) (outside : Footprint) :
    BinderPack n input (outside.sourceLift (.skip .refl) ++ [(0, ⟨n, input⟩)]) outside := by
  induction outside with
  | nil =>
    have h := BinderPack.local (n := n) ⟨n, input⟩ (Nat.le_refl n) BinderPack.nil
    simpa [Need.atGrade, Profile.union, Profile.empty, Profile.atoms, Profile.mk, Footprint.sourceLift] using h
  | cons entry rest ih =>
    obtain ⟨i, need⟩ := entry
    exact .external i need ih

private theorem code_union
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim (fun h => first.singleton h) (fun h => second.singleton h)

theorem Obs.expand_eta_atom
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {atom : Atom n} {support : Profile n} {footprint typeFootprint : Footprint}
    (observation : Obs env U registry target locals τ f (.singleton atom) footprint)
    (observationBound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available)
    (certificate : CodeCert env U registry target locals σ (.forallE A B) support typeFootprint)
    (certificateBound : certificate.nativeDepth current ≤ fuel)
    (typeAvailable : typeFootprint.Available available)
    (typed : (Profile.singleton atom).HasType support)
    (code : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A B).subst σ) support)
    (related : Related env U registry target (f.subst τ) (f.subst τ)
      ((VExpr.forallE A B).subst σ) (.singleton atom) support)
    (rawEta : env.IsDefEq U target ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ)
      (f.subst τ) ((VExpr.forallE A B).subst σ))
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available) :
    Nonempty (EtaExpansionResult current fuel env U registry target locals σ τ available A B f (.singleton atom)) := by
  have origins := CodeCert.piOrigins henv hscoped hTarget closed formedA formedB
    substitutions.left fits.left originalDomain originalCodomain certificate certificateBound typeAvailable
  have shape := origins.value_shape typed (List.mem_singleton_self _)
  cases n with
  | zero => exact shape.elim
  | succ n =>
    obtain ⟨key, output, normalEq⟩ := shape
    let normal : AtomView env U registry target atom (n := n + 1) (.fn key output) :=
      normalEq ▸ AdapterNormal.view henv atom
    let normalizedObs := Obs.view observation normal
    let normalizedCert := CodeCert.map normal certificate
    have normalizedTyped := normal.mapType_typed typed
    have normalizedRelated := normal.termMap henv hscoped hTarget related
    obtain ⟨resultSupport, ⟨row⟩, _⟩ := CodeCert.piRow henv hscoped hTarget closed
      formedA formedB substitutions.left fits.left originalDomain originalCodomain
      normalizedCert (by simpa only [normalizedCert, CodeCert.nativeDepth] using certificateBound) typeAvailable normalizedTyped
    have child : Transfer current fuel env U registry target locals σ τ available A A (.sort domainLevel) :=
      (originalDomain target locals σ τ available closed hTarget substitutions fits).1
    obtain ⟨domain⟩ := child.codeCertificate henv hscoped hTarget closed row.domain row.domainBound row.domainAvailable
    have path : TypeConversion env U target (A.subst σ) (A.subst τ) :=
      .single (formedA.substDF henv substitutions.wf hTarget substitutions)
    have admittedA := row.alignment.admission henv row.anchor
    have seed := Admitted.rekey (key := ⟨A.subst σ, key.anchor, key.input⟩) henv path row.inputTyped row.domain.formed domain.related admittedA
    let newKey : Key n := ⟨A.subst τ, key.anchor, key.input⟩
    have guard : LambdaGuard env U registry target τ A newKey row.domainSupport := {
      inputTyped := row.inputTyped
      formed := row.domain.formed
      path := .refl
      domains := (domain.related.symm henv row.inputTyped.wf_type).left_diagonal
      anchor := seed }
    have liftedPair : ∃ lifted : Obs env U registry target (Locals.push locals) (τ.cons key.anchor)
        (f.lift' (.skip .refl)) (Profile.fn key output) (footprint.sourceLift (.skip .refl)),
        lifted.nativeDepth current ≤ fuel :=
      ⟨normalizedObs.renameSource (.skip .refl) (τ.cons key.anchor) rfl (Locals.push locals), by
        simpa only [Obs.nativeDepth_renameSource, normalizedObs, Obs.nativeDepth] using observationBound⟩
    rw [← lift_eq_lift'] at liftedPair
    obtain ⟨lifted, liftedBound⟩ := liftedPair
    let application : Obs env U registry target (Locals.push locals) (τ.cons key.anchor)
        (.app f.lift (.bvar 0)) (.singleton output)
        (footprint.sourceLift (.skip .refl) ++ [(0, ⟨n, key.input⟩)]) := by
      exact .app lifted
        (.var _ _ 0 key.input) (.refl _) row.anchor
    let expanded := Obs.lam domain.certificate guard application (etaPack key.input footprint)
      (fun _ h => h)
    have changing : AtomView env U registry target (n := n + 1)
        (.fn key output) (.fn newKey output) :=
      .trans (row.alignment.view key.anchor output)
        (.domainRekey path row.inputTyped row.domain.formed domain.related)
    have whole : AtomView env U registry target atom (n := n + 1) (.fn newKey output) :=
      .trans normal changing
    have mappedTyped := whole.mapType_typed typed
    have mappedCode := whole.codeMap henv hscoped code
    have mappedRelated := whole.termMap henv hscoped hTarget related
    have rawEta' := rawEta
    rw [eta_subst] at rawEta'
    have etaLeft := Related.etaExpandAt henv rawEta' rawEta'.hasType.2 mappedRelated
    have etaRight := Related.symm henv etaLeft
    have etaSelf := Related.etaExpandAt henv rawEta' rawEta'.hasType.1 etaRight
    have oldRelated := (whole.inverse henv).termMap henv hscoped hTarget etaRight
    have oldTyped := (whole.inverse henv).mapType_typed mappedTyped
    have oldCode := (whole.inverse henv).codeMap henv hscoped mappedCode
    have back := Related.retag henv typed code oldRelated
    have allCode := code_union code mappedCode
    have wf := typed.wf_type.union mappedTyped.wf_type
    have requestedTyped := typed.enlarge (Profile.le_union_left _ _) wf
    have rawTyped := mappedTyped.enlarge (Profile.le_union_right _ _) wf
    exact ⟨{
      rawDemand := Profile.fn newKey output
      footprint := domain.footprint ++ footprint
      observation := expanded
      resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
        (domain.available i need) (resources i need)
      adapter := .cons (List.mem_singleton_self _) ((whole.inverse henv).toAdapter henv hscoped hTarget) (.nil _)
      support := _
      typeFootprint := typeFootprint ++ typeFootprint
      certificate := .union certificate (.map whole certificate)
      typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
        (typeAvailable i need) (typeAvailable i need)
      typed := requestedTyped
      rawTyped := rawTyped
      code := allCode
      related := by simpa only [eta_subst] using Related.retag henv requestedTyped allCode back
      rawRelated := by simpa only [eta_subst, Profile.fn] using Related.retag henv rawTyped allCode etaSelf
      observationBound := by
        simp only [expanded, application, Obs.nativeDepth]
        have zero : Obs.nativeDepth current (Obs.var (env := env) (U := U) (registry := registry)
            (target := target) (Locals.push locals) (τ.cons key.anchor) 0 key.input) = 0 := by
          rw [Obs.nativeDepth]
        rw [zero, Nat.max_zero]
        exact Nat.max_le.mpr ⟨domain.certificateBound, liftedBound⟩
      certificateBound := by simpa only [CodeCert.nativeDepth, Nat.max_self] using certificateBound }⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
