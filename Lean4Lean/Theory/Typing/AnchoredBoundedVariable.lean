import Lean4Lean.Theory.Typing.AnchoredBoundedStage

/-! The first declaration-stage producer: variable interpretation consumes
bounded valuation certificates through the ORIGINAL same-fuel type child.
All outer observation closures preserve the same native-depth bound. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat} {env : VEnv} {U : Nat}
  {registry : CanonicalHead.Registry} {source target : List VExpr}
  {locals : List Nat} {σ τ : Subst} {available : Valuation}
  {left right sourceType : VExpr}

/-- Interpret only the actual finite certificate leaves. This theorem neither
invokes an unrestricted Joint nor recursively interprets a returned observer. -/
theorem Transfer.code
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (original : Transfer current fuel env U registry target locals σ τ available left right sourceType)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ left profile footprint)
    (bound : certificate.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    TypeRelated env U registry target (left.subst σ) (right.subst τ) profile := by
  match certificate with
  | .seed observation formed =>
    simp only [CodeCert.nativeDepth] at bound
    obtain ⟨result⟩ := original observation bound resources
    exact (result.toGradedTransferResult.requestedRelated henv hTarget).code_of_sortable
      henv hscoped hTarget formed
  | .union first second =>
    simp only [CodeCert.nativeDepth] at bound
    have bounds := Nat.max_le.mp bound
    have a := original.code henv hscoped hTarget first bounds.1
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    have b := original.code henv hscoped hTarget second bounds.2
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim (fun h => a.singleton h) (fun h => b.singleton h)
  | .pad child =>
    simp only [CodeCert.nativeDepth] at bound
    exact (original.code henv hscoped hTarget child bound resources).pad henv
  | .familyPad child =>
    simp only [CodeCert.nativeDepth] at bound
    exact (original.code henv hscoped hTarget child bound resources).familyPad henv
  | .unpad child =>
    simp only [CodeCert.nativeDepth] at bound
    exact (TypeRelated.pad_iff henv).mp (original.code henv hscoped hTarget child bound resources)
  | .down child =>
    simp only [CodeCert.nativeDepth] at bound
    exact (original.code henv hscoped hTarget child bound resources).down henv
  | .map transformation child =>
    simp only [CodeCert.nativeDepth] at bound
    exact transformation.codeMap henv hscoped (original.code henv hscoped hTarget child bound resources)
  | .select child member =>
    simp only [CodeCert.nativeDepth] at bound
    exact (original.code henv hscoped hTarget child bound resources).singleton member
  | .focusMinimal child minimal focusedBound =>
    simp only [CodeCert.nativeDepth] at bound
    exact (original.code henv hscoped hTarget child bound resources).focusMinimal henv minimal focusedBound
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; omega

namespace Result

def empty : Result current fuel env U registry target locals σ τ available left right sourceType
    (Profile.empty (n := n)) where
  toGradedTransferResult := .empty
  observationBound := by simp only [GradedTransferResult.empty, Obs.nativeDepth]; exact Nat.zero_le _
  certificateBound := by simp only [GradedTransferResult.empty, CodeCert.nativeDepth, Obs.nativeDepth]; exact Nat.zero_le _

def unpad {demand : Profile n}
    (result : Result current fuel env U registry target locals σ τ available left right sourceType demand.pad) :
    Result current fuel env U registry target locals σ τ available left right sourceType demand where
  toGradedTransferResult := result.toGradedTransferResult.unpad
  observationBound := result.observationBound
  certificateBound := result.certificateBound

noncomputable def pad (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U)) {demand : Profile n}
    (result : Result current fuel env U registry target locals σ τ available left right sourceType demand) :
    Result current fuel env U registry target locals σ τ available left right sourceType demand.pad where
  toGradedTransferResult := result.toGradedTransferResult.pad henv hscoped hTarget
  observationBound := by simpa only [GradedTransferResult.pad, Obs.nativeDepth] using result.observationBound
  certificateBound := by simpa only [GradedTransferResult.pad, CodeCert.nativeDepth] using result.certificateBound

noncomputable def view (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U)) {a b : Atom n}
    (change : AtomView env U registry target a b)
    (result : Result current fuel env U registry target locals σ τ available left right sourceType (.singleton a)) :
    Result current fuel env U registry target locals σ τ available left right sourceType (.singleton b) where
  toGradedTransferResult := result.toGradedTransferResult.view henv hscoped hTarget change
  observationBound := result.observationBound
  certificateBound := by
    simpa only [GradedTransferResult.view, CodeCert.nativeDepth,
      CodeCert.nativeDepth_raise, GradedTransferResult.requestedCertificate,
      CodeCert.nativeDepth_lower, Nat.max_self] using result.certificateBound

noncomputable def union (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U)) {p q : Profile n}
    (first : Result current fuel env U registry target locals σ τ available left right sourceType p)
    (second : Result current fuel env U registry target locals σ τ available left right sourceType q) :
    Result current fuel env U registry target locals σ τ available left right sourceType (p.union q) where
  toGradedTransferResult := first.toGradedTransferResult.union henv hscoped hTarget second.toGradedTransferResult
  observationBound := by
    simp only [GradedTransferResult.union, GradedTransferResult.raiseTo,
      Obs.nativeDepth, Obs.nativeDepth_raise]
    exact Nat.max_le.mpr ⟨first.observationBound, second.observationBound⟩
  certificateBound := by
    simp only [GradedTransferResult.union, GradedTransferResult.raiseTo,
      CodeCert.nativeDepth, CodeCert.nativeDepth_raise]
    exact Nat.max_le.mpr ⟨first.certificateBound, second.certificateBound⟩
end Result

theorem bvarTransfer
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {index : Nat} {A : VExpr}
    (lookup : Lookup source index A)
    (originalType : Joint current fuel env U registry source A A (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    {n : Nat} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.bvar index) demand footprint)
    (bound : observation.nativeDepth current ≤ fuel) (resources : footprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ τ available (.bvar index) (.bvar index) A demand) := by
  match observation with
  | .var _ _ _ demand =>
    obtain ⟨entry, certificateBound⟩ := fits.forward.entry index ⟨n, demand⟩
      (resources index _ List.mem_cons_self) A lookup
    have producer : Transfer current fuel env U registry target locals σ σ available A A (.sort level) :=
      (originalType target locals σ σ available closed hTarget substitutions.left fits.left).1
    have code := producer.code henv hscoped hTarget entry.certificate certificateBound entry.available
    exact ⟨{
      rank := n
      bound := Nat.le_refl n
      rawDemand := demand
      resultFootprint := [(index, ⟨n, demand⟩)]
      observation := .var locals τ index demand
      adapter := by rw [raiseProfile_self]; exact .refl _
      resultAvailable := resources
      support := entry.support
      typeFootprint := entry.footprint
      certificate := entry.certificate
      typeAvailable := entry.available
      typed := by simpa only [raiseProfile_self] using entry.typed
      rawTyped := entry.typed
      typeCode := code
      related := by simpa only [raiseProfile_self, subst_bvar] using entry.related
      rawRelated := (entry.related.symm henv).left_diagonal
      observationBound := by simp only [GradedTransferResult.empty, Obs.nativeDepth]; exact Nat.zero_le _
      certificateBound := certificateBound }⟩
  | .empty => exact ⟨.empty⟩
  | .union left right =>
    simp only [Obs.nativeDepth] at bound
    have bounds := Nat.max_le.mp bound
    obtain ⟨a⟩ := bvarTransfer henv hscoped lookup originalType closed hTarget substitutions fits
      left bounds.1 (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := bvarTransfer henv hscoped lookup originalType closed hTarget substitutions fits
      right bounds.2 (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view child change =>
    simp only [Obs.nativeDepth] at bound
    obtain ⟨a⟩ := bvarTransfer henv hscoped lookup originalType closed hTarget substitutions fits child bound resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad child =>
    simp only [Obs.nativeDepth] at bound
    obtain ⟨a⟩ := bvarTransfer henv hscoped lookup originalType closed hTarget substitutions fits child bound resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad child =>
    simp only [Obs.nativeDepth] at bound
    obtain ⟨a⟩ := bvarTransfer henv hscoped lookup originalType closed hTarget substitutions fits child bound resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ child =>
    simp only [Obs.nativeDepth] at bound
    obtain ⟨a⟩ := bvarTransfer henv hscoped lookup originalType closed hTarget substitutions fits child bound resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem Transfer.sortCorrect (henv : env.Ordered)
    (hTarget : OnCtx target (env.IsType U))
    (original : Transfer current fuel env U registry target locals σ τ available left right sourceType) :
    SortCorrect current fuel env U registry target locals σ available left sourceType := by
  intro level relevant he flag n demand footprint observation bound resources
  subst sourceType
  obtain ⟨result⟩ := original observation bound resources
  have code := TypeRelated.lower henv result.bound result.typeCode
  exact TypeRelated.sort_typed hTarget flag code result.toGradedTransferResult.requestedTyped

theorem Joint.bvar (henv : env.Ordered) (hscoped : registry.Scoped)
    {index : Nat} {A : VExpr} (lookup : Lookup source index A)
    (originalType : Joint current fuel env U registry source A A (.sort level)) :
    Joint current fuel env U registry source (.bvar index) (.bvar index) A := by
  intro target locals σ τ available closed hTarget substitutions fits
  have transfer : Transfer current fuel env U registry target locals σ τ available (.bvar index) (.bvar index) A :=
    fun observation bound resources =>
      bvarTransfer henv hscoped lookup originalType closed hTarget substitutions fits observation bound resources
  exact ⟨transfer, transfer, Transfer.sortCorrect henv hTarget transfer, Transfer.sortCorrect henv hTarget transfer⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
