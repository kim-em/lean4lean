import Lean4Lean.Theory.Typing.AnchoredSortableDepthSupply
import Lean4Lean.Theory.Typing.AnchoredSortableLive
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiRebind

/-! Full hereditary substitution preserves all caller declaration bounds on
one actual returned payload. Every replacement is a stored finite query;
binder extension and generalized app/lambda reconstruction retain its bounds. -/
namespace Lean4Lean.AnchoredSource.Adapted.AllDepth
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private append_available replacement_lift anchor_live guardAnchor obsFootprint certFootprint from
  Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

structure CertificateResult (budget : Budget) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (relevant : Bool) (profile : Profile n) where
  footprint : Footprint
  certificate : SortableCert env U registry Γ locals σ expression relevant profile footprint
  resources : footprint.Available available
  bounded : ∀ current, certificate.nativeDepth current ≤ budget current

structure RowsResult (budget : Budget) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) (relevant : Bool) (ambient : Profile n) (rows : List (Key n × Profile n)) where
  footprint : Footprint
  bodies : SortableRows env U registry Γ locals σ A B relevant ambient rows footprint
  resources : footprint.Available available
  bounded : ∀ current, bodies.nativeDepth current ≤ budget current

private def sortableFootprint {footprint : Footprint}
    (_ : SortableCert env U registry Γ locals σ expression relevant demand footprint) : Footprint := footprint

private def sortableObsFootprint {footprint : Footprint}
    (_ : SortableObs env U registry Γ locals σ expression demand footprint) : Footprint := footprint

mutual
theorem Obs.substituteSortable
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (observation : Obs env U registry Γ locals sourceRealization expression demand required)
    (depth : ∀ current, observation.nativeDepth current ≤ budget current)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : GradedSupply budget env U registry Γ newLocals realization replacement available required) :
    Nonempty (GradedResult budget env U registry Γ newLocals realization available
      (expression.subst replacement) demand) := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    exact ⟨GradedResult.exact
      (.legacy (.delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body))
      (fun _ _ h => nomatch h) (body.live henv hscoped hΓ (fun _ _ h => nomatch h))
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega)⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨GradedResult.exact
      (.legacy (.native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree))
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h))
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega)⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨GradedResult.exact
      (.legacy (.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree))
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h))
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega)⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨GradedResult.exact
      (.legacy (.constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree))
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h))
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega)⟩
  | .var _ _ _ _ =>
    cases supply with
    | cons value tail => exact ⟨value⟩
  | .empty =>
    exact ⟨GradedResult.exact (.legacy .empty) (fun _ _ h => nomatch h) .empty
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega)⟩
  | .sort relevant =>
    exact ⟨GradedResult.exact (.legacy (.sort relevant)) (fun _ _ h => nomatch h)
      (by cases n <;> simp [Profile.Live, Profile.sort, Atom.Live, Profile.atoms])
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega)⟩
  | .app fn arg arguments admitted =>
    obtain ⟨⟨fnSupply⟩, ⟨argSupply⟩⟩ := supply.split
    obtain ⟨hf⟩ := Obs.substituteSortable henv hscoped hΓ fn
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed fnSupply
    obtain ⟨ha⟩ := Obs.substituteSortable henv hscoped hΓ arg
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed argSupply
    exact GradedResult.app henv hscoped hΓ closed hf ha arguments.toGeneral
      (by simpa only [subst_subst, realized] using admitted)
  | .lam domain guard body normal covered =>
    obtain ⟨⟨domainSupply⟩, ⟨externalSupply⟩⟩ := supply.split
    obtain ⟨hd⟩ := CodeCert.substituteSortable henv hscoped hΓ domain
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed domainSupply
    let bodyFootprint := obsFootprint body
    let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have localCoverage := normal.atomized_localNeeds
    have localLive := (anchor_live henv hscoped hΓ guard.anchor).subset (fun _ hm => covered _ hm)
    obtain ⟨bodySupply⟩ := externalSupply.underBinder normal localLive
      (fun _ hm => List.mem_append_left _ hm) (guardAnchor guard)
    obtain ⟨hb⟩ := Obs.substituteSortable henv hscoped hΓ body
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement.lift
      (realization.cons _) (by rw [replacement_lift, realized]; rfl)
      (Locals.push newLocals) (Valuation.push head available) headClosed bodySupply
    exact GradedResult.lam henv hscoped hΓ closed hd.certificate hd.bounded hd.resources
      (guard.sourceSubstitute replacement realization realized) head
      (fun need hm => (localCoverage need hm).1)
      (fun need hm atom ha => covered atom ((localCoverage need hm).2 atom ha)) hb headClosed
  | .pi domain guard bodies =>
    obtain ⟨⟨domainSupply⟩, ⟨rowSupply⟩⟩ := supply.split
    obtain ⟨hd⟩ := CodeCert.substituteSortable henv hscoped hΓ domain
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed domainSupply
    obtain ⟨hb⟩ := PiRows.substituteSortable henv hscoped hΓ bodies
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed rowSupply
    exact ⟨GradedResult.exact
      (.code true (.pi hd.certificate (guard.sourceSubstitute replacement realization realized) hb.bodies))
      (append_available hd.resources hb.resources) (by
        intro atom member
        cases List.mem_singleton.mp member
        trivial) (by
        intro current
        simp only [SortableObs.nativeDepth, SortableCert.nativeDepth]
        exact Nat.max_le.mpr ⟨hd.bounded current, hb.bounded current⟩)⟩
  | .union left right =>
    obtain ⟨⟨leftSupply⟩, ⟨rightSupply⟩⟩ := supply.split
    obtain ⟨hl⟩ := Obs.substituteSortable henv hscoped hΓ left
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed leftSupply
    obtain ⟨hr⟩ := Obs.substituteSortable henv hscoped hΓ right
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed rightSupply
    exact ⟨hl.union henv hscoped hΓ hr⟩
  | .view source view =>
    obtain ⟨hs⟩ := Obs.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨hs.view henv hscoped hΓ view⟩
  | .pad source =>
    obtain ⟨hs⟩ := Obs.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨hs.pad henv hscoped hΓ⟩
  | .unpad source =>
    obtain ⟨hs⟩ := Obs.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨hs.unpad⟩
  | .rowShift source =>
    obtain ⟨hs⟩ := Obs.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨(hs.pad henv hscoped hΓ).view henv hscoped hΓ (.commutePadFn _ _)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.substituteSortable
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (certificate : CodeCert env U registry Γ locals sourceRealization expression demand required)
    (depth : ∀ current, certificate.nativeDepth current ≤ budget current)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : GradedSupply budget env U registry Γ newLocals realization replacement available required) :
    Nonempty (CertificateResult budget env U registry Γ newLocals realization available
      (expression.subst replacement) true demand) := by
  match certificate with
  | .seed observation formed =>
    obtain ⟨result⟩ := Obs.substituteSortable henv hscoped hΓ observation
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    obtain ⟨footprint, cert, resources, bound⟩ := result.code henv closed formed
    exact ⟨⟨footprint, cert, resources, bound⟩⟩
  | .union left right =>
    obtain ⟨⟨leftSupply⟩, ⟨rightSupply⟩⟩ := supply.split
    obtain ⟨hl⟩ := CodeCert.substituteSortable henv hscoped hΓ left
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed leftSupply
    obtain ⟨hr⟩ := CodeCert.substituteSortable henv hscoped hΓ right
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed rightSupply
    exact ⟨⟨_, .union hl.certificate hr.certificate, append_available hl.resources hr.resources, by
      intro current
      simp only [SortableCert.nativeDepth]
      exact Nat.max_le.mpr ⟨hl.bounded current, hr.bounded current⟩⟩⟩
  | .pad source =>
    obtain ⟨hs⟩ := CodeCert.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .pad hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .familyPad source =>
    obtain ⟨hs⟩ := CodeCert.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .familyPad hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .unpad source =>
    obtain ⟨hs⟩ := CodeCert.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .unpad hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .down source =>
    obtain ⟨hs⟩ := CodeCert.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .down hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .map view source =>
    obtain ⟨hs⟩ := CodeCert.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .map view hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .select source member =>
    obtain ⟨hs⟩ := CodeCert.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .select hs.certificate member, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨hs⟩ := CodeCert.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .focusMinimal hs.certificate minimal bound, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

theorem PiRows.substituteSortable
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {required : Footprint}
    (bodies : PiRows env U registry Γ locals sourceRealization A B ambient rows required)
    (depth : ∀ current, bodies.nativeDepth current ≤ budget current)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : GradedSupply budget env U registry Γ newLocals realization replacement available required) :
    Nonempty (RowsResult budget env U registry Γ newLocals realization available
      (A.subst replacement) (B.subst replacement.lift) true ambient rows) := by
  match bodies with
  | .nil => exact ⟨⟨[], .nil, (fun _ _ h => nomatch h), by intro current; simp only [SortableRows.nativeDepth]; exact Nat.zero_le _⟩⟩
  | .cons guard body normal covered tail =>
    obtain ⟨⟨externalSupply⟩, ⟨tailSupply⟩⟩ := supply.split
    let bodyFootprint := certFootprint body
    let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have localCoverage := normal.atomized_localNeeds
    have localLive := (anchor_live henv hscoped hΓ guard.anchor).subset (fun _ hm => covered _ hm)
    obtain ⟨bodySupply⟩ := externalSupply.underBinder normal localLive
      (fun _ hm => List.mem_append_left _ hm) (guardAnchor guard)
    obtain ⟨hb⟩ := CodeCert.substituteSortable henv hscoped hΓ body
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement.lift
      (realization.cons _) (by rw [replacement_lift, realized]; rfl)
      (Locals.push newLocals) (Valuation.push head available) headClosed bodySupply
    obtain ⟨packed, outside, normal', covered', resources⟩ :=
      Footprint.pack_available hb.resources (fun need hm => (localCoverage need hm).1)
        (fun need hm atom ha => covered atom ((localCoverage need hm).2 atom ha))
    obtain ⟨ht⟩ := PiRows.substituteSortable henv hscoped hΓ tail
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed tailSupply
    exact ⟨⟨_, .cons (guard.sourceSubstitute replacement realization realized)
      hb.certificate normal' covered' ht.bodies, append_available resources ht.resources, by
        intro current
        simp only [SortableRows.nativeDepth]
        exact Nat.max_le.mpr ⟨hb.bounded current, ht.bounded current⟩⟩⟩
termination_by sizeOf bodies
decreasing_by all_goals (simp_wf <;> omega)
theorem SortableObs.substitute
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (observation : SortableObs env U registry Γ locals sourceRealization expression demand required)
    (depth : ∀ current, observation.nativeDepth current ≤ budget current)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : GradedSupply budget env U registry Γ newLocals realization replacement available required) :
    Nonempty (GradedResult budget env U registry Γ newLocals realization available
      (expression.subst replacement) demand) := by
  match observation with
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨GradedResult.exact
      (.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree)
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h))
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega)⟩
  | .legacy source =>
    exact Obs.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
  | .code relevant source =>
    obtain ⟨changed⟩ := SortableCert.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨GradedResult.exact (.code relevant changed.certificate)
      changed.resources changed.certificate.live
      (by intro current; simpa only [SortableObs.nativeDepth] using changed.bounded current)⟩
  | .app fn arg arguments admitted =>
    obtain ⟨⟨fnSupply⟩, ⟨argSupply⟩⟩ := supply.split
    obtain ⟨hf⟩ := SortableObs.substitute henv hscoped hΓ fn
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed fnSupply
    obtain ⟨ha⟩ := SortableObs.substitute henv hscoped hΓ arg
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed argSupply
    exact GradedResult.app henv hscoped hΓ closed hf ha arguments
      (by simpa only [subst_subst, realized] using admitted)
  | .lam domain guard body normal covered =>
    obtain ⟨⟨domainSupply⟩, ⟨externalSupply⟩⟩ := supply.split
    obtain ⟨hd⟩ := SortableCert.substitute henv hscoped hΓ domain
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed domainSupply
    let bodyFootprint := sortableObsFootprint body
    let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have localCoverage := normal.atomized_localNeeds
    have localLive := (anchor_live henv hscoped hΓ guard.anchor).subset (fun _ hm => covered _ hm)
    obtain ⟨bodySupply⟩ := externalSupply.underBinder normal localLive
      (fun _ hm => List.mem_append_left _ hm) (guardAnchor guard)
    obtain ⟨hb⟩ := SortableObs.substitute henv hscoped hΓ body
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement.lift
      (realization.cons _) (by rw [replacement_lift, realized]; rfl)
      (Locals.push newLocals) (Valuation.push head available) headClosed bodySupply
    exact GradedResult.lam henv hscoped hΓ closed hd.certificate hd.bounded hd.resources
      (guard.sourceSubstitute replacement realization realized) head
      (fun need hm => (localCoverage need hm).1)
      (fun need hm atom ha => covered atom ((localCoverage need hm).2 atom ha)) hb headClosed
  | .union left right =>
    obtain ⟨⟨leftSupply⟩, ⟨rightSupply⟩⟩ := supply.split
    obtain ⟨hl⟩ := SortableObs.substitute henv hscoped hΓ left
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed leftSupply
    obtain ⟨hr⟩ := SortableObs.substitute henv hscoped hΓ right
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed rightSupply
    exact ⟨hl.union henv hscoped hΓ hr⟩
  | .view source view =>
    obtain ⟨hs⟩ := SortableObs.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨hs.view henv hscoped hΓ view⟩
  | .action source act =>
    obtain ⟨hs⟩ := SortableObs.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨hs.action henv hscoped hΓ act⟩
  | .pad source =>
    obtain ⟨hs⟩ := SortableObs.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨hs.pad henv hscoped hΓ⟩
  | .unpad source =>
    obtain ⟨hs⟩ := SortableObs.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨hs.unpad⟩
  | .rowShift source =>
    obtain ⟨hs⟩ := SortableObs.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨(hs.pad henv hscoped hΓ).view henv hscoped hΓ (.commutePadFn _ _)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableCert.substitute
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (certificate : SortableCert env U registry Γ locals sourceRealization expression relevant demand required)
    (depth : ∀ current, certificate.nativeDepth current ≤ budget current)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : GradedSupply budget env U registry Γ newLocals realization replacement available required) :
    Nonempty (CertificateResult budget env U registry Γ newLocals realization available
      (expression.subst replacement) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    obtain ⟨changed⟩ := CodeCert.substituteSortable henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨changed.footprint, .observe (.code true changed.certificate) formed, changed.resources, by intro current; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using changed.bounded current⟩⟩
  | .pi domain guard bodies =>
    obtain ⟨⟨domainSupply⟩, ⟨bodySupply⟩⟩ := supply.split
    obtain ⟨domainResult⟩ := SortableCert.substitute henv hscoped hΓ domain
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed domainSupply
    obtain ⟨bodyResult⟩ := SortableRows.substitute henv hscoped hΓ bodies
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed bodySupply
    exact ⟨⟨_, .pi domainResult.certificate (guard.sourceSubstitute replacement realization realized)
      bodyResult.bodies, append_available domainResult.resources bodyResult.resources, by
        intro current
        simp only [SortableCert.nativeDepth]
        exact Nat.max_le.mpr ⟨domainResult.bounded current, bodyResult.bounded current⟩⟩⟩
  | .seed observation formed =>
    obtain ⟨result⟩ := Obs.substituteSortable henv hscoped hΓ observation
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    obtain ⟨footprint, cert, resources, bound⟩ := result.code henv closed formed
    exact ⟨⟨footprint, cert, resources, bound⟩⟩
  | .observe observation formed =>
    obtain ⟨result⟩ := SortableObs.substitute henv hscoped hΓ observation
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    obtain ⟨footprint, cert, resources, bound⟩ := result.code henv closed formed
    exact ⟨⟨footprint, cert, resources, bound⟩⟩
  | .union left right =>
    obtain ⟨⟨leftSupply⟩, ⟨rightSupply⟩⟩ := supply.split
    obtain ⟨hl⟩ := SortableCert.substitute henv hscoped hΓ left
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed leftSupply
    obtain ⟨hr⟩ := SortableCert.substitute henv hscoped hΓ right
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed rightSupply
    exact ⟨⟨_, .union hl.certificate hr.certificate, append_available hl.resources hr.resources, by
      intro current
      simp only [SortableCert.nativeDepth]
      exact Nat.max_le.mpr ⟨hl.bounded current, hr.bounded current⟩⟩⟩
  | .pad source =>
    obtain ⟨hs⟩ := SortableCert.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .pad hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .sortPad source =>
    obtain ⟨hs⟩ := SortableCert.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .sortPad hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .familyPad source =>
    obtain ⟨hs⟩ := SortableCert.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .familyPad hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .unpad source =>
    obtain ⟨hs⟩ := SortableCert.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .unpad hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .support act source =>
    obtain ⟨hs⟩ := SortableCert.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .support act hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .down source =>
    obtain ⟨hs⟩ := SortableCert.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .down hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .map view source =>
    obtain ⟨hs⟩ := SortableCert.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .map view hs.certificate, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .select source member =>
    obtain ⟨hs⟩ := SortableCert.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .select hs.certificate member, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨hs⟩ := SortableCert.substitute henv hscoped hΓ source
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .focusMinimal hs.certificate minimal bound, hs.resources, by intro current; simpa only [SortableCert.nativeDepth] using hs.bounded current⟩⟩
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableRows.substitute
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {required : Footprint}
    (bodies : SortableRows env U registry Γ locals sourceRealization A B relevant ambient rows required)
    (depth : ∀ current, bodies.nativeDepth current ≤ budget current)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : GradedSupply budget env U registry Γ newLocals realization replacement available required) :
    Nonempty (RowsResult budget env U registry Γ newLocals realization available
      (A.subst replacement) (B.subst replacement.lift) relevant ambient rows) := by
  match bodies with
  | .nil => exact ⟨⟨[], .nil, (fun _ _ h => nomatch h), by intro current; simp only [SortableRows.nativeDepth]; exact Nat.zero_le _⟩⟩
  | .cons guard body normal covered tail =>
    obtain ⟨⟨externalSupply⟩, ⟨tailSupply⟩⟩ := supply.split
    let bodyFootprint := sortableFootprint body
    let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have localCoverage := normal.atomized_localNeeds
    have localLive := (anchor_live henv hscoped hΓ guard.anchor).subset (fun _ hm => covered _ hm)
    obtain ⟨bodySupply⟩ := externalSupply.underBinder normal localLive
      (fun _ hm => List.mem_append_left _ hm) (guardAnchor guard)
    obtain ⟨hb⟩ := SortableCert.substitute henv hscoped hΓ body
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement.lift
      (realization.cons _) (by rw [replacement_lift, realized]; rfl)
      (Locals.push newLocals) (Valuation.push head available) headClosed bodySupply
    obtain ⟨packed, outside, normal', covered', resources⟩ :=
      Footprint.pack_available hb.resources (fun need hm => (localCoverage need hm).1)
        (fun need hm atom ha => covered atom ((localCoverage need hm).2 atom ha))
    obtain ⟨ht⟩ := SortableRows.substitute henv hscoped hΓ tail
      (by intro current; have h := depth current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth, SortableObs.nativeDepth, SortableCert.nativeDepth, SortableRows.nativeDepth] at h ⊢; omega) replacement realization realized
      newLocals available closed tailSupply
    exact ⟨⟨_, .cons (guard.sourceSubstitute replacement realization realized)
      hb.certificate normal' covered' ht.bodies, append_available resources ht.resources, by
        intro current
        simp only [SortableRows.nativeDepth]
        exact Nat.max_le.mpr ⟨hb.bounded current, ht.bounded current⟩⟩⟩
termination_by sizeOf bodies
decreasing_by all_goals (simp_wf <;> omega)
end

end Lean4Lean.AnchoredSource.Adapted.AllDepth
