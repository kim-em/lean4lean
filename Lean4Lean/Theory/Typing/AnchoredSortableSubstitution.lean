import Lean4Lean.Theory.Typing.AnchoredSortableGradedAction
import Lean4Lean.Theory.Typing.AnchoredSortableLive
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiRebind

/-! Hereditary finite substitution retains native formation queries at both
sort flags, including inside computational arguments and binder domains.
Legacy syntax is traversed into the larger grammar, so no conversion back to
legacy certificates or semantic reconstruction hypothesis is needed. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private append_available replacement_lift anchor_live guardAnchor obsFootprint certFootprint from
  Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution
set_option backward.isDefEq.respectTransparency false

structure SortableCertificateResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (relevant : Bool) (profile : Profile n) where
  footprint : Footprint
  certificate : SortableCert env U registry Γ locals σ expression relevant profile footprint
  resources : footprint.Available available

structure SortableRowsResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) (relevant : Bool) (ambient : Profile n) (rows : List (Key n × Profile n)) where
  footprint : Footprint
  bodies : SortableRows env U registry Γ locals σ A B relevant ambient rows footprint
  resources : footprint.Available available

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
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : SortableGradedSupply env U registry Γ newLocals realization replacement available required) :
    Nonempty (SortableGradedResult env U registry Γ newLocals realization available
      (expression.subst replacement) demand) := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    exact ⟨SortableGradedResult.exact
      (.legacy (.delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body))
      (fun _ _ h => nomatch h) (body.live henv hscoped hΓ (fun _ _ h => nomatch h))⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨SortableGradedResult.exact
      (.legacy (.native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree))
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h))⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨SortableGradedResult.exact
      (.legacy (.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree))
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h))⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨SortableGradedResult.exact
      (.legacy (.constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree))
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h))⟩
  | .var _ _ _ _ =>
    cases supply with
    | cons value tail => exact ⟨value⟩
  | .empty =>
    exact ⟨SortableGradedResult.exact (.legacy .empty) (fun _ _ h => nomatch h) .empty⟩
  | .sort relevant =>
    exact ⟨SortableGradedResult.exact (.legacy (.sort relevant)) (fun _ _ h => nomatch h)
      (by cases n <;> simp [Profile.Live, Profile.sort, Atom.Live, Profile.atoms])⟩
  | .app fn arg arguments admitted =>
    obtain ⟨⟨fnSupply⟩, ⟨argSupply⟩⟩ := supply.split
    obtain ⟨hf⟩ := fn.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed fnSupply
    obtain ⟨ha⟩ := arg.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed argSupply
    exact SortableGradedResult.app henv hscoped hΓ closed hf ha arguments.toGeneral
      (by simpa only [subst_subst, realized] using admitted)
  | .lam domain guard body normal covered =>
    obtain ⟨⟨domainSupply⟩, ⟨externalSupply⟩⟩ := supply.split
    obtain ⟨hd⟩ := domain.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed domainSupply
    let bodyFootprint := obsFootprint body
    let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have localCoverage := normal.atomized_localNeeds
    have localLive := (anchor_live henv hscoped hΓ guard.anchor).subset (fun _ hm => covered _ hm)
    obtain ⟨bodySupply⟩ := externalSupply.underBinder normal localLive
      (fun _ hm => List.mem_append_left _ hm) (guardAnchor guard)
    obtain ⟨hb⟩ := body.substituteSortable henv hscoped hΓ replacement.lift
      (realization.cons _) (by rw [replacement_lift, realized]; rfl)
      (Locals.push newLocals) (Valuation.push head available) headClosed bodySupply
    exact SortableGradedResult.lam henv hscoped hΓ closed hd.certificate hd.resources
      (guard.sourceSubstitute replacement realization realized) head
      (fun need hm => (localCoverage need hm).1)
      (fun need hm atom ha => covered atom ((localCoverage need hm).2 atom ha)) hb headClosed
  | .pi domain guard bodies =>
    obtain ⟨⟨domainSupply⟩, ⟨rowSupply⟩⟩ := supply.split
    obtain ⟨hd⟩ := domain.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed domainSupply
    obtain ⟨hb⟩ := bodies.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed rowSupply
    exact ⟨SortableGradedResult.exact
      (.code true (.pi hd.certificate (guard.sourceSubstitute replacement realization realized) hb.bodies))
      (append_available hd.resources hb.resources) (by
        intro atom member
        cases List.mem_singleton.mp member
        trivial)⟩
  | .union left right =>
    obtain ⟨⟨leftSupply⟩, ⟨rightSupply⟩⟩ := supply.split
    obtain ⟨hl⟩ := left.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed leftSupply
    obtain ⟨hr⟩ := right.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed rightSupply
    exact ⟨hl.union henv hscoped hΓ hr⟩
  | .view source view =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨hs.view henv hscoped hΓ view⟩
  | .pad source =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨hs.pad henv hscoped hΓ⟩
  | .unpad source =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨hs.unpad⟩
  | .rowShift source =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
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
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : SortableGradedSupply env U registry Γ newLocals realization replacement available required) :
    Nonempty (SortableCertificateResult env U registry Γ newLocals realization available
      (expression.subst replacement) true demand) := by
  match certificate with
  | .seed observation formed =>
    obtain ⟨result⟩ := observation.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    obtain ⟨footprint, ⟨cert⟩, resources⟩ := result.code henv closed formed
    exact ⟨⟨footprint, cert, resources⟩⟩
  | .union left right =>
    obtain ⟨⟨leftSupply⟩, ⟨rightSupply⟩⟩ := supply.split
    obtain ⟨hl⟩ := left.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed leftSupply
    obtain ⟨hr⟩ := right.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed rightSupply
    exact ⟨⟨_, .union hl.certificate hr.certificate, append_available hl.resources hr.resources⟩⟩
  | .pad source =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .pad hs.certificate, hs.resources⟩⟩
  | .familyPad source =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .familyPad hs.certificate, hs.resources⟩⟩
  | .unpad source =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .unpad hs.certificate, hs.resources⟩⟩
  | .down source =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .down hs.certificate, hs.resources⟩⟩
  | .map view source =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .map view hs.certificate, hs.resources⟩⟩
  | .select source member =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .select hs.certificate member, hs.resources⟩⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨hs⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .focusMinimal hs.certificate minimal bound, hs.resources⟩⟩
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

theorem PiRows.substituteSortable
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {required : Footprint}
    (bodies : PiRows env U registry Γ locals sourceRealization A B ambient rows required)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : SortableGradedSupply env U registry Γ newLocals realization replacement available required) :
    Nonempty (SortableRowsResult env U registry Γ newLocals realization available
      (A.subst replacement) (B.subst replacement.lift) true ambient rows) := by
  match bodies with
  | .nil => exact ⟨⟨[], .nil, fun _ _ h => nomatch h⟩⟩
  | .cons guard body normal covered tail =>
    obtain ⟨⟨externalSupply⟩, ⟨tailSupply⟩⟩ := supply.split
    let bodyFootprint := certFootprint body
    let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have localCoverage := normal.atomized_localNeeds
    have localLive := (anchor_live henv hscoped hΓ guard.anchor).subset (fun _ hm => covered _ hm)
    obtain ⟨bodySupply⟩ := externalSupply.underBinder normal localLive
      (fun _ hm => List.mem_append_left _ hm) (guardAnchor guard)
    obtain ⟨hb⟩ := body.substituteSortable henv hscoped hΓ replacement.lift
      (realization.cons _) (by rw [replacement_lift, realized]; rfl)
      (Locals.push newLocals) (Valuation.push head available) headClosed bodySupply
    obtain ⟨packed, outside, normal', covered', resources⟩ :=
      Footprint.pack_available hb.resources (fun need hm => (localCoverage need hm).1)
        (fun need hm atom ha => covered atom ((localCoverage need hm).2 atom ha))
    obtain ⟨ht⟩ := tail.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed tailSupply
    exact ⟨⟨_, .cons (guard.sourceSubstitute replacement realization realized)
      hb.certificate normal' covered' ht.bodies, append_available resources ht.resources⟩⟩
termination_by sizeOf bodies
decreasing_by all_goals (simp_wf <;> omega)
theorem SortableObs.substitute
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (observation : SortableObs env U registry Γ locals sourceRealization expression demand required)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : SortableGradedSupply env U registry Γ newLocals realization replacement available required) :
    Nonempty (SortableGradedResult env U registry Γ newLocals realization available
      (expression.subst replacement) demand) := by
  match observation with
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨SortableGradedResult.exact
      (.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree)
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h))⟩
  | .legacy source =>
    exact source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
  | .code relevant source =>
    obtain ⟨changed⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨SortableGradedResult.exact (.code relevant changed.certificate)
      changed.resources changed.certificate.live⟩
  | .app fn arg arguments admitted =>
    obtain ⟨⟨fnSupply⟩, ⟨argSupply⟩⟩ := supply.split
    obtain ⟨hf⟩ := fn.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed fnSupply
    obtain ⟨ha⟩ := arg.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed argSupply
    exact SortableGradedResult.app henv hscoped hΓ closed hf ha arguments
      (by simpa only [subst_subst, realized] using admitted)
  | .lam domain guard body normal covered =>
    obtain ⟨⟨domainSupply⟩, ⟨externalSupply⟩⟩ := supply.split
    obtain ⟨hd⟩ := domain.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed domainSupply
    let bodyFootprint := sortableObsFootprint body
    let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have localCoverage := normal.atomized_localNeeds
    have localLive := (anchor_live henv hscoped hΓ guard.anchor).subset (fun _ hm => covered _ hm)
    obtain ⟨bodySupply⟩ := externalSupply.underBinder normal localLive
      (fun _ hm => List.mem_append_left _ hm) (guardAnchor guard)
    obtain ⟨hb⟩ := body.substitute henv hscoped hΓ replacement.lift
      (realization.cons _) (by rw [replacement_lift, realized]; rfl)
      (Locals.push newLocals) (Valuation.push head available) headClosed bodySupply
    exact SortableGradedResult.lam henv hscoped hΓ closed hd.certificate hd.resources
      (guard.sourceSubstitute replacement realization realized) head
      (fun need hm => (localCoverage need hm).1)
      (fun need hm atom ha => covered atom ((localCoverage need hm).2 atom ha)) hb headClosed
  | .union left right =>
    obtain ⟨⟨leftSupply⟩, ⟨rightSupply⟩⟩ := supply.split
    obtain ⟨hl⟩ := left.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed leftSupply
    obtain ⟨hr⟩ := right.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed rightSupply
    exact ⟨hl.union henv hscoped hΓ hr⟩
  | .view source view =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨hs.view henv hscoped hΓ view⟩
  | .action source act =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact hs.action henv hscoped hΓ closed act
  | .pad source =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨hs.pad henv hscoped hΓ⟩
  | .unpad source =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨hs.unpad⟩
  | .rowShift source =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
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
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : SortableGradedSupply env U registry Γ newLocals realization replacement available required) :
    Nonempty (SortableCertificateResult env U registry Γ newLocals realization available
      (expression.subst replacement) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    obtain ⟨changed⟩ := source.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨changed.footprint, .observe (.code true changed.certificate) formed, changed.resources⟩⟩
  | .pi domain guard bodies =>
    obtain ⟨⟨domainSupply⟩, ⟨bodySupply⟩⟩ := supply.split
    obtain ⟨domainResult⟩ := domain.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed domainSupply
    obtain ⟨bodyResult⟩ := bodies.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed bodySupply
    exact ⟨⟨_, .pi domainResult.certificate (guard.sourceSubstitute replacement realization realized)
      bodyResult.bodies, append_available domainResult.resources bodyResult.resources⟩⟩
  | .seed observation formed =>
    obtain ⟨result⟩ := observation.substituteSortable henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    obtain ⟨footprint, ⟨cert⟩, resources⟩ := result.code henv closed formed
    exact ⟨⟨footprint, cert, resources⟩⟩
  | .observe observation formed =>
    obtain ⟨result⟩ := observation.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    obtain ⟨footprint, ⟨cert⟩, resources⟩ := result.code henv closed formed
    exact ⟨⟨footprint, cert, resources⟩⟩
  | .union left right =>
    obtain ⟨⟨leftSupply⟩, ⟨rightSupply⟩⟩ := supply.split
    obtain ⟨hl⟩ := left.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed leftSupply
    obtain ⟨hr⟩ := right.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed rightSupply
    exact ⟨⟨_, .union hl.certificate hr.certificate, append_available hl.resources hr.resources⟩⟩
  | .pad source =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .pad hs.certificate, hs.resources⟩⟩
  | .sortPad source =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .sortPad hs.certificate, hs.resources⟩⟩
  | .familyPad source =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .familyPad hs.certificate, hs.resources⟩⟩
  | .unpad source =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .unpad hs.certificate, hs.resources⟩⟩
  | .support act source =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .support act hs.certificate, hs.resources⟩⟩
  | .down source =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .down hs.certificate, hs.resources⟩⟩
  | .map view source =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .map view hs.certificate, hs.resources⟩⟩
  | .select source member =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .select hs.certificate member, hs.resources⟩⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨hs⟩ := source.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .focusMinimal hs.certificate minimal bound, hs.resources⟩⟩
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableRows.substitute
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {required : Footprint}
    (bodies : SortableRows env U registry Γ locals sourceRealization A B relevant ambient rows required)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : SortableGradedSupply env U registry Γ newLocals realization replacement available required) :
    Nonempty (SortableRowsResult env U registry Γ newLocals realization available
      (A.subst replacement) (B.subst replacement.lift) relevant ambient rows) := by
  match bodies with
  | .nil => exact ⟨⟨[], .nil, fun _ _ h => nomatch h⟩⟩
  | .cons guard body normal covered tail =>
    obtain ⟨⟨externalSupply⟩, ⟨tailSupply⟩⟩ := supply.split
    let bodyFootprint := sortableFootprint body
    let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have localCoverage := normal.atomized_localNeeds
    have localLive := (anchor_live henv hscoped hΓ guard.anchor).subset (fun _ hm => covered _ hm)
    obtain ⟨bodySupply⟩ := externalSupply.underBinder normal localLive
      (fun _ hm => List.mem_append_left _ hm) (guardAnchor guard)
    obtain ⟨hb⟩ := body.substitute henv hscoped hΓ replacement.lift
      (realization.cons _) (by rw [replacement_lift, realized]; rfl)
      (Locals.push newLocals) (Valuation.push head available) headClosed bodySupply
    obtain ⟨packed, outside, normal', covered', resources⟩ :=
      Footprint.pack_available hb.resources (fun need hm => (localCoverage need hm).1)
        (fun need hm atom ha => covered atom ((localCoverage need hm).2 atom ha))
    obtain ⟨ht⟩ := tail.substitute henv hscoped hΓ replacement realization realized
      newLocals available closed tailSupply
    exact ⟨⟨_, .cons (guard.sourceSubstitute replacement realization realized)
      hb.certificate normal' covered' ht.bodies, append_available resources ht.resources⟩⟩
termination_by sizeOf bodies
decreasing_by all_goals (simp_wf <;> omega)
end

end Lean4Lean.AnchoredSource.Adapted
