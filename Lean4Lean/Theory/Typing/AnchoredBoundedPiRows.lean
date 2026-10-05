import Lean4Lean.Theory.Typing.AnchoredBoundedRowReplay
import Lean4Lean.Theory.Typing.AnchoredBoundedBinder
import Lean4Lean.Theory.Typing.AnchoredBoundedNativeFuture
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiExtraction

/-! The changed-anchor and changed-input Pi rows needed by bounded eta.
Source code provenance is transferred only by original same-fuel children or
finite bounded substitution; every resulting domain/body certificate is bounded. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure PiRowCertificate (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) (key : Key n) (result : Profile n)
    extends Adapted.PiRowCertificate env U registry target locals σ available A B key result where
  domainBound : domain.nativeDepth current ≤ fuel
  bodyBound : body.nativeDepth current ≤ fuel

variable {current : Name → Bool} {fuel : Nat}

private theorem variableProfileView_bound
    (view : ProfileView env U registry Γ input output) (locals : List Nat) (σ : Subst) :
    (variableProfileView view locals σ).nativeDepth current ≤ fuel := by
  match input, output, view with
  | _, _, .nil => simp only [variableProfileView, Obs.nativeDepth]; exact Nat.zero_le _
  | _, _, .cons head tail =>
    simpa only [variableProfileView, Obs.nativeDepth, Nat.zero_max] using
      variableProfileView_bound tail locals σ
termination_by sizeOf view

private theorem mapProfileBounded
    (certificate : CodeCert env U registry target locals σ A support footprint)
    (bound : certificate.nativeDepth current ≤ fuel)
    (resources : footprint.Available available)
    (change : ProfileView env U registry target input output) :
    ∃ foot, ∃ result : CodeCert env U registry target locals σ A (change.mapType support) foot,
      foot.Available available ∧ result.nativeDepth current ≤ fuel := by
  match input, output, change with
  | _, _, .nil => exact ⟨footprint, certificate, resources, bound⟩
  | _, _, .cons head tail =>
    obtain ⟨foot, result, available, bounded⟩ := mapProfileBounded certificate bound resources tail
    exact ⟨_, .union (.map head certificate) result,
      (fun i need hm => (List.mem_append.mp hm).elim (resources i need) (available i need)),
      by simpa only [CodeCert.nativeDepth] using Nat.max_le.mpr ⟨bound, bounded⟩⟩
termination_by sizeOf change

theorem PiRowCertificate.input_view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (row : PiRowCertificate current fuel env U registry target locals σ available A B key result)
    (forward : ProfileView env U registry target input key.input)
    (backward : ProfileView env U registry target key.input input)
    (externalLive : Footprint.Live env U registry target row.outside) :
    Nonempty (PiRowCertificate current fuel env U registry target locals σ available A B (inputKey key input) result) := by
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := row.anchor
  have live := Related.live henv hscoped hTarget anchorRelated
  obtain ⟨bodyFootprint, outside, packed, ⟨body, bodyBound⟩, pack, covered, outsideAvailable⟩ :=
    row.body.rebind_localBounded henv hscoped hTarget row.bodyBound
      (variableProfileView forward (Locals.push locals) (σ.cons key.anchor))
      (variableProfileView_bound forward _ _)
      (variableProfileView_available input available) live row.pack row.covered
      row.outsideAvailable externalLive closed
  obtain ⟨domainFootprint, domain, domainAvailable, domainBound⟩ :=
    mapProfileBounded row.domain row.domainBound row.domainAvailable backward
  exact ⟨{
    domainSupport := backward.mapType row.domainSupport
    domainFootprint := domainFootprint
    domain := domain
    domainAvailable := domainAvailable
    inputTyped := backward.mapType_typed row.inputTyped
    alignment := row.alignment.mapInput henv hscoped backward
    anchor := (AdapterSeed.view .same backward).admission henv hscoped hTarget row.anchor
    bodyFootprint := bodyFootprint
    body := body
    packed := packed
    outside := outside
    pack := pack
    covered := covered
    outsideAvailable := outsideAvailable
    domainBound := domainBound
    bodyBound := bodyBound }⟩

theorem PiRowCertificate.reanchor
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {σ : Subst} {available : Valuation} {anchor : VExpr}
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits current fuel env U registry source target locals σ σ available)
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (row : PiRowCertificate current fuel env U registry target locals σ available A B (key : Key n) result)
    (admitted : Admitted env U registry target key anchor anchor) :
    Nonempty (PiRowCertificate current fuel env U registry target locals σ available A B
      (reanchorKey key anchor) result) := by
  have domainChild : Transfer current fuel env U registry target locals σ σ available A A (.sort domainLevel) := (originalDomain target locals σ σ available closed hTarget substitutions fits).1
  obtain ⟨domainCode⟩ := domainChild.codeCertificate henv hscoped hTarget closed row.domain row.domainBound row.domainAvailable
  have atA : Admitted env U registry target ⟨A.subst σ, key.anchor, key.input⟩ anchor anchor :=
    row.alignment.admission henv admitted
  obtain ⟨raw, _, _, _, _, _, first, _⟩ := atA
  have arguments := Related.retag henv row.inputTyped domainCode.related first
  let needs := row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n :=
    fun need hm => (row.pack.atomized_localNeeds need hm).1
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need hm atom ha => row.covered atom ((row.pack.atomized_localNeeds need hm).2 atom ha)
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons anchor) (A :: source) :=
    .cons substitutions formedA raw
  have bodyFits := fits.pushCertificates henv hTarget row.domain row.domain
    row.domainBound row.domainBound row.domainAvailable row.domainAvailable row.inputTyped row.inputTyped arguments
    (arguments.symm henv) needs bounded covered
  have bodyChild : Transfer current fuel env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons anchor) (Valuation.push needs available) B B (.sort bodyLevel) := (originalBody target (Locals.push locals) (σ.cons key.anchor)
    (σ.cons anchor) (Valuation.push needs available) (Valuation.push_atomized_closed closed _)
    hTarget paired bodyFits).1
  obtain ⟨changed⟩ := bodyChild.codeCertificate henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) row.body row.bodyBound
    (row.pack.available_atomized_localNeeds row.outsideAvailable)
  obtain ⟨packed, outside, pack, coverage, resources⟩ :=
    Footprint.pack_available changed.available bounded covered
  exact ⟨{
    domainSupport := row.domainSupport
    domainFootprint := row.domainFootprint
    domain := row.domain
    domainAvailable := row.domainAvailable
    inputTyped := row.inputTyped
    alignment := row.alignment
    anchor := admitted.reset_anchor
    bodyFootprint := changed.footprint
    body := changed.certificate
    packed := packed
    outside := outside
    pack := pack
    covered := coverage
    outsideAvailable := resources
    domainBound := row.domainBound
    bodyBound := changed.certificateBound }⟩


noncomputable def PiRowCertificate.map_output
    (row : PiRowCertificate current fuel env U registry target locals σ available A B key result)
    (change : AtomView env U registry target old new) :
    PiRowCertificate current fuel env U registry target locals σ available A B key (change.mapType result) :=
  { row with body := .map change row.body
             bodyBound := by simpa only [CodeCert.nativeDepth] using row.bodyBound }

noncomputable def PiRowCertificate.domainRekey
    (henv : env.Ordered)
    (row : PiRowCertificate current fuel env U registry target locals σ available A B key result)
    (path : TypeConversion env U target key.domain newDomain)
    (typed : key.input.HasType support) (formed : support.HasType (.sort true))
    (related : TypeRelated env U registry target key.domain newDomain support) :
    PiRowCertificate current fuel env U registry target locals σ available A B (domainKey key newDomain) result :=
  { row with alignment := .step path.symm typed formed (related.symm henv typed.wf_type) row.alignment
             anchor := row.anchor.rekey henv path typed formed related }


noncomputable def PiRowCertificate.pad
    (henv : env.Ordered)
    (row : PiRowCertificate current fuel env U registry target locals σ available A B (key : Key n) result) :
    PiRowCertificate current fuel env U registry target locals σ available A B key.pad result.pad where
  domainSupport := row.domainSupport.pad
  domainFootprint := row.domainFootprint
  domain := .pad row.domain
  domainAvailable := row.domainAvailable
  inputTyped := row.inputTyped.pad
  alignment := row.alignment.pad henv
  anchor := Admitted.pad henv row.anchor
  bodyFootprint := row.bodyFootprint
  body := .pad row.body
  packed := row.packed.pad
  outside := row.outside
  pack := by
    simpa only [raiseProfile_step (Nat.le_refl n), raiseProfile_self] using row.pack.raise (Nat.le_succ n)
  covered := by
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨old, row.covered old ho, rfl⟩
  outsideAvailable := row.outsideAvailable
  domainBound := by simpa only [CodeCert.nativeDepth] using row.domainBound
  bodyBound := by simpa only [CodeCert.nativeDepth] using row.bodyBound

theorem PiRowCertificate.unpad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (row : PiRowCertificate current fuel env U registry target locals σ available A B (key : Key n).pad result)
    (externalLive : Footprint.Live env U registry target row.outside) :
    Nonempty (PiRowCertificate current fuel env U registry target locals σ available A B key result.down) := by
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := row.anchor
  have live := Related.live henv hscoped hTarget anchorRelated
  have resources : Footprint.Available [(0, ⟨n, key.input⟩)]
      (Valuation.push (rowInputNeeds key.input) available) := by
    intro i need hm
    cases List.mem_singleton.mp hm
    exact List.mem_append_left _ List.mem_cons_self
  obtain ⟨bodyFootprint, outside, packed, ⟨body, bodyBound⟩, pack, covered, outsideAvailable⟩ :=
    (CodeCert.down row.body).rebind_localBounded henv hscoped hTarget
      (by simpa only [CodeCert.nativeDepth] using row.bodyBound)
      (Obs.pad (.var (Locals.push locals) (σ.cons key.pad.anchor) 0 key.input))
      (by simp only [Obs.nativeDepth]; exact Nat.zero_le _) resources live row.pack row.covered row.outsideAvailable externalLive closed
  exact ⟨{
    domainSupport := row.domainSupport.down
    domainFootprint := row.domainFootprint
    domain := .down row.domain
    domainAvailable := row.domainAvailable
    inputTyped := row.inputTyped.pad_inv
    alignment := row.alignment.unpad henv
    anchor := Admitted.unpad henv hTarget row.anchor
    bodyFootprint := bodyFootprint
    body := body
    packed := packed
    outside := outside
    pack := pack
    covered := covered
    outsideAvailable := outsideAvailable
    domainBound := by simpa only [CodeCert.nativeDepth] using row.domainBound
    bodyBound := bodyBound }⟩


end Lean4Lean.AnchoredSource.Adapted.Staged
