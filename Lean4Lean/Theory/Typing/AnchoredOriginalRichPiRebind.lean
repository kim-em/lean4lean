import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax
import Lean4Lean.Theory.Typing.AnchoredSortablePiRebind
import Lean4Lean.Theory.Typing.AnchoredSortableRenaming

/-! Exact identity-source replay of finite variable resources. Unlike general
source substitution, this operation preserves every original endpoint and
projection annotation. It supplies Pi input adaptation without erasing native
projected queries or asking for a semantic reconstruction. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalRecordSource
open private BinderPack.external_mem available_shift from Lean4Lean.Theory.Typing.AnchoredSourceBinder
set_option backward.isDefEq.respectTransparency false

/-- Concrete observations of the same source variables, at exactly the old
profiles, with finite resources in the replacement valuation. -/
def VariableResourceReplay (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst)
    (available : Valuation) (required : Footprint) : Prop :=
  ∀ index need, (index, need) ∈ required → ∃ footprint,
    Nonempty (Obs env U registry target locals σ (.bvar index) need.profile footprint) ∧
    footprint.Available available

private theorem replay_left
    (supply : VariableResourceReplay env U registry target locals σ available (first ++ second)) :
    VariableResourceReplay env U registry target locals σ available first :=
  fun i need member => supply i need (List.mem_append_left _ member)

private theorem replay_right
    (supply : VariableResourceReplay env U registry target locals σ available (first ++ second)) :
    VariableResourceReplay env U registry target locals σ available second :=
  fun i need member => supply i need (List.mem_append_right _ member)

private theorem replay_underBinder
    (supply : VariableResourceReplay env U registry target locals σ available outside)
    (pack : BinderPack n packed required outside) (anchor : VExpr) :
    VariableResourceReplay env U registry target (Locals.push locals) (σ.cons anchor)
      (Valuation.push (required.localNeeds ++ required.localNeeds.flatMap Need.singletons) available)
      required := by
  intro index need member
  cases index with
  | zero =>
    refine ⟨[(0, need)], ⟨.var _ _ 0 need.profile⟩, ?_⟩
    intro i wanted belongs
    cases List.mem_singleton.mp belongs
    exact List.mem_append_left _ (Footprint.mem_localNeeds.mpr member)
  | succ index =>
    obtain ⟨footprint, ⟨observation⟩, resources⟩ := supply index need (BinderPack.external_mem pack member)
    have shifted := observation.renameSource (.skip .refl) (σ.cons anchor) rfl (Locals.push locals)
    exact ⟨_, ⟨shifted⟩, available_shift resources⟩

private theorem replay_pack {input : Profile n}
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (resources : changed.Available
      (Valuation.push (required.localNeeds ++ required.localNeeds.flatMap Need.singletons) available)) :
    ∃ packed' outside', BinderPack n packed' changed outside' ∧
      (∀ atom ∈ packed'.atoms, atom ∈ input.atoms) ∧ outside'.Available available :=
  Footprint.pack_available resources
    (fun need member => (pack.atomized_localNeeds need member).1)
    (fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present))

private theorem replay_append {first second : Footprint}
    (left : first.Available available) (right : second.Available available) :
    (first ++ second).Available available := by
  intro i need member
  exact (List.mem_append.mp member).elim (left i need) (right i need)

mutual
theorem Obs.replayVariables
    (observation : Obs env U registry target locals σ expression profile required)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ expression profile footprint) ∧
      footprint.Available available := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body => exact ⟨[], ⟨.delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body⟩, fun _ _ member => nomatch member⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree => exact ⟨[], ⟨.native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, fun _ _ member => nomatch member⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree => exact ⟨[], ⟨.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, fun _ _ member => nomatch member⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree => exact ⟨[], ⟨.constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, fun _ _ member => nomatch member⟩
  | .var _ _ index profile => exact supply index _ (List.mem_singleton_self _)
  | .empty => exact ⟨[], ⟨.empty⟩, fun _ _ member => nomatch member⟩
  | .sort relevant => exact ⟨[], ⟨.sort relevant⟩, fun _ _ member => nomatch member⟩
  | .app fn arg arguments admitted =>
    obtain ⟨ff, ⟨fn'⟩, fr⟩ := fn.replayVariables (replay_left supply)
    obtain ⟨af, ⟨arg'⟩, ar⟩ := arg.replayVariables (replay_right supply)
    exact ⟨ff ++ af, ⟨.app fn' arg' arguments admitted⟩, replay_append fr ar⟩
  | .lam domain guard body pack covered =>
    obtain ⟨df, ⟨domain'⟩, dr⟩ := domain.replayVariables (replay_left supply)
    obtain ⟨bf, ⟨body'⟩, br⟩ := body.replayVariables (replay_underBinder (replay_right supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    exact ⟨df ++ outside, ⟨.lam domain' guard body' pack' covered'⟩, replay_append dr external⟩
  | .pi domain guard rows =>
    obtain ⟨df, ⟨domain'⟩, dr⟩ := domain.replayVariables (replay_left supply)
    obtain ⟨rf, ⟨rows'⟩, rr⟩ := rows.replayVariables (replay_right supply)
    exact ⟨df ++ rf, ⟨.pi domain' guard rows'⟩, replay_append dr rr⟩
  | .union left right =>
    obtain ⟨lf, ⟨left'⟩, lr⟩ := left.replayVariables (replay_left supply)
    obtain ⟨rf, ⟨right'⟩, rr⟩ := right.replayVariables (replay_right supply)
    exact ⟨lf ++ rf, ⟨.union left' right'⟩, replay_append lr rr⟩
  | .pad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.pad changed⟩, resources⟩
  | .unpad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.unpad changed⟩, resources⟩
  | .view source view =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.view changed view⟩, resources⟩
  | .rowShift source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.rowShift changed⟩, resources⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem CodeCert.replayVariables
    (certificate : CodeCert env U registry target locals σ expression profile required)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, Nonempty (CodeCert env U registry target locals σ expression profile footprint) ∧
      footprint.Available available := by
  match certificate with
  | .seed source formed =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.seed changed formed⟩, resources⟩
  | .union left right =>
    obtain ⟨lf, ⟨left'⟩, lr⟩ := left.replayVariables (replay_left supply)
    obtain ⟨rf, ⟨right'⟩, rr⟩ := right.replayVariables (replay_right supply)
    exact ⟨lf ++ rf, ⟨.union left' right'⟩, replay_append lr rr⟩
  | .pad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.pad changed⟩, resources⟩
  | .unpad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.unpad changed⟩, resources⟩
  | .familyPad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.familyPad changed⟩, resources⟩
  | .down source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.down changed⟩, resources⟩
  | .map view source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.map view changed⟩, resources⟩
  | .select source member =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.select changed member⟩, resources⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.focusMinimal changed minimal bound⟩, resources⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem PiRows.replayVariables
    (rows : PiRows env U registry target locals σ A B ambient values required)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, Nonempty (PiRows env U registry target locals σ A B ambient values footprint) ∧
      footprint.Available available := by
  match rows with
  | .nil => exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | .cons guard body pack covered tail =>
    obtain ⟨bf, ⟨body'⟩, br⟩ := body.replayVariables (replay_underBinder (replay_left supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    obtain ⟨tf, ⟨tail'⟩, tr⟩ := tail.replayVariables (replay_right supply)
    exact ⟨outside ++ tf, ⟨.cons guard body' pack' covered' tail'⟩, replay_append external tr⟩
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem SortableObs.replayVariables
    (observation : SortableObs env U registry target locals σ expression profile required)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, Nonempty (SortableObs env U registry target locals σ expression profile footprint) ∧
      footprint.Available available := by
  match observation with
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨[], ⟨.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, fun _ _ member => nomatch member⟩
  | .legacy source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.legacy changed⟩, resources⟩
  | .code relevant source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.code relevant changed⟩, resources⟩
  | .app fn arg arguments admitted =>
    obtain ⟨ff, ⟨fn'⟩, fr⟩ := fn.replayVariables (replay_left supply)
    obtain ⟨af, ⟨arg'⟩, ar⟩ := arg.replayVariables (replay_right supply)
    exact ⟨ff ++ af, ⟨.app fn' arg' arguments admitted⟩, replay_append fr ar⟩
  | .lam domain guard body pack covered =>
    obtain ⟨df, ⟨domain'⟩, dr⟩ := domain.replayVariables (replay_left supply)
    obtain ⟨bf, ⟨body'⟩, br⟩ := body.replayVariables (replay_underBinder (replay_right supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    exact ⟨df ++ outside, ⟨.lam domain' guard body' pack' covered'⟩, replay_append dr external⟩
  | .union left right =>
    obtain ⟨lf, ⟨left'⟩, lr⟩ := left.replayVariables (replay_left supply)
    obtain ⟨rf, ⟨right'⟩, rr⟩ := right.replayVariables (replay_right supply)
    exact ⟨lf ++ rf, ⟨.union left' right'⟩, replay_append lr rr⟩
  | .pad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.pad changed⟩, resources⟩
  | .unpad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.unpad changed⟩, resources⟩
  | .view source view =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.view changed view⟩, resources⟩
  | .rowShift source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.rowShift changed⟩, resources⟩
  | .action source action =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.action changed action⟩, resources⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.replayVariables
    (certificate : SortableCert env U registry target locals σ expression relevant profile required)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, Nonempty (SortableCert env U registry target locals σ expression relevant profile footprint) ∧
      footprint.Available available := by
  match certificate with
  | .pi domain guard rows =>
    obtain ⟨df, ⟨domain'⟩, dr⟩ := domain.replayVariables (replay_left supply)
    obtain ⟨rf, ⟨rows'⟩, rr⟩ := rows.replayVariables (replay_right supply)
    exact ⟨df ++ rf, ⟨.pi domain' guard rows'⟩, replay_append dr rr⟩
  | .ofCode source formed =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.ofCode changed formed⟩, resources⟩
  | .observe source formed =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.observe changed formed⟩, resources⟩
  | .seed source formed =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.seed changed formed⟩, resources⟩
  | .union left right =>
    obtain ⟨lf, ⟨left'⟩, lr⟩ := left.replayVariables (replay_left supply)
    obtain ⟨rf, ⟨right'⟩, rr⟩ := right.replayVariables (replay_right supply)
    exact ⟨lf ++ rf, ⟨.union left' right'⟩, replay_append lr rr⟩
  | .pad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.pad changed⟩, resources⟩
  | .unpad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.unpad changed⟩, resources⟩
  | .familyPad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.familyPad changed⟩, resources⟩
  | .down source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.down changed⟩, resources⟩
  | .map view source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.map view changed⟩, resources⟩
  | .select source member =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.select changed member⟩, resources⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.focusMinimal changed minimal bound⟩, resources⟩
  | .sortPad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.sortPad changed⟩, resources⟩
  | .support action source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.support action changed⟩, resources⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableRows.replayVariables
    (rows : SortableRows env U registry target locals σ A B relevant ambient values required)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, Nonempty (SortableRows env U registry target locals σ A B relevant ambient values footprint) ∧
      footprint.Available available := by
  match rows with
  | .nil => exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | .cons guard body pack covered tail =>
    obtain ⟨bf, ⟨body'⟩, br⟩ := body.replayVariables (replay_underBinder (replay_left supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    obtain ⟨tf, ⟨tail'⟩, tr⟩ := tail.replayVariables (replay_right supply)
    exact ⟨outside ++ tf, ⟨.cons guard body' pack' covered' tail'⟩, replay_append external tr⟩
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

end

/-- Choose the actual finite replay observations once, retaining their exact
footprints for the charged recipe instead of assuming direct need membership. -/
theorem VariableResourceReplay.transfer
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, Nonempty (RecipeResourceTransfer env U registry target locals σ required footprint) ∧
      footprint.Available available := by
  induction required with
  | nil => exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | cons entry tail ih =>
    obtain ⟨headFootprint, ⟨query⟩, resources⟩ := supply entry.1 entry.2 List.mem_cons_self
    obtain ⟨tailFootprint, ⟨rest⟩, restResources⟩ :=
      ih (fun index need member => supply index need (List.mem_cons_of_mem _ member))
    exact ⟨headFootprint ++ tailFootprint, ⟨.cons query rest⟩, replay_append resources restResources⟩

namespace OriginalRecordSource
mutual
theorem RichCert.replayVariables
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile required)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, Nonempty (RichCert sourceEnv env U registry target node locals σ relevant profile footprint) ∧
      footprint.Available available := by
  match certificate with
  | .recipe code =>
    obtain ⟨footprint, ⟨transfer⟩, resources⟩ := supply.transfer
    exact ⟨footprint, ⟨.recipe (.resources code transfer)⟩, resources⟩
  | .legacy source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.legacy changed⟩, resources⟩
  | .route path source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.route path changed⟩, resources⟩
  | .union left right =>
    obtain ⟨lf, ⟨left'⟩, lr⟩ := left.replayVariables (replay_left supply)
    obtain ⟨rf, ⟨right'⟩, rr⟩ := right.replayVariables (replay_right supply)
    exact ⟨lf ++ rf, ⟨.union left' right'⟩, replay_append lr rr⟩
  | .observe source formed =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.observe changed formed⟩, resources⟩
  | .pi hu hv domain guard rows =>
    obtain ⟨df, ⟨domain'⟩, dr⟩ := domain.replayVariables (replay_left supply)
    obtain ⟨rf, ⟨rows'⟩, rr⟩ := rows.replayVariables (replay_right supply)
    exact ⟨df ++ rf, ⟨.pi hu hv domain' guard rows'⟩, replay_append dr rr⟩
  | .pad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.pad changed⟩, resources⟩
  | .down source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.down changed⟩, resources⟩
  | .map view source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.map view changed⟩, resources⟩
  | .support action source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.support action changed⟩, resources⟩
  | .select source member =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.select changed member⟩, resources⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem RichRows.replayVariables
    (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values required)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, Nonempty (RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint) ∧
      footprint.Available available := by
  match rows with
  | .nil => exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | .cons guard body pack covered tail =>
    obtain ⟨bf, ⟨body'⟩, br⟩ := body.replayVariables (replay_underBinder (replay_left supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    obtain ⟨tf, ⟨tail'⟩, tr⟩ := tail.replayVariables (replay_right supply)
    exact ⟨outside ++ tf, ⟨.cons guard body' pack' covered' tail'⟩, replay_append external tr⟩
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem RichObs.replayVariables
    (observation : RichObs sourceEnv env U registry target node locals σ profile required)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, Nonempty (RichObs sourceEnv env U registry target node locals σ profile footprint) ∧
      footprint.Available available := by
  match observation with
  | .rigidFamily (node := node) origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed =>
    exact ⟨[], ⟨.rigidFamily (node := node) origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed⟩,
      fun _ _ member => nomatch member⟩
  | .family (name := name) (levels := levels) (node := node) origin lookup notDefinition notNative notQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    exact ⟨[], ⟨.family (node := node) origin lookup notDefinition notNative notQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree⟩,
      fun _ _ member => nomatch member⟩
  | .constructor (name := name) (levels := levels) (node := node) origin lookup notDefinition notNative notQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    exact ⟨[], ⟨.constructor (node := node) origin lookup notDefinition notNative notQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree⟩,
      fun _ _ member => nomatch member⟩
  | .canonicalDelta (strata := strata) (name := name) (levels := levels) (node := node)
      lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    exact ⟨[], ⟨.canonicalDelta (strata := strata) (node := node) lookup nameEq registered seedWF seedLength levelsWF equivalent
      bodyClosed typeClosed certificate typed body⟩, fun _ _ member => nomatch member⟩
  | .canonicalConst (name := name) (levels := levels) (node := node) origin realization query resources =>
    exact ⟨[], ⟨.canonicalConst origin realization query resources⟩,
      fun _ _ member => nomatch member⟩
  | .legacy source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.legacy changed⟩, resources⟩
  | .route path source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.route path changed⟩, resources⟩
  | .union left right =>
    obtain ⟨lf, ⟨left'⟩, lr⟩ := left.replayVariables (replay_left supply)
    obtain ⟨rf, ⟨right'⟩, rr⟩ := right.replayVariables (replay_right supply)
    exact ⟨lf ++ rf, ⟨.union left' right'⟩, replay_append lr rr⟩
  | .code source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.code changed⟩, resources⟩
  | .projection head nameEq member major field typed alignment =>
    obtain ⟨mf, ⟨major'⟩, mr⟩ := major.replayVariables (replay_left supply)
    obtain ⟨ff, ⟨field'⟩, fr⟩ := field.replayVariables (replay_right supply)
    exact ⟨mf ++ ff, ⟨.projection head nameEq member major' field' typed alignment⟩, replay_append mr fr⟩
  | .projectionSortable head nameEq member major selected path sortable field typed =>
    obtain ⟨mf, ⟨major'⟩, mr⟩ := major.replayVariables (replay_left supply)
    obtain ⟨ff, ⟨field'⟩, fr⟩ := field.replayVariables (replay_right supply)
    exact ⟨mf ++ ff, ⟨.projectionSortable head nameEq member major' selected path sortable field' typed⟩, replay_append mr fr⟩
  | .app hu hv fn arg arguments admitted =>
    obtain ⟨ff, ⟨fn'⟩, fr⟩ := fn.replayVariables (replay_left supply)
    obtain ⟨af, ⟨arg'⟩, ar⟩ := arg.replayVariables (replay_right supply)
    exact ⟨ff ++ af, ⟨.app hu hv fn' arg' arguments admitted⟩, replay_append fr ar⟩
  | .lam hu hv domain guard body pack covered =>
    obtain ⟨df, ⟨domain'⟩, dr⟩ := domain.replayVariables (replay_left supply)
    obtain ⟨bf, ⟨body'⟩, br⟩ := body.replayVariables (replay_underBinder (replay_right supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    exact ⟨df ++ outside, ⟨.lam hu hv domain' guard body' pack' covered'⟩, replay_append dr external⟩
  | .view source view =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.view changed view⟩, resources⟩
  | .action source action =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.action changed action⟩, resources⟩
  | .select source member =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.select changed member⟩, resources⟩
  | .pad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.pad changed⟩, resources⟩
  | .unpad source =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := source.replayVariables supply
    exact ⟨fp, ⟨.unpad changed⟩, resources⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

end
/-- Rebinding a Pi input preserves the exact original body node, including
all projected subqueries. The new finite pack is computed from the concrete
variable observations; no source typing or semantic liveness is assumed. -/
theorem RichCert.rebind_local
    {oldInput packed : Profile n} {newInput : Profile m}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant result required)
    (replay : Obs env U registry target locals σ (.bvar 0) oldInput replayFootprint)
    (replayAvailable : replayFootprint.Available (Valuation.push (rowInputNeeds newInput) available))
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (closed : available.AtomClosed) :
    ∃ footprint outside' packed',
      Nonempty (RichCert sourceEnv env U registry target node locals σ relevant result footprint) ∧
      BinderPack m packed' footprint outside' ∧
      (∀ atom ∈ packed'.atoms, atom ∈ newInput.atoms) ∧ outside'.Available available := by
  have localClosed := Valuation.push_atomized_closed closed [⟨m, newInput⟩]
  have supply : VariableResourceReplay env U registry target locals σ
      (Valuation.push (rowInputNeeds newInput) available) required := by
    clear certificate
    induction pack with
    | nil => intro _ _ member; cases member
    | «local» need bound rest ih =>
      have inclusion : List.Subset (raiseProfile n bound need.profile) oldInput := by
        intro atom member
        apply covered atom (List.mem_append_left _ ?_)
        simpa only [Need.atGrade, dif_pos bound, Profile.atoms] using member
      obtain ⟨fp, ⟨selected⟩, selection⟩ := replay.subprofile inclusion
      have observation := selected.lower bound
      have resources := selection.available_closed replayAvailable localClosed
      have tail := ih (fun atom member => covered atom (List.mem_append_right _ member)) outsideAvailable
      intro index wanted member
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        exact ⟨fp, ⟨observation⟩, resources⟩
      · exact tail index wanted member
    | external index need rest ih =>
      have tail := ih covered
        (fun i wanted member => outsideAvailable i wanted (List.mem_cons_of_mem _ member))
      intro i wanted member
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        refine ⟨[(index + 1, need)], ⟨.var locals σ (index + 1) need.profile⟩, ?_⟩
        intro i wanted member
        cases List.mem_singleton.mp member
        exact outsideAvailable index need List.mem_cons_self
      · exact tail i wanted member
  obtain ⟨footprint, ⟨changed⟩, resources⟩ := certificate.replayVariables supply
  obtain ⟨packed', outside', pack', covered', outsideAvailable'⟩ :=
    Footprint.pack_available resources
      (fun need member => (rowInputNeeds_bounded newInput need member).1)
      (fun need member => (rowInputNeeds_bounded newInput need member).2)
  exact ⟨footprint, outside', packed', ⟨changed⟩, pack', covered', outsideAvailable'⟩

end OriginalRecordSource
end Lean4Lean.AnchoredSource.Adapted
