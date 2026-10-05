import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceRealization
import Lean4Lean.Theory.Typing.AnchoredNativeSyntaxTransport

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem subst_cons_future (σ : Subst) (anchor : VExpr) (ρ : Lift) :
    (σ.cons anchor).lift_r ρ = (σ.lift_r ρ).cons (anchor.lift' ρ) := by
  funext i
  cases i <;> rfl

private theorem key_rename_map (ρ : Lift) :
    DataRequest.rename (n := n) ρ = DataRequest.map (·.lift' ρ) (Profile.rename ρ) := by
  funext key
  rfl


private theorem native_resources_rename
    (resources : Footprint.Available footprint available) (ρ : Lift) :
    Footprint.Available (Footprint.rename ρ footprint)
      (fun i => (available i).map (Need.rename ρ)) := by
  intro i need hm
  obtain ⟨⟨j, original⟩, hj, he⟩ := List.mem_map.mp hm
  cases he
  exact List.mem_map_of_mem (resources _ _ hj)

/- Target extension changes the realization and frozen target guards only.
Every source observation and every code-certificate leaf is retained. -/
mutual
noncomputable def Obs.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {expression : VExpr} {demand : Profile n}
    {footprint : Footprint} (observation : Obs env U registry Γ locals σ expression demand footprint) :
    Obs env U registry Δ locals (σ.lift_r ρ) expression (demand.rename ρ)
      (Footprint.rename ρ footprint) := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    simpa only [Profile.rename_singleton, Footprint.rename, List.map_nil] using
      Obs.delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed
        (certificate.future henv W) (by simpa only [Profile.rename_singleton] using Profile.rename_hasType_iff.mpr typed)
        (by simpa only [Profile.rename_singleton, Footprint.rename, List.map_nil] using body.future henv W)
  | .native lookup notDefinition name_eq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact .native lookup notDefinition name_eq registered seedWF levelsWF equivalent signature typeClosed
      (typeCertificate.future henv W) (Profile.rename_hasType_iff.mpr typed)
      (tree.future henv W typeClosed)
  | .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    exact .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed (typeCertificate.future henv W) (Profile.rename_hasType_iff.mpr typed)
      (tree.future henv W typeClosed.instL)
  | .constructor lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    exact .constructor lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed (typeCertificate.future henv W) (Profile.rename_hasType_iff.mpr typed)
      (tree.future henv W typeClosed.instL)
  | .var locals σ i demand => exact .var locals _ i (demand.rename ρ)
  | .empty => exact .empty
  | .sort relevant => simpa only [Profile.rename_sort, Footprint.rename, List.map_nil] using Obs.sort relevant
  | .app fn arg arguments admitted =>
    have ihfn := fn.future henv W
    have iharg := arg.future henv W
    simp only [Profile.fn, Profile.rename_singleton, Atom.rename_fn] at ihfn
    have admitted' := Admitted.future henv W admitted
    rw [lift'_subst] at admitted'
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append, lift'_subst] using Obs.app ihfn iharg (NormalProfileAdapter.future henv W arguments) admitted'
  | .lam domain guard body normal covered =>
    have ihdomain := domain.future henv W
    have ihbody := body.future henv W
    rw [subst_cons_future, Profile.rename_singleton] at ihbody
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append] using
      Obs.lam ihdomain (guard.future henv W) ihbody (normal.rename ρ)
        (by
          intro atom hm
          obtain ⟨old, hsource, rfl⟩ := List.mem_map.mp hm
          exact List.mem_map_of_mem (covered old hsource))
  | .pi domain guard bodies =>
    have hd := domain.future henv W
    have hb := bodies.future henv W
    simpa only [Profile.pi, Profile.rename_singleton, Atom.rename_pi,
      Footprint.rename_append] using Obs.pi hd (guard.future henv W) hb
  | .union left right =>
    simpa only [Profile.rename_union, Footprint.rename_append] using
      Obs.union (left.future henv W) (right.future henv W)
  | .view source view =>
    simpa only [Profile.rename_singleton] using
      Obs.view (source.future henv W) (view.future henv W)
  | .pad source =>
    simpa only [Profile.rename_pad] using Obs.pad (source.future henv W)
  | .unpad source =>
    have ih := source.future henv W
    rw [Profile.rename_pad] at ih
    exact Obs.unpad ih
  | .rowShift source =>
    have ih := source.future henv W
    simp only [Profile.fn, Profile.rename_singleton, Atom.rename_fn] at ih
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pad,
      Key.pad_rename] using Obs.rowShift ih
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

noncomputable def CodeCert.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {expression : VExpr} {profile : Profile n}
    {footprint : Footprint} (cert : CodeCert env U registry Γ locals σ expression profile footprint) :
    CodeCert env U registry Δ locals (σ.lift_r ρ) expression (profile.rename ρ)
      (Footprint.rename ρ footprint) := by
  match cert with
  | .seed observation formed =>
    have hf := (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
    rw [Profile.rename_sort] at hf
    exact .seed (observation.future henv W) hf
  | .union left right =>
    simpa only [Profile.rename_union, Footprint.rename_append] using
      CodeCert.union (left.future henv W) (right.future henv W)
  | .pad source =>
    simpa only [Profile.rename_pad] using CodeCert.pad (source.future henv W)
  | .familyPad source =>
    have child := source.future henv W
    simp only [Profile.rename_singleton, Atom.rename_family] at child
    simpa only [Profile.rename_singleton, Atom.rename_family, FamilyData.rename,
      FamilyData.map_map, Profile.pad_rename, Function.comp_def, id_eq] using
      CodeCert.familyPad child
  | .unpad source =>
    have ih := source.future henv W
    rw [Profile.rename_pad] at ih
    exact CodeCert.unpad ih
  | .down source =>
    simpa only [Profile.down_rename] using CodeCert.down (source.future henv W)
  | .map view source =>
    have ih := source.future henv W
    simpa only [← AtomView.mapType_future] using
      CodeCert.map (view.future henv W) ih
  | .select source member =>
    simpa only [Profile.rename_singleton] using
      CodeCert.select (source.future henv W) (List.mem_map_of_mem (f := Atom.rename ρ) member)
  | .focusMinimal source minimal bound =>
    exact .focusMinimal (source.future henv W) (minimal.rename ρ)
      (Profile.rename_le_iff.mpr bound)
termination_by sizeOf cert
decreasing_by all_goals simp_wf; omega
noncomputable def PiRows.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals σ A B ambient rows footprint) :
    PiRows env U registry Δ locals (σ.lift_r ρ) A B (ambient.rename ρ)
      (Rows.rename ρ rows) (Footprint.rename ρ footprint) := by
  match bodies with
  | .nil => exact .nil
  | .cons guard body normal covered tail =>
    have hb := body.future henv W
    rw [subst_cons_future] at hb
    simpa only [Rows.rename, List.map_cons, Footprint.rename_append] using
      PiRows.cons (guard.future henv W) hb (normal.rename ρ)
        (by
          intro atom hm
          obtain ⟨old, hsource, rfl⟩ := List.mem_map.mp hm
          exact List.mem_map_of_mem (covered old hsource)) (tail.future henv W)
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; omega

noncomputable def NativeCaptures.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {levels : List VLevel} {arguments witnesses : List VExpr}
    (typeClosed : ∀ type, data.recursorType = some type → type.Closed)
    (selected : data.saturatedProgram levels arguments = some program)
    (rhsClosed : program.equation.rhs.Closed)
    (witnessLength : witnesses.length = program.equationBody.domains.length)
    {field : Nat} {required nativeFootprint : Footprint}
    (captures : NativeCaptures env U registry Γ program witnesses field required nativeFootprint) :
    NativeCaptures env U registry Δ (program.rename ρ) (witnesses.map (·.lift' ρ)) field
      (Footprint.rename ρ required) (Footprint.rename ρ nativeFootprint) := by
  match captures with
  | .prefix required =>
    simpa only [SaturatedProgram.rename, List.length_map, Footprint.sourceLift,
      Footprint.rename, List.map_map, Function.comp_def] using
      NativeCaptures.prefix (program := program.rename ρ)
        (witnesses := witnesses.map (·.lift' ρ)) (Footprint.rename ρ required)
  | @NativeCaptures.index _ _ _ _ rank _ _ _ templates naturalAvailable captureAvailable
      input packed required outside previousNative value naturalSupport declaredSupport naturalFootprint declaredFootprint
      naturalCertificate naturalResources declaredCertificate declaredResources naturalTyped declaredTyped alignment declaredCode
      nativeValue copiedValue pack covered previous =>
    have naturalScope := templates.natural_scope (typeClosed _ templates.registeredType)
    have declaredScope := templates.declared_scope rhsClosed witnessLength
    have natural := (naturalCertificate.future henv W).realizePrefix naturalScope
      (nativeCaptureSubst ((program.prefixArgs.take (data.indexOffset + templates.slot)).map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix _ ρ hi)
    have declared := (declaredCertificate.future henv W).realizePrefix declaredScope
      (nativeCaptureSubst ((witnesses.take (data.indexOffset + templates.field)).map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix _ ρ hi)
    have alignment' := alignment.future henv W
    have declaredCode' := declaredCode.future henv W
    rw [nativeCaptureSubst_rename_expression naturalScope,
      nativeCaptureSubst_rename_expression declaredScope] at alignment'
    rw [nativeCaptureSubst_rename_expression declaredScope] at declaredCode'
    have prior := previous.future henv W typeClosed selected rhsClosed witnessLength
    rw [Footprint.rename_append] at prior
    have result := NativeCaptures.index (templates := templates.rename rhsClosed ρ)
      (naturalAvailable := fun i => (naturalAvailable i).map (Need.rename ρ))
      (captureAvailable := fun i => (captureAvailable i).map (Need.rename ρ))
      (input := input.rename ρ) (packed := packed.rename ρ)
      (value := value.lift' ρ)
      (by simpa only [NativeIndexTemplates.rename, SaturatedProgram.rename, List.map_take] using natural)
      (native_resources_rename naturalResources ρ)
      (by simpa only [NativeIndexTemplates.rename, SaturatedProgram.rename, List.map_take] using declared)
      (native_resources_rename declaredResources ρ)
      (Profile.rename_hasType_iff.mpr naturalTyped)
      (Profile.rename_hasType_iff.mpr declaredTyped)
      (by simpa only [NativeIndexTemplates.rename, SaturatedProgram.rename, List.map_take] using alignment')
      (by simpa only [NativeIndexTemplates.rename, SaturatedProgram.rename, List.map_take] using declaredCode')
      (by simpa only [NativeIndexTemplates.rename, SaturatedProgram.rename, List.getElem?_map, nativeValue, Option.map_some])
      (by simpa only [NativeIndexTemplates.rename, List.getElem?_map, copiedValue, Option.map_some])
      (pack.rename ρ)
      (by intro atom hm; obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
          exact List.mem_map_of_mem (covered old ho)) prior
    simpa only [NativeIndexTemplates.rename, SaturatedProgram.rename, List.length_map,
      Footprint.rename_append, Footprint.rename, Footprint.sourceLift, List.map_map,
      List.map_cons, List.map_nil, List.map_append, Function.comp_def, Need.rename] using result
  | @NativeCaptures.proof _ _ _ _ rank _ _ _ field domain witness required outside native
      instruction captured sourceProof domainProof inhabitant pack previous =>
    have scope : domain.ClosedN (data.indexOffset + field) :=
      native_instruction_scope selected rhsClosed instruction
    have enough : data.indexOffset + field ≤ witnesses.length := by
      obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp captured
      omega
    have scopedDomain := scope
    rw [← Nat.min_eq_left enough, ← List.length_take] at scopedDomain
    have hd := domainProof.weak' henv W.weakening
    have hv := inhabitant.weak' henv W.weakening
    rw [nativeCaptureSubst_rename_expression scopedDomain] at hd hv
    have prior := previous.future henv W typeClosed selected rhsClosed witnessLength
    exact .proof (witness := witness.lift' ρ) instruction
      (by simpa only [List.getElem?_map, captured, Option.map_some])
      sourceProof
      (by simpa only [List.map_take, lift'] using hd)
      (by simpa only [List.map_take] using hv)
      (by simpa only [Profile.rename_empty] using pack.rename ρ) prior
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

noncomputable def NativePlan.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    (typeClosed : signature.type.Closed)
    {demand : Profile n} {footprint : Footprint}
    (plan : NativePlan env U registry Γ signature arguments demand footprint) :
    NativePlan env U registry Δ signature (arguments.map (·.lift' ρ)) (demand.rename ρ)
      (Footprint.rename ρ footprint) := by
  match plan with
  | .terminal program selected lhsClosed rhsClosed saturated noTrailing prefixEq
      witnesses witnessLength witnessPrefix argumentAlignment argumentsEq body captures =>
    have spec := saturatedProgram_spec selected
    have bodyScope : (program.equationBody.rhs.instL levels).ClosedN witnesses.length := by
      rw [witnessLength]
      exact (scope_of_extract spec.2.2.2.2.2.2.2.2.2.1 rhsClosed).2.instL
    have body' := (body.future henv W).realizePrefix bodyScope
      (nativeCaptureSubst (witnesses.map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix witnesses ρ hi)
    have captures' := captures.future henv W
      (fun type ht => (Option.some.inj (ht.symm.trans signature.typeOrigin)) ▸ typeClosed)
      selected rhsClosed witnessLength
    have alignment := native_substEq_prefix henv
      (argumentAlignment.weakenTarget henv W.weakening)
      (σ' := nativeCaptureSubst (arguments.map (·.lift' ρ)))
      (τ' := nativeCaptureSubst ((nativeEquationArguments program witnesses).map (·.lift' ρ)))
      (by intro i hi; apply nativeCaptureSubst_rename_prefix
          simpa only [List.length_reverse, takeForalls_length signature.telescope, ← saturated] using hi)
      (by intro i hi; apply nativeCaptureSubst_rename_prefix
          simpa only [List.length_reverse, takeForalls_length signature.telescope,
            nativeEquationArguments_length selected] using hi)
    rw [← nativeEquationArguments_rename selected lhsClosed witnessLength ρ] at alignment
    exact .terminal (program.rename ρ)
      (saturatedProgram_rename_of_closed_rhs selected rhsClosed.instL ρ).1 lhsClosed rhsClosed
      (by simpa only [List.length_map] using saturated)
      (by simpa only [SaturatedProgram.rename, noTrailing, List.map_nil])
      (by simpa only [SaturatedProgram.rename, prefixEq])
      (witnesses.map (fun x : VExpr => x.lift' ρ))
      (by simpa only [List.length_map, SaturatedProgram.rename] using witnessLength)
      (by simpa only [List.map_take] using congrArg (List.map (·.lift' ρ)) witnessPrefix)
      alignment (by
        rw [nativeEquationArguments_rename selected lhsClosed witnessLength]
        exact congrArg (List.map (·.lift' ρ)) argumentsEq) body' captures'
  | @NativePlan.binder _ _ _ _ rank _ _ _ arguments domain key output support packed
      domainFootprint bodyFootprint outside domainOrigin domainCode guard body pack covered =>
    have scope := signature.domain_scope typeClosed domainOrigin
    have domain' := (domainCode.future henv W).realizePrefix scope
      (nativeCaptureSubst (arguments.map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)
    have guard' := guard.future henv W
    have he := subst_congr_closedN scope
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)
    have guard'' : LambdaGuard env U registry Δ
        (nativeCaptureSubst (arguments.map (·.lift' ρ))) domain (key.rename ρ) (support.rename ρ) :=
      ⟨guard'.inputTyped, guard'.formed, he ▸ guard'.path, he ▸ guard'.domains, guard'.anchor⟩
    have body' := body.future henv W typeClosed
    simp only [List.map_append, List.map_cons, List.map_nil, Profile.rename_singleton] at body'
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append, List.map_append, List.map_cons, List.map_nil] using
      NativePlan.binder (by simpa only [List.length_map] using domainOrigin)
        (by simpa only [List.length_map] using domain') guard'' body' (pack.rename ρ)
        (by intro atom hm; obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
            exact List.mem_map_of_mem (covered old ho))
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

noncomputable def FamilyCaptures.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {source : List VExpr} {locals : List Nat} {σ : Subst} {expressions : List VExpr}
    {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (captures : FamilyCaptures env U registry Γ source locals σ expressions keys footprint) :
    FamilyCaptures env U registry Δ source locals (σ.lift_r ρ) expressions
      (keys.map (DataRequest.rename ρ)) (Footprint.rename ρ footprint) := by
  match captures with
  | .nil => exact .nil
  | .cons lookup value adapter alignment anchor tail =>
    obtain ⟨rawAnchor, rawPair, typed, formed, code, first, second⟩ := anchor
    have anchor' : RankedData.RequestAdmission env U (relations env U registry _) Δ
        (DataRequest.rename ρ _) ((σ _).lift' ρ) ((σ _).lift' ρ) :=
      ⟨rawAnchor.weak' henv W.weakening, rawPair.weak' henv W.weakening,
        Profile.rename_hasType_iff.mpr typed,
        by simpa only [Profile.rename_sort, DataRequest.rename, DataRequest.map] using
          (Profile.rename_hasType_iff (ρ := ρ)).mpr formed,
        TypeRelated.future henv W code,
        Related.future henv W first, Related.future henv W second⟩
    have alignment' := alignment.future henv W
    rw [lift'_subst] at alignment'
    simpa only [List.map_cons, Footprint.rename_append] using
      FamilyCaptures.cons lookup (value.future henv W) (adapter.future henv W)
        alignment' anchor' (tail.future henv W)
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

noncomputable def FamilyPlan.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    (typeClosed : declaredType.Closed)
    {demand : Profile n} {footprint : Footprint}
    (plan : FamilyPlan env U registry Γ name levels signature arguments demand footprint) :
    FamilyPlan env U registry Δ name levels signature (arguments.map (·.lift' ρ))
      (demand.rename ρ) (Footprint.rename ρ footprint) := by
  match plan with
  | .terminal saturated resultSort relevance captures =>
    have captures' := (captures.future henv W).realizePrefix
      (signature.contextClosed typeClosed)
      (nativeCaptureSubst (arguments.map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ
        (by simpa only [List.length_reverse, ← saturated] using hi))
    simpa only [List.length_map, Profile.rename_singleton, Atom.rename_family,
      FamilyData.map] using FamilyPlan.terminal
      (by simpa only [List.length_map] using saturated) resultSort relevance
      (by simpa only [List.length_map, key_rename_map] using captures')
  | .binder origin domainCode guard body pack covered =>
    have scope := signature.domain_scope typeClosed origin
    have domain' := (domainCode.future henv W).realizePrefix scope
      (nativeCaptureSubst (arguments.map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)
    have guard' := guard.future henv W
    have he := subst_congr_closedN scope
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)
    have guard'' : LambdaGuard env U registry Δ
        (nativeCaptureSubst (arguments.map (·.lift' ρ))) _ _ _ :=
      ⟨guard'.inputTyped, guard'.formed, he ▸ guard'.path, he ▸ guard'.domains, guard'.anchor⟩
    have body' := body.future henv W typeClosed
    simp only [List.map_append, List.map_cons, List.map_nil, Profile.rename_singleton] at body'
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append, List.map_append, List.map_cons, List.map_nil] using
      FamilyPlan.binder (by simpa only [List.length_map] using origin)
        (by simpa only [List.length_map] using domain') guard'' body' (pack.rename ρ)
        (by intro atom hm; obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
            exact List.mem_map_of_mem (covered old ho))
  | .view source view =>
    simpa only [Profile.rename_singleton] using
      FamilyPlan.view (source.future henv W typeClosed) (view.future henv W)
  | .pad source =>
    simpa only [Profile.rename_pad] using FamilyPlan.pad (source.future henv W typeClosed)
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

noncomputable def ConstructorPlan.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    (typeClosed : declaredType.Closed)
    {demand : Profile n} {footprint : Footprint}
    (plan : ConstructorPlan env U registry Γ name levels signature arguments demand footprint) :
    ConstructorPlan env U registry Δ name levels signature (arguments.map (·.lift' ρ))
      (demand.rename ρ) (Footprint.rename ρ footprint) := by
  match plan with
  | @ConstructorPlan.terminal _ _ _ _ n captureFootprint resultFootprint name levels declaredType signature arguments
      family keys familyLevels familyArguments saturated resultShape relevant captures resultCode =>
    have captures' := (captures.future henv W).realizePrefix
      (signature.contextClosed typeClosed)
      (nativeCaptureSubst (arguments.map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ
        (by simpa only [List.length_reverse, ← saturated] using hi))
    have result' := (resultCode.future henv W).realizePrefix
      (signature.result_scope typeClosed)
      (nativeCaptureSubst (arguments.map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ (by simpa only [saturated] using hi))
    simpa only [List.length_map, Profile.rename_singleton, Atom.rename_ctor,
      ConstructorData.map, FamilyData.rename, FamilyData.map, key_rename_map, Footprint.rename_append] using
      ConstructorPlan.terminal (arguments := arguments.map (·.lift' ρ))
        (family := family.rename ρ) (keys := keys.map (DataRequest.rename ρ))
        (by simpa only [List.length_map] using saturated)
        resultShape relevant
        (by simpa only [List.length_map, key_rename_map] using captures')
        (by simpa only [List.length_map, Profile.rename_singleton, Atom.rename_family, FamilyData.rename] using result')
  | .binder origin domainCode guard body pack covered =>
    have scope := signature.domain_scope typeClosed origin
    have domain' := (domainCode.future henv W).realizePrefix scope
      (nativeCaptureSubst (arguments.map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)
    have guard' := guard.future henv W
    have he := subst_congr_closedN scope
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)
    have guard'' : LambdaGuard env U registry Δ
        (nativeCaptureSubst (arguments.map (·.lift' ρ))) _ _ _ :=
      ⟨guard'.inputTyped, guard'.formed, he ▸ guard'.path, he ▸ guard'.domains, guard'.anchor⟩
    have body' := body.future henv W typeClosed
    simp only [List.map_append, List.map_cons, List.map_nil, Profile.rename_singleton] at body'
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append, List.map_append, List.map_cons, List.map_nil] using
      ConstructorPlan.binder (by simpa only [List.length_map] using origin)
        (by simpa only [List.length_map] using domain') guard'' body' (pack.rename ρ)
        (by intro atom hm; obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
            exact List.mem_map_of_mem (covered old ho))
  | .view source view =>
    simpa only [Profile.rename_singleton] using
      ConstructorPlan.view (source.future henv W typeClosed) (view.future henv W)
  | .pad source =>
    simpa only [Profile.rename_pad] using ConstructorPlan.pad (source.future henv W typeClosed)
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

end

end Lean4Lean.AnchoredSource.Adapted
