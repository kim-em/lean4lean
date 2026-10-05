import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryContinuation

/-! Code extraction at the SAME original endpoint preserves the opening
sites actually carried by the incoming annotation. Finite code actions may
duplicate or omit sites; none are reconstructed from a fresh environment.
This is the code-extraction seam in controlled R/equality/R route replay. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private actionFormation from Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem RichCert.raise_worlds_depth
    {profile : Profile n}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (annotation : WorldCertProvenance strata source) (bound : n ≤ N) :
    ∃ raised : RichCert sourceEnv env U registry target node locals σ relevant
        (raiseProfile N bound profile) footprint,
      ∃ output : WorldCertProvenance strata raised,
        output.worlds = annotation.worlds ∧
        ∀ policy, raised.headDepth policy = source.headDepth policy := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact ⟨source, annotation, rfl, fun _ => rfl⟩
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      rw [raiseProfile_self]
      exact ⟨source, annotation, rfl, fun _ => rfl⟩
    · have previous : n ≤ N := by omega
      obtain ⟨raised, output, worlds, depth⟩ := ih previous
      rw [raiseProfile_step previous]
      refine ⟨.pad raised, .pad output, worlds, ?_⟩
      intro policy
      simpa only [RichCert.headDepth] using depth policy

theorem RichCert.codeActionAtom_worlds_depth
    {profile : Profile n} {output : Profile m} {atom : Atom m}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (annotation : WorldCertProvenance strata source)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (member : atom ∈ output.atoms) :
    ∃ result : RichCert sourceEnv env U registry target node locals σ next (.singleton atom) footprint,
      ∃ resultAnnotation : WorldCertProvenance strata result,
        resultAnnotation.worlds = annotation.worlds ∧
        ∀ policy, result.headDepth policy = source.headDepth policy := by
  obtain ⟨original, originalMember, ⟨selected⟩⟩ := action.atom member
  let N := max n m
  have hn : n ≤ N := Nat.le_max_left _ _
  have hm : m ≤ N := Nat.le_max_right _ _
  have high := (RichCert.select source originalMember).raise_worlds_depth
    (.select annotation originalMember) hn
  rw [raiseProfile_singleton] at high
  obtain ⟨raised, raisedAnnotation, raisedWorlds, raisedDepth⟩ := high
  have selectedHigh := selected.atomAtGrade hn hm
  let changed := RichObs.action (RichObs.code raised) (AtomAction.code selectedHigh raised.formed)
  let changedAnnotation : WorldObsProvenance strata changed :=
    .action (.code raisedAnnotation) (AtomAction.code selectedHigh raised.formed)
  have formed := (actionFormation action source.formed).singleton_of_mem member
  have highResult : ∃ observation : RichObs sourceEnv env U registry target node locals σ
      (raiseProfile N hm (.singleton atom)) footprint,
      ∃ resultAnnotation : WorldObsProvenance strata observation,
        resultAnnotation.worlds = annotation.worlds ∧
        ∀ policy, observation.headDepth policy = source.headDepth policy := by
    rw [raiseProfile_singleton]
    refine ⟨changed, changedAnnotation, raisedWorlds, ?_⟩
    intro policy
    simpa only [changed, RichCert.headDepth, RichObs.headDepth] using raisedDepth policy
  obtain ⟨observation, resultAnnotation, worlds, depth⟩ := highResult
  refine ⟨.observe observation.lowerRaised formed, .observe (.lowerRaised resultAnnotation) formed,
    worlds, ?_⟩
  intro policy
  simp only [RichCert.headDepth]
  rw [RichObs.headDepth_lowerRaised]
  exact depth policy

theorem RichCert.codeAction_worlds_depth
    {profile : Profile n} {output : Profile m}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (annotation : WorldCertProvenance strata source)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (resources : footprint.Available available) :
    ∃ resultFootprint, ∃ result : RichCert sourceEnv env U registry target node locals σ next output resultFootprint,
      ∃ resultAnnotation : WorldCertProvenance strata result,
        resultFootprint.Available available ∧ resultAnnotation.worlds ⊆ annotation.worlds ∧
        ∀ policy, result.headDepth policy ≤ source.headDepth policy := by
  have each := fun atom member => source.codeActionAtom_worlds_depth annotation action (atom := atom) member
  suffices build : ∀ atoms : List (Atom m),
      (∀ atom ∈ atoms, ∃ result : RichCert sourceEnv env U registry target node locals σ next (.singleton atom) footprint,
        ∃ resultAnnotation : WorldCertProvenance strata result,
          resultAnnotation.worlds = annotation.worlds ∧
          ∀ policy, result.headDepth policy = source.headDepth policy) →
      ∃ resultFootprint, ∃ result : RichCert sourceEnv env U registry target node locals σ next (.mk atoms) resultFootprint,
        ∃ resultAnnotation : WorldCertProvenance strata result,
          resultFootprint.Available available ∧ resultAnnotation.worlds ⊆ annotation.worlds ∧
          ∀ policy, result.headDepth policy ≤ source.headDepth policy
      from build output.atoms each
  intro atoms
  induction atoms with
  | nil =>
    intro _
    let formed : (Profile.empty : Profile m).HasType (.sort next) :=
      Profile.HasType.empty (Profile.WF.sort next)
    refine ⟨[], .observe (.legacy (.legacy .empty)) formed, .observe .empty formed,
      (fun _ _ member => by cases member), (by intro world member; cases member), ?_⟩
    intro policy
    simp only [RichCert.headDepth, RichObs.headDepth, SortableObs.headDepth, Obs.headDepth]
    exact Nat.zero_le _
  | cons atom rest ih =>
    intro each
    obtain ⟨head, headAnnotation, headWorlds, headDepth⟩ := each atom List.mem_cons_self
    obtain ⟨tailFootprint, tail, tailAnnotation, tailResources, tailWorlds, tailDepth⟩ :=
      ih (fun a h => each a (List.mem_cons_of_mem _ h))
    refine ⟨footprint ++ tailFootprint, .union head tail, .union headAnnotation tailAnnotation, ?_, ?_, ?_⟩
    · intro index need member
      exact (List.mem_append.mp member).elim (resources index need) (tailResources index need)
    · intro world member
      rcases List.mem_append.mp member with member | member
      · rwa [headWorlds] at member
      · exact tailWorlds member
    · intro policy
      simp only [RichCert.headDepth, headDepth policy]
      exact Nat.max_le.mpr ⟨Nat.le_refl _, tailDepth policy⟩

theorem RichObs.codeFromGeneral_worlds_depth
    (henv : env.Ordered) {raw requested : Profile n}
    (observation : RichObs sourceEnv env U registry target node locals σ raw footprint)
    (annotation : WorldObsProvenance strata observation)
    (adapter : GeneralNormalProfileAdapter env U registry target raw requested)
    (formed : requested.HasType (.sort relevant))
    (resources : footprint.Available available) :
    ∃ nextFootprint,
      ∃ certificate : RichCert sourceEnv env U registry target node locals σ relevant requested nextFootprint,
        ∃ output : WorldCertProvenance strata certificate,
          nextFootprint.Available available ∧ output.worlds ⊆ annotation.worlds ∧
          ∀ policy, certificate.headDepth policy ≤ observation.headDepth policy := by
  have canonical : AdapterNormal.profile requested = requested := AdapterNormal.profile_sortable formed
  change GeneralProfileAdapter env U registry target (AdapterNormal.profile raw)
    (AdapterNormal.profile requested) at adapter
  rw [canonical] at adapter
  induction requested with
  | nil =>
    refine ⟨[], .observe (.legacy (.legacy .empty)) formed, .observe .empty formed,
      (fun _ _ member => by cases member), (by intro world member; cases member), ?_⟩
    intro policy
    simp only [RichCert.headDepth, RichObs.headDepth, SortableObs.headDepth, Obs.headDepth]
    exact Nat.zero_le _
  | cons head tail ih =>
    obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin List.mem_cons_self
    obtain ⟨original, originalMember, normalEq⟩ := List.mem_map.mp member
    subst normal
    obtain ⟨flag, sourceFormed, ⟨program⟩⟩ :=
      entry.toCodeAtOutput (formed.singleton_of_mem List.mem_cons_self)
    let selected := RichObs.view (RichObs.select observation originalMember) (AdapterNormal.view henv original)
    let selectedAnnotation : WorldObsProvenance strata selected :=
      .view (.select annotation originalMember) (AdapterNormal.view henv original)
    obtain ⟨headFootprint, headCode, headAnnotation, headResources, headWorlds, headDepth⟩ :=
      (RichCert.observe selected sourceFormed).codeAction_worlds_depth
        (.observe selectedAnnotation sourceFormed) program resources
    have tailAdapter : GeneralProfileAdapter env U registry target (AdapterNormal.profile raw) tail := by
      cases adapter with
      | cons _ _ rest => exact rest
    obtain ⟨tailFootprint, tailCode, tailAnnotation, tailResources, tailWorlds, tailDepth⟩ :=
      ih (ProfileView.typed_tail formed)
        (AdapterNormal.profile_sortable (ProfileView.typed_tail formed)) tailAdapter
    refine ⟨headFootprint ++ tailFootprint, .union headCode tailCode,
      .union headAnnotation tailAnnotation, ?_, ?_, ?_⟩
    · intro index need member
      exact (List.mem_append.mp member).elim (headResources index need) (tailResources index need)
    · intro world member
      exact (List.mem_append.mp member).elim (fun member => headWorlds member) (fun member => tailWorlds member)
    · intro policy
      simp only [RichCert.headDepth]
      exact Nat.max_le.mpr ⟨by
        simpa only [selected, RichCert.headDepth, RichObs.headDepth] using headDepth policy,
        tailDepth policy⟩

theorem RichGradedResult.code_worlds_depth
    (henv : env.Ordered)
    (result : RichGradedResult sourceEnv env U registry target node locals σ available requested)
    (annotation : WorldObsProvenance strata result.observation)
    (formed : requested.HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target node locals σ relevant requested footprint,
      ∃ output : WorldCertProvenance strata certificate,
        footprint.Available available ∧ output.worlds ⊆ annotation.worlds ∧
        ∀ policy, certificate.headDepth policy ≤ result.observation.headDepth policy := by
  obtain ⟨footprint, certificate, output, resources, worlds, depth⟩ :=
    result.observation.codeFromGeneral_worlds_depth henv annotation result.adapter
      (Profile.HasType.raise_sort result.bound formed) result.resources
  refine ⟨footprint, .observe (RichObs.code certificate).lowerRaised formed,
    .observe (.lowerRaised (.code output)) formed, resources, worlds, ?_⟩
  intro policy
  simp only [RichCert.headDepth]
  rw [RichObs.headDepth_lowerRaised]
  simpa only [RichObs.headDepth] using depth policy

theorem RichGradedResult.code_controlled
    {strata : EquationStratification env}
    (henv : env.Ordered)
    (result : RichGradedResult sourceEnv env U registry target node locals σ available requested)
    (controls : OriginalWorldControls strata controlSource)
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (ready : ControlledStoredQuery controls frontier (.observation result.observation))
    (formed : requested.HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target node locals σ relevant requested footprint,
      ∃ output : ControlledStoredQuery controls frontier (.certificate certificate),
        footprint.Available available ∧ output.annotation.worlds ⊆ ready.annotation.worlds := by
  obtain ⟨footprint, certificate, annotation, resources, worlds, depth⟩ :=
    result.code_worlds_depth henv ready.annotation formed
  refine ⟨footprint, certificate, ⟨annotation, ?_, ?_⟩, resources, worlds⟩
  · intro control active
    exact Nat.le_trans (depth _) (ready.within control active)
  · intro world member
    exact ready.sponsored world (worlds member)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
