import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedApplication
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionGrades

/-! Every finite code action produces rich source syntax at the same actual
original endpoint. Rank-changing leaves normalize at a common grade; each
output atom keeps its concrete input atom and finite action. Conjunction
computes the repeated finite resource footprint. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

noncomputable def RichCert.raise {n N : Nat} {profile : Profile n}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (bound : n ≤ N) :
    RichCert sourceEnv env U registry target node locals σ relevant (raiseProfile N bound profile) footprint := by
  induction N with
  | zero => have equal : n = 0 := by omega
            subst n; exact source
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simpa only [raiseProfile_self] using source
    · have previous : n ≤ N := by omega
      simpa only [raiseProfile_step previous] using RichCert.pad (ih previous)

noncomputable def RichCert.lowerRaised {n N : Nat} {profile : Profile n} (bound : n ≤ N)
    (source : RichCert sourceEnv env U registry target node locals σ relevant
      (raiseProfile N bound profile) footprint) :
    RichCert sourceEnv env U registry target node locals σ relevant profile footprint := by
  induction N with
  | zero => have equal : n = 0 := by omega
            subst n; exact source
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simpa only [raiseProfile_self] using source
    · have previous : n ≤ N := by omega
      rw [raiseProfile_step previous] at source
      exact ih previous (by simpa only [Profile.down_pad] using RichCert.down source)

theorem RichCert.nativeDepth_raise (current : Name → Bool)
    {n N : Nat} {profile : Profile n}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (bound : n ≤ N) : (source.raise bound).nativeDepth current = source.nativeDepth current := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simp only [RichCert.raise, dif_pos]
      exact RichCert.nativeDepth_mpr current rfl rfl (raiseProfile_self ..).symm rfl _ source
    · have previous : n ≤ N := by omega
      simp only [RichCert.raise, dif_neg equal]
      refine (RichCert.nativeDepth_mpr current rfl rfl
        (raiseProfile_step previous profile).symm rfl _ _).trans ?_
      change (RichCert.pad (source.raise previous)).nativeDepth current = _
      simpa only [RichCert.nativeDepth] using ih previous

theorem RichCert.nativeDepth_lowerRaised (current : Name → Bool)
    {n N : Nat} {profile : Profile n} (bound : n ≤ N)
    (source : RichCert sourceEnv env U registry target node locals σ relevant
      (raiseProfile N bound profile) footprint) :
    (source.lowerRaised bound).nativeDepth current = source.nativeDepth current := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simp only [RichCert.lowerRaised, dif_pos]
      exact RichCert.nativeDepth_mpr current rfl rfl (raiseProfile_self ..) rfl
        (congrArg (fun p => RichCert sourceEnv env U registry target node locals σ relevant p footprint)
          (raiseProfile_self profile).symm) source
    · have previous : n ≤ N := by omega
      simp only [RichCert.lowerRaised, dif_neg equal]
      let changed := (congrArg (fun p => RichCert sourceEnv env U registry target node locals σ relevant p footprint)
        (raiseProfile_step previous profile)).mp source
      let lowered : RichCert sourceEnv env U registry target node locals σ relevant
          (raiseProfile N previous profile) footprint := by
        simpa only [Profile.down_pad] using RichCert.down changed
      change (lowered.lowerRaised previous).nativeDepth current = _
      refine (ih previous lowered).trans ?_
      unfold lowered
      refine (RichCert.nativeDepth_mpr current rfl rfl (Profile.down_pad _)
        rfl (congrArg (fun p => RichCert sourceEnv env U registry target node locals σ relevant p footprint)
          (Profile.down_pad (raiseProfile N previous profile)).symm) changed.down).trans ?_
      simp only [RichCert.nativeDepth]
      exact RichCert.nativeDepth_mp current rfl rfl (raiseProfile_step previous profile) rfl _ source

private theorem actionFormation
    (action : SortableCodeAction env U registry target relevant profile next output)
    (formed : profile.HasType (.sort relevant)) : output.HasType (.sort next) := by
  induction action with
  | id => exact formed
  | retag target => exact target
  | comp first second firstIH secondIH => exact secondIH (firstIH formed)
  | union first second firstIH secondIH => exact (firstIH formed).union (secondIH formed)
  | support action => exact action.preservesSort formed
  | pad => exact formed.pad_sort
  | down => simpa only [Profile.down_sort] using formed.down
  | unpad => simpa only [Profile.down_sort] using formed.pad_inv
  | sortPad => exact formed.sortPad
  | familyPad => exact formed.familyPad
  | map view => exact view.mapType_sort formed
  | select member => exact formed.singleton_of_mem member
  | focusMinimal minimal bound => exact formed.restrict bound minimal.formation.wf_value

/-- An action's exact output singleton is reconstructed with the unchanged
source footprint, even when its source and destination ranks differ. -/
theorem RichCert.codeActionAtom_nativeDepth
    {profile : Profile n} {output : Profile m} {atom : Atom m}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (member : atom ∈ output.atoms) :
    ∃ result : RichCert sourceEnv env U registry target node locals σ next (.singleton atom) footprint,
      ∀ current, result.nativeDepth current = source.nativeDepth current := by
  obtain ⟨original, originalMember, ⟨selected⟩⟩ := action.atom member
  let N := max n m
  have hn : n ≤ N := Nat.le_max_left _ _
  have hm : m ≤ N := Nat.le_max_right _ _
  have high : ∃ raised : RichCert sourceEnv env U registry target node locals σ relevant
      (raiseProfile N hn (.singleton original)) footprint,
      ∀ current, raised.nativeDepth current = source.nativeDepth current := by
    refine ⟨(RichCert.select source originalMember).raise hn, ?_⟩
    intro current
    simpa only [RichCert.nativeDepth] using (RichCert.select source originalMember).nativeDepth_raise current hn
  rw [raiseProfile_singleton] at high
  obtain ⟨raised, raisedDepth⟩ := high
  have selectedHigh := selected.atomAtGrade hn hm
  let changed := RichObs.action (RichObs.code raised) (AtomAction.code selectedHigh raised.formed)
  have formed := (actionFormation action source.formed).singleton_of_mem member
  have highFormed := (SortableCodeAction.raiseTo (env := env) (U := U)
    (registry := registry) (target := target) (relevant := next) hm).preservesSort formed
  rw [raiseProfile_singleton] at highFormed
  have highResult : ∃ result : RichCert sourceEnv env U registry target node locals σ next
      (raiseProfile N hm (.singleton atom)) footprint,
      ∀ current, result.nativeDepth current = source.nativeDepth current := by
    rw [raiseProfile_singleton]
    refine ⟨RichCert.observe changed highFormed, ?_⟩
    intro current
    simpa only [changed, RichCert.nativeDepth, RichObs.nativeDepth] using raisedDepth current
  obtain ⟨result, resultDepth⟩ := highResult
  exact ⟨result.lowerRaised hm, fun current => (result.nativeDepth_lowerRaised current hm).trans (resultDepth current)⟩

theorem RichCert.codeActionAtom
    {profile : Profile n} {output : Profile m} {atom : Atom m}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (member : atom ∈ output.atoms) :
    Nonempty (RichCert sourceEnv env U registry target node locals σ next (.singleton atom) footprint) := by
  obtain ⟨result, _⟩ := source.codeActionAtom_nativeDepth action member
  exact ⟨result⟩

/-- Full code output construction: only actual source atoms are selected,
and every newly repeated leaf remains available in the incoming valuation. -/
theorem RichCert.codeAction_nativeDepth
    {profile : Profile n} {output : Profile m}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (resources : footprint.Available available) :
    ∃ resultFootprint, ∃ result : RichCert sourceEnv env U registry target node locals σ next output resultFootprint,
      resultFootprint.Available available ∧ ∀ current, result.nativeDepth current ≤ source.nativeDepth current := by
  have each : ∀ atom ∈ output.atoms,
      ∃ result : RichCert sourceEnv env U registry target node locals σ next (.singleton atom) footprint,
        ∀ current, result.nativeDepth current = source.nativeDepth current :=
    fun atom member => source.codeActionAtom_nativeDepth action member
  suffices build : ∀ atoms : List (Atom m),
      (∀ atom ∈ atoms, ∃ result : RichCert sourceEnv env U registry target node locals σ next (.singleton atom) footprint,
        ∀ current, result.nativeDepth current = source.nativeDepth current) →
      ∃ resultFootprint, ∃ result : RichCert sourceEnv env U registry target node locals σ next (.mk atoms) resultFootprint,
        resultFootprint.Available available ∧ (∀ current, result.nativeDepth current ≤ source.nativeDepth current)
        from build output.atoms each
  intro atoms
  induction atoms with
  | nil =>
    intro _
    exact ⟨[], .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort next))),
      (fun _ _ member => by cases member), fun _ => by
        simp only [RichCert.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth]
        exact Nat.zero_le _⟩
  | cons atom rest ih =>
    intro each
    obtain ⟨head, headDepth⟩ := each atom (by simp)
    obtain ⟨tailFootprint, tail, tailResources, tailDepth⟩ := ih (fun a h => each a (by simp [h]))
    refine ⟨footprint ++ tailFootprint, RichCert.union head tail, ?_, ?_⟩
    · intro index need member
      exact (List.mem_append.mp member).elim (resources index need) (tailResources index need)
    · intro current
      simp only [RichCert.nativeDepth, headDepth current]
      exact Nat.max_le.mpr ⟨Nat.le_refl _, tailDepth current⟩

theorem RichCert.codeAction
    {profile : Profile n} {output : Profile m}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (resources : footprint.Available available) :
    ∃ resultFootprint, Nonempty (RichCert sourceEnv env U registry target node locals σ next output resultFootprint) ∧
      resultFootprint.Available available := by
  obtain ⟨footprint, result, resources, _⟩ := source.codeAction_nativeDepth action resources
  exact ⟨footprint, ⟨result⟩, resources⟩

/-- General adapters retract an actual rich computational query to the
requested code profile. Selection retains the whole available footprint,
so no legacy atom-pruning or erasure of projection metadata is needed. -/
theorem RichObs.codeFromGeneral_nativeDepth
    (henv : env.Ordered) {raw requested : Profile n}
    (observation : RichObs sourceEnv env U registry target node locals σ raw footprint)
    (adapter : GeneralNormalProfileAdapter env U registry target raw requested)
    (formed : requested.HasType (.sort relevant))
    (resources : footprint.Available available) :
    ∃ nextFootprint,
      ∃ certificate : RichCert sourceEnv env U registry target node locals σ relevant requested nextFootprint,
      nextFootprint.Available available ∧
      ∀ current, certificate.nativeDepth current ≤ observation.nativeDepth current := by
  have canonical : AdapterNormal.profile requested = requested := AdapterNormal.profile_sortable formed
  change GeneralProfileAdapter env U registry target (AdapterNormal.profile raw)
    (AdapterNormal.profile requested) at adapter
  rw [canonical] at adapter
  induction requested with
  | nil =>
    exact ⟨[], .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort relevant))),
      (fun _ _ member => by cases member), fun _ => by
        simp only [RichCert.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth]
        exact Nat.zero_le _⟩
  | cons head tail ih =>
    obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin List.mem_cons_self
    obtain ⟨original, originalMember, normalEq⟩ := List.mem_map.mp member
    subst normal
    obtain ⟨flag, sourceFormed, ⟨program⟩⟩ :=
      entry.toCodeAtOutput (formed.singleton_of_mem List.mem_cons_self)
    let selected := RichObs.view (RichObs.select observation originalMember) (AdapterNormal.view henv original)
    obtain ⟨headFootprint, headCode, headResources, headDepth⟩ :=
      (RichCert.observe selected sourceFormed).codeAction_nativeDepth program resources
    have tailAdapter : GeneralProfileAdapter env U registry target (AdapterNormal.profile raw) tail := by
      cases adapter with
      | cons _ _ rest => exact rest
    obtain ⟨tailFootprint, tailCode, tailResources, tailDepth⟩ :=
      ih (ProfileView.typed_tail formed)
        (AdapterNormal.profile_sortable (ProfileView.typed_tail formed)) tailAdapter
    refine ⟨headFootprint ++ tailFootprint, .union headCode tailCode, ?_, ?_⟩
    · intro index need member
      exact (List.mem_append.mp member).elim (headResources index need) (tailResources index need)
    · intro current
      simp only [RichCert.nativeDepth]
      exact Nat.max_le.mpr ⟨by
        simpa only [selected, RichCert.nativeDepth, RichObs.nativeDepth] using headDepth current,
        tailDepth current⟩

theorem RichObs.codeFromGeneral
    (henv : env.Ordered) {raw requested : Profile n}
    (observation : RichObs sourceEnv env U registry target node locals σ raw footprint)
    (adapter : GeneralNormalProfileAdapter env U registry target raw requested)
    (formed : requested.HasType (.sort relevant))
    (resources : footprint.Available available) :
    ∃ nextFootprint,
      Nonempty (RichCert sourceEnv env U registry target node locals σ relevant requested nextFootprint) ∧
      nextFootprint.Available available := by
  obtain ⟨footprint, result, resources, _⟩ := observation.codeFromGeneral_nativeDepth henv adapter formed resources
  exact ⟨footprint, ⟨result⟩, resources⟩

/-- Recover exact formation syntax from a concrete generalized application
result, including native projected leaves under the returned source query. -/
theorem RichGradedResult.code_nativeDepth
    (henv : env.Ordered)
    (result : RichGradedResult sourceEnv env U registry target node locals σ available requested)
    (formed : requested.HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target node locals σ relevant requested footprint,
      footprint.Available available ∧
      ∀ current, certificate.nativeDepth current ≤ result.observation.nativeDepth current := by
  obtain ⟨footprint, certificate, resources, depth⟩ :=
    result.observation.codeFromGeneral_nativeDepth henv result.adapter
      (Profile.HasType.raise_sort result.bound formed) result.resources
  refine ⟨footprint, certificate.lowerRaised result.bound, resources, ?_⟩
  intro current
  rw [RichCert.nativeDepth_lowerRaised]
  exact depth current

theorem RichGradedResult.code
    (henv : env.Ordered)
    (result : RichGradedResult sourceEnv env U registry target node locals σ available requested)
    (formed : requested.HasType (.sort relevant)) :
    ∃ footprint, Nonempty (RichCert sourceEnv env U registry target node locals σ relevant requested footprint) ∧
      footprint.Available available := by
  obtain ⟨footprint, certificate, resources, _⟩ := result.code_nativeDepth henv formed
  exact ⟨footprint, ⟨certificate⟩, resources⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
