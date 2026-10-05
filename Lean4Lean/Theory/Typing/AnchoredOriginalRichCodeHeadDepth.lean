import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth

/-! Finite code reconstruction preserves arbitrary named-head policies on
its actual output witness. This includes stratified masking policies. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private actionFormation from Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

@[simp] theorem RichObs.headDepth_mp (current : Name → Nat → Nat)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : RichObs sourceEnv env U registry target node ls σ p f = RichObs sourceEnv env U registry target node ms τ q g)
    (query : RichObs sourceEnv env U registry target node ls σ p f) :
    (equal.mp query).headDepth current = query.headDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem RichObs.headDepth_mpr (current : Name → Nat → Nat)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : RichObs sourceEnv env U registry target node ms τ q g = RichObs sourceEnv env U registry target node ls σ p f)
    (query : RichObs sourceEnv env U registry target node ls σ p f) :
    (equal.mpr query).headDepth current = query.headDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem RichCert.headDepth_mp (current : Name → Nat → Nat)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : RichCert sourceEnv env U registry target node ls σ relevant p f = RichCert sourceEnv env U registry target node ms τ relevant q g)
    (query : RichCert sourceEnv env U registry target node ls σ relevant p f) :
    (equal.mp query).headDepth current = query.headDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem RichCert.headDepth_mpr (current : Name → Nat → Nat)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : RichCert sourceEnv env U registry target node ms τ relevant q g = RichCert sourceEnv env U registry target node ls σ relevant p f)
    (query : RichCert sourceEnv env U registry target node ls σ relevant p f) :
    (equal.mpr query).headDepth current = query.headDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl


theorem RichObs.headDepth_raise (current : Name → Nat → Nat)
    {n N : Nat} {profile : Profile n}
    (source : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (bound : n ≤ N) : (source.raise bound).headDepth current = source.headDepth current := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simp only [RichObs.raise, dif_pos]
      exact RichObs.headDepth_mpr current rfl rfl (raiseProfile_self ..).symm rfl _ source
    · have previous : n ≤ N := by omega
      simp only [RichObs.raise, dif_neg equal]
      refine (RichObs.headDepth_mpr current rfl rfl
        (raiseProfile_step previous profile).symm rfl _ _).trans ?_
      change (RichObs.pad (source.raise previous)).headDepth current = _
      simpa only [RichObs.headDepth] using ih previous


theorem RichCert.headDepth_raise (current : Name → Nat → Nat)
    {n N : Nat} {profile : Profile n}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (bound : n ≤ N) : (source.raise bound).headDepth current = source.headDepth current := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simp only [RichCert.raise, dif_pos]
      exact RichCert.headDepth_mpr current rfl rfl (raiseProfile_self ..).symm rfl _ source
    · have previous : n ≤ N := by omega
      simp only [RichCert.raise, dif_neg equal]
      refine (RichCert.headDepth_mpr current rfl rfl
        (raiseProfile_step previous profile).symm rfl _ _).trans ?_
      change (RichCert.pad (source.raise previous)).headDepth current = _
      simpa only [RichCert.headDepth] using ih previous

theorem RichCert.headDepth_lowerRaised (current : Name → Nat → Nat)
    {n N : Nat} {profile : Profile n} (bound : n ≤ N)
    (source : RichCert sourceEnv env U registry target node locals σ relevant
      (raiseProfile N bound profile) footprint) :
    (source.lowerRaised bound).headDepth current = source.headDepth current := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simp only [RichCert.lowerRaised, dif_pos]
      exact RichCert.headDepth_mpr current rfl rfl (raiseProfile_self ..) rfl
        (congrArg (fun p => RichCert sourceEnv env U registry target node locals σ relevant p footprint)
          (raiseProfile_self profile).symm) source
    · have previous : n ≤ N := by omega
      simp only [RichCert.lowerRaised, dif_neg equal]
      let changed := (congrArg (fun p => RichCert sourceEnv env U registry target node locals σ relevant p footprint)
        (raiseProfile_step previous profile)).mp source
      let lowered : RichCert sourceEnv env U registry target node locals σ relevant
          (raiseProfile N previous profile) footprint := by
        simpa only [Profile.down_pad] using RichCert.down changed
      change (lowered.lowerRaised previous).headDepth current = _
      refine (ih previous lowered).trans ?_
      unfold lowered
      refine (RichCert.headDepth_mpr current rfl rfl (Profile.down_pad _)
        rfl (congrArg (fun p => RichCert sourceEnv env U registry target node locals σ relevant p footprint)
          (Profile.down_pad (raiseProfile N previous profile)).symm) changed.down).trans ?_
      simp only [RichCert.headDepth]
      exact RichCert.headDepth_mp current rfl rfl (raiseProfile_step previous profile) rfl _ source


theorem RichCert.codeActionAtom_headDepth
    {profile : Profile n} {output : Profile m} {atom : Atom m}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (member : atom ∈ output.atoms) :
    ∃ result : RichCert sourceEnv env U registry target node locals σ next (.singleton atom) footprint,
      ∀ current, result.headDepth current = source.headDepth current := by
  obtain ⟨original, originalMember, ⟨selected⟩⟩ := action.atom member
  let N := max n m
  have hn : n ≤ N := Nat.le_max_left _ _
  have hm : m ≤ N := Nat.le_max_right _ _
  have high : ∃ raised : RichCert sourceEnv env U registry target node locals σ relevant
      (raiseProfile N hn (.singleton original)) footprint,
      ∀ current, raised.headDepth current = source.headDepth current := by
    refine ⟨(RichCert.select source originalMember).raise hn, ?_⟩
    intro current
    simpa only [RichCert.headDepth] using (RichCert.select source originalMember).headDepth_raise current hn
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
      ∀ current, result.headDepth current = source.headDepth current := by
    rw [raiseProfile_singleton]
    refine ⟨RichCert.observe changed highFormed, ?_⟩
    intro current
    simpa only [changed, RichCert.headDepth, RichObs.headDepth] using raisedDepth current
  obtain ⟨result, resultDepth⟩ := highResult
  exact ⟨result.lowerRaised hm, fun current => (result.headDepth_lowerRaised current hm).trans (resultDepth current)⟩


theorem RichCert.codeAction_headDepth
    {profile : Profile n} {output : Profile m}
    (source : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (resources : footprint.Available available) :
    ∃ resultFootprint, ∃ result : RichCert sourceEnv env U registry target node locals σ next output resultFootprint,
      resultFootprint.Available available ∧ ∀ current, result.headDepth current ≤ source.headDepth current := by
  have each : ∀ atom ∈ output.atoms,
      ∃ result : RichCert sourceEnv env U registry target node locals σ next (.singleton atom) footprint,
        ∀ current, result.headDepth current = source.headDepth current :=
    fun atom member => source.codeActionAtom_headDepth action member
  suffices build : ∀ atoms : List (Atom m),
      (∀ atom ∈ atoms, ∃ result : RichCert sourceEnv env U registry target node locals σ next (.singleton atom) footprint,
        ∀ current, result.headDepth current = source.headDepth current) →
      ∃ resultFootprint, ∃ result : RichCert sourceEnv env U registry target node locals σ next (.mk atoms) resultFootprint,
        resultFootprint.Available available ∧ (∀ current, result.headDepth current ≤ source.headDepth current)
        from build output.atoms each
  intro atoms
  induction atoms with
  | nil =>
    intro _
    exact ⟨[], .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort next))),
      (fun _ _ member => by cases member), fun _ => by
        simp only [RichCert.headDepth, SortableCert.headDepth, Obs.headDepth]
        exact Nat.zero_le _⟩
  | cons atom rest ih =>
    intro each
    obtain ⟨head, headDepth⟩ := each atom (by simp)
    obtain ⟨tailFootprint, tail, tailResources, tailDepth⟩ := ih (fun a h => each a (by simp [h]))
    refine ⟨footprint ++ tailFootprint, RichCert.union head tail, ?_, ?_⟩
    · intro index need member
      exact (List.mem_append.mp member).elim (resources index need) (tailResources index need)
    · intro current
      simp only [RichCert.headDepth, headDepth current]
      exact Nat.max_le.mpr ⟨Nat.le_refl _, tailDepth current⟩


theorem RichObs.codeFromGeneral_headDepth
    (henv : env.Ordered) {raw requested : Profile n}
    (observation : RichObs sourceEnv env U registry target node locals σ raw footprint)
    (adapter : GeneralNormalProfileAdapter env U registry target raw requested)
    (formed : requested.HasType (.sort relevant))
    (resources : footprint.Available available) :
    ∃ nextFootprint,
      ∃ certificate : RichCert sourceEnv env U registry target node locals σ relevant requested nextFootprint,
      nextFootprint.Available available ∧
      ∀ current, certificate.headDepth current ≤ observation.headDepth current := by
  have canonical : AdapterNormal.profile requested = requested := AdapterNormal.profile_sortable formed
  change GeneralProfileAdapter env U registry target (AdapterNormal.profile raw)
    (AdapterNormal.profile requested) at adapter
  rw [canonical] at adapter
  induction requested with
  | nil =>
    exact ⟨[], .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort relevant))),
      (fun _ _ member => by cases member), fun _ => by
        simp only [RichCert.headDepth, SortableCert.headDepth, Obs.headDepth]
        exact Nat.zero_le _⟩
  | cons head tail ih =>
    obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin List.mem_cons_self
    obtain ⟨original, originalMember, normalEq⟩ := List.mem_map.mp member
    subst normal
    obtain ⟨flag, sourceFormed, ⟨program⟩⟩ :=
      entry.toCodeAtOutput (formed.singleton_of_mem List.mem_cons_self)
    let selected := RichObs.view (RichObs.select observation originalMember) (AdapterNormal.view henv original)
    obtain ⟨headFootprint, headCode, headResources, headDepth⟩ :=
      (RichCert.observe selected sourceFormed).codeAction_headDepth program resources
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
      simp only [RichCert.headDepth]
      exact Nat.max_le.mpr ⟨by
        simpa only [selected, RichCert.headDepth, RichObs.headDepth] using headDepth current,
        tailDepth current⟩


theorem RichGradedResult.code_headDepth
    (henv : env.Ordered)
    (result : RichGradedResult sourceEnv env U registry target node locals σ available requested)
    (formed : requested.HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target node locals σ relevant requested footprint,
      footprint.Available available ∧
      ∀ current, certificate.headDepth current ≤ result.observation.headDepth current := by
  obtain ⟨footprint, certificate, resources, depth⟩ :=
    result.observation.codeFromGeneral_headDepth henv result.adapter
      (Profile.HasType.raise_sort result.bound formed) result.resources
  refine ⟨footprint, certificate.lowerRaised result.bound, resources, ?_⟩
  intro current
  rw [RichCert.headDepth_lowerRaised]
  exact depth current


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
