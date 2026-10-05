import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedLambda

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

private def RecordShape : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .record _ => True
  | _ + 1, .pad atom => RecordShape atom
  | _, _ => False

private theorem RecordShape.not_sortable {atom : Atom n}
    (shape : RecordShape atom) (formed : (Profile.singleton atom).HasType (.sort relevant)) : False := by
  induction n with
  | zero => exact shape
  | succ n ih =>
    cases atom with
    | sort | pi | family | ctor | fn => exact shape
    | record data =>
      obtain ⟨cover, member, typed⟩ := formed.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp member
      contradiction
    | pad atom =>
      change (Profile.singleton atom).pad.HasType (.sort relevant) at formed
      have lower := formed.pad_inv
      simp only [Profile.down_sort] at lower
      exact ih shape lower

private theorem recordAdapter_rigid {a b : Atom n}
    (adapter : GeneralAtomAdapter env U registry Γ a b) (shape : RecordShape b) : a = b := by
  cases adapter with
  | refl => rfl
  | fn => exact shape.elim
  | pad child => exact congrArg AtomData.pad (recordAdapter_rigid child shape)
  | code action formed => exact (shape.not_sortable (action.preservesSort formed)).elim
termination_by n

private theorem recordShape_raise (record : RecordData (Profile n)) (bound : n + 1 ≤ N) :
    RecordShape (raiseAtom N bound (.record record)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases same : n + 1 = N + 1
    · cases same
      simp only [raiseAtom_self, RecordShape]
    · have previous : n + 1 ≤ N := by omega
      rw [raiseAtom_step previous]
      exact ih previous

private theorem recordShape_normal {a : Atom n} (shape : RecordShape a) : AdapterNormal.atom a = a := by
  induction n with
  | zero => exact shape.elim
  | succ n ih =>
    cases a with
    | record => rfl
    | pad a =>
      change AdapterNormal.shiftAtom (AdapterNormal.atom a) = .pad a
      rw [ih shape]
      cases n with
      | zero => exact shape.elim
      | succ n => cases a <;> simp_all [RecordShape, AdapterNormal.shiftAtom]
    | _ => exact shape.elim

noncomputable def RichObs.lowerRaised
    {n N : Nat} {profile : Profile n} {bound : n ≤ N}
    (observation : RichObs sourceEnv env U registry Γ node locals σ
      (raiseProfile N bound profile) footprint) :
    RichObs sourceEnv env U registry Γ node locals σ profile footprint := by
  induction N with
  | zero => have equal : n = 0 := by omega
            subst n; exact observation
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simpa only [raiseProfile_self] using observation
    · have previous : n ≤ N := by omega
      rw [raiseProfile_step previous] at observation
      exact ih (.unpad observation)

@[simp] theorem RichObs.nativeDepth_lowerRaised (current : Name → Bool)
    {n N : Nat} {profile : Profile n} {bound : n ≤ N}
    (source : RichObs sourceEnv env U registry Γ node locals σ (raiseProfile N bound profile) footprint) :
    source.lowerRaised.nativeDepth current = source.nativeDepth current := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simp only [RichObs.lowerRaised, dif_pos]
      exact RichObs.nativeDepth_mpr current rfl rfl (raiseProfile_self ..) rfl
        (congrArg (fun p => RichObs sourceEnv env U registry Γ node locals σ p footprint)
          (raiseProfile_self profile).symm) source
    · have previous : n ≤ N := by omega
      simp only [RichObs.lowerRaised, dif_neg equal]
      let changed := (congrArg (fun p => RichObs sourceEnv env U registry Γ node locals σ p footprint)
        (raiseProfile_step previous profile)).mp source
      change (RichObs.unpad changed).lowerRaised.nativeDepth current = _
      refine (ih (source := .unpad changed)).trans ?_
      simp only [RichObs.nativeDepth]
      exact RichObs.nativeDepth_mp current rfl rfl (raiseProfile_step previous profile) rfl _ source

/-- A generalized computational answer at a record demand yields an exact
source record observer. No inverse code support or stronger R answer is used. -/
theorem RichGradedResult.recordObservation_nativeDepth
    (henv : env.Ordered)
    (result : RichGradedResult sourceEnv env U registry Γ node locals σ available
      (Profile.singleton (n := n + 1) (.record (record : RecordData (Profile n))))) :
    ∃ footprint, ∃ observation : RichObs sourceEnv env U registry Γ node locals σ
      (Profile.singleton (n := n + 1) (.record record)) footprint, footprint.Available available ∧
      ∀ current, observation.nativeDepth current = result.observation.nativeDepth current := by
  have adapter := result.adapter
  rw [raiseProfile_singleton] at adapter
  have shape := recordShape_raise record result.bound
  have normalized := recordShape_normal shape
  change GeneralProfileAdapter env U registry Γ _ (.singleton (AdapterNormal.atom _)) at adapter
  rw [normalized] at adapter
  obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
  subst normal
  have same := recordAdapter_rigid entry shape
  let selected := RichObs.view (.select result.observation originalMember) (AdapterNormal.view henv original)
  have outputEq : Profile.singleton (AdapterNormal.atom original) =
      raiseProfile result.rank result.bound (Profile.singleton (n := n + 1) (.record record)) := by
    simp only [raiseProfile_singleton, same]
  let observed : RichObs sourceEnv env U registry Γ node locals σ
      (raiseProfile result.rank result.bound (Profile.singleton (n := n + 1) (.record record))) result.footprint :=
    (congrArg (fun profile => RichObs sourceEnv env U registry Γ node locals σ profile result.footprint) outputEq).mp selected
  refine ⟨result.footprint, observed.lowerRaised, result.resources, ?_⟩
  intro current
  rw [RichObs.nativeDepth_lowerRaised]
  exact (RichObs.nativeDepth_mp current rfl rfl outputEq rfl _ selected).trans
    (by simp only [selected, RichObs.nativeDepth])


/-- Compatibility projection of the same bounded extraction. -/
theorem RichGradedResult.recordObservation
    (henv : env.Ordered)
    (result : RichGradedResult sourceEnv env U registry Γ node locals σ available
      (Profile.singleton (n := n + 1) (.record (record : RecordData (Profile n))))) :
    ∃ footprint, Nonempty (RichObs sourceEnv env U registry Γ node locals σ
      (Profile.singleton (n := n + 1) (.record record)) footprint) ∧ footprint.Available available := by
  obtain ⟨footprint, observation, resources, _⟩ := result.recordObservation_nativeDepth henv
  exact ⟨footprint, ⟨observation⟩, resources⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
