import Lean4Lean.Theory.Typing.AnchoredViews

/-! Intrinsic typing for the computed support action of a concrete atomic
view. Matching function rows are copied with their changed key or output;
all old rows remain. Explicit padding uses the proved intrinsic projection.
-/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem reanchorTypes.wf {oldKey newKey : Key n} {profile : Profile (n + 1)}
    (hinput : newKey.input = oldKey.input) (H : profile.WF) :
    (reanchorTypes oldKey newKey profile).WF := by
  intro atom hmem
  obtain ⟨oldAtom, hsource, rfl⟩ := List.mem_map.mp hmem
  have hw := H oldAtom hsource
  cases oldAtom with
  | sort | fn | pad | family | ctor | record => exact hw
  | pi A B domain rows =>
    refine ⟨hw.1, ?_⟩
    intro key output hm
    rcases mem_reanchorRows.mp hm with h | ⟨rfl, h⟩
    · exact hw.2 key output h
    · exact ⟨hinput ▸ (hw.2 oldKey output h).1, (hw.2 oldKey output h).2⟩

theorem reanchorTypes.sort {oldKey newKey : Key n} {profile : Profile (n + 1)}
    (hinput : newKey.input = oldKey.input) (H : profile.HasType (.sort relevant)) :
    (reanchorTypes oldKey newKey profile).HasType (.sort relevant) := by
  refine ⟨reanchorTypes.wf hinput H.wf_value, H.wf_type, ?_⟩
  intro atom hmem
  obtain ⟨oldAtom, hsource, rfl⟩ := List.mem_map.mp hmem
  obtain ⟨cover, hc, ht⟩ := H.2.2 oldAtom hsource
  have heq : cover = .sort relevant := List.mem_singleton.mp hc
  subst cover
  refine ⟨.sort relevant, List.mem_singleton_self _, ?_⟩
  cases oldAtom with
  | sort | fn | pad | family | ctor | record => exact ht
  | pi A B domain rows =>
    intro key output hm
    rcases mem_reanchorRows.mp hm with h | ⟨rfl, h⟩
    · exact ht key output h
    · exact ht oldKey output h

private theorem outputTypes_wf {key : Key n} {map : Profile n → Profile n}
    (preserves : ∀ profile, profile.WF → (map profile).WF)
    {profile : Profile (n + 1)} (H : profile.WF) : (outputTypes key map profile).WF := by
  intro atom hmem
  obtain ⟨oldAtom, hsource, rfl⟩ := List.mem_map.mp hmem
  have hw := H oldAtom hsource
  cases oldAtom with
  | sort | fn | pad | family | ctor | record => exact hw
  | pi A B domain rows =>
    refine ⟨hw.1, ?_⟩
    intro other output hm
    rcases mem_outputRows.mp hm with h | ⟨rfl, oldOutput, hrow, rfl⟩
    · exact hw.2 other output h
    · exact ⟨(hw.2 other oldOutput hrow).1, preserves _ (hw.2 other oldOutput hrow).2⟩

private theorem outputTypes_sort {key : Key n} {map : Profile n → Profile n}
    (preservesWF : ∀ profile, profile.WF → (map profile).WF)
    (preservesSort : ∀ profile relevant,
      profile.HasType (.sort relevant) → (map profile).HasType (.sort relevant))
    {profile : Profile (n + 1)} (H : profile.HasType (.sort relevant)) :
    (outputTypes key map profile).HasType (.sort relevant) := by
  refine ⟨outputTypes_wf preservesWF H.wf_value, H.wf_type, ?_⟩
  intro atom hmem
  obtain ⟨oldAtom, hsource, rfl⟩ := List.mem_map.mp hmem
  obtain ⟨cover, hc, ht⟩ := H.2.2 oldAtom hsource
  have heq : cover = .sort relevant := List.mem_singleton.mp hc
  subst cover
  refine ⟨.sort relevant, List.mem_singleton_self _, ?_⟩
  cases oldAtom with
  | sort | fn | pad | family | ctor | record => exact ht
  | pi A B domain rows =>
    intro other output hm
    rcases mem_outputRows.mp hm with h | ⟨rfl, oldOutput, hrow, rfl⟩
    · exact ht other output h
    · exact preservesSort _ relevant (ht other oldOutput hrow)

theorem reanchorTypes.typed {oldKey newKey : Key n} {output : Atom n}
    {profile : Profile (n + 1)} (hinput : newKey.input = oldKey.input)
    (H : (Profile.fn oldKey output).HasType profile) :
    (Profile.fn newKey output).HasType (reanchorTypes oldKey newKey profile) := by
  obtain ⟨A, B, domain, rows, result, hpi, hw, _, _, hrow, ht⟩ :=
    H.fn_inv (List.mem_singleton_self _)
  have hp := reanchorTypes.wf hinput hw
  change (Profile.pi A B domain (reanchorRows oldKey newKey rows)).WF at hp
  have hnew := Profile.HasType.fn hp (reanchorRows.changed hrow) ht
  apply hnew.enlarge ?_ (reanchorTypes.wf hinput H.wf_type)
  intro atom hm
  cases List.mem_singleton.mp hm
  exact Profile.le_refl (reanchorTypes oldKey newKey profile) _
    (List.mem_map.mpr ⟨.pi A B domain rows, hpi, rfl⟩)

private theorem outputTypes_typed {key : Key n} {output output' : Atom n}
    {map : Profile n → Profile n}
    (preservesWF : ∀ profile, profile.WF → (map profile).WF)
    (preservesType : ∀ profile, (Profile.singleton output).HasType profile →
      (Profile.singleton output').HasType (map profile))
    {profile : Profile (n + 1)} (H : (Profile.fn key output).HasType profile) :
    (Profile.fn key output').HasType (outputTypes key map profile) := by
  obtain ⟨A, B, domain, rows, result, hpi, hw, _, _, hrow, ht⟩ :=
    H.fn_inv (List.mem_singleton_self _)
  have hp := outputTypes_wf (key := key) preservesWF hw
  change (Profile.pi A B domain (outputRows key map rows)).WF at hp
  have hnew := Profile.HasType.fn hp (outputRows.changed hrow) (preservesType result ht)
  apply hnew.enlarge ?_ (outputTypes_wf preservesWF H.wf_type)
  intro atom hm
  cases List.mem_singleton.mp hm
  exact Profile.le_refl (outputTypes key map profile) _
    (List.mem_map.mpr ⟨.pi A B domain rows, hpi, rfl⟩)

theorem ProfileView.typed_tail {a : Atom n} {rest profile : Profile n}
    (h : Profile.HasType (a :: rest) profile) : rest.HasType profile := by
  cases n with
  | zero => exact fun atom hm => h atom (List.mem_cons_of_mem _ hm)
  | succ n => exact ⟨fun atom hm => h.1 atom (List.mem_cons_of_mem _ hm),
      h.2.1, fun atom hm => h.2.2 atom (List.mem_cons_of_mem _ hm)⟩

mutual
private theorem AtomView.typing
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {a b : Atom n} (view : AtomView env U registry Γ a b) :
    (∀ profile, profile.WF → (view.mapType profile).WF) ∧
    (∀ profile relevant, profile.HasType (.sort relevant) →
      (view.mapType profile).HasType (.sort relevant)) ∧
    (∀ profile, (Profile.singleton a).HasType profile →
      (Profile.singleton b).HasType (view.mapType profile)) := by
  match n, a, b, view with
  | _, _, _, .refl _ => exact ⟨fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  | _ + 1, _, _, .reanchor admitted =>
    exact ⟨fun _ h => reanchorTypes.wf rfl h,
      fun _ _ h => reanchorTypes.sort rfl h,
      fun _ h => reanchorTypes.typed rfl h⟩
  | _ + 1, _, _, .domainRekey path typed formation bridge =>
    exact ⟨fun _ h => domainRekeyTypes.wf h,
      fun _ _ h => domainRekeyTypes.sort h,
      fun _ h => domainRekeyTypes.typed h⟩
  | _ + 1, _, _, .input forward backward =>
    have ih := backward.typing
    exact ⟨fun _ h => inputTypes.wf (fun d => ih.2.1 d true) ih.2.2 h,
      fun _ _ h => inputTypes.sort (fun d => ih.2.1 d true) ih.2.2 h,
      fun _ h => inputTypes.typed (fun d => ih.2.1 d true) ih.2.2 h⟩
  | _ + 2, _, _, .commutePadFn key output =>
    refine ⟨fun _ h => h.down.rankShift, ?_, ?_⟩
    · intro profile relevant h
      have hd : profile.down.HasType (.sort relevant) := by
        simpa only [Profile.down_sort] using h.down
      exact hd.rankShift_sort
    · intro profile h
      change (Profile.fn key output).pad.HasType profile at h
      exact (Profile.HasType.pad_inv h).rankShiftFn
  | _ + 2, _, _, .uncommutePadFn key output =>
    refine ⟨fun _ h => (h.unshift key).pad,
      fun _ _ h => (h.unshift_sort key).pad_sort, ?_⟩
    intro profile h
    exact h.unshiftFn.pad
  | _ + 1, _, _, .fn key view =>
    have ih := view.typing
    exact ⟨fun _ h => outputTypes_wf ih.1 h,
      fun _ _ h => outputTypes_sort ih.1 ih.2.1 h,
      fun _ h => outputTypes_typed ih.1 ih.2.2 h⟩
  | _ + 1, _, _, .pad view =>
    have ih := view.typing
    refine ⟨fun _ h => (ih.1 _ h.down).pad, ?_, ?_⟩
    · intro profile relevant h
      have hd : profile.down.HasType (.sort relevant) := by
        simpa only [Profile.down_sort] using h.down
      exact (ih.2.1 _ relevant hd).pad_sort
    · intro profile h
      have ht := ih.2.2 profile.down (show (Profile.singleton _).HasType profile.down from
        Profile.HasType.pad_inv h)
      exact ht.pad
  | _, _, _, .trans first second =>
    have ihfirst := first.typing
    have ihsecond := second.typing
    exact ⟨fun _ h => ihsecond.1 _ (ihfirst.1 _ h),
      fun _ _ h => ihsecond.2.1 _ _ (ihfirst.2.1 _ _ h),
      fun _ h => ihsecond.2.2 _ (ihfirst.2.2 _ h)⟩

termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

private theorem ProfileView.typing
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {source target : Profile n} (view : ProfileView env U registry Γ source target) :
    (∀ profile, profile.WF → (view.mapType profile).WF) ∧
    (∀ profile relevant, profile.HasType (.sort relevant) →
      (view.mapType profile).HasType (.sort relevant)) ∧
    (∀ profile, source.HasType profile → target.HasType (view.mapType profile)) := by
  match source, target, view with
  | _, _, .nil => exact ⟨fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  | _, _, .cons head tail =>
    have ihhead := head.typing
    have ihtail := tail.typing
    exact ⟨fun d h => (ihhead.1 d h).union (ihtail.1 d h),
      fun d r h => (ihhead.2.1 d r h).union (ihtail.2.1 d r h),
      fun d h => (ihhead.2.2 d (h.singleton_of_mem List.mem_cons_self)).union_types
        (ihtail.2.2 d (ProfileView.typed_tail h))⟩
termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega
end

theorem AtomView.mapType_wf
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {a b : Atom n} (view : AtomView env U registry Γ a b)
    {profile : Profile n} (H : profile.WF) : (view.mapType profile).WF :=
  view.typing.1 profile H

theorem AtomView.mapType_sort
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {a b : Atom n} (view : AtomView env U registry Γ a b)
    {profile : Profile n} (H : profile.HasType (.sort relevant)) :
    (view.mapType profile).HasType (.sort relevant) := view.typing.2.1 profile relevant H

theorem AtomView.mapType_typed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {a b : Atom n} (view : AtomView env U registry Γ a b)
    {profile : Profile n} (H : (Profile.singleton a).HasType profile) :
    (Profile.singleton b).HasType (view.mapType profile) := view.typing.2.2 profile H

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ : List VExpr}

theorem ProfileView.mapType_wf {source target : Profile n}
    (view : ProfileView env U registry Γ source target)
    {profile : Profile n} (h : profile.WF) : (view.mapType profile).WF :=
  view.typing.1 profile h

theorem ProfileView.mapType_sort {source target : Profile n}
    (view : ProfileView env U registry Γ source target)
    {profile : Profile n} (h : profile.HasType (.sort relevant)) :
    (view.mapType profile).HasType (.sort relevant) := view.typing.2.1 profile relevant h

theorem ProfileView.mapType_typed {source target : Profile n}
    (view : ProfileView env U registry Γ source target)
    {profile : Profile n} (h : source.HasType profile) :
    target.HasType (view.mapType profile) := view.typing.2.2 profile h

end Lean4Lean.AnchoredSemantics
