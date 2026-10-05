import Lean4Lean.Theory.Typing.AnchoredDomainRekey
import Lean4Lean.Theory.Typing.AnchoredFunctionShift
import Lean4Lean.Theory.Typing.AnchoredFunctionUnshift
import Lean4Lean.Theory.Typing.AnchoredReanchorInverse
import Lean4Lean.Theory.Typing.AnchoredInputSupport

/-! Finite hereditary atomic views with concrete semantic guards. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

mutual
inductive AtomView (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : {n : Nat} → Atom n → Atom n → Type where
  | refl (atom : Atom n) : AtomView env U registry Γ atom atom
  | reanchor {key : Key n} {output : Atom n} {anchor : VExpr}
      (admitted : Admitted env U registry Γ key anchor anchor) :
      AtomView env U registry Γ (n := n + 1)
        (.fn key output) (.fn (reanchorKey key anchor) output)
  | domainRekey {key : Key n} {output : Atom n} {newDomain : VExpr} {guard : Profile n}
      (path : TypeConversion env U Γ key.domain newDomain)
      (typed : key.input.HasType guard) (formation : guard.HasType (.sort true))
      (bridge : TypeRelated env U registry Γ key.domain newDomain guard) :
      AtomView env U registry Γ (n := n + 1)
        (.fn key output) (.fn (domainKey key newDomain) output)
  | input {key : Key n} {output : Atom n} {newInput : Profile n}
      (forward : ProfileView env U registry Γ newInput key.input)
      (backward : ProfileView env U registry Γ key.input newInput) :
      AtomView env U registry Γ (n := n + 1)
        (.fn key output) (.fn (inputKey key newInput) output)
  | commutePadFn (key : Key n) (output : Atom n) :
      AtomView env U registry Γ (n := n + 2)
        (.pad (.fn key output)) (.fn key.pad (.pad output))
  | uncommutePadFn (key : Key n) (output : Atom n) :
      AtomView env U registry Γ (n := n + 2)
        (.fn key.pad (.pad output)) (.pad (.fn key output))
  | fn (key : Key n) {output output' : Atom n}
      (view : AtomView env U registry Γ output output') :
      AtomView env U registry Γ (n := n + 1) (.fn key output) (.fn key output')
  | pad {atom atom' : Atom n} (view : AtomView env U registry Γ atom atom') :
      AtomView env U registry Γ (n := n + 1) (.pad atom) (.pad atom')
  | trans {a b c : Atom n} (first : AtomView env U registry Γ a b)
      (second : AtomView env U registry Γ b c) : AtomView env U registry Γ a c

inductive ProfileView (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : {n : Nat} → Profile n → Profile n → Type where
  | nil : ProfileView env U registry Γ [] []
  | cons {a b : Atom n} {source target : Profile n}
      (head : AtomView env U registry Γ a b)
      (tail : ProfileView env U registry Γ source target) :
      ProfileView env U registry Γ (a :: source) (b :: target)

end

mutual
noncomputable def AtomView.mapType {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {Γ : List VExpr} :
    {n : Nat} → {a b : Atom n} → AtomView env U registry Γ a b → Profile n → Profile n
  | _, _, _, .refl _, profile => profile
  | _ + 1, _, _, @AtomView.reanchor _ _ _ _ _ key _ anchor _, profile =>
      reanchorTypes key (reanchorKey key anchor) profile
  | _ + 1, _, _, @AtomView.domainRekey _ _ _ _ _ key _ newDomain _ _ _ _ _, profile =>
      domainRekeyTypes key newDomain profile
  | _ + 1, _, _, @AtomView.input _ _ _ _ _ key _ newInput _ backward, profile =>
      inputTypes key newInput backward.mapType profile
  | _ + 2, _, _, .commutePadFn _ _, profile => profile.down.rankShift
  | _ + 2, _, _, .uncommutePadFn key _, profile => (profile.unshift key).pad
  | _ + 1, _, _, .fn key view, profile => outputTypes key view.mapType profile
  | _ + 1, _, _, .pad view, profile => (view.mapType profile.down).pad
  | _, _, _, .trans first second, profile => second.mapType (first.mapType profile)

/-- Each atomic map receives the original support. The old support remains
as the final summand; the result is fixed before any future argument is used. -/
noncomputable def ProfileView.mapType {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {Γ : List VExpr} :
    {n : Nat} → {source target : Profile n} →
    ProfileView env U registry Γ source target → Profile n → Profile n
  | _, _, _, .nil, profile => profile
  | _, _, _, .cons head tail, profile => (head.mapType profile).union (tail.mapType profile)

end

mutual
noncomputable def AtomView.future {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ) {a b : Atom n}
    (view : AtomView env U registry Γ a b) :
    AtomView env U registry Δ (a.rename ρ) (b.rename ρ) := by
  match n, a, b, view with
  | _, _, _, .refl atom => exact .refl _
  | _ + 1, _, _, .reanchor admitted =>
    simpa only [Atom.rename_fn, reanchorKey, Key.rename] using
      AtomView.reanchor (Admitted.future henv W admitted)
  | _ + 1, _, _, @AtomView.domainRekey _ _ _ _ _ key output newDomain guard path typed formation bridge =>
    have hf := (Profile.rename_hasType_iff (ρ := ρ)).mpr formation
    rw [Profile.rename_sort] at hf
    simpa only [Atom.rename_fn, domainKey, Key.rename] using
      (AtomView.domainRekey (key := key.rename ρ) (output := output.rename ρ)
        (path.weak' henv W.weakening) (Profile.rename_hasType_iff.mpr typed) hf
        (TypeRelated.future henv W bridge))
  | _ + 1, _, _, @AtomView.input _ _ _ _ _ key output newInput forward backward =>
    simpa only [Atom.rename_fn, inputKey, Key.rename] using
      (AtomView.input (key := key.rename ρ) (output := output.rename ρ)
        (forward.future henv W) (backward.future henv W))
  | k + 2, _, _, .commutePadFn key output =>
    simpa only [Atom.rename_pad (n := k + 1), Atom.rename_pad (n := k),
      Atom.rename_fn, Key.pad_rename] using
      AtomView.commutePadFn (key.rename ρ) (output.rename ρ)
  | k + 2, _, _, .uncommutePadFn key output =>
    simpa only [Atom.rename_pad (n := k + 1), Atom.rename_pad (n := k),
      Atom.rename_fn, Key.pad_rename] using
      AtomView.uncommutePadFn (key.rename ρ) (output.rename ρ)
  | _ + 1, _, _, .fn key view => exact .fn (key.rename ρ) (view.future henv W)
  | _ + 1, _, _, .pad view => exact .pad (view.future henv W)
  | _, _, _, .trans first second => exact .trans (first.future henv W) (second.future henv W)

termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

noncomputable def ProfileView.future {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {Γ Δ : List VExpr} {ρ : Lift}
    {n : Nat} {source target : Profile n} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (view : ProfileView env U registry Γ source target) :
    ProfileView env U registry Δ (source.rename ρ) (target.rename ρ) := by
  match source, target, view with
  | _, _, .nil => exact .nil
  | _, _, .cons head tail => exact .cons (head.future henv W) (ProfileView.future henv W tail)

termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

end

private theorem AtomView.mapType_heq {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {Γ : List VExpr} {a b c d : Atom n}
    {first : AtomView env U registry Γ a b} {second : AtomView env U registry Γ c d}
    (ha : a = c) (hb : b = d) (h : HEq first second) (profile : Profile n) :
    first.mapType profile = second.mapType profile := by
  cases ha
  cases hb
  cases eq_of_heq h
  rfl

mutual
theorem AtomView.mapType_future {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {Γ Δ : List VExpr} {ρ : Lift}
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {a b : Atom n} (view : AtomView env U registry Γ a b) (profile : Profile n) :
    (view.mapType profile).rename ρ = (view.future henv W).mapType (profile.rename ρ) := by
  match n, a, b, view with
  | _, _, _, .refl atom => simp only [AtomView.future, AtomView.mapType]
  | _ + 1, _, _, @AtomView.reanchor _ _ _ _ _ key output anchor admitted =>
    rw [AtomView.future]
    exact reanchorTypes_rename key (reanchorKey key anchor) profile ρ
  | _ + 1, _, _, @AtomView.domainRekey _ _ _ _ _ key output newDomain guard path typed formation bridge =>
    rw [AtomView.future]
    exact domainRekeyTypes_rename key newDomain profile ρ
  | _ + 1, _, _, @AtomView.input _ _ _ _ _ key output newInput forward backward =>
    rw [AtomView.future]
    exact inputTypes.rename key newInput profile ρ backward.mapType
      (backward.future henv W).mapType (fun d => backward.mapType_future henv W d)
  | k + 2, _, _, .commutePadFn key output =>
    have heq : HEq (AtomView.future (registry := registry) henv W (AtomView.commutePadFn key output))
        (AtomView.commutePadFn (env := env) (U := U) (registry := registry) (Γ := Δ)
          (key.rename ρ) (output.rename ρ)) := by
      simp only [AtomView.future, Eq.mp, Eq.mpr, eqRec_heq_iff, HEq.rfl]
    have hm : (AtomView.future (registry := registry) henv W (AtomView.commutePadFn key output)).mapType (profile.rename ρ) =
        (profile.rename ρ).down.rankShift := by
      exact AtomView.mapType_heq
        (by simp only [Atom.rename_pad (n := k + 1), Atom.rename_fn])
        (by simp only [Atom.rename_pad, Atom.rename_fn, Key.pad_rename])
        heq (profile.rename ρ)
    rw [hm]
    exact (Profile.rankShift_rename profile.down ρ).symm.trans
      (congrArg Profile.rankShift (Profile.down_rename profile ρ).symm)
  | k + 2, _, _, .uncommutePadFn key output =>
    have heq : HEq (AtomView.future (registry := registry) henv W (AtomView.uncommutePadFn key output))
        (AtomView.uncommutePadFn (env := env) (U := U) (registry := registry) (Γ := Δ)
          (key.rename ρ) (output.rename ρ)) := by
      simp only [AtomView.future, Eq.mp, Eq.mpr, eqRec_heq_iff, HEq.rfl]
    have hm : (AtomView.future (registry := registry) henv W (AtomView.uncommutePadFn key output)).mapType (profile.rename ρ) =
        ((profile.rename ρ).unshift (key.rename ρ)).pad := by
      exact AtomView.mapType_heq
        (by simp only [Atom.rename_pad, Atom.rename_fn, Key.pad_rename])
        (by simp only [Atom.rename_pad (n := k + 1), Atom.rename_fn])
        heq (profile.rename ρ)
    rw [hm]
    change ((profile.unshift key).pad).rename ρ =
      ((profile.rename ρ).unshift (key.rename ρ)).pad
    rw [Profile.rename_pad, Profile.unshift_rename]
  | _ + 1, _, _, .fn key view =>
    rw [AtomView.future]
    exact outputTypes_rename key _ _ (fun p => view.mapType_future henv W p) profile
  | _ + 1, _, _, .pad view =>
    simpa only [AtomView.mapType, AtomView.future, Profile.rename_pad, Profile.down_rename] using
      congrArg Profile.pad (view.mapType_future henv W profile.down)
  | _, _, _, .trans first second =>
    rw [AtomView.future]
    exact (second.mapType_future henv W (first.mapType profile)).trans
      (congrArg _ (first.mapType_future henv W profile))

termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

theorem ProfileView.mapType_future {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {Γ Δ : List VExpr} {ρ : Lift}
    {n : Nat} {source target : Profile n} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (view : ProfileView env U registry Γ source target) (profile : Profile n) :
    (view.mapType profile).rename ρ =
      (view.future henv W).mapType (profile.rename ρ) := by
  match source, target, view with
  | _, _, .nil => simp only [ProfileView.future, ProfileView.mapType]
  | _, _, .cons head tail =>
    change ((head.mapType profile).union (tail.mapType profile)).rename ρ = _
    rw [Profile.rename_union, head.mapType_future henv W profile, ProfileView.mapType_future henv W tail profile]
    rw [ProfileView.future]
    rfl

termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

end

mutual
noncomputable def AtomView.mixed {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : MixedInsertion env U Γ Δ ρ) {a b : Atom n}
    (view : AtomView env U registry Γ a b) :
    AtomView env U registry Δ (a.rename ρ) (b.rename ρ) := by
  match n, a, b, view with
  | _, _, _, .refl atom => exact .refl _
  | _ + 1, _, _, .reanchor admitted =>
    simpa only [Atom.rename_fn, reanchorKey, Key.rename] using
      AtomView.reanchor (W.admitted henv admitted)
  | _ + 1, _, _, @AtomView.domainRekey _ _ _ _ _ key output newDomain guard path typed formation bridge =>
    have hf := (Profile.rename_hasType_iff (ρ := ρ)).mpr formation
    rw [Profile.rename_sort] at hf
    simpa only [Atom.rename_fn, domainKey, Key.rename] using
      (AtomView.domainRekey (key := key.rename ρ) (output := output.rename ρ)
        (W.path henv path) (Profile.rename_hasType_iff.mpr typed) hf
        (W.code henv bridge))
  | _ + 1, _, _, @AtomView.input _ _ _ _ _ key output newInput forward backward =>
    simpa only [Atom.rename_fn, inputKey, Key.rename] using
      (AtomView.input (key := key.rename ρ) (output := output.rename ρ)
        (forward.mixed henv W) (backward.mixed henv W))
  | k + 2, _, _, .commutePadFn key output =>
    simpa only [Atom.rename_pad (n := k + 1), Atom.rename_pad (n := k),
      Atom.rename_fn, Key.pad_rename] using
      AtomView.commutePadFn (key.rename ρ) (output.rename ρ)
  | k + 2, _, _, .uncommutePadFn key output =>
    simpa only [Atom.rename_pad (n := k + 1), Atom.rename_pad (n := k),
      Atom.rename_fn, Key.pad_rename] using
      AtomView.uncommutePadFn (key.rename ρ) (output.rename ρ)
  | _ + 1, _, _, .fn key view => exact .fn (key.rename ρ) (view.mixed henv W)
  | _ + 1, _, _, .pad view => exact .pad (view.mixed henv W)
  | _, _, _, .trans first second => exact .trans (first.mixed henv W) (second.mixed henv W)

termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

noncomputable def ProfileView.mixed {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {Γ Δ : List VExpr} {ρ : Lift}
    {n : Nat} {source target : Profile n} (henv : env.Ordered)
    (W : MixedInsertion env U Γ Δ ρ)
    (view : ProfileView env U registry Γ source target) :
    ProfileView env U registry Δ (source.rename ρ) (target.rename ρ) := by
  match source, target, view with
  | _, _, .nil => exact .nil
  | _, _, .cons head tail => exact .cons (head.mixed henv W) (ProfileView.mixed henv W tail)

termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

end

mutual
theorem AtomView.mapType_mixed {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {Γ Δ : List VExpr} {ρ : Lift}
    (henv : env.Ordered) (W : MixedInsertion env U Γ Δ ρ)
    {a b : Atom n} (view : AtomView env U registry Γ a b) (profile : Profile n) :
    (view.mapType profile).rename ρ = (view.mixed henv W).mapType (profile.rename ρ) := by
  match n, a, b, view with
  | _, _, _, .refl atom => simp only [AtomView.mixed, AtomView.mapType]
  | _ + 1, _, _, @AtomView.reanchor _ _ _ _ _ key output anchor admitted =>
    rw [AtomView.mixed]
    exact reanchorTypes_rename key (reanchorKey key anchor) profile ρ
  | _ + 1, _, _, @AtomView.domainRekey _ _ _ _ _ key output newDomain guard path typed formation bridge =>
    rw [AtomView.mixed]
    exact domainRekeyTypes_rename key newDomain profile ρ
  | _ + 1, _, _, @AtomView.input _ _ _ _ _ key output newInput forward backward =>
    rw [AtomView.mixed]
    exact inputTypes.rename key newInput profile ρ backward.mapType
      (backward.mixed henv W).mapType (fun d => backward.mapType_mixed henv W d)
  | k + 2, _, _, .commutePadFn key output =>
    have heq : HEq (AtomView.mixed (registry := registry) henv W (AtomView.commutePadFn key output))
        (AtomView.commutePadFn (env := env) (U := U) (registry := registry) (Γ := Δ)
          (key.rename ρ) (output.rename ρ)) := by
      simp only [AtomView.mixed, Eq.mp, Eq.mpr, eqRec_heq_iff, HEq.rfl]
    have hm : (AtomView.mixed (registry := registry) henv W (AtomView.commutePadFn key output)).mapType (profile.rename ρ) =
        (profile.rename ρ).down.rankShift := by
      exact AtomView.mapType_heq
        (by simp only [Atom.rename_pad (n := k + 1), Atom.rename_fn])
        (by simp only [Atom.rename_pad, Atom.rename_fn, Key.pad_rename])
        heq (profile.rename ρ)
    rw [hm]
    exact (Profile.rankShift_rename profile.down ρ).symm.trans
      (congrArg Profile.rankShift (Profile.down_rename profile ρ).symm)
  | k + 2, _, _, .uncommutePadFn key output =>
    have heq : HEq (AtomView.mixed (registry := registry) henv W (AtomView.uncommutePadFn key output))
        (AtomView.uncommutePadFn (env := env) (U := U) (registry := registry) (Γ := Δ)
          (key.rename ρ) (output.rename ρ)) := by
      simp only [AtomView.mixed, Eq.mp, Eq.mpr, eqRec_heq_iff, HEq.rfl]
    have hm : (AtomView.mixed (registry := registry) henv W (AtomView.uncommutePadFn key output)).mapType (profile.rename ρ) =
        ((profile.rename ρ).unshift (key.rename ρ)).pad := by
      exact AtomView.mapType_heq
        (by simp only [Atom.rename_pad, Atom.rename_fn, Key.pad_rename])
        (by simp only [Atom.rename_pad (n := k + 1), Atom.rename_fn])
        heq (profile.rename ρ)
    rw [hm]
    change ((profile.unshift key).pad).rename ρ =
      ((profile.rename ρ).unshift (key.rename ρ)).pad
    rw [Profile.rename_pad, Profile.unshift_rename]
  | _ + 1, _, _, .fn key view =>
    rw [AtomView.mixed]
    exact outputTypes_rename key _ _ (fun p => view.mapType_mixed henv W p) profile
  | _ + 1, _, _, .pad view =>
    simpa only [AtomView.mapType, AtomView.mixed, Profile.rename_pad, Profile.down_rename] using
      congrArg Profile.pad (view.mapType_mixed henv W profile.down)
  | _, _, _, .trans first second =>
    rw [AtomView.mixed]
    exact (second.mapType_mixed henv W (first.mapType profile)).trans
      (congrArg _ (first.mapType_mixed henv W profile))

termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

theorem ProfileView.mapType_mixed {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {Γ Δ : List VExpr} {ρ : Lift}
    {n : Nat} {source target : Profile n} (henv : env.Ordered)
    (W : MixedInsertion env U Γ Δ ρ)
    (view : ProfileView env U registry Γ source target) (profile : Profile n) :
    (view.mapType profile).rename ρ =
      (view.mixed henv W).mapType (profile.rename ρ) := by
  match source, target, view with
  | _, _, .nil => simp only [ProfileView.mixed, ProfileView.mapType]
  | _, _, .cons head tail =>
    change ((head.mapType profile).union (tail.mapType profile)).rename ρ = _
    rw [Profile.rename_union, head.mapType_mixed henv W profile, ProfileView.mapType_mixed henv W tail profile]
    rw [ProfileView.mixed]
    rfl

termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

end

/-- Every guarded value view has a guarded inverse. The inverse transports
arbitrary new covers; it does not assert that the computed maps are identities. -/
noncomputable def AtomView.inverse
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) {a b : Atom n} (view : AtomView env U registry Γ a b) :
    AtomView env U registry Γ b a := by
  match n, a, b, view with
  | _, _, _, .refl atom => exact .refl _
  | _ + 1, _, _, @AtomView.reanchor _ _ _ _ _ key output anchor admitted =>
    simpa only [reanchorKey] using
      (AtomView.reanchor (output := output) (Admitted.reanchor_reverse henv admitted))
  | _ + 1, _, _, @AtomView.domainRekey _ _ _ _ _ key output newDomain guard path typed formation bridge =>
    simpa only [domainKey] using
      (AtomView.domainRekey (key := domainKey key newDomain) (output := output)
        path.symm typed formation (TypeRelated.symm henv typed.wf_type bridge))
  | _ + 1, _, _, @AtomView.input _ _ _ _ _ key output newInput forward backward =>
    simpa only [inputKey] using
      (AtomView.input (key := inputKey key newInput) (output := output) backward forward)
  | k + 2, _, _, .commutePadFn key output => exact .uncommutePadFn key output
  | k + 2, _, _, .uncommutePadFn key output => exact .commutePadFn key output
  | _ + 1, _, _, .fn key view => exact .fn key (view.inverse henv)
  | _ + 1, _, _, .pad view => exact .pad (view.inverse henv)
  | _, _, _, .trans first second => exact .trans (second.inverse henv) (first.inverse henv)

termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ Δ : List VExpr} {ρ : Lift}

/-- Every paired atom has a concrete reverse view; no source demand is discarded. -/
noncomputable def ProfileView.inverse {source target : Profile n} (henv : env.Ordered)
    (view : ProfileView env U registry Γ source target) :
    ProfileView env U registry Γ target source := by
  match source, target, view with
  | _, _, .nil => exact .nil
  | _, _, .cons head tail => exact .cons (head.inverse henv) (inverse henv tail)

termination_by sizeOf view
decreasing_by all_goals simp_wf; omega

theorem ProfileView.mapType_contains {source target : Profile n} (view : ProfileView env U registry Γ source target)
    {profile : Profile n} {atom : Atom n} (h : atom ∈ profile.atoms) :
    atom ∈ (view.mapType profile).atoms := by
  match source, target, view with
  | _, _, .nil => exact h
  | _, _, .cons head tail => exact List.mem_append_right _ (mapType_contains tail h)

termination_by sizeOf view
decreasing_by all_goals simp_wf; omega

theorem ProfileView.le_mapType {source target : Profile n} (view : ProfileView env U registry Γ source target)
    (profile : Profile n) : profile ≤ view.mapType profile := by
  match source, target, view with
  | _, _, .nil => exact profile.le_refl
  | _, _, .cons head tail =>
    exact Profile.le_trans (le_mapType tail profile) (Profile.le_union_right _ _)
termination_by sizeOf view
decreasing_by all_goals simp_wf; omega



end Lean4Lean.AnchoredSemantics
