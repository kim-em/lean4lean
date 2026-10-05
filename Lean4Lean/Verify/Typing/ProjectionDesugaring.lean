import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.ProjectionProgram
import Lean4Lean.Theory.Typing.ProjectionProgramTyping

/-! Typed projection abbreviations use fixed, declaration-derived case
programs. Only the occurrence's universe and term arguments vary. -/

namespace Lean4Lean

open InductiveSignature.CaseSchema

inductive ProjectionDesugaring (env : VEnv) (U : Nat) (Γ : List VExpr)
    (structName : Name) (index : Nat) (major : VExpr) : VExpr → Prop
  | intro {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size}
      {program : ProjectionFunction}
      (registered : env.eliminators block schema)
      (original : schema.originalFamilies[owner.val]? = some structName)
      (family : schema.signature.families[owner].name = structName)
      (generated : schema.genericProjectionPrefix block owner (index + 1) = some programs)
      (selected : programs[index]? = some program)
      (sourceLevels : levels.length = schema.signature.uvars)
      (fieldLevels : fieldSorts.length = index + 1)
      (levelWF : ∀ level ∈ fieldSorts ++ levels, level.WF U)
      (permission : ∀ target ∈ fieldSorts, schema.ProjectionAdmissible owner levels target)
      (parameterCount : params.length = schema.signature.params.length)
      (indexCount : indices.length = schema.signature.families[owner].indices.length)
      (source : env.HasType U Γ major
        (VExpr.mkApps (.const structName levels) (params ++ indices)))
      (target : VExpr.WF env U Γ
        (VExpr.mkApps (program.value.instL (fieldSorts ++ levels))
          (params ++ indices ++ [major]))) :
      ProjectionDesugaring env U Γ structName index major
        (VExpr.mkApps (program.value.instL (fieldSorts ++ levels))
          (params ++ indices ++ [major]))

namespace ProjectionDesugaring

theorem sourceWF (H : ProjectionDesugaring env U Γ name index major target) :
    VExpr.WF env U Γ major := by
  cases H with
  | intro _ _ _ _ _ _ _ _ _ _ _ h _ => exact ⟨_, h⟩

theorem targetWF (H : ProjectionDesugaring env U Γ name index major target) :
    VExpr.WF env U Γ target := by
  cases H
  assumption

/-- The actual abbreviation is typed by instantiating its generated function
type. The field dependencies are those computed by the shared program
generator, even when its original well-formedness witness used conversion. -/
theorem targetTyping (H : ProjectionDesugaring env U Γ name index major target)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    ∃ (program : ProjectionFunction) (packed : List VLevel) (args : List VExpr) (resultType : VExpr),
      target = VExpr.mkApps (program.value.instL packed) args ∧
      env.HasType U Γ (program.value.instL packed) (program.type.instL packed) ∧
      VEnv.InstForallsC env U Γ (program.type.instL packed) args resultType ∧
      env.HasType U Γ target resultType := by
  cases H with
  | @intro block programs fieldSorts levels params indices schema owner program
      hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    obtain ⟨hfn, resultType, hargs, hresult⟩ :=
      VEnv.HasType.projectionPrefix_instL_application_type henv hΓ hr hg
        (List.mem_of_getElem? hs)
        (args := params ++ indices ++ [major])
        (by simp only [List.length_append, List.length_singleton, hn, hi]) ht
    exact ⟨program, fieldSorts ++ levels, params ++ indices ++ [major], resultType,
      rfl, hfn, hargs, hresult⟩

theorem program_closed {index : Nat} {program : ProjectionFunction} {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size}
    (hgen : schema.genericProjectionPrefix block owner count = some programs)
    (hselected : programs[index]? = some program) : program.value.Closed :=
  (schema.genericProjectionPrefix_closed hgen program
    (List.mem_of_getElem? hselected)).1

/-- A projection abbreviation has an explicit lambda head. Its implementation
cannot be mistaken for a constructor, recursive field, or native constant. -/
theorem target_lamApp (H : ProjectionDesugaring env U Γ name index major target) :
    ∃ domain body args, target = VExpr.mkApps (.lam domain body) args := by
  cases H with
  | intro _ _ _ hg hs _ _ _ _ _ _ _ _ =>
    obtain ⟨domain, body, hvalue⟩ :=
      genericProjectionPrefix_outer_lambdas hg _ (List.mem_of_getElem? hs)
    rw [hvalue]
    exact ⟨_, _, _, rfl⟩

private theorem mkApps_not_forall {fn : VExpr}
    (hfn : ∀ domain body, fn ≠ .forallE domain body) (args : List VExpr) :
    ∀ domain body, VExpr.mkApps fn args ≠ .forallE domain body := by
  induction args generalizing fn with
  | nil => exact hfn
  | cons arg args ih => exact ih (fun _ _ h => by cases h)

/-- Generated projection functions remain opaque to strict forall-shape
inversion, including when their source was accepted as a WHNF cache key. -/
theorem target_not_forall
    (H : ProjectionDesugaring env U Γ name index major target) :
    target ≠ .forallE domain body := by
  obtain ⟨_, _, args, rfl⟩ := H.target_lamApp
  exact mkApps_not_forall (fun _ _ h => by cases h) args _ _

private theorem app_head (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).getAppFnArgs.1 = fn.getAppFnArgs.1 := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simpa only [VExpr.mkApps, List.foldl_cons, VExpr.getAppFnArgs_app]
      using ih (.app fn arg)

theorem target_bvarHead?_eq_none
    (H : ProjectionDesugaring env U Γ name index major target) :
    target.bvarHead? = none := by
  obtain ⟨domain, body, args, rfl⟩ := H.target_lamApp
  unfold VExpr.bvarHead?
  rw [app_head]
  rfl

theorem mono (H : ProjectionDesugaring env U Γ name index major target)
    (hle : env ≤ env') : ProjectionDesugaring env' U Γ name index major target := by
  cases H with
  | intro hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    exact .intro (hle.eliminators hr) ho hf hg hs hlu hfu hw hp hn hi
      (hm.mono hle) (ht.mono hle)

theorem defeqCtx (H : ProjectionDesugaring env U Γ₁ name index major target)
    (henv : env.Ordered) (hctx : env.IsDefEqCtx U base Γ₁ Γ₂) :
    ProjectionDesugaring env U Γ₂ name index major target := by
  cases H with
  | intro hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    exact .intro hr ho hf hg hs hlu hfu hw hp hn hi
      (hm.defeqDFC henv hctx) (ht.defeqDFC henv hctx)

/-- The generated abbreviation respects typed equality of its major argument.
The chosen program and its implicit arguments are retained. -/
theorem congr_major (H : ProjectionDesugaring env U Γ name index major target)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (he : env.IsDefEqU U Γ major major') :
    ∃ target', ProjectionDesugaring env U Γ name index major' target' ∧
      env.IsDefEqU U Γ target target' := by
  cases H with
  | @intro block programs fieldSorts levels params indices schema owner program
      hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    obtain ⟨resultType, ht⟩ := ht
    have happ : VExpr.mkApps (program.value.instL (fieldSorts ++ levels))
        (params ++ indices ++ [major]) =
        .app (VExpr.mkApps (program.value.instL (fieldSorts ++ levels))
          (params ++ indices)) major := by
      simp only [VExpr.mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [happ] at ht
    obtain ⟨A, B, hfn, harg⟩ := VEnv.HasType.app_inv henv.ordered hΓ ht
    have hmajor := (he.of_l henv hΓ hm).hasType.2
    have htarget := VEnv.IsDefEq.appDF hfn (he.of_l henv hΓ harg)
    have htarget' : env.IsDefEqU U Γ
        (VExpr.mkApps (program.value.instL (fieldSorts ++ levels)) (params ++ indices ++ [major]))
        (VExpr.mkApps (program.value.instL (fieldSorts ++ levels)) (params ++ indices ++ [major'])) := by
      simpa only [VExpr.mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil] using
        (show env.IsDefEqU U Γ _ _ from ⟨_, htarget⟩)
    exact ⟨_, .intro hr ho hf hg hs hlu hfu hw hp hn hi hmajor
      ⟨_, htarget'.choose_spec.hasType.2⟩, htarget'⟩

/-- Move a projection through both a context conversion and equality of its
source major, as required when translating the same concrete occurrence. -/
theorem defeqDFC (H : ProjectionDesugaring env U Γ₁ name index major target)
    (henv : env.WF) (hctx : env.IsDefEqCtx U [] Γ₁ Γ₂)
    (he : env.IsDefEqU U Γ₁ major major') :
    ∃ target', ProjectionDesugaring env U Γ₂ name index major' target' ∧
      env.IsDefEqU U Γ₂ target target' :=
  (H.defeqCtx henv.ordered hctx).congr_major henv
    (hctx.symm henv.ordered).isType (he.defeqDFC henv.ordered hctx)

theorem instL (H : ProjectionDesugaring env U Γ name index major target)
    (hsub : ∀ level ∈ substitution, level.WF U') :
    ProjectionDesugaring env U' (Γ.map (·.instL substitution)) name index
      (major.instL substitution) (target.instL substitution) := by
  cases H with
  | @intro block programs fieldSorts levels params indices schema owner program
      hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    have hpermission : ∀ target ∈ fieldSorts.map (·.inst substitution),
        schema.ProjectionAdmissible owner (levels.map (·.inst substitution)) target := by
      intro target htarget
      rcases List.mem_map.mp htarget with ⟨level, hlevel, rfl⟩
      have permission : schema.Permission U owner levels level :=
        ⟨hlu, fun l hl => hw l (List.mem_append_right _ hl),
          hw level (List.mem_append_left _ hlevel), hp level hlevel⟩
      exact (permission.instL hsub).admissible
    have hm' := hm.instL hsub
    have ht' := ht.instL hsub
    simp only [VExpr.instL_mkApps, VExpr.instL, VExpr.instL_instL,
      List.map_append, List.map_cons, List.map_nil] at hm' ht' ⊢
    exact .intro hr ho hf hg hs (by simpa using hlu) (by simpa using hfu)
      (by intro l hl; simp only [← List.map_append, List.mem_map] at hl
          rcases hl with ⟨_, _, rfl⟩; exact VLevel.WF.inst hsub)
      hpermission (by simpa using hn) (by simpa using hi) hm' ht'

theorem weakN (H : ProjectionDesugaring env U Γ name index major target)
    (henv : env.Ordered) (W : Ctx.LiftN n k Γ Γ') :
    ProjectionDesugaring env U Γ' name index (major.liftN n k) (target.liftN n k) := by
  cases H with
  | @intro block programs fieldSorts levels params indices schema owner program
      hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    have hc := (program_closed hg hs).instL (ls := fieldSorts ++ levels)
    have hm' := hm.weakN henv W
    have ht' := ht.weakN henv W
    simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append,
      List.map_cons, List.map_nil, hc.liftN_eq (Nat.zero_le _)] at hm' ht' ⊢
    exact .intro hr ho hf hg hs hlu hfu hw hp (by simpa using hn)
      (by simpa using hi) hm' ht'

private theorem skips_mkApps_arguments {fn : VExpr} {args : List VExpr}
    (h : (VExpr.mkApps fn args).Skips n k) : ∀ arg ∈ args, arg.Skips n k := by
  induction args generalizing fn with
  | nil => simp
  | cons arg args ih =>
    have hfn (fn : VExpr) : (VExpr.mkApps fn args).Skips n k → fn.Skips n k := by
      clear h ih
      induction args generalizing fn with
      | nil => exact id
      | cons a args ih =>
        intro ha
        exact VExpr.skips_iff.mpr (VExpr.skips_iff.mp (ih (.app fn a) ha)).1
    have happ : (VExpr.app fn arg).Skips n k := hfn (.app fn arg) h
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact VExpr.skips_iff.mpr (VExpr.skips_iff.mp happ).2
    · exact ih h a ha

/-- Inverse weakening of an occurrence whose whole generated program is in
scope. Every implicit argument is recovered from that same program spine. -/
theorem weakN_inv
    (H : ProjectionDesugaring env U Γ' name index (major.liftN n k) (target.liftN n k))
    (henv : env.WF) (hΓ : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ') :
    ProjectionDesugaring env U Γ name index major target := by
  generalize he : target.liftN n k = raw at H
  cases H with
  | @intro block programs fieldSorts levels params indices schema owner program
      hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    have hskips : (VExpr.mkApps (program.value.instL (fieldSorts ++ levels))
        (params ++ indices ++ [major.liftN n k])).Skips n k := he ▸ .liftN
    have hargs := skips_mkApps_arguments hskips
    let params' := params.map fun e => e.unliftN n k
    let indices' := indices.map fun e => e.unliftN n k
    have hparams : params'.map (fun e => e.liftN n k) = params := by
      simp only [params', List.map_map]
      apply List.ext_getElem
      · simp
      · intro i h₁ h₂
        simp only [List.getElem_map]
        exact hargs _ (List.mem_append_left _ (List.mem_append_left _ (List.getElem_mem h₂)))
    have hindices : indices'.map (fun e => e.liftN n k) = indices := by
      simp only [indices', List.map_map]
      apply List.ext_getElem
      · simp
      · intro i h₁ h₂
        simp only [List.getElem_map]
        exact hargs _ (List.mem_append_left _ (List.mem_append_right _ (List.getElem_mem h₂)))
    have hsource : env.HasType U Γ major
        (VExpr.mkApps (.const name levels) (params' ++ indices')) := by
      apply (VEnv.HasType.weakN_iff henv hΓ W).mp
      simpa only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append, hparams, hindices] using hm
    have hc := (program_closed hg hs).instL (ls := fieldSorts ++ levels)
    have heq : VExpr.mkApps (program.value.instL (fieldSorts ++ levels))
        (params' ++ indices' ++ [major]) = target := by
      apply (VExpr.liftN_inj (n := n) (k := k)).mp
      simpa only [VExpr.liftN_mkApps, hc.liftN_eq (Nat.zero_le _), List.map_append,
        List.map_cons, List.map_nil, hparams, hindices] using he.symm
    have htarget : VExpr.WF env U Γ target := by
      apply (VEnv.IsDefEqU.weakN_iff henv hΓ W).mp
      rwa [he]
    rw [← heq] at htarget ⊢
    exact .intro hr ho hf hg hs hlu hfu hw hp (by simpa [params'] using hn)
      (by simpa [indices'] using hi) hsource htarget

private theorem lift'_mkApps (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).lift' ρ = VExpr.mkApps (fn.lift' ρ) (args.map (·.lift' ρ)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih => exact ih (.app fn arg)

theorem weak' (H : ProjectionDesugaring env U Γ name index major target)
    (henv : env.Ordered) (W : Ctx.Lift' ρ Γ Γ') :
    ProjectionDesugaring env U Γ' name index (major.lift' ρ) (target.lift' ρ) := by
  cases H with
  | @intro block programs fieldSorts levels params indices schema owner program
      hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    have hc := (program_closed hg hs).instL (ls := fieldSorts ++ levels)
    have hm' := hm.weak' henv W
    have ht' := ht.weak' henv W
    simp only [lift'_mkApps, VExpr.lift', List.map_append, List.map_cons,
      List.map_nil, hc.lift'_eq Lift.Fixes.zero] at hm' ht' ⊢
    exact .intro hr ho hf hg hs hlu hfu hw hp (by simpa using hn)
      (by simpa using hi) hm' ht'

/-- Inverse transport for arbitrary binder insertions, reduced to the proved
single-cutoff inverse while retaining the exact generated occurrence. -/
theorem weak'_inv
    (H : ProjectionDesugaring env U Γ' name index (major.lift' ρ) (target.lift' ρ))
    (henv : env.WF) (hΓ : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' ρ Γ Γ') :
    ProjectionDesugaring env U Γ name index major target := by
  generalize hd : ρ.depth = count
  induction count generalizing ρ Γ' with
  | zero => simpa only [VExpr.lift'_depth_zero hd, W.depth_zero hd] using H
  | succ count ih =>
    obtain ⟨ρ, k, rfl, rfl⟩ := Lift.depth_succ hd
    obtain ⟨middle, W₁, W₂⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, VExpr.lift'_comp,
      ← Lift.skipN_one, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN] at H
    exact ih (H.weakN_inv henv hΓ W₂) (hΓ.weakN_inv henv W₂) W₁ Lift.depth_consN

theorem instN (H : ProjectionDesugaring env U Γ₁ name index major target)
    (henv : env.Ordered) (W : Ctx.InstN Γ₀ value valueType k Γ₁ Γ)
    (hvalue : env.HasType U Γ₀ value valueType) :
    ProjectionDesugaring env U Γ name index (major.inst value k) (target.inst value k) := by
  cases H with
  | @intro block programs fieldSorts levels params indices schema owner program
      hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    have hc := (program_closed hg hs).instL (ls := fieldSorts ++ levels)
    have hm' := hm.instN henv W hvalue
    have ht' := ht.instN henv W hvalue
    simp only [VExpr.inst_mkApps, VExpr.inst, List.map_append, List.map_cons,
      List.map_nil, hc.instN_eq (Nat.zero_le _)] at hm' ht' ⊢
    exact .intro hr ho hf hg hs hlu hfu hw hp (by simpa using hn)
      (by simpa using hi) hm' ht'

end ProjectionDesugaring
end Lean4Lean
