import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Instantiating constructor telescopes

`VProjectionInfo.fieldType` walks a constructor type one binder at a time, instantiating
each binder with a parameter or with the primitive projection of the preceding field.
`InstForalls` is the typed counterpart of that walk; it is what the checker's projection
inference and projection reduction refine, and it is congruent under definitional equality of
its inputs.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- `InstForalls env U Γ T args res`: instantiating the leading binders of `T` by `args`, one
at a time, yields `res`. Each argument is either typed at its binder, or the remaining body does
not depend on the binder (in which case nothing is required of the argument). -/
inductive InstForalls (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → List VExpr → VExpr → Prop
  | nil : InstForalls env U Γ T [] T
  | cons : env.HasType U Γ a A → InstForalls env U Γ (B.inst a) args res →
      InstForalls env U Γ (.forallE A B) (a :: args) res
  | vacuous : InstForalls env U Γ B args res →
      InstForalls env U Γ (.forallE A B.lift) (a :: args) res

/-- The walk is congruent under definitional equality of the telescope and of the arguments. -/
theorem InstForalls.defeq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (H : InstForalls env U Γ T args res) (H' : InstForalls env U Γ T' args' res')
    (hT : env.IsDefEqU U Γ T T') (hargs : List.Forall₂ (env.IsDefEqU U Γ) args args') :
    env.IsDefEqU U Γ res res' := by
  induction H generalizing T' args' res' with
  | nil => cases H' <;> cases hargs <;> exact hT
  | @cons a A B args res ha _ ih =>
    cases hargs with | cons haa hargs
    cases H' with
    | @cons a' A' B' _ _ ha' H' =>
      have ⟨⟨_, hA⟩, _, hB⟩ := hT.forallE_inv henv hΓ
      have := IsDefEq.instDF henv.ordered hΓ hB (haa.of_l henv hΓ ha)
      exact ih H' ⟨_, this⟩ hargs
    | @vacuous _ _ _ A' _ H' =>
      have ⟨⟨_, hA⟩, _, hB⟩ := hT.forallE_inv henv hΓ
      have := IsDefEq.instDF henv.ordered hΓ hB (haa.of_l henv hΓ ha)
      rw [VExpr.inst_lift] at this
      exact ih H' ⟨_, this⟩ hargs
  | @vacuous B args res A a _ ih =>
    cases hargs with | cons haa hargs
    cases H' with
    | @cons a' A' B' _ _ ha' H' =>
      have ⟨⟨_, hA⟩, _, hB⟩ := hT.forallE_inv henv hΓ
      have ha : env.HasType U Γ a A := (haa.of_r henv hΓ (ha'.defeqU_r henv hΓ ⟨_, hA.symm⟩)).hasType.1
      have := IsDefEq.instDF henv.ordered hΓ hB (haa.of_l henv hΓ ha)
      rw [VExpr.inst_lift] at this
      exact ih H' ⟨_, this⟩ hargs
    | @vacuous _ _ _ A' _ H' =>
      have ⟨⟨_, hA⟩, _, hB⟩ := hT.forallE_inv henv hΓ
      have hΓ' : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, hA.hasType.1⟩
      have := (IsDefEqU.weakN_iff henv hΓ' (.one (A := A))).1 ⟨_, hB⟩
      exact ih H' this hargs

end VEnv
end Lean4Lean

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

theorem InstForalls.instantiateProjectionParameters_eq
    (H : InstForalls env U Γ T params res) :
    VProjectionInfo.instantiateProjectionParameters T params = some res := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simpa [VProjectionInfo.instantiateProjectionParameters] using ih
  | vacuous _ ih =>
    simpa [VProjectionInfo.instantiateProjectionParameters, VExpr.inst_lift] using ih

theorem InstForalls.instantiateProjectionFields_eq
    (H : InstForalls env U Γ tail
      ((List.range k).map fun j => .proj typeName (current + j) major) (.forallE F rest)) :
    VProjectionInfo.instantiateProjectionFields typeName major (current + k) current (k + 1)
      tail = some F := by
  induction k generalizing tail current with
  | zero =>
    cases H
    simp [VProjectionInfo.instantiateProjectionFields]
  | succ k ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map] at H
    generalize hargs : (List.range k).map ((fun j => VExpr.proj typeName (current + j) major) ∘
      Nat.succ) = args at H
    have hargs' : args = (List.range k).map fun j => VExpr.proj typeName (current + 1 + j) major := by
      rw [← hargs]; congr 1; funext j; simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 j]
    subst hargs'
    cases H with
    | cons _ H' =>
      have := ih (current := current + 1) H'
      simp only [VProjectionInfo.instantiateProjectionFields, Nat.add_zero]
      rw [if_neg (by omega)]
      simpa [Nat.add_assoc, Nat.add_comm 1 k, Nat.add_left_comm] using this
    | vacuous H' =>
      have := ih (current := current + 1) H'
      simp only [VProjectionInfo.instantiateProjectionFields, Nat.add_zero, VExpr.inst_lift]
      rw [if_neg (by omega)]
      simpa [Nat.add_assoc, Nat.add_comm 1 k, Nat.add_left_comm] using this

/-- `fieldType` is determined by two typed walks: the parameters through the constructor
telescope, then the projections of the earlier fields. -/
theorem VProjectionInfo.fieldType_eq_of_instForalls (info : VProjectionInfo)
    (hlevels : levels.length = info.uvars) (hparams : params.length = info.nparams)
    (Hparams : InstForalls env U Γ (info.ctorType.instL levels) params tail)
    (Hfields : InstForalls env U Γ tail
      ((List.range index).map fun j => .proj typeName j major) (.forallE F rest)) :
    info.fieldType typeName levels params index major = some F := by
  have h1 := Hparams.instantiateProjectionParameters_eq
  have Hfields' : InstForalls env U Γ tail
      ((List.range index).map fun j => .proj typeName (0 + j) major) (.forallE F rest) := by
    simpa using Hfields
  have h2 := Hfields'.instantiateProjectionFields_eq
  simp only [Nat.zero_add] at h2
  simp [VProjectionInfo.fieldType, hlevels, hparams, h1, h2]

theorem _root_.Lean4Lean.VExpr.takeForalls_inst {T : VExpr}
    (H : T.takeForalls n = some (doms, rest)) :
    ∃ doms', (T.inst a k).takeForalls n = some (doms', rest.inst a (k + n)) := by
  induction n generalizing T doms rest k with
  | zero =>
    simp [VExpr.takeForalls] at H
    obtain ⟨rfl, rfl⟩ := H
    exact ⟨[], by simp [VExpr.takeForalls]⟩
  | succ n ih =>
    cases T <;> simp [VExpr.takeForalls] at H
    case forallE A B =>
      obtain ⟨doms', h, rfl, rfl⟩ := H
      obtain ⟨doms'', h'⟩ := ih (k := k + 1) h
      exact ⟨A.inst a k :: doms'', by
        simp [VExpr.inst, VExpr.takeForalls, h', Nat.add_assoc, Nat.add_comm 1]⟩

theorem _root_.Lean4Lean.VExpr.WF.of_mkApps (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : VExpr.WF env U Γ (VExpr.mkApps f args)) : VExpr.WF env U Γ f := by
  induction args generalizing f with
  | nil => simpa [VExpr.mkApps] using H
  | cons a args ih =>
    have ⟨_, _, hf, _⟩ := (ih (f := .app f a) H).app_inv henv hΓ
    exact ⟨_, hf⟩

/-- An application spine typed against a syntactic forall telescope instantiates that telescope:
every argument is typed at its binder, and the whole application has the residual type. -/
theorem HasType.mkApps_telescope (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ f T) (H : VExpr.WF env U Γ (VExpr.mkApps f args))
    (hT : T.takeForalls args.length = some (doms, rest)) :
    ∃ res, InstForalls env U Γ T args res ∧ env.HasType U Γ (VExpr.mkApps f args) res := by
  induction args generalizing f T doms rest with
  | nil => exact ⟨_, .nil, by simpa [VExpr.mkApps] using hf⟩
  | cons a args ih =>
    cases T <;> simp [VExpr.takeForalls] at hT
    case forallE A B =>
      obtain ⟨doms', hB, rfl, rfl⟩ := hT
      have hfa : VExpr.WF env U Γ (.app f a) :=
        VExpr.WF.of_mkApps henv.ordered hΓ (f := .app f a) (by simpa [VExpr.mkApps] using H)
      have ⟨A', B', hf', ha'⟩ := hfa.app_inv henv.ordered hΓ
      have ⟨⟨_, hA⟩, _, hB'⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
      have ha : env.HasType U Γ a A := ha'.defeqU_r henv hΓ ⟨_, hA.symm⟩
      have hfa' : env.HasType U Γ (.app f a) (B.inst a) := hf.app ha
      obtain ⟨_, hB''⟩ := VExpr.takeForalls_inst (a := a) (k := 0) hB
      have ⟨res, H1, H2⟩ := ih hfa' (by simpa [VExpr.mkApps] using H) hB''
      exact ⟨res, .cons ha H1, by simpa [VExpr.mkApps] using H2⟩

/-- If a body with a free occurrence of `bvar k` is well formed after substituting `a` for that
variable, then `a` itself is well formed in the context below the `k` binders. -/
theorem _root_.Lean4Lean.VExpr.WF.of_inst_occurs (henv : VEnv.WF env) {a : VExpr} :
    ∀ (B : VExpr) (Δ : List VExpr), OnCtx (Δ ++ Γ) (env.IsType U) →
      VExpr.WF env U (Δ ++ Γ) (B.inst a Δ.length) → ¬ B.Skips' 1 Δ.length →
      VExpr.WF env U Γ a := by
  intro B
  induction B with
  | bvar i =>
    intro Δ hΓ' H hocc
    simp only [VExpr.Skips', Classical.not_imp, Nat.not_lt] at hocc
    obtain ⟨h1, h2⟩ := hocc
    obtain rfl : i = Δ.length := Nat.le_antisymm (Nat.lt_succ_iff.1 h1) h2
    simp only [VExpr.inst, VExpr.instVar, Nat.lt_irrefl, if_false, if_true] at H
    exact (IsDefEqU.weakN_iff henv hΓ' (.zero Δ)).1 H
  | sort | const => exact fun _ _ _ hocc => (hocc trivial).elim
  | app f x ihf ihx =>
    intro Δ hΓ' H hocc
    simp only [VExpr.inst] at H
    have ⟨_, _, hf, hx⟩ := H.app_inv henv.ordered hΓ'
    simp only [VExpr.Skips', not_and] at hocc
    by_cases hfs : f.Skips' 1 Δ.length
    · exact ihx Δ hΓ' ⟨_, hx⟩ (hocc hfs)
    · exact ihf Δ hΓ' ⟨_, hf⟩ hfs
  | lam A e ihA ihe =>
    intro Δ hΓ' H hocc
    simp only [VExpr.inst] at H
    have ⟨⟨_, hA⟩, he⟩ := H.lam_inv henv.ordered hΓ'
    simp only [VExpr.Skips', not_and] at hocc
    by_cases hAs : A.Skips' 1 Δ.length
    · exact ihe (A.inst a Δ.length :: Δ) ⟨hΓ', _, hA⟩ (by simpa using he) (by simpa using hocc hAs)
    · exact ihA Δ hΓ' ⟨_, hA⟩ hAs
  | forallE A e ihA ihe =>
    intro Δ hΓ' H hocc
    simp only [VExpr.inst] at H
    have ⟨_, H⟩ := H
    have ⟨⟨_, hA⟩, _, he⟩ := HasType.forallE_inv henv.ordered H
    simp only [VExpr.Skips', not_and] at hocc
    by_cases hAs : A.Skips' 1 Δ.length
    · exact ihe (A.inst a Δ.length :: Δ) ⟨hΓ', _, hA⟩ (by simpa using ⟨_, he⟩)
        (by simpa using hocc hAs)
    · exact ihA Δ hΓ' ⟨_, hA⟩ hAs
  | proj _ _ e ihe =>
    intro Δ hΓ' H hocc
    simp only [VExpr.inst] at H
    have ⟨_, H⟩ := H
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      HasType.proj_inv henv.ordered hΓ' H
    exact ihe Δ hΓ' ⟨_, hmajor.hasType.2⟩ hocc

/-- Instantiate the outermost binders of a telescope body one at a time: the first argument replaces
the outermost variable (de Bruijn index `args.length - 1`), and so on. -/
def _root_.Lean4Lean.VExpr.instOuter : VExpr → List VExpr → VExpr
  | body, [] => body
  | body, a :: as => VExpr.instOuter (body.inst a as.length) as

@[simp] theorem _root_.Lean4Lean.VExpr.instOuter_nil (body : VExpr) : body.instOuter [] = body := rfl

@[simp] theorem _root_.Lean4Lean.VExpr.instOuter_cons (body a : VExpr) (as : List VExpr) :
    body.instOuter (a :: as) = (body.inst a as.length).instOuter as := rfl

@[simp] theorem _root_.Lean4Lean.VExpr.instOuter_mkApps (fn : VExpr) (xs args : List VExpr) :
    (VExpr.mkApps fn xs).instOuter args =
      VExpr.mkApps (fn.instOuter args) (xs.map fun x => x.instOuter args) := by
  induction args generalizing fn xs with
  | nil => simp
  | cons a as ih => simp [ih, List.map_map, Function.comp_def]

@[simp] theorem _root_.Lean4Lean.VExpr.instOuter_const (args : List VExpr) :
    (VExpr.const c ls).instOuter args = .const c ls := by
  induction args <;> simp [VExpr.inst, *]

theorem _root_.Lean4Lean.VExpr.instOuter_liftN (a : VExpr) (args : List VExpr) :
    (a.liftN args.length).instOuter args = a := by
  induction args with
  | nil => simp
  | cons b as ih =>
    simp only [List.length_cons, VExpr.instOuter_cons]
    rw [← VExpr.liftN'_liftN' (n1 := as.length) (n2 := 1) (Nat.zero_le _) (Nat.le_refl _)]
    simp only [Nat.add_zero]
    rw [VExpr.inst_liftN]
    exact ih

theorem _root_.Lean4Lean.VExpr.instOuter_bvar (args : List VExpr) (h : k < args.length) :
    (VExpr.bvar k).instOuter args = args[args.length - 1 - k] := by
  induction args generalizing k with
  | nil => simp at h
  | cons a as ih =>
    simp only [VExpr.instOuter_cons, VExpr.inst, VExpr.instVar]
    by_cases hk : k < as.length
    · rw [if_pos hk, ih hk, List.getElem_cons, dif_neg (by simp; omega)]
      congr 1
      simp
      omega
    · have hk' : k = as.length := by simp at h; omega
      subst hk'
      rw [if_neg hk, if_pos rfl, VExpr.instOuter_liftN]
      simp

/-- Instantiate the domains of a telescope, the `k`-th domain sitting under `k` binders. -/
def _root_.Lean4Lean.VExpr.instDomains : List VExpr → VExpr → Nat → List VExpr
  | [], _, _ => []
  | d :: ds, a, k => d.inst a k :: VExpr.instDomains ds a (k + 1)

@[simp] theorem _root_.Lean4Lean.VExpr.instDomains_length (doms : List VExpr) :
    (VExpr.instDomains doms a k).length = doms.length := by
  induction doms generalizing k <;> simp [VExpr.instDomains, *]

theorem _root_.Lean4Lean.VExpr.wrapForalls_inst (doms : List VExpr) (body a : VExpr) (k : Nat) :
    (VExpr.wrapForalls doms body).inst a k =
      VExpr.wrapForalls (VExpr.instDomains doms a k) (body.inst a (k + doms.length)) := by
  induction doms generalizing k with
  | nil => rfl
  | cons d ds ih =>
    show (VExpr.forallE d (VExpr.wrapForalls ds body)).inst a k =
      VExpr.forallE (d.inst a k) (VExpr.wrapForalls (VExpr.instDomains ds a (k + 1))
        (body.inst a (k + (ds.length + 1))))
    simp only [VExpr.inst]
    rw [ih, Nat.add_assoc, Nat.add_comm 1]

/-- A typed walk through a complete wrapped telescope instantiates its body. -/
theorem InstForalls.wrapForalls_eq (H : InstForalls env U Γ (VExpr.wrapForalls doms body) args res)
    (hlen : args.length = doms.length) : res = body.instOuter args := by
  induction args generalizing doms body res with
  | nil =>
    cases doms with
    | nil => cases H; rfl
    | cons => simp at hlen
  | cons a as ih =>
    cases doms with
    | nil => simp at hlen
    | cons dom doms =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have H' : InstForalls env U Γ ((VExpr.wrapForalls doms body).inst a 0) as res := by
        generalize hT : VExpr.wrapForalls (dom :: doms) body = T at H
        simp only [VExpr.wrapForalls, List.foldr_cons] at hT
        cases H with
        | cons _ H' => cases hT; exact H'
        | vacuous H' =>
          injection hT with _ h2
          rw [show VExpr.wrapForalls doms body = _ from h2, VExpr.inst_lift]; exact H'
      rw [VExpr.wrapForalls_inst] at H'
      have := ih H' (by simpa using hlen)
      simpa [hlen] using this

theorem _root_.Lean4Lean.VInductDecl.paramVars_instOuter (decl : VInductDecl)
    (args : List VExpr) (h : args.length = depth + decl.nparams) :
    (decl.paramVars depth).map (·.instOuter args) = args.take decl.nparams := by
  apply List.ext_getElem
  · simp [VInductDecl.paramVars]; omega
  · intro j h1 h2
    simp only [VInductDecl.paramVars, List.getElem_map, List.getElem_reverse, List.getElem_range,
      List.getElem_take, List.length_range]
    simp only [VInductDecl.paramVars, List.length_map, List.length_reverse, List.length_range,
      List.length_take] at h1 h2
    rw [VExpr.instOuter_bvar args (by omega)]
    congr 1
    omega

theorem _root_.Lean4Lean.VExpr.mkApps_getAppFnArgs_eq (e : VExpr) :
    VExpr.mkApps (VExpr.getAppFnArgs.go e []).1 (VExpr.getAppFnArgs.go e []).2 = e := by
  have go : ∀ (e : VExpr) (suffix : List VExpr),
      VExpr.mkApps (VExpr.getAppFnArgs.go e suffix).1 (VExpr.getAppFnArgs.go e suffix).2 =
        VExpr.mkApps e suffix := by
    intro e
    induction e with
    | app fn arg ihFn _ =>
      intro suffix
      simpa [VExpr.getAppFnArgs.go, VExpr.mkApps] using ihFn (arg :: suffix)
    | bvar | sort | const | proj | lam | forallE => intro suffix; rfl
  simpa [VExpr.mkApps] using go e []


/-- Fully instantiating a valid inductive application replaces its parameter variables by the
corresponding arguments. -/
theorem _root_.Lean4Lean.VInductDecl.ValidIndAppAt.instOuter {decl : VInductDecl}
    (H : decl.ValidIndAppAt (some typeName) depth result)
    (args : List VExpr) (h : args.length = depth + decl.nparams) :
    ∃ levels indices, result.instOuter args =
        VExpr.mkApps (.const typeName levels) (args.take decl.nparams ++ indices) ∧
      levels.length = decl.uvars ∧
      ∃ type ∈ decl.types, type.name = typeName ∧ indices.length = type.numIndices := by
  obtain ⟨type, htype, hname, levels, hfn, hlevels, hlen, hparams, -⟩ := H
  rcases hname with hname | hname
  · cases hname
  cases Option.some.inj hname
  have hresult := VExpr.mkApps_getAppFnArgs_eq result
  rw [hfn] at hresult
  generalize hxs : (VExpr.getAppFnArgs.go result []).2 = xs at hlen hparams hresult
  refine ⟨levels, (xs.drop decl.nparams).map (·.instOuter args), ?_, hlevels, type, htype, rfl, ?_⟩
  · have e1 : result.instOuter args = ((VExpr.const type.name levels).mkApps xs).instOuter args := by
      rw [hresult]
    rw [e1, VExpr.instOuter_mkApps, VExpr.instOuter_const]
    congr 1
    conv => lhs; rw [← List.take_append_drop decl.nparams xs]
    rw [List.map_append, hparams, decl.paramVars_instOuter args h]
  · simp [hlen]

/-- `Occurs a e d`: the term `a`, lifted over the `d` binders enclosing the position, occurs as a
subterm of `e`. -/
inductive _root_.Lean4Lean.VExpr.Occurs (a : VExpr) : VExpr → Nat → Prop
  | refl : VExpr.Occurs a (a.liftN d) d
  | appL : VExpr.Occurs a f d → VExpr.Occurs a (.app f x) d
  | appR : VExpr.Occurs a x d → VExpr.Occurs a (.app f x) d
  | lamA : VExpr.Occurs a A d → VExpr.Occurs a (.lam A b) d
  | lamB : VExpr.Occurs a b (d + 1) → VExpr.Occurs a (.lam A b) d
  | forallA : VExpr.Occurs a A d → VExpr.Occurs a (.forallE A b) d
  | forallB : VExpr.Occurs a b (d + 1) → VExpr.Occurs a (.forallE A b) d
  | proj : VExpr.Occurs a e d → VExpr.Occurs a (.proj n i e) d

/-- Instantiation acts on the occurring subterm. -/
theorem _root_.Lean4Lean.VExpr.Occurs.inst (H : VExpr.Occurs b E d) (x : VExpr) (j : Nat) :
    VExpr.Occurs (b.inst x j) (E.inst x (j + d)) d := by
  induction H with
  | @refl d' =>
    have := VExpr.liftN_instN_lo d' b x j 0 (Nat.zero_le _)
    rw [Nat.add_comm] at this
    rw [← this]
    exact .refl
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih
  | lamA _ ih => exact .lamA ih
  | lamB _ ih => exact .lamB (by simpa [Nat.add_assoc] using ih)
  | forallA _ ih => exact .forallA ih
  | forallB _ ih => exact .forallB (by simpa [Nat.add_assoc] using ih)
  | proj _ ih => exact .proj ih

theorem _root_.Lean4Lean.VExpr.Occurs.instOuter (H : VExpr.Occurs b E 0) (args : List VExpr) :
    VExpr.Occurs (b.instOuter args) (E.instOuter args) 0 := by
  induction args generalizing b E with
  | nil => exact H
  | cons a as ih =>
    simp only [VExpr.instOuter_cons]
    exact ih (by simpa using H.inst a as.length)

/-- A free variable occurs. -/
theorem _root_.Lean4Lean.VExpr.Occurs.of_not_skips' :
    ∀ (E : VExpr) (d : Nat), ¬ E.Skips' 1 (k + d) → VExpr.Occurs (.bvar k) E d := by
  intro E
  induction E with
  | bvar i =>
    intro d h
    simp only [VExpr.Skips', Classical.not_imp, Nat.not_lt] at h
    obtain rfl : i = k + d := by omega
    have : VExpr.bvar (k + d) = (VExpr.bvar k).liftN d := by
      simp [VExpr.liftN, liftVar, Nat.add_comm]
    rw [this]; exact .refl
  | sort | const => intro _ h; exact (h trivial).elim
  | app f x ihf ihx =>
    intro d h
    simp only [VExpr.Skips', not_and] at h
    by_cases hf : f.Skips' 1 (k + d)
    · exact .appR (ihx d (h hf))
    · exact .appL (ihf d hf)
  | lam A b ihA ihb =>
    intro d h
    simp only [VExpr.Skips', not_and] at h
    by_cases hA : A.Skips' 1 (k + d)
    · exact .lamB (ihb (d + 1) (by simpa [Nat.add_assoc] using h hA))
    · exact .lamA (ihA d hA)
  | forallE A b ihA ihb =>
    intro d h
    simp only [VExpr.Skips', not_and] at h
    by_cases hA : A.Skips' 1 (k + d)
    · exact .forallB (ihb (d + 1) (by simpa [Nat.add_assoc] using h hA))
    · exact .forallA (ihA d hA)
  | proj _ _ e ih => intro d h; exact .proj (ih d h)

/-- A subterm of a well-formed term is well formed, below the binders enclosing it. -/
theorem _root_.Lean4Lean.VExpr.WF.of_occurs (henv : VEnv.WF env) {a : VExpr} :
    ∀ {e : VExpr} (Δ : List VExpr), VExpr.Occurs a e Δ.length →
      OnCtx (Δ ++ Γ) (env.IsType U) → VExpr.WF env U (Δ ++ Γ) e → VExpr.WF env U Γ a := by
  intro e Δ H
  generalize hd : Δ.length = d at H
  induction H generalizing Δ with
  | refl =>
    intro hΓ' H
    subst hd
    exact (IsDefEqU.weakN_iff henv hΓ' (.zero Δ)).1 H
  | appL _ ih =>
    intro hΓ' H
    have ⟨_, _, hf, _⟩ := H.app_inv henv.ordered hΓ'
    exact ih Δ hd hΓ' ⟨_, hf⟩
  | appR _ ih =>
    intro hΓ' H
    have ⟨_, _, _, hx⟩ := H.app_inv henv.ordered hΓ'
    exact ih Δ hd hΓ' ⟨_, hx⟩
  | lamA _ ih =>
    intro hΓ' H
    have ⟨⟨_, hA⟩, _⟩ := H.lam_inv henv.ordered hΓ'
    exact ih Δ hd hΓ' ⟨_, hA⟩
  | @lamB _ _ A _ ih =>
    intro hΓ' H
    have ⟨⟨_, hA⟩, hb⟩ := H.lam_inv henv.ordered hΓ'
    exact ih (A :: Δ) (by simp [hd]) ⟨hΓ', _, hA⟩ hb
  | forallA _ ih =>
    intro hΓ' H
    have ⟨_, H⟩ := H
    have ⟨⟨_, hA⟩, _⟩ := HasType.forallE_inv henv.ordered H
    exact ih Δ hd hΓ' ⟨_, hA⟩
  | @forallB _ _ A _ ih =>
    intro hΓ' H
    have ⟨_, H⟩ := H
    have ⟨⟨_, hA⟩, _, hb⟩ := HasType.forallE_inv henv.ordered H
    exact ih (A :: Δ) (by simp [hd]) ⟨hΓ', _, hA⟩ ⟨_, hb⟩
  | proj _ ih =>
    intro hΓ' H
    have ⟨_, H⟩ := H
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      HasType.proj_inv henv.ordered hΓ' H
    exact ih Δ hd hΓ' ⟨_, hmajor.hasType.2⟩

/-- Instantiating a variable that does not occur is irrelevant: the corresponding argument may be
replaced by any other term. -/
theorem _root_.Lean4Lean.VExpr.instOuter_set_of_skips :
    ∀ (args : List VExpr) (E : VExpr), k < args.length → E.Skips 1 k →
      E.instOuter args = E.instOuter (args.set (args.length - 1 - k) b) := by
  intro args
  induction args with
  | nil => intro _ h; simp at h
  | cons a as ih =>
    intro E hk hs
    obtain ⟨E', rfl⟩ := VExpr.skips_iff_exists.1 hs
    simp only [List.length_cons] at hk
    by_cases hkm : k = as.length
    · subst hkm
      simp [VExpr.inst_liftN]
    · have hk' : k < as.length := by omega
      have e1 : (VExpr.liftN 1 E' k).inst a as.length = VExpr.liftN 1 (E'.inst a (as.length - 1)) k := by
        have := VExpr.liftN_instN_lo 1 E' a (as.length - 1) k (by omega)
        rw [this]; congr 1; omega
      have e2 : (VExpr.liftN 1 E' k).inst b as.length = VExpr.liftN 1 (E'.inst b (as.length - 1)) k := by
        have := VExpr.liftN_instN_lo 1 E' b (as.length - 1) k (by omega)
        rw [this]; congr 1; omega
      have hidx : (a :: as).length - 1 - k = (as.length - 1 - k) + 1 := by simp; omega
      rw [hidx, List.set_cons_succ]
      simp only [VExpr.instOuter_cons, List.length_set]
      rw [e1]
      exact ih _ hk' .liftN

end VEnv
end Lean4Lean
