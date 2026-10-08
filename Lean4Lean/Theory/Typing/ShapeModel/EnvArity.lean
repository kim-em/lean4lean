import Lean4Lean.Theory.Typing.ShapeModel.EnvRuleShape

/-!
# Field counts of native equations versus constructor arities

A compiled declaration describes its constructors by a *normalized* signature whose constructor
types are only definitionally equal to the source constructor types (`Models.constructors`,
`RestoresFamily.constructors`). The number of fields of a native equation is the normalized
count, while the constructor tables count the syntactic binders of the source constructor
type. Equating the two needs that definitionally equal telescopes ending in constant
applications have the same length (`ForallArityRigid`), a consequence of Pi injectivity and
rigid/Pi separation. It is *not* derivable in the uniqueness-free base, so it is a hypothesis
here; it is used only in the header environment of the compilation, which lies below the
environment in which the equation is installed.
-/

namespace Lean4Lean.ShapeModel
open VEnv InductiveSignature

/-- `e` is an application spine headed by a constant. -/
def isConstApp : VExpr → Bool
  | .app f _ => isConstApp f
  | .const .. => true
  | _ => false

/-- The length of a forall telescope ending in a constant application. -/
def teleArity : VExpr → Option Nat
  | .forallE _ b => (teleArity b).map (· + 1)
  | e => if isConstApp e then some 0 else none

/-- Definitionally equal telescopes ending in constant applications have the same length. -/
def ForallArityRigid (env : VEnv) : Prop :=
  ∀ {U : Nat} {e e' : VExpr} {n m : Nat}, teleArity e = some n → teleArity e' = some m →
    env.IsDefEqU U [] e e' → n = m

theorem ForallArityRigid.mono {env env' : VEnv} (H : ForallArityRigid env') (hle : env ≤ env') :
    ForallArityRigid env := fun h h' ⟨_, hd⟩ => H h h' ⟨_, hd.mono hle⟩

theorem isConstApp_mkApps : isConstApp (VExpr.mkApps (.const c ls) args) = true := by
  suffices ∀ f, isConstApp f = true → isConstApp (VExpr.mkApps f args) = true from
    this _ rfl
  induction args with
  | nil => intro f h; exact h
  | cons a args ih => intro f h; exact ih (.app f a) h

theorem teleArity_mkApps : teleArity (VExpr.mkApps (.const c ls) args) = some 0 := by
  have h := isConstApp_mkApps (c := c) (ls := ls) (args := args)
  generalize VExpr.mkApps (.const c ls) args = e at h
  cases e <;> simp_all [teleArity, isConstApp]

theorem teleArity_of_isConstApp {e : VExpr} (h : isConstApp e = true) : teleArity e = some 0 := by
  cases e <;> simp_all [teleArity, isConstApp]

theorem teleArity_wrapForalls {body : VExpr} (h : teleArity body = some n) :
    teleArity (VExpr.wrapForalls doms body) = some (doms.length + n) := by
  induction doms with
  | nil => simpa [VExpr.wrapForalls] using h
  | cons d ds ih =>
    simp only [VExpr.wrapForalls, List.foldr_cons] at ih ⊢
    simp only [teleArity, ih, Option.map_some, List.length_cons]
    congr 1; omega

theorem teleArity_ctorShape :
    teleArity (VExpr.wrapForalls doms (VExpr.mkApps (.const c ls) args)) = some doms.length := by
  simpa using teleArity_wrapForalls (doms := doms) teleArity_mkApps

theorem isConstApp_subst {e : VExpr} (h : isConstApp e = true) (σ : VExpr.Subst) :
    isConstApp (e.subst σ) = true := by
  induction e with
  | app f _ ih _ => exact ih h
  | const => rfl
  | _ => simp [isConstApp] at h

theorem teleArity_subst {e : VExpr} (h : teleArity e = some n) (σ : VExpr.Subst) :
    teleArity (e.subst σ) = some n := by
  induction e generalizing n σ with
  | forallE d b _ ih =>
    simp only [teleArity, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    simp [VExpr.subst, teleArity, ih hm]
  | _ =>
    simp only [teleArity] at h
    split at h <;> cases h
    rename_i hc
    exact teleArity_of_isConstApp (isConstApp_subst hc σ)

theorem isConstApp_instL {e : VExpr} (h : isConstApp e = true) (ls : List VLevel) :
    isConstApp (e.instL ls) = true := by
  induction e with
  | app f _ ih _ => exact ih h
  | const => rfl
  | _ => simp [isConstApp] at h

theorem teleArity_instL {e : VExpr} (h : teleArity e = some n) (ls : List VLevel) :
    teleArity (e.instL ls) = some n := by
  induction e generalizing n with
  | forallE d b _ ih =>
    simp only [teleArity, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    simp [VExpr.instL, teleArity, ih hm]
  | _ =>
    simp only [teleArity] at h
    split at h <;> cases h
    rename_i hc
    exact teleArity_of_isConstApp (isConstApp_instL hc ls)

theorem isConstApp_eq {e : VExpr} (h : isConstApp e = true) :
    ∃ c ls args, e = VExpr.mkApps (.const c ls) args := by
  induction e with
  | app f a ih _ =>
    obtain ⟨c, ls, args, rfl⟩ := ih h
    exact ⟨c, ls, args ++ [a], by simp [VExpr.mkApps, List.foldl_append]⟩
  | const c ls => exact ⟨c, ls, [], rfl⟩
  | _ => simp [isConstApp] at h

theorem teleArity_restore {r : Restoration} {e e' : VExpr} (h : teleArity e = some n)
    (hr : r.expr e = some e') : teleArity e' = some n := by
  induction e generalizing n e' with
  | forallE d b _ ih =>
    simp only [teleArity, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    change (do let d' ← Restoration.expr.go r d []; let b' ← Restoration.expr.go r b []
               pure (VExpr.mkApps (.forallE d' b') [])) = some e' at hr
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr
    obtain ⟨d', _, b', hb, rfl⟩ := hr
    simp [VExpr.mkApps, teleArity, ih hm hb]
  | _ =>
    simp only [teleArity] at h
    split at h <;> cases h
    rename_i hc
    obtain ⟨c, ls, args, he⟩ := isConstApp_eq hc
    rw [he] at hr
    obtain ⟨ls', args', rfl⟩ := r.const_mkApps hr
    exact teleArity_mkApps

theorem teleArity_takeForalls {e body : VExpr} {ds : List VExpr} (h : teleArity e = some n)
    (ht : e.takeForalls k = some (ds, body)) : k ≤ n ∧ teleArity body = some (n - k) := by
  induction k generalizing e n ds with
  | zero =>
    cases Option.some.inj ht
    simpa using h
  | succ k ih =>
    cases e with
    | forallE d b =>
      cases hb : b.takeForalls k with
      | none => simp [VExpr.takeForalls, hb] at ht
      | some out =>
        rw [VExpr.takeForalls, hb] at ht
        cases Option.some.inj ht
        simp only [teleArity, Option.map_eq_some_iff] at h
        obtain ⟨m, hm, rfl⟩ := h
        obtain ⟨h1, h2⟩ := ih hm hb
        exact ⟨by omega, by simpa using h2⟩
    | _ => simp [VExpr.takeForalls] at ht

theorem teleArity_specializeType {type t : VExpr} {args : List VExpr}
    (h : teleArity type = some n) (hs : specializeType type args = some t) :
    args.length ≤ n ∧ teleArity t = some (n - args.length) := by
  simp only [specializeType, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs
  obtain ⟨⟨ds, body⟩, ht, rfl⟩ := hs
  obtain ⟨h1, h2⟩ := teleArity_takeForalls h ht
  exact ⟨h1, teleArity_subst h2 _⟩

theorem teleArity_of_head {e : VExpr} (h : e.getAppFnArgs.1 = .const c ls) :
    teleArity e = some 0 := by
  rw [← mkApps_getAppFnArgs e, h]; exact teleArity_mkApps

theorem teleArity_of_forallResult {e : VExpr} (h : e.forallResult.getAppFnArgs.1 = .const c ls) :
    teleArity e = some e.forallArity := by
  induction e with
  | forallE d b _ ih =>
    simp only [teleArity, ih h, Option.map_some, VExpr.forallArity]
  | _ =>
    simp only [VExpr.forallResult] at h
    simpa [VExpr.forallArity] using teleArity_of_head h

theorem directFamily_ctor {a : ContainerSpecialization} {uvars : Nat} {params : List VExpr}
    {direct : VInductiveType} (H : a.directFamily uvars params = some direct)
    (hdc : dc ∈ direct.ctors) :
    ∃ c ∈ a.source.ctors, ∃ t, specializeType (c.type.instL a.levels) a.arguments = some t ∧
      dc.name = a.constructorName c ∧ dc.type = VExpr.wrapForalls params t := by
  unfold ContainerSpecialization.directFamily at H
  cases htype : specializeType (a.source.type.instL a.levels) a.arguments with
  | none => simp [htype] at H
  | some type =>
    simp [htype] at H
    rcases H with ⟨ctors, hctors, H⟩
    cases H
    obtain ⟨c, hc, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hctors) dc hdc
    cases hspec : specializeType (c.type.instL a.levels) a.arguments with
    | none => simp [hspec] at hrel
    | some t =>
      simp [hspec] at hrel
      cases hrel
      exact ⟨c, hc, t, hspec, rfl, rfl⟩

theorem addConstVals_le_of {base E envTypes : VEnv} {cis : List VConstVal}
    (h : base.addConstVals cis = some envTypes) (hle : base ≤ E)
    (hc : ∀ ci ∈ cis, E.constants ci.name = some ci.toVConstant) : envTypes ≤ E := by
  induction cis generalizing base with
  | nil => simp [VEnv.addConstVals] at h; subst h; exact hle
  | cons ci cis ih =>
    cases hadd : base.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hadd] at h
    | some mid =>
      simp [VEnv.addConstVals, hadd] at h
      refine ih h ?_ (fun c hc' => hc c (List.mem_cons_of_mem _ hc'))
      refine ⟨fun {n x} hn => ?_, fun hd => ?_, fun hp => ?_, fun he => ?_⟩
      · rw [VEnv.addConst_constants_eq hadd] at hn
        by_cases he : ci.name = n
        · simp only [he, if_true, Option.some.injEq] at hn
          subst hn; rw [← he]; exact hc ci List.mem_cons_self
        · simp only [he, if_false] at hn; exact hle.constants hn
      · rw [VEnv.addConst_defeqs hadd] at hd; exact hle.defeqs hd
      · rw [VEnv.addConst_projections hadd] at hp; exact hle.projections hp
      · rw [VEnv.addConst_eliminators hadd] at he; exact hle.eliminators he

/-- Field counts of a compilation's equations against the source constructor arities. -/
theorem CaseCompilationData.ctor_arity {base E : VEnv} {src exp : VInductDecl}
    {s : InductiveSignature} {aux : List ContainerSpecialization}
    {block : VInductBlock}
    (hdata : CaseCompilationData base src exp s aux block)
    (hrfresh : RecursorNamesFresh base src exp aux)
    (hprior : CertifiedSpecializations base aux)
    (hP : ForallArityRigid E) (hle : base ≤ E)
    (htypes : ∀ t ∈ src.types, E.constants t.name = some t.toVConstant)
    (index : Fin s.constructors.size) :
    (∃ F ∈ src.types, ∃ c ∈ F.ctors, s.constructors[index].name = c.name ∧
      (compilationRestoration src aux).headName s.constructors[index].name = c.name ∧
      s.params.length + s.constructors[index].fields.length = c.type.forallArity) ∨
    (∃ a ∈ aux, ∃ c ∈ a.source.ctors, s.constructors[index].name = a.constructorName c ∧
      (compilationRestoration src aux).headName s.constructors[index].name = c.name ∧
      s.constructors[index].fields.length + a.arguments.length = c.type.forallArity) := by
  obtain ⟨envTypes, direct, hT, hdirect, _, hfamilies⟩ := hdata.correspondence
  have hTE : envTypes ≤ E := addConstVals_le_of hT hle (fun ci hci => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hci; exact htypes t ht)
  have hP' : ForallArityRigid envTypes := hP.mono hTE
  obtain ⟨fam, hfam, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l hfamilies _
    (s.declarationFamily_mem s.constructors[index].owner)
  obtain ⟨sc, hsc, hname, _, restored, hres, hdefeq⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors _ (s.declarationCtor_family index)
  have hnorm : teleArity (s.declarationCtor index).type =
      some (s.params.length + s.constructors[index].fields.length) := by
    have := teleArity_ctorShape (doms := s.params ++ s.fieldTypes s.constructors[index])
      (c := s.families[s.constructors[index].owner].name) (ls := VLevel.params s.uvars)
      (args := vars s.params.length s.constructors[index].fields.length ++
        s.constructors[index].indices)
    simpa [declarationCtor, constructorType, familyApp, fieldTypes] using this
  have hrestA := teleArity_restore hnorm hres
  have hname' : s.constructors[index].name = sc.name := hname
  rcases List.mem_append.mp hfam with hsrc | hdir
  · left
    refine ⟨fam, hsrc, sc, hsc, hname', ?_, ?_⟩
    · rw [hname']
      exact hdata.headName_source hrfresh (List.mem_flatMap.mpr ⟨fam, hsrc,
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨sc, hsc, rfl⟩)⟩)
    · obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
      obtain ⟨doms, result, heq, _, _, hhead, harity⟩ := (hraw fam hsrc sc hsc).forallArity
      have hsrcA : teleArity sc.type = some sc.type.forallArity := by
        rw [harity, heq]; simpa using teleArity_wrapForalls (doms := doms) (teleArity_of_head hhead)
      exact hP' hrestA hsrcA hdefeq
  · right
    obtain ⟨a, ha, hdf⟩ := Lean4Lean.List.Forall₂.forall_exists_r
      (List.mapM_eq_some.mp hdirect) fam hdir
    obtain ⟨c, hc, t, hspec, hdcn, hdct⟩ := directFamily_ctor hdf hsc
    refine ⟨a, ha, c, hc, hname'.trans hdcn, ?_, ?_⟩
    · rw [hname', hdcn]
      exact hdata.headName_auxiliary_constructor ha hc
    · obtain ⟨_, ls, hres'⟩ := (hprior.container_ctor a ha c hc)
      have hcA := teleArity_instL (teleArity_of_forallResult hres') a.levels
      obtain ⟨hk, htA⟩ := teleArity_specializeType hcA hspec
      have hscA : teleArity sc.type = some (s.params.length + (c.type.forallArity -
          a.arguments.length)) := by
        rw [hdct]; exact teleArity_wrapForalls htA
      have := hP' hrestA hscA hdefeq
      omega

end Lean4Lean.ShapeModel
