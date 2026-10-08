import Lean4Lean.Theory.Typing.EnvTables.EnvTables

/-!
# Shapes of installed native equations (M4a, T2)

A restored native recursor equation is a lambda telescope over the parameters, motives, minors
and constructor fields; its left body applies the recursor to the parameter, motive and minor
variables, to arbitrary index expressions, and to a constructor application whose trailing
arguments are the field variables. Restoration may specialize the constructor's parameters
(nested auxiliaries), but never touches the field variables.
-/

namespace Lean4Lean.EnvTables
open VEnv InductiveSignature

theorem restoration_vars' (r : Restoration) (count below : Nat) :
    (vars count below).mapM r.expr = some (vars count below) := by
  unfold vars
  generalize (List.range count).reverse = is
  induction is with
  | nil => rfl
  | cons i is ih =>
    simpa [List.mapM_cons, Restoration.expr, Restoration.expr.go, VExpr.mkApps] using ih

theorem vars_length (count below : Nat) : (vars count below).length = count := by
  simp [vars]

theorem vars_append (p f : Nat) : vars p f ++ vars f 0 = vars (p + f) 0 := by
  rw [Nat.add_comm p f]
  simp [vars, List.range_add, List.reverse_append, List.map_append, List.map_map]

/-- Restoration of a constructor application with parameter and field variables. -/
theorem restored_ctorApp {r : Restoration} {np e nf : Nat}
    (hparams : ∀ h ∈ r.heads, h.nparams = np) {name : Name} {levels : List VLevel}
    {out : VExpr}
    (h : r.expr (VExpr.mkApps (.const name levels) (vars np (e + nf) ++ vars nf 0)) = some out) :
    (r.heads.find? (fun h => h.auxiliary == name) = none ∧
      out = VExpr.mkApps (.const (r.recursorName name) levels) (vars np (e + nf) ++ vars nf 0)) ∨
    (∃ spec ∈ r.heads, r.heads.find? (fun h => h.auxiliary == name) = some spec ∧
      levels.length = spec.uvars ∧
      out = VExpr.mkApps (.const spec.target (spec.levels.map (·.inst levels)))
        (spec.arguments.map (fun arg => instantiateParams (arg.instL levels) (vars np (e + nf)))
          ++ vars nf 0)) := by
  change Restoration.expr.go r (VExpr.mkApps (.const name levels) _) [] = _ at h
  rw [restoration_mkApps] at h
  simp only [List.mapM_append, restoration_vars', bind, Option.bind_some, pure,
    List.append_nil] at h
  simp only [Restoration.expr.go] at h
  split at h
  · rename_i spec hspec
    have hmem := List.mem_of_find?_eq_some hspec
    have hnp := hparams spec hmem
    unfold HeadSpecialization.apply at h
    split at h
    · cases h
    · rename_i hcond
      cases h
      refine .inr ⟨spec, hmem, hspec, ?_, ?_⟩
      · simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.or_eq_true, not_or] at hcond
        exact Classical.not_not.mp hcond.1
      · rw [hnp, List.take_left' (vars_length np (e + nf)), List.drop_left' (vars_length np (e + nf))]
  · rename_i hnone
    cases h
    exact .inl ⟨hnone, rfl⟩

theorem compilationRestoration_nparams {source : VInductDecl}
    {aux : List ContainerSpecialization} :
    ∀ h ∈ (compilationRestoration source aux).heads, h.nparams = source.nparams := by
  intro h hh
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hh
  simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at ha
  rcases ha with rfl | ⟨c, _, rfl⟩ <;> rfl

/-- T2 for one restored native equation of a finite compilation. -/
theorem CompilationData.rule_shape
    {s : InductiveSignature} {g : Instance s} {aux : List ContainerSpecialization}
    {block : VInductBlock} {env : VEnv} {src exp : VInductDecl} {df : VDefEq}
    (hdata : CompilationData env src exp s g aux block)
    (index : Fin s.constructors.size)
    (hrestore : (compilationRestoration src aux).equation (g.equation index) = some df) :
    ∃ (Ds idx : List VExpr) (R major : VExpr),
      df.lhs = VExpr.wrapLams Ds (VExpr.mkApps
        (.const ((compilationRestoration src aux).recursorName
          (g.recursorName s.constructors[index].owner)) (VLevel.params g.uvars))
        (vars (s.params.length + (s.families.size + s.constructors.size))
          s.constructors[index].fields.length ++ idx ++ [major])) ∧
      df.rhs = VExpr.wrapLams Ds R ∧
      Ds.length = s.params.length + (s.families.size + s.constructors.size) +
        s.constructors[index].fields.length ∧
      idx.length = s.constructors[index].indices.length ∧
      df.uvars = g.uvars ∧
      (((compilationRestoration src aux).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = none ∧
        major = VExpr.mkApps (.const ((compilationRestoration src aux).recursorName
          s.constructors[index].name) g.levels)
          (vars s.params.length (s.families.size + s.constructors.size +
            s.constructors[index].fields.length) ++ vars s.constructors[index].fields.length 0)) ∨
      (∃ spec ∈ (compilationRestoration src aux).heads,
        (compilationRestoration src aux).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = some spec ∧
        g.levels.length = spec.uvars ∧
        major = VExpr.mkApps (.const spec.target (spec.levels.map (·.inst g.levels)))
          (spec.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
            (vars s.params.length (s.families.size + s.constructors.size +
              s.constructors[index].fields.length))) ++
            vars s.constructors[index].fields.length 0))) := by
  let r := compilationRestoration src aux
  obtain ⟨hl, hr, ht⟩ := Restoration.equation_parts hrestore
  obtain ⟨Ds, lBody, rBody, tBody, hlBody, _, _, hel, her, _, hlen⟩ :=
    restored_common_telescope hl hr ht
  let ctor := s.constructors[index]
  let nf := ctor.fields.length
  let extra := s.families.size + s.constructors.size
  let np := s.params.length
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra nf
  have hnone : r.heads.find? (fun h => h.auxiliary == g.recursorName ctor.owner) = none := by
    apply List.find?_eq_none.mpr
    intro spec hs
    simpa only [beq_iff_eq] using hdata.heads_not_recursors ctor.owner spec hs
  change r.expr (VExpr.mkApps (.const (g.recursorName ctor.owner) (VLevel.params g.uvars))
    (vars (np + extra) nf ++ indices ++ [g.constructorApp ctor extra 0])) = some lBody at hlBody
  change Restoration.expr.go r (VExpr.mkApps _ _) [] = _ at hlBody
  rw [restoration_mkApps] at hlBody
  simp only [List.mapM_append, restoration_vars', List.mapM_cons, List.mapM_nil, bind,
    Option.bind_eq_some_iff, pure, Option.some.injEq] at hlBody
  obtain ⟨_, ⟨_, ⟨_, rfl, idx', hi, rfl⟩, _, ⟨major', hmajor, _, rfl, rfl⟩, rfl⟩, hout⟩ := hlBody
  simp only [List.append_nil, Restoration.expr.go, hnone] at hout
  have hidx : idx'.length = ctor.indices.length := by
    have := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hi)
    simpa [indices] using this.symm
  have hparams : ∀ h ∈ r.heads, h.nparams = np := by
    intro h hh
    rw [compilationRestoration_nparams h hh, ← hdata.nparams, ← hdata.model.nparams]
  have hmaj := restored_ctorApp (e := extra) hparams (by
    simpa only [Instance.constructorApp, Nat.add_zero] using hmajor)
  refine ⟨Ds, idx', rBody, major', ?_, her, ?_, hidx, ?_, hmaj⟩
  · rw [hel, ← Option.some.inj hout]
  · rw [hlen]
    simp [Instance.equation, Instance.params, Instance.motives, Instance.minors,
      insertBinders, fieldTypes]
    omega
  · simp only [Restoration.equation, bind, Option.bind_eq_some_iff] at hrestore
    obtain ⟨_, _, _, _, _, _, he⟩ := hrestore
    cases he
    rfl

/-- The shape of a computation rule with a constructor major (T2): a lambda telescope `Ds`
shared by both sides; the left body applies `head` (at its own universe parameters) to the
`npre` distinct prefix variables (parameters, motives, minors), arbitrary index expressions
`idx`, and the constructor `c` applied to parameter expressions `ps` and the `nf` distinct
trailing field variables. The prefix variables and the field variables together are all the
binders (`vars_append`). -/
def RuleShape (df : VDefEq) (head : Name) (npre nf : Nat) (idx : List VExpr) (c : Name)
    (lv : List VLevel) (ps : List VExpr) : Prop :=
  ∃ Ds R, df.lhs = VExpr.wrapLams Ds (VExpr.mkApps (.const head (VLevel.params df.uvars))
      (vars npre nf ++ idx ++ [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)])) ∧
    df.rhs = VExpr.wrapLams Ds R ∧ Ds.length = npre + nf

/-- The quotient equation has the rule shape (two parameters, `β`, `f`, `c` as prefix
variables, one field). -/
theorem quot_ruleShape :
    RuleShape quotDefEq ``Quot.lift 5 1 [] ``Quot.mk [.param 0] [.bvar 5, .bvar 4] :=
  ⟨[.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort (.param 1),
    .forallE (.bvar 2) (.bvar 1),
    .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
        (.app (.bvar 3) (.bvar 1))))),
    .bvar 4], _, rfl, rfl, rfl⟩

/-- The native equation `data.equation index` of a registered recursor has the rule shape. -/
theorem ruleShape_of_registered {env : VEnv} {data : NativeRecursorData}
    (H : VEnv.NativeRecursorRegistered env data)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hgen : data.equation index = some df) :
    ∃ npre idx lv ps, RuleShape df data.name npre
      data.schema.signature.constructors[index].fields.length idx
      (data.schema.restoration.headName data.schema.signature.constructors[index].name) lv ps ∧
      npre = data.schema.signature.params.length +
        (data.schema.signature.families.size + data.schema.signature.constructors.size) ∧
      idx.length = data.schema.signature.constructors[index].indices.length := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, _, _⟩ := H
  have hinstance : data.nativeInstance = g := by
    cases g with
    | mk U levels target recNames =>
      simp only [NativeRecursorData.nativeInstance, Instance.mk.injEq]
      exact ⟨hu, hl, ht, funext fun owner => (hdata.recursorNames owner).symm⟩
  have hg : (compilationRestoration source auxiliaries).equation (g.equation index) = some df := by
    simpa only [NativeRecursorData.equation, hinstance, hr] using hgen
  obtain ⟨Ds, idx, R, major, hlhs, hrhs, hlen, hidx, huv, hmaj⟩ :=
    CompilationData.rule_shape hdata index hg
  have hname : (compilationRestoration source auxiliaries).recursorName
      (g.recursorName data.schema.signature.constructors[index].owner) = data.name := by
    rw [hdata.recursorNames, howner, ← hr]; rfl
  rw [hname] at hlhs
  have hu' : VLevel.params g.uvars = VLevel.params df.uvars := by rw [huv]
  rw [hu'] at hlhs
  rcases hmaj with ⟨hnone, rfl⟩ | ⟨spec, _, hsome, _, rfl⟩
  · refine ⟨_, idx, g.levels, vars data.schema.signature.params.length
      (data.schema.signature.families.size + data.schema.signature.constructors.size +
        data.schema.signature.constructors[index].fields.length),
      ⟨Ds, R, ?_, hrhs, hlen⟩, rfl, hidx⟩
    rw [← hr] at hnone
    rw [hlhs, Restoration.headName, hnone, hr]
  · refine ⟨_, idx, spec.levels.map (·.inst g.levels),
      spec.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
        (vars data.schema.signature.params.length (data.schema.signature.families.size +
          data.schema.signature.constructors.size +
          data.schema.signature.constructors[index].fields.length))),
      ⟨Ds, R, ?_, hrhs, hlen⟩, rfl, hidx⟩
    rw [← hr] at hsome
    rw [hlhs, Restoration.headName, hsome]

/-- T2: every equation of a well-formed environment is a definition (no binders, no arguments:
`lhs = .const v.name (VLevel.params v.uvars)`), the quotient equation, or a native equation of
its recursor entry, and the latter two have the rule shape (`RuleShape`). The prefix arguments
are distinct variables; the index arguments are arbitrary (they may repeat a parameter variable,
as in `Eq.rec`, so "all variable arguments before the major are distinct" is false in general). -/
theorem equation_shape {env : VEnv} (H : env.WF) (hdf : env.defeqs df) :
    (∃ v : VDefVal, df = v.toDefEq ∧ df.lhs = .const v.name (VLevel.params v.uvars)) ∨
    (df = quotDefEq ∧
      RuleShape quotDefEq ``Quot.lift 5 1 [] ``Quot.mk [.param 0] [.bvar 5, .bvar 4]) ∨
    (∃ data, (envTables env).natives data.name = some data ∧
      VEnv.NativeRecursorRegistered env data ∧
      ∃ index : Fin data.schema.signature.constructors.size,
        data.schema.signature.constructors[index].owner = data.owner ∧
        data.equation index = some df ∧
        ∃ npre idx lv ps, RuleShape df data.name npre
          data.schema.signature.constructors[index].fields.length idx
          (data.schema.restoration.headName data.schema.signature.constructors[index].name)
          lv ps ∧
        npre = data.schema.signature.params.length +
          (data.schema.signature.families.size + data.schema.signature.constructors.size) ∧
        idx.length = data.schema.signature.constructors[index].indices.length) := by
  rcases (envTables_inv H).equations hdf with ⟨v, _, rfl⟩ | ⟨_, rfl⟩ | ⟨data, hd, index, howner, hgen⟩
  · exact .inl ⟨v, rfl, rfl⟩
  · exact .inr (.inl ⟨rfl, quot_ruleShape⟩)
  · have hreg := ((envTables_inv H).natives hd).2.registered
    exact .inr (.inr ⟨data, hd, hreg, index, howner, hgen, ruleShape_of_registered hreg howner hgen⟩)

end Lean4Lean.EnvTables
