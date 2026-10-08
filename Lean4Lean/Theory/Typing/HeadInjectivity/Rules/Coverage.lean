import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.PatShape
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Typing.NativeConstructorRigidity
import Lean4Lean.Theory.Inductive.CaseRegistration
import Batteries.Tactic.OpenPrivate

/-! Coverage: every computation rule of a well-formed environment, and every
generic case equation of a registered eliminator schema, has the pattern shape.

The origin of an installed rule is recomputed here by induction on the
declaration history (`VEnv.WF'.defeq_origin`) rather than taken from
`WF'.nativeRegistry`, whose module transitively imports `ChurchRosser` and
`HeadInversion`. -/

namespace Lean4Lean
open InductiveSignature
open private addDefEqs_as_rules addConsts_as_values defeqs_addRules
  from Lean4Lean.Theory.Typing.NativeConstructorRigidity

/-- The restoration table of a finite compilation specializes exactly the
common parameters. -/
theorem InductiveSignature.CompilationData.restoration_nparams {s : InductiveSignature}
    {g : Instance s} (H : CompilationData env source expanded s g auxiliaries block) :
    ∀ head ∈ (compilationRestoration source auxiliaries).heads,
      head.nparams = s.params.length := by
  intro head hhead
  obtain ⟨a, _, hhead⟩ := List.mem_flatMap.mp hhead
  have hn := H.model.nparams.trans H.nparams
  change head ∈ _ :: _ at hhead
  rcases List.mem_cons.mp hhead with rfl | hhead
  · exact hn.symm
  · obtain ⟨ctor, _, rfl⟩ := List.mem_map.mp hhead
    exact hn.symm

/-- A restored native recursor equation of a finite compilation has the pattern
shape, headed by the restored recursor constant. -/
theorem InductiveSignature.CompilationData.equation_patShape {s : InductiveSignature}
    {g : Instance s} (H : CompilationData env source expanded s g auxiliaries block)
    (index : Fin s.constructors.size) {df : VDefEq}
    (he : (compilationRestoration source auxiliaries).equation (g.equation index) = some df) :
    df.PatShape (.const ((compilationRestoration source auxiliaries).recursorName
      (g.recursorName s.constructors[index].owner)) (VLevel.params g.uvars)) :=
  g.equation_patShape index .native
    (fun h hh => Nat.le_of_eq (H.restoration_nparams h hh))
    (fun _ _ heq h hh => by
      cases heq
      exact H.heads_not_recursors _ h hh) he

/-- A restored native recursor equation is never a bare constant. -/
theorem InductiveSignature.CompilationData.equation_not_const {s : InductiveSignature}
    {g : Instance s} (H : CompilationData env source expanded s g auxiliaries block)
    (index : Fin s.constructors.size) {df : VDefEq}
    (he : (compilationRestoration source auxiliaries).equation (g.equation index) = some df) :
    ∀ n ls, df.lhs ≠ .const n ls :=
  (g.equation_patShape_strong index .native
    (fun h hh => Nat.le_of_eq (H.restoration_nparams h hh))
    (fun _ _ heq h hh => by
      cases heq
      exact H.heads_not_recursors _ h hh) he).2

/-- Exact origin of every installed rule: a definition's delta rule, the quotient
rule, or a restored equation of a finite inductive compilation. -/
theorem VEnv.WF'.defeq_origin {env : VEnv} (H : env.WF' ds) {df : VDefEq}
    (hdf : env.defeqs df) :
    (∃ ci : VDefVal, df = ci.toDefEq) ∨ df = quotDefEq ∨
    ∃ (base : VEnv) (source expanded : VInductDecl) (s : InductiveSignature) (g : Instance s)
      (auxiliaries : List ContainerSpecialization) (block : VInductBlock)
      (index : Fin s.constructors.size),
      CompilationData base source expanded s g auxiliaries block ∧
      (compilationRestoration source auxiliaries).equation (g.equation index) = some df := by
  induction H with
  | empty => cases hdf
  | decl declaration _ ih =>
    cases declaration with
    | «axiom» _ installed | «opaque» _ installed =>
      exact ih (by rwa [VEnv.addConst_defeqs installed] at hdf)
    | «example» => exact ih hdf
    | «def» _ installed =>
      rcases hdf with rfl | hdf
      · exact .inl ⟨_, rfl⟩
      · exact ih (by rwa [VEnv.addConst_defeqs installed] at hdf)
    | mutualDef _ installed _ =>
      rw [addDefEqs_as_rules, defeqs_addRules] at hdf
      rcases hdf with member | hdf
      · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp member
        exact .inl ⟨ci, rfl⟩
      · exact ih (by rwa [VEnv.addConstVals_defeqs (addConsts_as_values ▸ installed)] at hdf)
    | quot _ installed =>
      simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at installed
      obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := installed
      rcases hdf with rfl | hdf
      · exact .inr (.inl rfl)
      · exact ih (by
          rwa [VEnv.addConst_defeqs hd, VEnv.addConst_defeqs hc,
            VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at hdf)
    | induct _ installed =>
      cases installed with
      | intro _ compiled _ installed =>
        obtain ⟨base, expanded, signature, generated, auxiliaries, _, compilation, _⟩ :=
          compiled.compiled.compilationOrigin
        have hrules := compilation.equations
        simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at installed
        obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := installed
        rw [defeqs_addRules] at hdf
        rcases hdf with member | hdf
        · obtain ⟨source, hsource, hrestore⟩ :=
            Lean4Lean.List.Forall₂.forall_exists_r (List.mapM_eq_some.mp hrules) _ member
          obtain ⟨index, _, rfl⟩ := List.mem_map.mp hsource
          exact .inr (.inr ⟨_, _, _, _, _, _, _, index, compilation, hrestore⟩)
        · exact ih (by
            rwa [VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs,
              VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at hdf)
  | inductEliminators _ _ _ _ _ _ _ _ _ ih => exact ih hdf
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ih (by simpa only [VEnv.addProjections_defeqs] using hdf)

private def lamDoms : VExpr → List VExpr
  | .lam d b => d :: lamDoms b
  | _ => []

private def forallBody : VExpr → VExpr
  | .forallE _ b => forallBody b
  | e => e

/-- The quotient rule `Quot.lift α r β f c (Quot.mk α r a) ≡ f a` has the pattern
shape: `α r β f c` are bare leading variables and `a` is the major's field. -/
theorem quotDefEq_patShape :
    quotDefEq.PatShape (.const `Quot.lift [.param 0, .param 1]) := by
  refine ⟨⟨lamDoms quotDefEq.lhs, [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
    VExpr.mkApps (.const `Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]],
    quotDefEq.rhs.stripLams, forallBody quotDefEq.type, rfl, rfl, rfl, ?_⟩⟩
  refine .inr ⟨[.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1], `Quot.mk, [.param 0],
    [.bvar 5, .bvar 4], [0], rfl, by simp, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact Nat.zero_lt_succ _
  · intro x hx
    change x < 6 at hx
    simp only [List.mem_cons, VExpr.bvar.injEq, List.not_mem_nil]
    omega

/-- **Coverage (a).** Every computation rule of a well-formed environment is either a
definition `const c ls ≡ value` with a closed value, or has the pattern shape at a
constant head (a restored native recursor, or `Quot.lift`). -/
theorem VEnv.WF.defeq_patShape {env : VEnv} (henv : env.WF) {df : VDefEq}
    (hdf : env.defeqs df) :
    (∃ c ls, df.lhs = .const c ls ∧ df.rhs.Closed) ∨ ∃ c ls, df.PatShape (.const c ls) := by
  obtain ⟨ds, H⟩ := henv
  rcases H.defeq_origin hdf with ⟨ci, rfl⟩ | rfl | ⟨_, _, _, _, _, _, _, index, H', he⟩
  · exact .inl ⟨_, _, rfl, ((VEnv.WF.ordered ⟨ds, H⟩).closed.2 hdf).2.1⟩
  · exact .inr ⟨_, _, quotDefEq_patShape⟩
  · exact .inr ⟨_, _, H'.equation_patShape index he⟩

/-- Every rule of a well-formed environment has the pattern shape at a constant head
(definitions being the degenerate case without arguments). -/
theorem VEnv.WF.defeq_patShape_const {env : VEnv} (henv : env.WF) {df : VDefEq}
    (hdf : env.defeqs df) : ∃ c ls, df.PatShape (.const c ls) := by
  rcases henv.defeq_patShape hdf with ⟨c, ls, h, _⟩ | h
  · exact ⟨c, ls, .ofConst h⟩
  · exact h

/-- **Coverage (b).** Every generic case equation of a registered eliminator schema has
the pattern shape at the abstract eliminator head. -/
theorem VEnv.WF.genericEquation_patShape {env : VEnv} (henv : env.WF)
    {schema : CaseSchema} (hlookup : env.eliminators block schema)
    {owner : Fin schema.signature.families.size} {rules : List VDefEq}
    (hrules : schema.genericEquations block owner = some rules) {df : VDefEq}
    (hdf : df ∈ rules) :
    df.PatShape (.elim block owner.val (.param 0 :: schema.genericLevels)) := by
  obtain ⟨_, _, _, _, _, ⟨_, _, auxiliaries, hdata, _, hr, _⟩, _, _⟩ :=
    henv.eliminator_origin hlookup
  have hparams : ∀ h ∈ schema.restoration.heads, h.nparams ≤ schema.signature.params.length := by
    rw [hr]
    exact fun h hh => Nat.le_of_eq (hdata.restoration_nparams h hh)
  obtain ⟨source, hsource, hrestore⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r (List.mapM_eq_some.mp hrules) _ hdf
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hsource
  have := (schema.specialize owner schema.genericUvars schema.genericLevels (.param 0)).equation_patShape
    index (.abstract block owner.val) hparams (fun _ _ heq => by cases heq) hrestore
  have hzero : ((schema.view owner).constructors[index]).owner.val = 0 := by
    have := ((schema.view owner).constructors[index]).owner.isLt
    simp only [CaseSchema.view_familyCount] at this
    omega
  simpa [Instance.recursorHead, hzero, Restoration.headOf, CaseSchema.specialize] using this

end Lean4Lean
