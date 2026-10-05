import Lean4Lean.Theory.Inductive.NativeEquationOrigin

/-! Every original constructor has its own generated native equation.
This supplies an actual prior equation witness when constructor rigidity is
transported through a later environment. -/

namespace Lean4Lean.InductiveSignature

theorem declarationCtor_index_of_mem (s : InductiveSignature)
    (hctor : ctor ∈ s.declaration.constructorConstants) :
    ∃ index : Fin s.constructors.size, s.declarationCtor index = ctor := by
  obtain ⟨family, hfamily, hctor⟩ := List.mem_flatMap.mp hctor
  obtain ⟨⟨family, owner⟩, howner, rfl⟩ := List.mem_map.mp hfamily
  obtain ⟨sigctor, hsigctor, hvalue⟩ := List.mem_filterMap.mp hctor
  split at hvalue
  · have hvalue := Option.some.inj hvalue
    obtain ⟨index, hindex, hget⟩ := List.mem_iff_getElem.mp hsigctor
    refine ⟨⟨index, by simpa using hindex⟩, ?_⟩
    simpa only [declarationCtor, ← hget, Array.getElem_toList, Fin.getElem_fin] using hvalue
  · cases hvalue

theorem CompilationData.source_constructor_index
    {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (hctor : ctor ∈ source.constructorConstants) :
    ∃ index : Fin s.constructors.size,
      (compilationRestoration source auxiliaries).headName s.constructors[index].name = ctor.name := by
  obtain ⟨family, hfamily, hctor⟩ := List.mem_flatMap.mp hctor
  obtain ⟨envTypes, direct, _, _, _, hfamilies⟩ := H.correspondence
  obtain ⟨normalized, hnormalized, hrestored⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r hfamilies family (List.mem_append_left _ hfamily)
  obtain ⟨normalizedCtor, hnormalizedCtor, hctorRestore⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r hrestored.constructors ctor hctor
  obtain ⟨index, hindex⟩ := s.declarationCtor_index_of_mem
    (List.mem_flatMap.mpr ⟨normalized, hnormalized, hnormalizedCtor⟩)
  have hname : s.constructors[index].name = ctor.name := by
    exact (congrArg VConstVal.name hindex).trans hctorRestore.1
  refine ⟨index, ?_⟩
  rw [hname]
  apply H.headName_source
  exact List.mem_flatMap.mpr ⟨family, hfamily,
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩


/-- Ordered restoration includes the equation of every original constructor;
auxiliary equations cannot replace or omit that source constructor's rule. -/
theorem CompilationData.constructor_equation
    {s : InductiveSignature} {g : Instance s}
    (H : CompilationData env source expanded s g auxiliaries block)
    (hctor : ctor ∈ source.constructorConstants) :
    ∃ equation ∈ block.rules, ∃ fn levels args,
      equation.lhs.stripLams = .app fn (VExpr.mkApps (.const ctor.name levels) args) := by
  obtain ⟨index, hname⟩ := H.source_constructor_index hctor
  have hgenerated : g.equation index ∈ g.equations :=
    List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  obtain ⟨equation, hmem, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp H.equations) _ hgenerated
  obtain ⟨fn, levels, args, hmajor⟩ := g.restored_equation_major H index hrestore
  rw [hname] at hmajor
  exact ⟨equation, hmem, fn, levels, args, hmajor⟩

end Lean4Lean.InductiveSignature

namespace Lean4Lean

/-- Finite compilation retains concrete native equation coverage for every
source constructor, including when the original derivation is replayed. -/
theorem CompiledInductive.constructor_equation
    (H : CompiledInductive env source block) :
    ∀ ctor ∈ source.constructorConstants, ∃ equation ∈ block.rules, ∃ fn levels args,
      equation.lhs.stripLams = .app fn (VExpr.mkApps (.const ctor.name levels) args) := by
  exact CompiledInductive.rec
    (motive_1 := fun _ source block _ =>
      ∀ ctor ∈ source.constructorConstants, ∃ equation ∈ block.rules, ∃ fn levels args,
        equation.lhs.stripLams = .app fn (VExpr.mkApps (.const ctor.name levels) args))
    (motive_2 := fun _ _ _ => True)
    (fun data _ _ ctor hctor => data.constructor_equation hctor)
    (fun _ _ _ ih => ih)
    trivial
    (fun _ _ _ _ _ _ _ => trivial)
    H

/-- Equation installation retains each actual generated rule. -/
theorem VEnv.addDefEqRules_mem {env : VEnv} (hmem : equation ∈ rules) :
    (env.addDefEqRules rules).defeqs equation := by
  induction rules generalizing env with
  | nil => cases hmem
  | cons rule rules ih =>
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact (VEnv.addDefEqRules_le (env := env.addDefEq equation) (dfs := rules)).defeqs
        (Or.inl rfl)
    · exact ih hmem

theorem VInductBlock.install_rule
    (H : VInductBlock.install base block = some installed)
    (hmem : equation ∈ block.rules) : installed.defeqs equation := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, _, ctors, _, recursors, _, rfl⟩ := H
  exact VEnv.addDefEqRules_mem hmem

/-- A prior specialization carries an actual already-installed constructor
equation. Environment extension transports this witness, without asserting
that rigidity itself is monotone. -/
theorem CertifiedSpecializations.constructor_equation
    (H : CertifiedSpecializations env auxiliaries) :
    ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors, ∃ equation,
      env.defeqs equation ∧ ∃ fn levels args,
        equation.lhs.stripLams = .app fn (VExpr.mkApps (.const ctor.name levels) args) := by
  exact CertifiedSpecializations.rec
    (motive_1 := fun _ source block _ =>
      ∀ ctor ∈ source.constructorConstants, ∃ equation ∈ block.rules, ∃ fn levels args,
        equation.lhs.stripLams = .app fn (VExpr.mkApps (.const ctor.name levels) args))
    (motive_2 := fun env auxiliaries _ =>
      ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors, ∃ equation,
        env.defeqs equation ∧ ∃ fn levels args,
          equation.lhs.stripLams = .app fn (VExpr.mkApps (.const ctor.name levels) args))
    (fun data _ _ ctor hctor => data.constructor_equation hctor)
    (fun _ _ _ ih => ih)
    (by simp)
    (fun _ _ hinstall hle _ hc hr => by
      intro a ha ctor hctor
      rcases List.mem_cons.mp ha with rfl | ha
      · have hsource : ctor ∈ a.container.constructorConstants :=
          List.mem_flatMap.mpr ⟨a.source, List.getElem_mem a.family.isLt, hctor⟩
        obtain ⟨equation, hmem, hmajor⟩ := hc ctor hsource
        exact ⟨equation, hle.defeqs (VInductBlock.install_rule hinstall hmem), hmajor⟩
      · exact hr a ha ctor hctor)
    H

end Lean4Lean
