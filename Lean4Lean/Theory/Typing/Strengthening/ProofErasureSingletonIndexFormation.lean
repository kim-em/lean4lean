import Lean4Lean.Theory.Typing.Confluence.SingletonRecursorTyping

/-! # Generic constructor-index typing from recursor type formation

The generated minor's type already certifies the constructor index telescope.
Instantiating its motive by the constant true proposition and inhabiting its
hypotheses extracts this certificate without an installed recursor or rule.
-/
namespace Lean4Lean.InductiveSignature.Instance
open _root_.Lean4Lean _root_.Lean4Lean.VExpr VEnv
variable {s : InductiveSignature} (g : Instance s)

/-- Well-formedness of the singleton recursor type alone supplies the generic
field context and constructor-index telescope typing. The environment need not
contain the recursor constant or any rule from its declaration. -/
theorem singleton_indices_of_type_formation {env : VEnv} (henv : env.WF)
    (hfam : s.families.size = 1) (hcs : s.constructors.size = 1)
    (owner : Fin s.families.size) (index : Fin s.constructors.size)
    {c : Constructor s.families.size} (hc : s.constructors[index] = c)
    (htarget : g.targetLevel = .zero)
    (H : env.IsType g.uvars [] (g.recursorType owner))
    (harity : (g.ctorIndicesAt c).length = (g.indicesAt owner).length) :
    OnCtx (g.params ++ g.fieldsAt c).reverse (env.IsType g.uvars) ∧
      TelInst env g.uvars (g.params ++ g.fieldsAt c).reverse (g.params ++ g.indicesAt owner)
        (bvarRange g.params.length (g.params.length + (g.fieldsAt c).length) ++ g.ctorIndicesAt c) := by
  have hPlen : g.params.length = s.params.length := by simp [params]
  have hown0 : c.owner.val = 0 := by
    have := c.owner.isLt; omega
  have hrec := g.recursorType_singletonShape hfam hcs owner index
  rw [hc] at hrec
  rw [g.motive_shape owner htarget, g.minor_shape hfam _ hown0, g.major_lift owner,
    g.constructorApp_shape] at hrec
  rw [hrec] at H
  have hpeel := (IsType.wrapForalls_inv henv (Γ := []) trivial H).1
  have hpeel2 : OnCtx ((insertBinders (g.indicesAt owner) 2 ++
      [(g.majorType owner).liftN 2 (g.indicesAt owner).length]).reverse ++
      (VExpr.wrapForalls (insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c)
        (VExpr.mkApps (.bvar ((g.fieldsAt c).length + (g.hypotheses c).length))
          ((g.ctorIndicesAt c).map (fun e => (e.liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)) ++
            [((g.ctorApp c).liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)])) ::
        VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero) ::
        g.params.reverse)) (env.IsType g.uvars) := by
    simpa [List.reverse_append, List.append_assoc] using hpeel
  obtain ⟨hMotCtx, hMinT⟩ := OnCtx.of_append hpeel2
  have ⟨hP, hMotT⟩ := hMotCtx
  have hMotInv := IsType.wrapForalls_inv henv hP hMotT
  have hM0 := HasType.wrapLams_of hMotInv.1 (HasType.trueTy (env := env) (U := g.uvars))
  have hMinInv := IsType.wrapForalls_inv henv hMotCtx hMinT
  have hall : OnCtx (g.params ++ [VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero)] ++
      insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c).reverse (env.IsType g.uvars) := by
    simpa [List.append_assoc] using hMinInv.1
  have hbody : env.IsType g.uvars (g.params ++
      [VExpr.wrapForalls (g.indicesAt owner ++ [g.majorType owner]) (.sort .zero)] ++
      insertBinders (g.fieldsAt c) 1 ++ g.hypotheses c).reverse
      (VExpr.mkApps (.bvar ((g.fieldsAt c).length + (g.hypotheses c).length))
          ((g.ctorIndicesAt c).map (fun e => (e.liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)) ++
            [((g.ctorApp c).liftN (g.hypotheses c).length).liftN 1
              ((g.fieldsAt c).length + (g.hypotheses c).length)])) := by
    simpa [List.append_assoc] using hMinInv.2
  have hallcl := OnCtx.closed_reverse henv.ordered hall
  have hFcl : ∀ i (hi : i < (g.fieldsAt c).length),
      ((g.fieldsAt c)[i]).ClosedN (g.params.length + i) := by
    intro i hi
    have := hallcl (g.params.length + 1 + i) (by simp; omega)
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp),
      VEnv.getElem_insertBinders (by simp; omega)] at this
    simp only [List.length_append, List.length_singleton,
      show g.params.length + 1 + i - (g.params.length + 1) = i by omega] at this
    exact VExpr.ClosedN.of_liftN (k := g.params.length + i) (by simpa [Nat.add_right_comm] using this)
      (by omega)
  have hCIcl : ∀ e ∈ g.ctorIndicesAt c, e.ClosedN (g.params.length + (g.fieldsAt c).length) := by
    intro e he
    obtain ⟨_, hb⟩ := hbody
    have hcl := hb.closedN henv.ordered (CtxWF.closed henv.ordered hall)
    have := (VExpr.ClosedN.mkApps_inv hcl).2 _ (List.mem_append_left _ (List.mem_map_of_mem he))
    simp only [List.length_reverse, List.length_append, List.length_singleton,
      InductiveSignature.Instance.length_insertBinders] at this
    have h1 := VExpr.ClosedN.of_liftN (k := g.params.length + (g.fieldsAt c).length + (g.hypotheses c).length)
      (j := (g.fieldsAt c).length + (g.hypotheses c).length) (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this) (by omega)
    exact VExpr.ClosedN.of_liftN (j := 0) (n := (g.hypotheses c).length)
      (k := g.params.length + (g.fieldsAt c).length) h1 (Nat.zero_le _)
  have hshape : ∀ j (hj : j < (g.hypotheses c).length) (args : List VExpr),
      args.length = g.params.length + 1 + (g.fieldsAt c).length + j →
      args[g.params.length]? = some
        ((VExpr.wrapLams (g.indicesAt owner ++ [g.majorType owner]) VExpr.trueTy).liftN
          (g.fieldsAt c).length) →
      ∃ B xs, ((g.hypotheses c)[j]).instOuter args =
        VExpr.wrapForalls B (VExpr.mkApps
          ((VExpr.wrapLams (g.indicesAt owner ++ [g.majorType owner]) VExpr.trueTy).liftN
            ((g.fieldsAt c).length + B.length)) xs) := by
    intro j hj args hl ha
    rw [hPlen] at hl ha
    exact g.hypothesis_shape hfam c j hj args _ hl ha
  have hccl : (g.ctorApp c).ClosedN (g.params.length + (g.fieldsAt c).length) := by
    apply ClosedN.mkApps_closed (show (VExpr.const c.name g.levels).ClosedN _ from trivial)
    intro a ha
    simp only [bvarRange, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    show _ < _
    omega
  obtain ⟨hctxF, hmb⟩ := minorBody_inst henv hP hM0 hall hFcl hshape hbody hCIcl hccl
  rw [← List.append_assoc] at hmb
  -- the constructor indices along the index telescope
  have hCItel : TelInst env g.uvars (g.params ++ g.fieldsAt c).reverse
      (g.params ++ g.indicesAt owner)
      (bvarRange g.params.length (g.params.length + (g.fieldsAt c).length) ++ g.ctorIndicesAt c) := by
    have := hmb.take
    rwa [List.take_append_of_le_length (by simp [harity]), List.take_of_length_le (by simp [harity])]
      at this
  exact ⟨hctxF, hCItel⟩

end Lean4Lean.InductiveSignature.Instance
