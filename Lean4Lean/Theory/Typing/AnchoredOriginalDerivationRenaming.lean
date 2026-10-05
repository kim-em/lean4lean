import Lean4Lean.Theory.Typing.AnchoredOriginalDerivation

/-! Structural weakening of the actual original derivation. This constructs
its finite tree directly, so a synthesized formal projection can be charged
against that same tree's dependency budget rather than an opaque reification.
-/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

/-- Transport only the indices of the same finite derivation. -/
def Derivation.castIndices (H : Derivation env U Γ e1 e2 A)
    (context : Γ = Γ') (left : e1 = e1') (right : e2 = e2') (assigned : A = A') :
    Derivation env U Γ' e1' e2' A' := by
  cases context; cases left; cases right; cases assigned
  exact H

variable! (henv : Ordered env) in
noncomputable def Derivation.weakN (W : Ctx.LiftN n k Γ Γ') (H : Derivation env U Γ e1 e2 A) :
    Derivation env U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar h1 h2 _ ih3 => refine .bvar (h1.weakN W) h2 (ih3 W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 h7 _ _ ih2 =>
    refine Derivation.castIndices (Derivation.constDF h1 h2 h3 h4 h5 h6 h7
      (by refine Derivation.castIndices (ih2 W) rfl ?_ ?_ ?_ <;>
          simp only [VExpr.liftN, (henv.closedC h1).instL.liftN_eq (Nat.zero_le _)])) rfl ?_ ?_ ?_
    all_goals first | rfl | simp only [VExpr.liftN, (henv.closedC h1).instL.liftN_eq (Nat.zero_le _)]
  | elimDF h1 h2 h3 h4 h5 h6 h7 _ ih =>
    refine Derivation.castIndices (Derivation.elimDF h1 h2 h3 h4 h5 h6 h7
      (by refine Derivation.castIndices (ih W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN, h3.instL.liftN_eq (Nat.zero_le _)])) rfl ?_ ?_ ?_
    all_goals first | rfl | simp only [VExpr.liftN, h3.instL.liftN_eq (Nat.zero_le _)]
  | elimIota h1 h2 h3 h4 h5 h6 _ _ _ ihT ihL ihR =>
    refine Derivation.castIndices (Derivation.elimIota h1 h2 h3 h4 h5 h6
      (by refine Derivation.castIndices (ihT W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN, h4.1.instL.liftN_eq (Nat.zero_le _), h4.2.1.instL.liftN_eq (Nat.zero_le _), h4.2.2.instL.liftN_eq (Nat.zero_le _)])
      (by refine Derivation.castIndices (ihL W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN, h4.1.instL.liftN_eq (Nat.zero_le _), h4.2.1.instL.liftN_eq (Nat.zero_le _), h4.2.2.instL.liftN_eq (Nat.zero_le _)])
      (by refine Derivation.castIndices (ihR W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN, h4.1.instL.liftN_eq (Nat.zero_le _), h4.2.1.instL.liftN_eq (Nat.zero_le _), h4.2.2.instL.liftN_eq (Nat.zero_le _)])) rfl ?_ ?_ ?_
    all_goals first | rfl | simp only [h4.1.instL.liftN_eq (Nat.zero_le _),
      h4.2.1.instL.liftN_eq (Nat.zero_le _), h4.2.2.instL.liftN_eq (Nat.zero_le _)]
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine Derivation.castIndices (Derivation.appDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W) (ih4 W)
      (by refine Derivation.castIndices (ih5 W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [liftN_inst_hi, VExpr.liftN])) rfl ?_ ?_ ?_
    all_goals first | rfl | simp only [VExpr.liftN, liftN_inst_hi]
  | @projDF typeName info levels params index sourceMajor fieldType _ fieldLevel
      major indexArgs major' hinfo hlevels huvars hparams hindices hfield hwf
      _ _ _ hclosed hguard ihField ihLeft ihRight =>
    have hfield' := VProjectionInfo.fieldType_liftN
      (typeName := typeName) (levels := levels) (params := params)
      (index := index) (major := sourceMajor) (n := n) (k := k) info hclosed
    rw [hfield] at hfield'
    exact .projDF (info := info) (params := params.map fun param => param.liftN n k)
      (indexArgs := indexArgs.map fun arg => arg.liftN n k)
      hinfo hlevels huvars (by simpa using hparams) (by simpa using hindices)
      hfield' hwf (ihField W)
      (by refine Derivation.castIndices (ihLeft W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN_mkApps, List.map_append, VExpr.liftN])
      (by refine Derivation.castIndices (ihRight W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN_mkApps, List.map_append, VExpr.liftN])
      hclosed hguard
  | lamDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .lamDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W.succ) (ih5 W.succ)
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 => exact .forallEDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ)
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 (ih1 W) (ih2 W)
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    refine Derivation.castIndices (Derivation.beta h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W)
      (by refine Derivation.castIndices (ih5 W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [liftN_inst_hi, VExpr.liftN])
      (by refine Derivation.castIndices (ih6 W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [liftN_inst_hi])) rfl ?_ ?_ ?_
    all_goals first | rfl | simp only [VExpr.liftN, liftN_inst_hi, liftN_instN_hi]
  | @eta Γ a u B v e h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    have commute := liftN'_comm B n 1 (k+1) 1 (Nat.le_add_left ..)
    rw [Nat.add_comm 1] at commute
    refine Derivation.castIndices (Derivation.eta h1 h2 (ih1 W) (ih2 W.succ)
      (by refine Derivation.castIndices (ih3 W.succ.succ) ?_ ?_ ?_ ?_ <;> first | rfl | simp only [← commute, ← lift_liftN']) (ih4 W)
      (by refine Derivation.castIndices (ih5 W.succ) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN, ← commute, ← lift_liftN'])
      (by refine Derivation.castIndices (ih6 W.succ) rfl ?_ ?_ ?_ <;> first | rfl | simp only [← lift_liftN'])) rfl ?_ ?_ ?_
    all_goals first | rfl | simp only [liftN, ← lift_liftN', liftVar_zero]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ ih4 ih5 =>
    have hA1 := (henv.closed.2 h1).1.1
    have hA2 := (henv.closed.2 h1).2.1
    have hA3 := (henv.closed.2 h1).2.2
    refine Derivation.castIndices (Derivation.extra h1 h2 h3 h4 h5 h6 h7
      (by refine Derivation.castIndices (ih4 W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [hA1.instL.liftN_eq (Nat.zero_le _), hA2.instL.liftN_eq (Nat.zero_le _), hA3.instL.liftN_eq (Nat.zero_le _)])
      (by refine Derivation.castIndices (ih5 W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [hA1.instL.liftN_eq (Nat.zero_le _), hA2.instL.liftN_eq (Nat.zero_le _), hA3.instL.liftN_eq (Nat.zero_le _)])) rfl ?_ ?_ ?_
    all_goals first | rfl | simp only [hA1.instL.liftN_eq (Nat.zero_le _),
      hA2.instL.liftN_eq (Nat.zero_le _), hA3.instL.liftN_eq (Nat.zero_le _)]
  | @projIota typeName info Γ index levels args fieldType field h1 _ h3 _ ih1 ih2 =>
    refine Derivation.castIndices (Derivation.projIota (index := index) (levels := levels) (args := args.map fun a => a.liftN n k) h1
      (by refine Derivation.castIndices (ih1 W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN_mkApps, VExpr.liftN])
      (by simp [h3]) (ih2 W)) rfl ?_ ?_ ?_
    all_goals first | rfl | simp only [VExpr.liftN_mkApps, VExpr.liftN]
  | @structEta typeName info Γ e levels params h1 h2 h3 _ _ ih1 ih2 =>
    refine Derivation.castIndices (Derivation.structEta (levels := levels) (params := params.map fun a => a.liftN n k) (e := e.liftN n k) h1 (by simpa using h2) h3
      (by refine Derivation.castIndices (ih1 W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append, List.map_map, Function.comp_def])
      (by refine Derivation.castIndices (ih2 W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append, List.map_map, Function.comp_def])) rfl ?_ ?_ ?_
    all_goals first | rfl | simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append, List.map_map, Function.comp_def]
  | @unitLike typeName info Γ e levels params other h1 h2 h3 h4 _ _ ih1 ih2 =>
    refine Derivation.castIndices (Derivation.unitLike (levels := levels) (params := params.map fun a => a.liftN n k) (e := e.liftN n k) (e' := other.liftN n k) h1 (by simpa using h2) h3 h4
      (by refine Derivation.castIndices (ih1 W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN_mkApps, VExpr.liftN])
      (by refine Derivation.castIndices (ih2 W) rfl ?_ ?_ ?_ <;> first | rfl | simp only [VExpr.liftN_mkApps, VExpr.liftN])) rfl ?_ ?_ ?_
    all_goals first | rfl | simp only [VExpr.liftN_mkApps, VExpr.liftN]

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
