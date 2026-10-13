import Lean4Lean.Theory.Typing.Strengthening.SingletonProofReconstruction
import Lean4Lean.Theory.Typing.Confluence.SingletonEquation
import Lean4Lean.Theory.Typing.PrefixUnfolding.GenerationSupply

/-! # The exact telescope of an unindexed singleton recursor

This identifies the generic recursor's parameter, motive/minor, and major binders
with the extraction layout. It is the metadata bridge needed to check a closed
singleton unfolding rather than an occurrence-specific aligned prefix.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
variable {env : VEnv} {data : RecursorData}
  {P X ps xs fs fields args : List VExpr} {ctor : VExpr} {a b np nf : Nat}

/-- At a Prop-source specialization, the unindexed recursor has its ordinary
parameter and motive/minor telescope followed by the extraction family's major. -/
theorem type_shape (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hE : data.propElim levels = some E)
    (hn : data.numIndices = 0) :
    (data.recursorInstance.recursorType data.owner).instL levels =
      wrapForalls (data.propParams levels ++
        (data.recursorInstance.motives ++ data.recursorInstance.minors).map (·.instL levels) ++
        [mkApps E.family (vars (data.propParams levels).length 2)])
        (.app (.bvar 2) (.bvar 0)) := by
  obtain ⟨k, hk, hfam, hcs, hrest, hS0, hE0, hP, hgl, hseq⟩ :=
    RecursorData.singleton_shape H hlarge hzero howner
  rw [hE0] at hE
  cases Option.some.inj hE
  have hidx : data.recursorInstance.indicesAt data.owner = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa [Instance.indicesAt, RecursorData.numIndices] using hn
  have hmot : data.recursorInstance.motives =
      [data.recursorInstance.motive data.schema.signature.families[data.owner] 0] := by
    have ho : data.owner.val = 0 := by have := data.owner.isLt; omega
    simp [Instance.motives, Instance.toList_of_size_one data.schema.signature.families hfam data.owner, ho]
  have hmin : data.recursorInstance.minors =
      [data.recursorInstance.minor data.schema.signature.constructors[index] 0] := by
    have hi : index.val = 0 := by have := index.isLt; omega
    simp [Instance.minors, Instance.toList_of_size_one data.schema.signature.constructors hcs index, hi]
  rw [Instance.recursorType_singletonShape data.recursorInstance hfam hcs _ index, hidx, hmot, hmin]
  simp only [List.length_nil, Nat.add_zero, insertBinders, List.zipIdx_nil, List.map_nil,
    List.append_nil, show vars 0 0 = [] from rfl, show vars 0 1 = [] from rfl,
    List.nil_append, instL_wrapForalls, List.map_append, List.map_cons, VExpr.instL,
    mkApps_cons, mkApps_nil]
  simp only [RecursorData.propParams, Instance.singletonElim, Instance.familyApp,
    InductiveSignature.familyApp, instL_mkApps, VExpr.instL, vars_instL, hgl,
    List.length_map, Instance.params, List.append_assoc, List.append_nil]
  rfl

/-- The generic parameter/motive/minor/major context provides the exact parameter
and major instance needed by singleton extraction. No constructor fields occur
in this context. -/
theorem generic_major_args (henv : env.WF)
    (W : E.WF S P env U) (hn : S.indices = []) (hX : X.length = 2)
    (ht : env.HasType U [] source (wrapForalls
      (P ++ X ++ [mkApps E.family (vars P.length 2)]) result)) :
    let Δ := (P ++ X ++ [mkApps E.family (vars P.length 2)]).reverse
    OnCtx Δ (env.IsType U) ∧
      TelInst env U Δ (P ++ X) (vars (P.length + 2) 1) ∧
      TelInst env U Δ (P ++ S.indices ++ [PropElim.majorTy S P E])
        (vars P.length 3 ++ [] ++ [.bvar 0]) := by
  let D := P ++ X ++ [mkApps E.family (vars P.length 2)]
  have hlen : D.length = P.length + 2 + 1 := by simp [D, hX]
  have hctx := (ht.etaOpen_wf henv.ordered (by trivial)).1
  simp only [List.append_nil] at hctx
  obtain ⟨_, htype⟩ := ht.isType henv.ordered (by trivial)
  have hclosed := htype.closedN henv.ordered (by trivial)
  have hdoms : ∀ j (hj : j < D.length), D[j].ClosedN j := by
    intro j hj
    simpa only [List.length_nil, Nat.zero_add] using closed_wrapForalls_domain hclosed (i := j) (by exact hj)
  have hid := TelInst.ident (env := env) (U := U) [] hdoms
  have hvars : bvarRange D.length D.length = vars (P.length + 2) 1 ++ [.bvar 0] := by
    rw [hlen, ← vars_eq_bvarRange_add (P.length + 2 + 1) 0]
    rw [vars_add]
    rfl
  rw [hvars] at hid
  have HA : TelInst env U D.reverse (P ++ X) (vars (P.length + 2) 1) := by
    have HH := (show TelInst env U D.reverse ((P ++ X) ++ [mkApps E.family (vars P.length 2)])
      (vars (P.length + 2) 1 ++ [.bvar 0]) by simpa only [List.append_nil] using hid).take
    rwa [List.take_left' (by simp [hX])] at HH
  have hsplit : vars (P.length + 2) 1 = vars P.length 3 ++ vars 2 1 := by rw [vars_add]
  have HP : TelInst env U D.reverse P (vars P.length 3) := by
    have HH := HA.take
    rw [hsplit, List.take_left' (by simp)] at HH
    exact HH
  have hm : env.HasType U D.reverse (.bvar 0) (mkApps E.family (vars P.length 3)) := by
    have HH : env.HasType U ((mkApps E.family (vars P.length 2)) :: (P ++ X).reverse)
      (.bvar 0) (mkApps E.family (vars P.length 2)).lift := .bvar .zero
    simpa only [D, List.reverse_append, List.reverse_singleton, List.singleton_append,
      liftN_mkApps, W.family_closed.liftN_eq (Nat.zero_le _), vars_map_lift] using HH
  refine ⟨hctx, HA, ?_⟩
  simp only [hn, List.append_nil]
  apply HP.append_one
  have he := W.majorTy_instOuter (ps := vars P.length 3) (idx := []) (by simp) (by simp [hn])
  simp only [List.append_nil] at he
  rw [he]
  exact hm

/-- Registration supplies every typing needed to reconstruct the generic major
of an unindexed Prop-source singleton. Parameters, motive and minor stay fresh;
there are no occurrence checks or pre-existing constructor fields among the premises. -/
theorem registered_reconstruction (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF U) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hn : data.numIndices = 0) :
    let P := data.propParams levels
    let X := (data.recursorInstance.motives ++ data.recursorInstance.minors).map (·.instL levels)
    let Δ := (P ++ X ++ [mkApps E.family (vars P.length 2)]).reverse
    let fields := (PropElim.occ S P E (vars P.length 3) [] (.bvar 0) S.fields.length).2
    OnCtx Δ (env.IsType U) ∧
      TelInst env U Δ (P ++ X) (vars (P.length + 2) 1) ∧
      TelInst env U Δ (P ++ S.fields) (vars P.length 3 ++ fields) ∧
      env.IsDefEq U Δ (.bvar 0) (mkApps E.ctor (vars P.length 3 ++ fields))
        (mkApps E.family (vars P.length 3)) := by
  obtain ⟨S', E', hS', hE', W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  have F := RecursorData.singletonSignature H hlarge hzero
  have hcs : data.schema.signature.constructors.size = 1 := by
    have := index.isLt
    have := F.constructors
    omega
  have hX : ((data.recursorInstance.motives ++ data.recursorInstance.minors).map (·.instL levels)).length = 2 := by
    simp [Instance.motives, Instance.minors, F.families, hcs]
  have hni : S.indices = [] := List.eq_nil_of_length_eq_zero
    ((RecursorData.singletonLayout_lengths hS).1.trans hn)
  have ht : env.HasType U [] (.const data.name levels)
      (wrapForalls (data.propParams levels ++
        (data.recursorInstance.motives ++ data.recursorInstance.minors).map (·.instL levels) ++
        [mkApps E.family (vars (data.propParams levels).length 2)])
        (.app (.bvar 2) (.bvar 0))) := by
    rw [← type_shape H hlarge hzero howner hE hn]
    exact .const F.recursor hw hlen
  obtain ⟨hΔ, hprefix, hargs⟩ := generic_major_args henv W hni hX ht
  have hfields := (SingletonProof.occ_typed henv heq W (by simp)
    (fun j _ => SingletonProof.slots_none W hni j) hargs S.fields.length (Nat.le_refl _)).2
  rw [List.take_length] at hfields
  have heta := SingletonProof.unindexed_eta henv heq W hni hΔ (by simp) hargs
  rw [W.majorTy_instOuter (by simp) (by simp [hni]), List.append_nil] at heta
  exact ⟨hΔ, hprefix, hfields, heta⟩

/-- Insert the motive/minor arguments between parameters and reconstructed fields
when forming the installed equation's capture telescope. -/
theorem captures_typed (hprefix : TelInst env U Γ (P ++ X) (ps ++ xs))
    (hfields : TelInst env U Γ (P ++ fields) (ps ++ fs))
    (hp : ps.length = P.length) (hx : xs.length = X.length)
    (hscope : ∀ j (hj : j < fields.length), fields[j].ClosedN (P.length + j)) :
    TelInst env U Γ (P ++ X ++ insertBinders fields X.length) (ps ++ xs ++ fs) := by
  have hf : fs.length = fields.length := by have := hfields.1; simp at this; omega
  refine hprefix.append (by simp [hf]) fun j hj => ?_
  simp only [Instance.length_insertBinders] at hj
  have H := TelInst.getD_mid (A := P) (a := ps) (B := fields) (b := fs)
    (C := []) (c := []) (by simpa using hfields) hp hf hj
  have hclosed : (fields.getD j default).ClosedN (P.length + j) := by
    rw [getD_of_lt hj]; exact hscope j hj
  have htl : (fs.take j).length = j := by simp [hf]; omega
  have hskip := instOuter_liftN_skip (X := fields.getD j default)
    (A := ps ++ xs) (B := fs.take j) (P := P.length) (r := X.length)
    (by rw [htl]; exact hclosed) (by simp [hp, hx])
  rw [htl, List.take_left' hp] at hskip
  rw [getD_of_lt (l := insertBinders fields X.length) (by simpa using hj),
    getElem_insertBinders, ← getD_of_lt hj, hskip]
  exact H

/-- A block of fresh telescope variables selects the corresponding capture slice. -/
theorem vars_instOuter (hlen : args.length = a + b) :
    (vars a b).map (·.instOuter args) = args.take a := by
  rw [vars_eq_bvarRange_add, instOuter_bvarRange _ _ _ (by omega) (by omega), hlen]
  simp

/-- Instantiating the unindexed equation's left side substitutes its recursor
prefix and its constructor fields exactly, including the skipped motive/minor slots. -/
theorem lhs_instOuter (hctor : ctor.Closed)
    (hps : ps.length = np) (hxs : xs.length = 2) (hfs : fs.length = nf) :
    (VExpr.app (mkApps (.const name levels) (vars (np + 2) nf))
      (mkApps ctor (vars np (2 + nf) ++ vars nf 0))).instOuter (ps ++ xs ++ fs) =
      .app (mkApps (.const name levels) (ps ++ xs)) (mkApps ctor (ps ++ fs)) := by
  have hlen : (ps ++ xs ++ fs).length = np + 2 + nf := by simp [hps, hxs, hfs, Nat.add_assoc]
  have happ : ∀ (f a : VExpr) (vs : List VExpr),
      (f.app a).instOuter vs = (f.instOuter vs).app (a.instOuter vs) := by
    intro f a vs; simp only [instOuter_eq_subst, VExpr.subst]
  simp only [happ, instOuter_mkApps, instOuter_const,
    instOuter_closed0 hctor, List.map_append]
  rw [vars_instOuter hlen, List.take_left' (by simp [hps, hxs])]
  have hp : (vars np (2 + nf)).map (·.instOuter (ps ++ xs ++ fs)) = ps := by
    rw [vars_instOuter (by omega), List.append_assoc, List.take_left' hps]
  have hf : (vars nf 0).map (·.instOuter (ps ++ xs ++ fs)) = fs := by
    rw [vars_eq_bvarRange_add, instOuter_bvarRange _ _ _ (by omega) (by omega), hlen]
    simp only [Nat.add_zero]
    rw [show np + 2 + nf - nf = (ps ++ xs).length by simp [hps, hxs], List.drop_left,
      ← hfs, List.take_length]
  rw [hp, hf]

end Lean4Lean.VEnv.Strengthening.ClosedSingleton
