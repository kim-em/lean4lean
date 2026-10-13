import Lean4Lean.Theory.Typing.Strengthening.SingletonUnindexedTelescope

/-! # Closed unfoldings of unindexed Prop-source singleton recursors

Reconstruct the major at the fresh, complete recursor telescope, apply its
realized equation there, and close by eta. The resulting closed value is exactly
the program generated at the empty prefix, so later occurrences replay it by
weakening and beta computation.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
variable {env : VEnv} {data : RecursorData}

/-- The generated zero-prefix program of an unindexed Prop-source singleton is
an actual equation of the bare constant in the empty context. All reconstruction
and equation-capture typings are derived from registration. -/
theorem zero_equation_exists (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF U) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hn : data.numIndices = 0) :
    ∃ program, data.singletonUnfolding env U levels [] = some program ∧
      env.IsDefEqU U [] (.const data.name levels) program.rhs := by
  obtain ⟨S, E, hS, hE, W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  obtain ⟨D, lb, rb, tb, X, hgen, hseq, hext, hD, hX, hlb, hio, hrt, hXdef⟩ :=
    RecursorData.singleton_equation_syntax H hlarge hzero hlen howner hS hE
  let P := data.propParams levels
  let Δ := P ++ X ++ [mkApps E.family (vars P.length 2)]
  let fs := (PropElim.occ S P E (vars P.length 3) [] (.bvar 0) S.fields.length).2
  let caps := vars P.length 3 ++ vars 2 1 ++ fs
  have hni : S.indices = [] := List.eq_nil_of_length_eq_zero
    ((RecursorData.singletonLayout_lengths hS).1.trans hn)
  have hci : E.ctorIndices = [] := List.eq_nil_of_length_eq_zero (by rw [W.ctorIndices_length, hni]; rfl)
  have hnp : P.length = data.numParams := (RecursorData.singletonLayout_lengths hS).2
  have hmajor : data.majorOffset = P.length + 2 := by
    simp only [RecursorData.majorOffset, hn, Nat.add_zero, hio]; rfl
  have hΔlen : Δ.length = P.length + 2 + 1 := by simp [Δ, hX]
  have hflen : fs.length = S.fields.length := (PropElim.occ_length S P E _ _ _ _).2
  have hDlen : D.length = P.length + 2 + S.fields.length := by
    have HH := congrArg List.length hD
    simpa only [List.length_map, List.length_append, Instance.length_insertBinders, hX] using HH
  have hcaplen : caps.length = D.length := by simp [caps, hflen, hDlen, Nat.add_assoc]
  have htype : (data.recursorInstance.recursorType data.owner).instL levels =
      wrapForalls Δ (.app (.bvar 2) (.bvar 0)) := by
    simpa only [Δ, P, hXdef] using type_shape H hlarge hzero howner hE hn
  have ht : env.HasType U [] (.const data.name levels) (wrapForalls Δ (.app (.bvar 2) (.bvar 0))) := by
    rw [← htype]
    exact .const (H.recursorType hrt) hw hlen
  have hrec := registered_reconstruction henv heq H hlarge hzero hw hlen howner hS hE hn
  rw [← hXdef] at hrec
  obtain ⟨hctx, hprefix, hfields, heta⟩ := hrec
  change OnCtx Δ.reverse (env.IsType U) at hctx
  change TelInst env U Δ.reverse (P ++ X) (vars (P.length + 2) 1) at hprefix
  change TelInst env U Δ.reverse (P ++ S.fields) (vars P.length 3 ++ fs) at hfields
  change env.IsDefEq U Δ.reverse (.bvar 0) (mkApps E.ctor (vars P.length 3 ++ fs))
    (mkApps E.family (vars P.length 3)) at heta
  have hcapT : TelInst env U Δ.reverse (D.map (·.instL levels)) caps := by
    rw [hD]
    rw [vars_add] at hprefix
    have HH := captures_typed hprefix hfields (by simp) (by simp [hX]) W.typed.scope.fields
    simpa only [hX] using HH
  have hleft : (lb.instL levels).instOuter caps =
      .app (mkApps (.const data.name levels) (vars P.length 3 ++ vars 2 1))
        (mkApps E.ctor (vars P.length 3 ++ fs)) := by
    rw [hlb, hci, List.map_nil, List.append_nil, hio]
    exact lhs_instOuter W.ctor_closed (by simp [P]) (by simp) hflen
  have hopened : etaOpen Δ.length (.const data.name levels) =
      .app (mkApps (.const data.name levels) (vars P.length 3 ++ vars 2 1)) (.bvar 0) := by
    rw [hΔlen, etaOpen_spine, vars_add (P.length + 2) 1 0]
    simp only [liftN, show vars 1 0 = [VExpr.bvar 0] from rfl, Nat.add_zero,
      mkApps_append, mkApps_cons, mkApps_nil]
    rw [vars_add P.length 2 1, mkApps_append]
  have hopen := (ht.etaOpen_wf henv.ordered (by trivial)).2
  simp only [List.append_nil] at hopen
  rw [hopened] at hopen
  obtain ⟨A, B, hfn, hm⟩ := hopen.app_inv henv hctx
  have hreplace := IsDefEq.appDF hfn ((show env.IsDefEqU U Δ.reverse (.bvar 0)
    (mkApps E.ctor (vars P.length 3 ++ fs)) from ⟨_, heta⟩).of_l henv hctx hm)
  have hpe := H.patEquation_of_empty henv (RecursorData.singletonSignature H hlarge hzero).restoration hgen
  have hiota := hpe.instOuter hctx hw hlen hext hcaplen
    (by simpa only [List.getElem_map, List.length_map] using hcapT.2)
    (hleft.symm ▸ hreplace.hasType.2)
  have hbody := ((show env.IsDefEqU U Δ.reverse _ _ from ⟨_, hreplace⟩).trans henv hctx
    (hleft ▸ hiota)).of_l henv hctx hopen
  rw [← hopened] at hbody
  have he : env.IsDefEq U [] (.const data.name levels)
      (wrapLams Δ ((rb.instL levels).instOuter caps)) (wrapForalls Δ (.app (.bvar 2) (.bvar 0))) :=
    (ht.etaOpen_defeq henv (by trivial)).trans
      ((show env.IsDefEq U (Δ.reverse ++ []) _ _ _ by simpa using hbody).etaOpen_wrapLams (by trivial)
        (by simpa using hctx))
  let program : RecursorData.PrefixUnfolding :=
    ⟨Δ, .app (.bvar 2) (.bvar 0), mkApps E.ctor (vars P.length 3 ++ fs),
      ⟨data.uvars, wrapLams D lb, wrapLams D rb, wrapForalls D tb⟩,
      ⟨D, lb, rb, tb⟩, caps, levels⟩
  refine ⟨program, ?_, ?_⟩
  · have hall : vars (data.majorOffset + 1) 0 =
        vars P.length 3 ++ vars 2 1 ++ [VExpr.bvar 0] := by
      rw [hmajor, vars_add, vars_add]
      rfl
    have htakeP : (vars P.length 3 ++ vars 2 1 ++ [VExpr.bvar 0]).take data.numParams = vars P.length 3 := by
      rw [← hnp, List.append_assoc, List.take_left' (by simp)]
    have htakeI : (vars P.length 3 ++ vars 2 1 ++ [VExpr.bvar 0]).take data.indexOffset =
        vars P.length 3 ++ vars 2 1 := by
      rw [hio, List.take_left' (by simp [P])]
    have hrecon : data.singletonReconstruction env levels (vars (data.majorOffset + 1) 0) =
        some (mkApps E.ctor (vars P.length 3 ++ fs), fs) := by
      simp only [RecursorData.singletonReconstruction, hS, hE, bind, Option.bind_some,
        hall, htakeP, hn, List.take_zero]
      rfl
    have htake := VExpr.takeForalls_wrapForalls Δ (.app (.bvar 2) (.bvar 0))
    rw [hΔlen, ← hmajor] at htake
    unfold RecursorData.singletonUnfolding
    rw [if_neg (by simp [hlen])]
    simp only [bind, hrt, Option.bind_some, RecursorData.supplyType, htype,
      List.length_nil, Nat.sub_zero, htake, List.map_nil, List.nil_append, hrecon,
      hseq, hgen, hext]
    simp only [hall, htakeI]
    rw [if_neg (by change ¬(caps.length != D.length) = true; simp [hcaplen])]
    rfl
  · exact ⟨_, by simpa only [program, RecursorData.PrefixUnfolding.rhs,
      instantiateParams_eq_instOuter] using he⟩

/-- A successful generated zero prefix supplies its owned constructor metadata;
the closed equation therefore needs no extra constructor-selection premise. -/
theorem zero_equation (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF U) (hlen : levels.length = data.uvars)
    (hg : data.singletonUnfolding env U levels [] = some program) (hn : data.numIndices = 0) :
    env.IsDefEqU U [] (.const data.name levels) program.rhs := by
  obtain ⟨_, _, _, _, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq hseq
  obtain ⟨program', hg', he⟩ := zero_equation_exists henv heq H hlarge hzero hw hlen howner hn
  cases RecursorData.singletonUnfolding_unique hg' hg
  exact he

/-- The generated equation body is scoped at its capture telescope, at every
prefix length, because its registered equation is closed. -/
theorem generated_template_closed (henv : env.WF) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hg : data.singletonUnfolding env U levels args = some program) :
    program.equationBody.rhs.ClosedN program.captures.length := by
  obtain ⟨_, _, _, _, hseq, hbody, hcaps⟩ := RecursorData.singletonUnfolding_spec hg
  obtain ⟨index, _, hgen⟩ := RecursorData.singletonEquation_eq hseq
  have hpe := H.patEquation_of_empty henv (RecursorData.singletonSignature H hlarge hzero).restoration hgen
  have hc := hpe.rhs_closed
  obtain ⟨_, hrhs, _⟩ := RecursorSchema.EquationBody.extract_sound hbody
  rw [← hrhs] at hc
  simpa only [Nat.zero_add, hcaps] using closed_wrapLams_body hc

/-- Every generated singleton prefix is a finite beta specialization of the
zero-prefix program. This syntax theorem does not require index alignment. -/
theorem generated_prefix_beta (henv : env.WF) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hg0 : data.singletonUnfolding env U levels [] = some zero)
    (hg : data.singletonUnfolding env U levels args = some program) :
    BetaRed (mkApps zero.rhs args) program.rhs := by
  induction args using List.snoc_induction generalizing program with
  | nil => cases RecursorData.singletonUnfolding_unique hg0 hg; exact .refl
  | snoc args a ih =>
    have hbound := (RecursorData.singletonUnfolding_spec hg).1
    obtain ⟨early, hearly⟩ := RecursorData.singletonUnfolding_anyArity hg
      (args' := args) (by simp only [List.length_append, List.length_singleton] at hbound; omega)
    obtain ⟨A, body, he, hb⟩ := RecursorData.singletonUnfolding_supply_one henv H hlarge hzero
      hearly hg (generated_template_closed henv H hlarge hzero hearly)
    rw [mkApps_snoc]
    apply (BetaRed.app (ih hearly) .refl).trans
    rw [he, ← hb]
    exact .beta

/-- The generated zero-prefix value is closed independently of any later occurrence. -/
theorem zero_closed (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF U) (hlen : levels.length = data.uvars)
    (hg : data.singletonUnfolding env U levels [] = some program) (hn : data.numIndices = 0) :
    program.rhs.Closed := by
  obtain ⟨_, he⟩ := zero_equation henv heq H hlarge hzero hw hlen hg hn
  exact he.hasType.2.closedN henv.ordered (by trivial)

end Lean4Lean.VEnv.Strengthening.ClosedSingleton
