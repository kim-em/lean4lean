import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativeEtaExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSubstitutionImages

/-! # Closed control types with an opaque positive carrier

An opaque closed positive carrier, universes and nondependent arrows type
the control frames introduced around a retained neutral value. The annotation on a raw lambda may differ from
its closed control domain; uniqueness supplies the conversion. These witnesses
retain ordinary typing, not native recovery at a preselected annotation.
-/
namespace Lean4Lean.VEnv.Strengthening.AtomicControl
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

variable [Params]

/-- A closed positive carrier separated from function types. Registered
non-propositional rigid families supply these data; the interface contains no
computation, recovery, or strengthening assumption. -/
class Atom where
  type : VExpr
  sortLevel : VLevel
  closed : type.Closed
  typed : env.HasType univs [] type (.sort (.succ sortLevel))
  noPi : ∀ {Γ A B}, OnCtx Γ (env.IsType univs) →
    env.IsDefEqU univs Γ type (.forallE A B) → False

variable [Atom]

/-- The simple, closed type assigned to a marked control frame. -/
inductive ControlType where
  | atom
  | sort (u : VLevel)
  | arrow (domain result : ControlType)

namespace ControlType
/-- Interpret a control type as an actual, closed object-language type. -/
def expr : ControlType → VExpr
  | .atom => Atom.type
  | .sort u => .sort u
  | .arrow A B => .forallE A.expr B.expr

/-- The canonical universe of a control type. -/
def level : ControlType → VLevel
  | .atom => .succ Atom.sortLevel
  | .sort u => .succ u
  | .arrow A B => .imax A.level B.level

/-- Only universe parameters require a well-formedness check. -/
def WF (U : Nat) : ControlType → Prop
  | .atom => True
  | .sort u => u.WF U
  | .arrow A B => A.WF U ∧ B.WF U

/-- Every control type is closed at every binder depth. -/
theorem closedN (t : ControlType) : t.expr.ClosedN k := by
  induction t generalizing k with
  | atom => exact Atom.closed.mono (Nat.zero_le _)
  | sort => trivial
  | arrow A B ihA ihB => exact ⟨ihA, ihB⟩

/-- Substitution leaves the assigned control type unchanged. -/
theorem expr_subst (t : ControlType) : t.expr.subst σ = t.expr :=
  (t.closedN (k := 0)).subst_eq (by intro i hi; omega)

/-- Every control universe is positive, including nested arrows. -/
theorem level_ne_zero (t : ControlType) : t.level.IsNeverZero := by
  induction t with
  | atom => intro ls; simp [level, VLevel.eval]
  | sort => intro ls; simp [level, VLevel.eval]
  | arrow A B ihA ihB =>
    intro ls
    simp [level, VLevel.eval, Lean.Nat.imax, ihB ls, Nat.max_eq_zero_iff]

/-- The closed interpretation has its canonical universe in every context. -/
theorem typed {t : ControlType} (H : t.WF univs) : env.HasType univs Γ t.expr (.sort t.level) := by
  induction t generalizing Γ with
  | atom => exact Atom.typed.weak0 henv.ordered
  | sort => exact .sort H
  | arrow A B ihA ihB => exact .forallE (ihA H.1) (ihB H.2)

/-- Any typing of the closed interpretation validates all its parameters. -/
theorem wf_of_typing {t : ControlType} (henv : env.Ordered) (ht : env.HasType univs Γ t.expr T) : t.WF univs := by
  induction t generalizing Γ T with
  | atom => trivial
  | sort => exact ht.sort_inv henv
  | arrow A B ihA ihB =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact ⟨ihA hA, ihB hB⟩
end ControlType

/-- A raw control expression has an ordinary typed representative at its
closed assigned type, in some well-formed realization of the raw context. -/
def ControlTyping (Δ : List ProofShape) (e : ProofShape) (t : ControlType) : Prop :=
  ∃ Γ f, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
    env.HasType univs Γ f t.expr ∧ proofErase Γ f = e

/-- An actual assigned typing introduces a control witness. -/
theorem ControlTyping.of_typed (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e t.expr) :
    ControlTyping (proofEraseCtx Γ) (proofErase Γ e) t := ⟨Γ, e, hΓ, rfl, ht, rfl⟩

/-- Control witnesses validate the universes of their assigned type. -/
theorem ControlTyping.wf (H : ControlTyping Δ e t) : t.WF univs := by
  obtain ⟨Γ, f, hΓ, _, hf, _⟩ := H
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  exact ControlType.wf_of_typing henv.ordered hT

/-- An inhabitant of a control type cannot be a proof: the type has a
strictly positive canonical universe. -/
theorem ControlType.not_isProof {t : ControlType} (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ f t.expr) : ¬ IsProof Γ f := by
  rintro ⟨P, hfP, hP⟩
  obtain ⟨_, hT⟩ := ht.isType henv hΓ
  have hW := ControlType.wf_of_typing henv.ordered hT
  have hT0 := hP.defeqU_l henv hΓ (ht.uniqU henv hΓ hfP).symm
  have E := ((ControlType.typed (Γ := Γ) hW).uniqU henv hΓ hT0).sort_inv henv hΓ
  exact t.level_ne_zero [] (congrFun E [])

/-- In particular, the raw proof marker carries no control witness. -/
theorem ControlTyping.ne_proof (H : ControlTyping Δ e t) : e ≠ .proof := by
  obtain ⟨Γ, f, hΓ, _, hf, Ef⟩ := H
  intro E
  exact ControlType.not_isProof hΓ hf (proofErase_eq_proof.1 (Ef.trans E))

/-- Ordinary interpreted substitution transports the witness at the same
closed control type, without any native-image assumption. -/
theorem ControlTyping.subst (H : ControlTyping Δ e t) (W : ContextSubstitution Δ Δ' τ) :
    ControlTyping Δ' (e.subst τ) t := by
  obtain ⟨Γ, f, hΓ, EΓ, hf, Ef⟩ := H
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HS, ES⟩ := W hΓ EΓ
  refine ⟨Γ₀, f.subst σ, hΓ₀, EΓ₀, ?_, ?_⟩
  · simpa only [ControlType.expr_subst] using hf.subst henv.orderedStrong HS hΓ₀
  · rw [proofErase_subst_with hΓ₀ HS hf ES, Ef]

/-- Source-typed replay preserves a control witness through compatible
computation, including all changes of displayed lambda annotations. -/
theorem ControlTyping.compute (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ControlTyping Δ e t) (R : ScopedCompute Step Δ e out) : ControlTyping Δ out t := by
  obtain ⟨Γ, f, hΓ, EΓ, hf, Ef⟩ := H
  obtain ⟨f', HE, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef R
  exact ⟨Γ, f', hΓ, EΓ, HE.hasType.2, Ef'⟩

/-- A typed binder permits ordinary weakening of every control witness in
its raw context; exact native oracle preservation is not needed by callers. -/
theorem ControlTyping.weak_interpretation (H : ControlTyping Δ e t) (S : DomainSort Δ A u) :
    ContextSubstitution Δ (A :: Δ) (fun i => .bvar (i+1)) := by
  obtain ⟨Γ, f, hΓ, rfl, hf, Ef⟩ := H
  obtain ⟨D, hD, ED⟩ := S.realize hΓ
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  intro Γ' hΓ' EΓ'
  have W := ContextRenaming.of_liftN hΓ hΓD Ctx.LiftN.one
  simpa only [proofEraseCtx, ED, liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm]
    using W.interpretation hΓ' EΓ'

/-- A retained lambda at a control arrow gives a control-typed body and
fresh variable in its actual displayed raw domain. Domain conversion follows
from Pi injectivity, so the displayed domain need not be canonical. -/
theorem ControlTyping.lam_parts (H : ControlTyping Δ (.lam D b) (.arrow A B)) :
    ControlTyping (D :: Δ) b B ∧ ControlTyping (D :: Δ) (.bvar 0) A := by
  obtain ⟨Γ, f, hΓ, rfl, hf, Ef⟩ := H
  obtain ⟨D', b', rfl, _, ED, Eb⟩ := erase_lam_inv Ef
  obtain ⟨⟨u, hD⟩, C, hb⟩ := hf.lam_inv henv hΓ
  have hb : env.HasType univs (D' :: Γ) b' C := hb
  have hΓD : OnCtx (D' :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  obtain ⟨⟨_, HD⟩, _, HC⟩ := ((HasType.lam hD hb).uniqU henv hΓ hf).forallE_inv henv hΓ
  have hb' : env.HasType univs (D' :: Γ) b' B.expr := hb.defeqU_r henv hΓD HC.toU
  have hx : env.HasType univs (D' :: Γ) (.bvar 0) A.expr := by
    have HX := (show env.HasType univs (D' :: Γ) (.bvar 0) D'.lift from .bvar .zero).defeqU_r henv hΓD (HD.toU.weak henv)
    simpa only [ControlType.expr, (A.closedN (k := 0)).lift_eq] using HX
  have EX : proofErase (D' :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (ControlType.not_isProof hΓD hx)
  exact ⟨⟨D' :: Γ, b', hΓD, by simp only [proofEraseCtx, ED], hb', Eb⟩,
    ⟨D' :: Γ, .bvar 0, hΓD, by simp only [proofEraseCtx, ED], hx, EX⟩⟩

/-- Native eta cannot expand a control payload assigned a universe: type
uniqueness separates its assigned sort from every recovered function type. -/
theorem ControlTyping.no_eta_sort (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ControlTyping Δ e (.sort u)) (R : NativeEtaExpansion Step Δ e out) : False := by
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  cases R with
  | intro RN S =>
    obtain ⟨D, C, hDC, _, _⟩ := proofErase_scoped_recovered_pi_descend
      hstep hΓ hΓ (Ctx.LiftN.zero []) hf (by simpa only [List.length_nil, ProofShape.liftN_zero] using RN)
    exact (hf.uniqU henv hΓ hDC).sort_forallE_inv henv hΓ

/-- Native eta cannot expand a value of the opaque atomic carrier. -/
theorem ControlTyping.no_eta_atom (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ControlTyping Δ e .atom) (R : NativeEtaExpansion Step Δ e out) : False := by
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  cases R with
  | intro RN S =>
    obtain ⟨D, C, hDC, _, _⟩ := proofErase_scoped_recovered_pi_descend
      hstep hΓ hΓ (Ctx.LiftN.zero []) hf (by simpa only [List.length_nil, ProofShape.liftN_zero] using RN)
    exact Atom.noPi hΓ (hf.uniqU henv hΓ hDC)

/-- A recovered domain of a control arrow is in a positive universe.
Consequently native eta retains its fresh argument, even when the selected
annotation differs from the closed assigned control domain. -/
theorem ControlTyping.eta_domain_ne_zero (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ControlTyping Δ e (.arrow A B))
    (RN : ScopedTypeRecovery Step Δ e (.forallE D C)) (S : DomainSort Δ D u) : ¬ u ≈ .zero := by
  have hWA := H.wf.1
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  obtain ⟨D', C', hDC, ED, _⟩ := proofErase_scoped_recovered_pi_descend
    hstep hΓ hΓ (Ctx.LiftN.zero []) hf (by simpa only [List.length_nil, ProofShape.liftN_zero] using RN)
  simp only [List.length_nil, ProofShape.liftN_zero] at ED
  obtain ⟨⟨_, HD⟩, _⟩ := (hf.uniqU henv hΓ hDC).forallE_inv henv hΓ
  have hD : env.HasType univs Γ D' (.sort A.level) :=
    (ControlType.typed hWA).defeqU_l henv hΓ HD.toU
  have S' : DomainSort (proofEraseCtx Γ) ((proofErase Γ D').liftN 0) u := by
    simpa only [ProofShape.liftN_zero, ED] using S
  have hDu := S'.descend hΓ hΓ (Ctx.LiftN.zero []) hD
  have E := (hD.uniqU henv hΓ hDu).sort_inv henv hΓ
  intro E0
  exact A.level_ne_zero [] ((congrFun E []).trans (congrFun E0 []))

/-- Typed native eta at a control arrow has the ordinary fresh-variable
shape and supplies both control witnesses beneath its selected binder. -/
theorem ControlTyping.eta_parts (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ControlTyping Δ e (.arrow A B)) (R : NativeEtaExpansion Step Δ e out) :
    ∃ D, out = .lam D (.app (e.liftN 1) (.bvar 0)) ∧
      ControlTyping Δ out (.arrow A B) ∧
      ControlTyping (D :: Δ) (.app (e.liftN 1) (.bvar 0)) B ∧
      ControlTyping (D :: Δ) (.bvar 0) A ∧ ∃ u, DomainSort Δ D u := by
  have HT := H.compute (erased_nativeEtaExpansion_descent hstep) (.base R)
  cases R with
  | intro RN S =>
    have E : etaArgument _ = .bvar 0 := if_neg (H.eta_domain_ne_zero hstep RN S)
    rw [E] at HT ⊢
    obtain ⟨HB, HX⟩ := HT.lam_parts
    exact ⟨_, rfl, HT, HB, HX, _, S⟩

/-- The fixed constant wrapper has the control arrow from Type to the
payload's control type. Its body keeps that type under the unused binder. -/
theorem ControlTyping.constant_frame (H : ControlTyping Δ e t) :
    ControlTyping Δ (.lam (.sort (.succ .zero)) (e.liftN 1))
      (.arrow (.sort (.succ .zero)) t) ∧ DomainSort Δ (.sort (.succ .zero)) (.succ (.succ .zero)) := by
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓS : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hbody : env.HasType univs (.sort (.succ .zero) :: Γ) f.lift t.expr := by
    have hb : env.HasType univs (.sort (.succ .zero) :: Γ) f.lift t.expr.lift := hf.weak henv
    rwa [(t.closedN (k := 0)).lift_eq] at hb
  have hF : env.HasType univs Γ (.lam (.sort (.succ .zero)) f.lift)
      (ControlType.arrow (.sort (.succ .zero)) t).expr := .lam hS hbody
  have ES : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
    if_neg (not_isProof_of_sort hΓ hS)
  refine ⟨⟨Γ, _, hΓ, rfl, hF, ?_⟩, ⟨Γ, _, hΓ, rfl, hS, ES⟩⟩
  rw [show proofErase Γ (.lam _ _) = .lam _ _ from if_neg (ControlType.not_isProof hΓ hF),
    ES, proofErase_liftN hΓ hΓS Ctx.LiftN.one hf]

/-- A natively selected identity annotation gives the closed control arrow
from the payload's type to itself. The displayed annotation is converted by
type uniqueness rather than required to equal that closed type syntactically. -/
theorem ControlTyping.identity_frame (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ControlTyping Δ e t) (RN : ScopedTypeRecovery Step Δ e D) :
    ControlTyping Δ (.lam D (.bvar 0)) (.arrow t t) := by
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  obtain ⟨D', hfD, ED⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf rfl
    (by simpa only [List.length_nil, ProofShape.liftN_zero] using RN)
  simp only [ProofShape.liftN_zero] at ED
  obtain ⟨u, hD⟩ := hfD.isType henv hΓ
  have hΓD : OnCtx (D' :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have HD := (hfD.uniqU henv hΓ hf).of_l henv hΓ hD
  have hx : env.HasType univs (D' :: Γ) (.bvar 0) D'.lift := .bvar .zero
  have HE := IsDefEq.forallEDF HD (HD.weak henv (B := D'))
  have hF : env.HasType univs Γ (.lam D' (.bvar 0)) (ControlType.arrow t t).expr := by
    simpa only [ControlType.expr, (t.closedN (k := 0)).lift_eq] using
      (HasType.lam hD hx).defeqU_r henv hΓ HE.toU
  have hx' : env.HasType univs (D' :: Γ) (.bvar 0) t.expr := by
    simpa only [(t.closedN (k := 0)).lift_eq] using hx.defeqU_r henv hΓD (HD.toU.weak henv)
  refine ⟨Γ, _, hΓ, rfl, hF, ?_⟩
  rw [show proofErase Γ (.lam _ _) = .lam _ _ from if_neg (ControlType.not_isProof hΓ hF),
    ED, show proofErase (D' :: Γ) (.bvar 0) = .bvar 0 from if_neg (ControlType.not_isProof hΓD hx')]

/-- A typed beta redex interprets its ordinary argument substitution at the
displayed binder. No native certificate for the argument is required. -/
theorem ControlTyping.beta_interpretation (H : ControlTyping Δ (.app (.lam D b) a) t) :
    ContextSubstitution (D :: Δ) Δ (ProofShape.Subst.one a) := by
  obtain ⟨Γ, f, hΓ, rfl, hf, Ef⟩ := H
  obtain ⟨f₀, a₀, rfl, _, EF, Ea⟩ := erase_app_inv Ef
  obtain ⟨D₀, b₀, rfl, _, ED, Eb⟩ := erase_lam_inv EF
  obtain ⟨_, _, hF, ha⟩ := hf.app_inv henv hΓ
  obtain ⟨⟨u, hD⟩, _, hb⟩ := hF.lam_inv henv hΓ
  have haD := argument_at_displayed_domain hΓ hF (HasType.lam hD hb) ha
  have hΓD : OnCtx (D₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have W : ContextSubstitution (proofEraseCtx (D₀ :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ a₀)) :=
    ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓD haD)
      (erasedSubstAgreement_one hΓD haD)
  rw [proofEraseCtx, ED, Ea] at W
  intro Γ' hΓ' EΓ'
  exact W hΓ' EΓ'

omit [Atom] in
/-- Definitionally equal actual contexts interpret the raw identity
substitution. This needs no equality between their raw lookup annotations. -/
theorem control_context_substitution (HC : IsDefEqCtx env univs [] Γ Γ') :
    ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ') ProofShape.Subst.id := by
  have hΓ' := (HC.symm henv.ordered).isType
  have W : Ctx.SubstEq env univs Γ' VExpr.Subst.id VExpr.Subst.id Γ :=
    substEq_source_convert hΓ' (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓ')
  have ES : ErasedSubstAgreement Γ Γ' VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    have hn' : ¬ IsProof Γ' (.bvar i) := fun hp => hn ((isProof_defeqCtx HC).2 hp)
    exact if_neg hn'
  intro Γ₀ hΓ₀ EΓ₀
  exact ContextSubstitution.of_typed hΓ' W ES hΓ₀ EΓ₀

end Lean4Lean.VEnv.Strengthening.AtomicControl
