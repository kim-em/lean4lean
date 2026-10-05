import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceReflection
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFundamental

/-! Restrict the native argument valuation to an actual earlier telescope
prefix. This removes syntactically absent source binders from the stored
certificates; it does not retract target semantic evidence or strengthen a
typing conversion through an arbitrary inhabitance assumption. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Restrict the actual raw tuple to the same original telescope prefix. -/
theorem Ctx.SubstEq.nativePrefix
    {env : VEnv} {U : Nat} {target later source : List VExpr} {σ τ : Subst}
    (raw : Ctx.SubstEq env U target σ τ (later ++ source)) :
    Ctx.SubstEq env U target (Subst.lift_l (.skipN .refl later.length) σ)
      (Subst.lift_l (.skipN .refl later.length) τ) source := by
  induction later generalizing σ τ with
  | nil => exact raw
  | cons A later ih =>
    cases raw with
    | cons tail _ _ =>
      have restricted := ih tail
      have shift (ρ : Subst) : Subst.lift_l (.skipN .refl later.length) ρ.tail =
          Subst.lift_l (.skipN .refl (later.length + 1)) ρ := by
        funext i
        simp [Subst.lift_l, Subst.tail, Lift.liftVar_skipN, Lift.liftVar, Nat.add_assoc]
      simpa only [List.length_cons, shift] using restricted

/-- The full native lookup type is literally the lifted prefix lookup type.
Reflecting that source certificate retains exactly its original leaves. -/
theorem Fits.nativeTail
    (fits : Fits env U registry (A :: source) target locals σ τ available)
    (prefixLocals : List Nat) :
    Fits env U registry source target prefixLocals σ.tail τ.tail
      (fun index => available (index + 1)) := by
  constructor
  intro index need member type lookup
  obtain ⟨entry⟩ := fits.entry (index + 1) need member type.lift (.succ lookup)
  obtain ⟨footprint, ⟨certificate⟩, hf⟩ := entry.certificate.reflectSource (.skip .refl)
    lift_eq_lift' prefixLocals
  refine ⟨{
    support := entry.support
    footprint := footprint
    certificate := certificate
    available := ?_
    typed := entry.typed
    related := ?_ }⟩
  · intro i needed hm
    apply entry.available (i + 1) needed
    rw [hf]
    exact List.mem_map.mpr ⟨(i, needed), hm, rfl⟩
  · have he : Subst.lift_l (.skip .refl) σ = σ.tail := rfl
    simpa only [lift_eq_lift', subst_lift', he, Subst.tail] using entry.related

theorem PairedFits.nativeTail
    (fits : PairedFits env U registry (A :: source) target locals σ τ available)
    (prefixLocals : List Nat) :
    PairedFits env U registry source target prefixLocals σ.tail τ.tail
      (fun index => available (index + 1)) :=
  ⟨fits.forward.nativeTail prefixLocals, fits.backward.nativeTail prefixLocals⟩

/-- Drop the later formal arguments in one finite pass. This is the exact
prefix restriction required by a natural-domain native guard. -/
theorem PairedFits.nativePrefix
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {later source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation}
    (fits : PairedFits env U registry (later ++ source) target locals σ τ available)
    (prefixLocals : List Nat) :
    PairedFits env U registry source target prefixLocals
      (Subst.lift_l (.skipN .refl later.length) σ)
      (Subst.lift_l (.skipN .refl later.length) τ)
      (fun index => available (index + later.length)) := by
  induction later generalizing locals σ τ available with
  | nil =>
    change PairedFits env U registry source target prefixLocals σ τ available
    constructor <;> constructor
    · intro index need member type lookup
      obtain ⟨entry⟩ := fits.forward.entry index need member type lookup
      have certificate := entry.certificate.renameSource .refl σ rfl prefixLocals
      refine ⟨⟨entry.support, entry.footprint, ?_, entry.available, entry.typed, entry.related⟩⟩
      simpa [Footprint.sourceLift, Lift.liftVar] using certificate
    · intro index need member type lookup
      obtain ⟨entry⟩ := fits.backward.entry index need member type lookup
      have certificate := entry.certificate.renameSource .refl τ rfl prefixLocals
      refine ⟨⟨entry.support, entry.footprint, ?_, entry.available, entry.typed, entry.related⟩⟩
      simpa [Footprint.sourceLift, Lift.liftVar] using certificate
  | cons A later ih =>
    have restricted := ih (fits.nativeTail prefixLocals)
    have shift (ρ : Subst) : Subst.lift_l (.skipN .refl later.length) ρ.tail =
        Subst.lift_l (.skipN .refl (later.length + 1)) ρ := by
      funext i
      simp [Subst.lift_l, Subst.tail, Lift.liftVar_skipN, Lift.liftVar, Nat.add_assoc]
    simpa only [List.length_cons, shift, Nat.add_assoc] using restricted

end Lean4Lean.AnchoredSource.Adapted
