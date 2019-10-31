{-# OPTIONS --rewriting --prop --without-K #-}
open import common renaming (Unit to metaUnit)
open import typetheory
open import reflection
open import syntx
open import rules

TmTy : {Γ : Ctx n} {A : TyExpr n} {u : TmExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A)
TmTy dΓ (VarLast du) = WeakTy du
TmTy dΓ (VarPrev du du₁) = WeakTy du
TmTy dΓ (Conv du du₁ du₂) = TyEqTy2 dΓ du₂
-- TmTy dΓ UUUU = UU
-- TmTy dΓ (PiUU du du₁) = UU
TmTy dΓ (Lam du du₁ du₂) = Pi du du₁
TmTy dΓ (App {Γ = Γ} {A = A} du du₁ du₂ du₃) = SubstTy {Δ = Γ , A} du₁ ((idMorDerivable dΓ) , congTmTy! ([idMor]Ty _) du₃) 
-- TmTy dΓ (SigUU du du₁) = UU
-- TmTy dΓ (Pair du du₁ du₂ du₃) = Sig du du₁
-- TmTy dΓ (Pr1 du du₁ du₂) = du
-- TmTy dΓ (Pr2 du du₁ du₂) = SubstTy du₁ ((idMorDerivable dΓ) , congTmTy! ([idMor]Ty _) (Pr1 du du₁ du₂))
-- TmTy dΓ EmptyUU = UU
-- TmTy dΓ (Emptyelim du du₁) = SubstTy du ((idMorDerivable dΓ) , du₁)
-- TmTy dΓ UnitUU = UU
-- TmTy dΓ TT = Unit
-- TmTy dΓ (Unitelim du du₁ du₂) = SubstTy du ((idMorDerivable dΓ) , du₂)
-- TmTy dΓ NatUU = UU
-- TmTy dΓ Zero = Nat
-- TmTy dΓ (Suc du) = Nat
-- TmTy dΓ (Natelim du du₁ du₂ du₃) = SubstTy du ((idMorDerivable dΓ) , du₃)
-- TmTy dΓ (IdUU du du₁ du₂) = UU
-- TmTy dΓ (Refl du du₁) = Id du du₁ du₁
-- TmTy dΓ (JJ {A = A} {P = P} {a = a} {b = b} du du₁ du₂ du₃ du₄ du₅) = SubstTy du₁ (((((idMorDerivable dΓ) , congTmTy! ([idMor]Ty _) du₃) , congTmTy! (weakenTyInsert A (idMor _) a) (congTmTy! ([idMor]Ty _) du₄) ) , congTmTy! (ap-id-Ty (subst2Ty-weakenTy) refl refl) du₅))

TmEqTy : {Γ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ A)
TmEqTy dΓ (VarLastCong du=) = WeakTy du=
TmEqTy dΓ (VarPrevCong du= du=₁) = WeakTy du=
TmEqTy dΓ (TmSymm du=) = TmEqTy dΓ du=
TmEqTy dΓ (TmTran du= du=₁ du=₂) = TmTy dΓ du=
TmEqTy dΓ (ConvEq du= du=₁ du=₂) = TyEqTy2 dΓ du=₂
TmEqTy dΓ (LamCong du= du=₁ du=₂ du=₃) = Pi du= (TyEqTy1 (dΓ , du=) du=₂)
TmEqTy dΓ (AppCong du= du=₁ du=₂ du=₃ du=₄) = SubstTy (TyEqTy1 (dΓ , du=) du=₂) (idMorDerivable dΓ , congTmTy! ([idMor]Ty _) (TmEqTm1 dΓ du=₄))
TmEqTy dΓ (BetaPi du= du=₁ du=₂ du=₃) = SubstTy du=₁ (idMorDerivable dΓ ,  congTmTy! ([idMor]Ty _) du=₃) 
TmEqTy dΓ (EtaPi du= du=₁ du=₂) = TmTy dΓ du=₂

getCtx : Judgment → ΣSS ℕ Ctx 
getCtx ( _⊢_ {n = n} Γ x) = (n , Γ)
getCtx (_⊢_:>_ {n = n} Γ x x₁) = n , Γ
getCtx (_⊢_==_ {n = n} Γ x x₁) = n , Γ
getCtx (_⊢_==_:>_ {n = n} Γ x x₁ x₂) = n , Γ
