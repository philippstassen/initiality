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
TmTy dΓ UUUU = UU
TmTy dΓ (PiUU du du₁) = UU
TmTy dΓ (Lam du du₁ du₂) = Pi du du₁
TmTy dΓ (App {Γ = Γ} {A = A} du du₁ du₂ du₃) = SubstTy {Δ = Γ , A} du₁ ((idMorDerivable dΓ) , congTmTy! ([idMor]Ty _) du₃) 
TmTy dΓ (SigUU du du₁) = UU
TmTy dΓ (Pair du du₁ du₂ du₃) = Sig du du₁
TmTy dΓ (Pr1 du du₁ du₂) = du
TmTy dΓ (Pr2 du du₁ du₂) = SubstTy du₁ ((idMorDerivable dΓ) , congTmTy! ([idMor]Ty _) (Pr1 du du₁ du₂))
TmTy dΓ EmptyUU = UU
TmTy dΓ (Emptyelim du du₁) = SubstTy du ((idMorDerivable dΓ) , du₁)
TmTy dΓ UnitUU = UU
TmTy dΓ TT = Unit
TmTy dΓ (Unitelim du du₁ du₂) = SubstTy du ((idMorDerivable dΓ) , du₂)
TmTy dΓ NatUU = UU
TmTy dΓ Zero = Nat
TmTy dΓ (Suc du) = Nat
TmTy dΓ (Natelim du du₁ du₂ du₃) = SubstTy du ((idMorDerivable dΓ) , du₃)
TmTy dΓ (IdUU du du₁ du₂) = UU
TmTy dΓ (Refl du du₁) = Id du du₁ du₁
TmTy dΓ (JJ {A = A} {P = P} {a = a} {b = b} du du₁ du₂ du₃ du₄ du₅) = SubstTy du₁ (((((idMorDerivable dΓ) , congTmTy! ([idMor]Ty _) du₃) , congTmTy! (weakenTyInsert A (idMor _) a) (congTmTy! ([idMor]Ty _) du₄) ) , congTmTy! (ap-id-Ty (subst2Ty-weakenTy) refl refl) du₅))