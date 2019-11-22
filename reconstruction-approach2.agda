{-# OPTIONS --rewriting --prop --without-K #-}

open import common renaming (Unit to metaUnit)
open import normal
import ex 
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)
open import translation

liftTy : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : TyExpr n) → ex.TyExpr n
liftTm : {n : ℕ} → (Γ : (ex.Ctx n)) → (u : TmExpr n) → ex.TmExpr n

liftTy Γ (uu i) = ex.uu i
liftTy Γ (el i v) = ex.el i (ex.coerc (ex.getTy Γ (liftTm Γ v)) (ex.uu i) (liftTm Γ v))
liftTy Γ (pi A A₁) = ex.pi (liftTy Γ A ) (liftTy (Γ ex., (liftTy Γ A)) A₁) 
-- liftTy (suc zero) Γ (uu i) <m = ex.uu i
-- liftTy (suc m) Γ (el i v) <m = ex.el i (ex.coerc (ex.getTy (liftCtx Γ) (liftTm m Γ v (suc-ref-< <m))) (ex.uu i) (liftTm (m) Γ v (suc-ref-< <m)))
-- liftTy (suc m) Γ (pi A A₁) <m = ex.pi (liftTy (m) Γ A {!!}) (liftTy m (Γ , A) A₁ {!!})

liftTm Γ (var x) = ex.var x
liftTm Γ (lam A B u) = ex.lam (liftTy Γ A) (liftTy (Γ ex., (liftTy Γ A)) B) (ex.coerc (ex.getTy (Γ ex., liftTy Γ A) (liftTm (Γ ex., liftTy Γ A) u)) (liftTy (Γ ex., liftTy Γ A) B) (liftTm (Γ ex., liftTy Γ A) u))
liftTm Γ (app A B u u₁) = ex.app (liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) (ex.coerc (ex.getTy Γ (liftTm Γ u)) (liftTy Γ (pi A B)) (liftTm Γ u)) (ex.coerc (ex.getTy Γ (liftTm Γ u₁)) (liftTy Γ A) (liftTm Γ u₁))
{- 
liftTy zero Γ (uu i) = ex.uu i
liftTy Γ (el i v) = ex.el i (ex.coerc (ex.getTy (liftCtx Γ) (liftTm Γ v)) (ex.uu i) (liftTm Γ v))
liftTy Γ (pi A A₁) = ex.pi (liftTy Γ A) (liftTy (Γ , A) A₁)

liftTm Γ (var x) = ex.var x
liftTm Γ (lam A B u) = ex.lam (liftTy Γ A) (liftTy (Γ , A) B) (ex.coerc (ex.getTy (liftCtx (Γ , A)) (liftTm (Γ , A) u)) (liftTy (Γ , A) B) (liftTm (Γ , A) u))
liftTm Γ (app A B u u₁) = ex.app (liftTy Γ A) (liftTy (Γ , A) B) (ex.coerc (ex.getTy (liftCtx Γ) (liftTm Γ u)) (liftTy Γ (pi A B)) (liftTm Γ u)) (ex.coerc (ex.getTy (liftCtx Γ) (liftTm Γ u₁)) (liftTy Γ A) (liftTm Γ u₁))
-}
liftCtx : {n : ℕ} → (Γ : Ctx n) → ex.Ctx n
liftCtx ◇ = ex.◇
liftCtx (Γ , A) = liftCtx Γ ex., liftTy (liftCtx Γ) A

liftMor : {n m : ℕ} → Mor n m → ex.Ctx n → ex.Mor n m
liftMor ◇ Γ = ex.◇
liftMor (δ , u) Γ = liftMor δ Γ ex., liftTm Γ u

liftJdg : Judgment → ex.Judgment
liftJdg (Γ ⊢ x) = liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) x
liftJdg (Γ ⊢ x :> x₁) = liftCtx Γ ⊢ₑ liftTm (liftCtx Γ) x :> liftTy (liftCtx Γ) x₁
liftJdg (Γ ⊢ x == x₁) = liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) x == liftTy (liftCtx Γ) x₁
liftJdg (Γ ⊢ x == x₁ :> x₂) = liftCtx Γ ⊢ₑ liftTm (liftCtx Γ) x == liftTm (liftCtx Γ) x₁ :> liftTy (liftCtx Γ) x₂

strip-liftTy : (Γ : ex.Ctx n) → (A : TyExpr n) → || liftTy Γ A ||Ty ≡ A
strip-liftTm : (Γ : ex.Ctx n) → (v : TmExpr n) → || liftTm Γ v ||Tm ≡ v

strip-liftTy Γ (uu i) = refl
strip-liftTy Γ (el i v) = ap (el i) (strip-liftTm Γ v)
strip-liftTy Γ (pi A A₁) = ap-pi-Ty (strip-liftTy Γ A) (strip-liftTy (Γ ex., liftTy Γ A) A₁)

strip-liftTm Γ (var x) = refl
strip-liftTm Γ (lam A B v) = ap-lam-Tm (strip-liftTy Γ A) (strip-liftTy (Γ ex., liftTy Γ A) B) (strip-liftTm (Γ ex., liftTy Γ A) v)
strip-liftTm Γ (app A B v v₁) = ap-app-Tm (strip-liftTy Γ A) (strip-liftTy (Γ ex., liftTy Γ A) B) (strip-liftTm Γ v) (strip-liftTm Γ v₁)

strip-liftCtx : (Γ : Ctx n) → || liftCtx Γ ||Ctx ≡ Γ
strip-liftCtx ◇ = refl
strip-liftCtx (Γ , A) = Ctx+= (strip-liftCtx Γ) (strip-liftTy (liftCtx Γ) A)

strip-lift : (j : Judgment) → || liftJdg j || ≡ j
strip-lift (Γ ⊢ x) = ap-jdg-ty (strip-liftCtx Γ) (strip-liftTy (liftCtx Γ) x)
strip-lift (Γ ⊢ x :> x₁) = ap-jdg-tm (strip-liftCtx Γ) (strip-liftTy (liftCtx Γ) x₁) (strip-liftTm (liftCtx Γ) x)
strip-lift (Γ ⊢ x == x₁) = ap-jdg-tyEq (strip-liftCtx Γ) (strip-liftTy (liftCtx Γ) x) (strip-liftTy (liftCtx Γ) x₁)
strip-lift (Γ ⊢ x == x₁ :> x₂) = ap-jdg-tmEq (strip-liftCtx Γ) (strip-liftTy (liftCtx Γ) x₂) (strip-liftTm (liftCtx Γ) x) (strip-liftTm (liftCtx Γ) x₁)

{- when lifting a weakened type or term, the last type in the context does not matter -}
weakenTm'-liftTm : (k : Fin (suc n)) (Γ : ex.Ctx n) (A : ex.TyExpr (n -F' k)) (u : TmExpr n) → liftTm (ex.weakenCtx k Γ A) (weakenTm' k u) ≡ ex.weakenTm' k (liftTm Γ u)
weakenTy'-liftTy : (k : Fin (suc n)) (Γ : ex.Ctx n) (B : ex.TyExpr (n -F' k)) (A : TyExpr n) → liftTy (ex.weakenCtx k Γ B) (weakenTy' k A) ≡ ex.weakenTy' k (liftTy Γ A)

weakenTy'-liftTy k Γ B (uu i) = refl
weakenTy'-liftTy k Γ B (el i v) rewrite
                ex.weakenTy'-getTy k Γ (liftTm Γ v) (B)
                | weakenTm'-liftTm k Γ B v
                = refl
weakenTy'-liftTy k Γ B (pi A A₁) rewrite weakenTy'-liftTy k Γ B A | weakenTy'-liftTy (prev k) (Γ ex., (liftTy Γ A)) B A₁ = refl

weakenTm'-liftTm k Γ A u = {!!}

Lift-Der : {jdg : Judgment} → Derivable (jdg) → ex.Derivable (liftJdg jdg)
Lift-Der (VarLast dj) = {!!}
Lift-Der (VarPrev dj dj₁) = {!!}
Lift-Der (VarLastCong dj) = {!!}
Lift-Der (VarPrevCong dj dj₁) = {!!}
Lift-Der (TySymm dj) = {!!}
Lift-Der (TyTran dj dj₁ dj₂) = {!!}
Lift-Der (TmSymm dj) = {!!}
Lift-Der (TmTran dj dj₁ dj₂) = {!!}
Lift-Der (Conv dj dj₁ dj₂) = {!!}
Lift-Der (ConvEq dj dj₁ dj₂) = {!!}
Lift-Der UU = {!!}
Lift-Der UUCong = {!!}
Lift-Der (El dj) = {!!}
Lift-Der (ElCong dj) = {!!}
Lift-Der (Pi dj dj₁) = {!!}
Lift-Der (PiCong dj dj₁ dj₂) = {!!}
Lift-Der (Lam dj dj₁ dj₂) = {!!}
Lift-Der (LamCong dj dj₁ dj₂ dj₃) = {!!}
Lift-Der (App dj dj₁ dj₂ dj₃) = {!!}
Lift-Der (AppCong dj dj₁ dj₂ dj₃ dj₄) = {!!}
Lift-Der (BetaPi dj dj₁ dj₂ dj₃) = {!!}
Lift-Der (EtaPi dj dj₁ dj₂) = {!!}
