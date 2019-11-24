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
liftJdg (Γ ⊢ x :> x₁) = liftCtx Γ ⊢ₑ ex.coerc (ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) x)) (liftTy (liftCtx Γ) x₁) (liftTm (liftCtx Γ) x) :> liftTy (liftCtx Γ) x₁
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

{- weakenVar and ex.weakenVar are the same -}
weakenVar-weakenVar : (k : Fin (suc n)) → (x : Fin n) → weakenVar' k x ≡ ex.weakenVar' k x
weakenVar-weakenVar last x = refl
weakenVar-weakenVar (prev k) last = refl
weakenVar-weakenVar (prev k) (prev x) = ap prev (weakenVar-weakenVar k x)

{- when lifting a weakened type or term, the last type in the context does not matter -}
weakenTm'-liftTm : (k : Fin (suc n)) (Γ : ex.Ctx n) (A : ex.TyExpr (n -F' k)) (u : TmExpr n) → liftTm (ex.weakenCtx k Γ A) (weakenTm' k u) ≡ ex.weakenTm' k (liftTm Γ u)
weakenTy'-liftTy : (k : Fin (suc n)) (Γ : ex.Ctx n) (B : ex.TyExpr (n -F' k)) (A : TyExpr n) → liftTy (ex.weakenCtx k Γ B) (weakenTy' k A) ≡ ex.weakenTy' k (liftTy Γ A)

weakenTy'-liftTy k Γ B (uu i) = refl
weakenTy'-liftTy k Γ B (el i v) rewrite
                ex.weakenTy'-getTy k Γ (liftTm Γ v) (B)
                | weakenTm'-liftTm k Γ B v
                = refl
weakenTy'-liftTy k Γ B (pi A A₁) rewrite weakenTy'-liftTy k Γ B A | weakenTy'-liftTy (prev k) (Γ ex., (liftTy Γ A)) B A₁ = refl

weakenTm'-liftTm last Γ A (var x) = refl
weakenTm'-liftTm (prev k) Γ A (var last) = refl
weakenTm'-liftTm (prev k) (Γ ex., A₁) A (var (prev x)) = ap ex.var (ap prev (weakenVar-weakenVar k x))
weakenTm'-liftTm k Γ A (lam A₁ B u) rewrite weakenTy'-liftTy k Γ A A₁ | weakenTm'-liftTm (prev k) (Γ ex., (liftTy Γ A₁)) A u = ex.ap-lam-Tm (refl) (weakenTy'-liftTy (prev k) (Γ ex., (liftTy Γ A₁)) A B) (ex.ap-coerc-Tm (! (ex.weakenTy'-getTy (prev k) (Γ ex., liftTy Γ A₁) (liftTm (Γ ex., liftTy Γ A₁) u) A)) (weakenTy'-liftTy (prev k) (Γ ex., (liftTy Γ A₁)) A B) refl)
weakenTm'-liftTm k Γ A (app A₁ B u u₁) rewrite weakenTy'-liftTy k Γ A A₁ = ex.ap-app-Tm refl (weakenTy'-liftTy (prev k) (Γ ex., (liftTy Γ A₁)) A B) (ex.ap-coerc-Tm {!!} {!!} {!!}) {!!}


{- getTy commutes with lifting -}
getTy-liftTy : {n : ℕ} (Γ : Ctx n) (u : TmExpr n) → ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) u) ≡ liftTy (liftCtx Γ) (getTy Γ u)
getTy-liftTy (Γ , A) (var last) = ! (weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) A)
getTy-liftTy (Γ , A) (var (prev x)) rewrite getTy-liftTy Γ (var x) = ! (weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) (getTy Γ (var x)))
getTy-liftTy Γ (lam A B u) = {!!}
getTy-liftTy Γ (app A B u u₁) = {!!}

Lift-Der : {jdg : Judgment} → Derivable (jdg) → ex.⊢ snd (ex.getCtx (liftJdg jdg)) → ex.Derivable (liftJdg jdg)
Lift-Der (VarLast {Γ = Γ} {A = A} dj) (dΓ , dA) rewrite weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) A = ex.Conv (ex.WeakTy (Lift-Der dj dΓ)) (ex.WeakTy (Lift-Der dj dΓ)) (ex.VarLast (Lift-Der dj dΓ)) (ex.TyRefl (ex.WeakTy (Lift-Der dj dΓ)))
Lift-Der (VarPrev dj dj₁) dΓ = {!!}
Lift-Der (VarLastCong dj) dΓ = {!!}
Lift-Der (VarPrevCong dj dj₁) dΓ = {!!}
Lift-Der (TySymm dj) dΓ = {!!}
Lift-Der (TyTran dj dj₁ dj₂) dΓ = {!!}
Lift-Der (TmSymm dj) dΓ = {!!}
Lift-Der (TmTran dj dj₁ dj₂) dΓ = {!!}
{- we need to make the case distinctions so that getTy reduces to cases -}
{- how to get derivation of equality weakenTy (lift A) ≡ lift B , seems to come out of nothing -}
Lift-Der (Conv {Γ = Γ} dA dB dA=) dΓ = ex.Conv (ex.getTy-Der {!!} dΓ) {!Lift!} {!!} {!!}
-- Lift-Der (Conv {Γ = Γ , A} {var last} dj dj₁ dj₂) (dΓ , dA) = ex.Conv (ex.WeakTy (Lift-Der dA dΓ)) (Lift-Der {!!} {!!}) {!!} {!!} 
-- Lift-Der (Conv {Γ = Γ , A} {var (prev x)} dj dj₁ dj₂) dΓ = {!!}
-- Lift-Der (Conv {u = lam A B u} dj dj₁ dj₂) dΓ = ex.Conv {!!} {!!} {!!} {!!}
-- Lift-Der (Conv {u = app A B u u₁} dj dj₁ dj₂) dΓ = ex.Conv {!!} {!!} {!!} {!!}
Lift-Der (ConvEq dj dj₁ dj₂) dΓ = {!!}
Lift-Der UU dΓ = {!!}
Lift-Der UUCong dΓ = {!!}
Lift-Der (El dj) dΓ = {!!}
Lift-Der (ElCong dj) dΓ = {!!}
Lift-Der (Pi dj dj₁) dΓ = {!!}
Lift-Der (PiCong dj dj₁ dj₂) dΓ = {!!}
Lift-Der (Lam dj dj₁ dj₂) dΓ = {!!}
Lift-Der (LamCong dj dj₁ dj₂ dj₃) dΓ = {!!}
Lift-Der (App dj dj₁ dj₂ dj₃) dΓ = {!!}
Lift-Der (AppCong dj dj₁ dj₂ dj₃ dj₄) dΓ = {!!}
Lift-Der (BetaPi dj dj₁ dj₂ dj₃) dΓ = {!!}
Lift-Der (EtaPi dj dj₁ dj₂) dΓ = {!!}
