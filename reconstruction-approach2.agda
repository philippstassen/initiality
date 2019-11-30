{-# OPTIONS --rewriting --prop #-}

open import common renaming (Unit to metaUnit)
open import normal
import ex
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)
open import translation

liftTy : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : TyExpr n) → ex.TyExpr n
liftTm : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : ex.TyExpr n) → (u : TmExpr n) → ex.TmExpr n

liftTy Γ (uu i) = ex.uu i
liftTy Γ (el i v) = ex.el i (liftTm Γ (ex.uu i) v)
liftTy Γ (pi A A₁) = ex.pi (liftTy Γ A ) (liftTy (Γ ex., (liftTy Γ A)) A₁) 
-- liftTy (suc zero) Γ (uu i) <m = ex.uu i
-- liftTy (suc m) Γ (el i v) <m = ex.el i (ex.coerc (ex.getTy (liftCtx Γ) (liftTm m Γ v (suc-ref-< <m))) (ex.uu i) (liftTm (m) Γ v (suc-ref-< <m)))
-- liftTy (suc m) Γ (pi A A₁) <m = ex.pi (liftTy (m) Γ A {!!}) (liftTy m (Γ , A) A₁ {!!})

liftTm Γ C (var x) = ex.coerc (ex.getTy Γ (ex.var x)) C (ex.var x)
liftTm Γ C (lam A B u) = ex.coerc (ex.pi (liftTy Γ A) (liftTy (Γ ex., (liftTy Γ A)) B)) C (ex.lam (liftTy Γ A) (liftTy (Γ ex., (liftTy Γ A)) B) (liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) u))
liftTm Γ C (app A B u u₁) = ex.coerc (ex.substTy (liftTy (Γ ex., liftTy Γ A) B) (liftTm Γ (liftTy Γ A) u₁)) C (ex.app (liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) (liftTm Γ (liftTy Γ (pi A B)) u) (liftTm Γ (liftTy Γ A) u₁))
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

{- morphism lifting needs coercions. Aim: Define lifting that preserves wellformed-ness -}
liftMor : {n m : ℕ} → ex.Ctx n → ex.Ctx m → Mor n m → ex.Mor n m
liftMor Γ Δ ◇ = ex.◇
liftMor Γ (Δ ex., A) (δ , u) =  liftMor Γ Δ δ ex., liftTm Γ (A ex.[ liftMor Γ Δ δ ]Ty) u
-- liftMor δ Γ ex., coerc (ex.getTy Γ (liftTm Γ u)) liftTm Γ u

liftJdg : Judgment → ex.Judgment
liftJdg (Γ ⊢ x) = liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) x
liftJdg (Γ ⊢ x :> x₁) = liftCtx Γ ⊢ₑ liftTm (liftCtx Γ) (liftTy (liftCtx Γ) x₁) x :> liftTy (liftCtx Γ) x₁
liftJdg (Γ ⊢ x == x₁) = liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) x == liftTy (liftCtx Γ) x₁
liftJdg (Γ ⊢ x == x₁ :> x₂) = liftCtx Γ ⊢ₑ (liftTm (liftCtx Γ) (liftTy (liftCtx Γ) x₂) x) ==
                    (liftTm (liftCtx Γ) (liftTy (liftCtx Γ) x₂) x₁) :> liftTy (liftCtx Γ) x₂

{- not sure what type expression to pass to liftTm. Should not really matter I guess, maybe getTy? -}
strip-liftTy : (Γ : ex.Ctx n) → (A : TyExpr n) → || liftTy Γ A ||Ty ≡ A
strip-liftTm : (Γ : ex.Ctx n) → (A : ex.TyExpr n) → (v : TmExpr n) → || liftTm Γ A v ||Tm ≡ v

strip-liftTy Γ (uu i) = refl
strip-liftTy Γ (el i v) = ap (el i) (strip-liftTm Γ (ex.uu i) v)
strip-liftTy Γ (pi A A₁) = ap-pi-Ty (strip-liftTy Γ A) (strip-liftTy (Γ ex., liftTy Γ A) A₁)

strip-liftTm Γ C (var x) = refl
strip-liftTm Γ C (lam A B v) = ap-lam-Tm (strip-liftTy Γ A) (strip-liftTy (Γ ex., liftTy Γ A) B) (strip-liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) v)
strip-liftTm Γ C (app A B v v₁) =  ap-app-Tm (strip-liftTy Γ A) (strip-liftTy (Γ ex., liftTy Γ A) B) (strip-liftTm Γ (liftTy Γ (pi A B)) v) (strip-liftTm Γ (liftTy Γ A) v₁)

strip-liftCtx : (Γ : Ctx n) → || liftCtx Γ ||Ctx ≡ Γ
strip-liftCtx ◇ = refl
strip-liftCtx (Γ , A) = Ctx+= (strip-liftCtx Γ) (strip-liftTy (liftCtx Γ) A)

strip-lift : (j : Judgment) → || liftJdg j || ≡ j
strip-lift (Γ ⊢ x) = ap-jdg-ty (strip-liftCtx Γ) (strip-liftTy (liftCtx Γ) x)
strip-lift (Γ ⊢ x :> x₁) = ap-jdg-tm (strip-liftCtx Γ) (strip-liftTy (liftCtx Γ) x₁) (strip-liftTm (liftCtx Γ) (liftTy (liftCtx Γ) x₁) x)
strip-lift (Γ ⊢ x == x₁) = ap-jdg-tyEq (strip-liftCtx Γ) (strip-liftTy (liftCtx Γ) x) (strip-liftTy (liftCtx Γ) x₁)
strip-lift (Γ ⊢ x == x₁ :> x₂) = ap-jdg-tmEq (strip-liftCtx Γ) (strip-liftTy (liftCtx Γ) x₂) (strip-liftTm (liftCtx Γ) (liftTy (liftCtx Γ) x₂) x) (strip-liftTm (liftCtx Γ) (liftTy (liftCtx Γ) x₂) x₁)

{- weakenVar and ex.weakenVar are the same -}
weakenVar-weakenVar : (k : Fin (suc n)) → (x : Fin n) → weakenVar' k x ≡ ex.weakenVar' k x
weakenVar-weakenVar last x = refl
weakenVar-weakenVar (prev k) last = refl
weakenVar-weakenVar (prev k) (prev x) = ap prev (weakenVar-weakenVar k x)

{- when lifting a weakened type or term, the last type in the context does not matter -}
weakenTm'-liftTm : (k : Fin (suc n)) (Γ : ex.Ctx n) (A : ex.TyExpr (n -F' k)) (B : ex.TyExpr n) (u : TmExpr n) → liftTm (ex.weakenCtx k Γ A) (ex.weakenTy' k B) (weakenTm' k u) ≡ ex.weakenTm' k (liftTm Γ B u)
weakenTy'-liftTy : (k : Fin (suc n)) (Γ : ex.Ctx n) (B : ex.TyExpr (n -F' k)) (A : TyExpr n) → liftTy (ex.weakenCtx k Γ B) (weakenTy' k A) ≡ ex.weakenTy' k (liftTy Γ A)

weakenTy'-liftTy k Γ B (uu i) = refl
weakenTy'-liftTy k Γ B (el i v) = ex.ap-el-Ty refl (weakenTm'-liftTm k Γ B (ex.uu i) v)
weakenTy'-liftTy k Γ B (pi A A₁) rewrite weakenTy'-liftTy k Γ B A | weakenTy'-liftTy (prev k) (Γ ex., (liftTy Γ A)) B A₁ = refl

weakenTm'-liftTm last Γ A C (var x) = refl
weakenTm'-liftTm (prev k) (Γ ex., A₁) A C (var last) = ex.ap-coerc-Tm (! ex.weakenTy-weakenTy) refl refl
weakenTm'-liftTm (prev k) (Γ ex., A₁) A C (var (prev x)) = ex.ap-coerc-Tm {!!} {!!} {!!}
-- ap ex.var (ap prev (weakenVar-weakenVar k x))
weakenTm'-liftTm k Γ A C (lam A₁ B u) rewrite weakenTy'-liftTy k Γ A A₁ |  weakenTy'-liftTy (prev k) (Γ ex., liftTy Γ A₁) A B =  ex.ap-coerc-Tm (ex.ap-pi-Ty refl (refl)) refl (ex.ap-lam-Tm refl refl (weakenTm'-liftTm (prev k) (Γ ex., liftTy Γ A₁) A (liftTy (Γ ex., liftTy Γ A₁) B) u ))
weakenTm'-liftTm k Γ A C (app A₁ B u u₁) rewrite weakenTy'-liftTy k Γ A A₁ | weakenTy'-liftTy (prev k) (Γ ex., liftTy Γ A₁) A B | weakenTm'-liftTm k Γ A (liftTy Γ (pi A₁ B)) u | weakenTm'-liftTm k Γ A (liftTy Γ A₁) u₁ =  ex.ap-coerc-Tm (! ex.weakenTy-substTy) refl (ex.ap-app-Tm refl refl refl refl)

weakenTm-liftTm : (Γ : ex.Ctx n) (A B : ex.TyExpr n) (u : TmExpr n) → liftTm (ex.weakenCtx last Γ A) (ex.weakenTy' last B) (weakenTm' last u) ≡ ex.weakenTm' last (liftTm Γ B u)
weakenTm-liftTm Γ A B u = weakenTm'-liftTm last Γ A B u

weakenTy-liftTy : (Γ : ex.Ctx n) (B : ex.TyExpr n) (A : TyExpr n) → liftTy (ex.weakenCtx last Γ B) (weakenTy' last A) ≡ ex.weakenTy' last (liftTy Γ A)
weakenTy-liftTy Γ B A = weakenTy'-liftTy last Γ B A

weakenMor-liftMor : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : ex.TyExpr n) (δ : Mor n m) → liftMor (Γ ex., A) Δ (weakenMor δ) ≡ ex.weakenMor (liftMor Γ Δ δ)
weakenMor-liftMor Γ ex.◇ A ◇ = refl
weakenMor-liftMor Γ (Δ ex., A₁) A (δ , u) rewrite weakenMor-liftMor Γ Δ A δ | ! (ex.weaken[]Ty A₁ (liftMor Γ Δ δ) last) | weakenTm-liftTm Γ A (A₁ ex.[ liftMor Γ Δ δ ]Ty) u = refl

{- substitution does not commute with lifting, since getTy and substitution do not commute (see syntx explicit, this still is here the problem.  Maybe a similar statement holds judgmentally-}
[]-liftTy : (Γ : ex.Ctx n) (Δ : ex.Ctx m) {A : TyExpr m} (δ : Mor n m) → (liftTy Δ A) ex.[ (liftMor Γ Δ δ) ]Ty ≡ liftTy Γ (A [ δ ]Ty)
-- []-liftVar : (Γ : ex.Ctx n) (Δ : Ctx m) (A : TyExpr m) (var x : TmExpr m) (δ : Mor n m) → (liftVar (liftCtx (Δ , A)) (liftTy Δ A)) (var x)) ex.[ (liftMor Γ Δ δ) ]Tm ≡ liftTm Γ (liftTy Γ (A [ δ ]Ty)) ((var x) [ δ ]Tm)
[]-liftTm : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : TyExpr m) (u : TmExpr m) (δ : Mor n m) → (liftTm Δ (liftTy Δ B) u) ex.[ (liftMor Γ Δ δ) ]Tm ≡ liftTm Γ (liftTy Γ (B [ δ ]Ty)) (u [ δ ]Tm)

[]-liftTy Γ Δ {uu i} δ = refl
[]-liftTy Γ Δ {el i v} δ = ex.ap-el-Ty refl ([]-liftTm Γ Δ (uu i) v δ)
[]-liftTy Γ Δ {pi A A₁} δ rewrite ! (weakenMor-liftMor Γ Δ (liftTy Γ (A [ δ ]Ty)) δ) = {!!}
-- ex.ap-pi-Ty ([]-liftTy Γ Δ δ) ([]-liftTy (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) (weakenMor δ , var last))

-- []-liftVar Γ (Δ , A) (var x) δ = {!!}
[]-liftTm (Γ ex., A₁) (Δ ex., A) B (var last) (δ , var last) = ex.ap-coerc-Tm {!!} {!!} {!!}
[]-liftTm Γ (Δ ex., A) B (var last) (δ , var (prev x)) = {!!}
[]-liftTm Γ (Δ ex., A) B (var last) (δ , lam A₁ B₁ u) = {!!}
[]-liftTm Γ (Δ ex., A) B (var last) (δ , app A₁ B₁ u u₁) = {!!}
[]-liftTm Γ (Δ ex., A) B (var (prev x)) (δ , u) = {!!}
[]-liftTm Γ Δ B (lam A B₁ u) δ = {!!}
[]-liftTm Γ Δ B (app A B₁ u u₁) δ = {!!}

-- []-substTy : {Γ : ex.Ctx n} (A : ex.TyExpr n) (B : TyExpr (suc n)) (u : TmExpr n) → ex.substTy (liftTy (Γ ex., A) B) (ex.coerc (ex.getTy Γ (liftTm Γ u)) A (liftTm Γ u)) ≡ liftTy Γ (substTy B u)
-- []-substTm : {Γ : ex.Ctx n} (A : ex.TyExpr n) (u : TmExpr (suc n)) (u₁ : TmExpr n) → ex.substTm (liftTm (Γ ex., A) u) (ex.coerc (ex.getTy Γ (liftTm Γ u)) A (liftTm Γ u)) ≡ liftTy Γ (substTy B u)
-- []-substTy {Γ = Γ ex., A₁} A (uu i) (var last) = refl
-- []-substTy {Γ = Γ ex., A₁} A (el i v) (var last) = ex.ap-el-Ty refl (ex.ap-coerc-Tm {!!} refl {!!})
-- []-substTy {Γ = Γ ex., A₁} A (pi B B₁) (var last) = {!!}
-- []-substTy {Γ = Γ ex., A₁} A B (var (prev x)) = {!!}
-- []-substTy {Γ = Γ} A B (lam A₁ B₁ u) = {!!}
-- []-substTy {Γ = Γ} A B (app A₁ B₁ u u₁) = {!!}

{- getTy commutes with lifting 
The seemingly superfluous pattern matching is necessary to reduce getTy to its clauses -}
-- getTy-liftTy : {n : ℕ} (Γ : Ctx n) (A : ex.TyExpr n) (u : TmExpr n) → ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) A u) ≡ liftTy (liftCtx Γ) (getTy Γ u)
-- getTy-liftTy (Γ , A) C (var last) = ! (weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) A)
-- getTy-liftTy (Γ , A) C (var (prev x)) = {!!}
-- rewrite getTy-liftTy Γ (var x) = ! (weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) (getTy Γ (var x)))
-- getTy-liftTy ◇ C (lam A B (var x)) = {!!}
-- getTy-liftTy (Γ , A₁) C (lam A B (var x)) = {!!}
-- getTy-liftTy ◇ C (lam A B (lam A₁ B₁ u)) = {!!}
-- getTy-liftTy (Γ , A₂) C (lam A B (lam A₁ B₁ u)) = {!!}
-- getTy-liftTy ◇ C (lam A B (app A₁ B₁ u u₁)) = {!!}
-- getTy-liftTy (Γ , A₂) C (lam A B (app A₁ B₁ u u₁)) = {!!}
-- getTy-liftTy ◇ C (app A B u u₁) = {!!}
-- getTy-liftTy (Γ , A₁) C (app A B u u₁) = {!!}

Lift-Der : {jdg : Judgment} → Derivable (jdg) → ex.Derivable (liftJdg jdg)
Lift-Der (VarLast {Γ = Γ} {A = A} dj) rewrite weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) A = {!!}
-- ex.Conv (ex.WeakTy (Lift-Der dj)) (ex.WeakTy (Lift-Der dj)) (ex.VarLast (Lift-Der dj)) (ex.TyRefl (ex.WeakTy (Lift-Der dj)))
Lift-Der (VarPrev dj dj₁) = {!!}
Lift-Der (VarLastCong dj) = {!!}
Lift-Der (VarPrevCong dj dj₁) = {!!}
Lift-Der (TySymm dj) = {!!}
Lift-Der (TyTran dj dj₁ dj₂) = {!!}
Lift-Der (TmSymm dj) = {!!}
Lift-Der (TmTran dj dj₁ dj₂) = {!!}
Lift-Der (Conv {u = var x} {A} {B} dA dB du dA=) =  ex.Conv (ex.coercTy1 (Lift-Der du)) (Lift-Der dB) (ex.coercTm (Lift-Der du)) (ex.TyTran (Lift-Der dA) (ex.coercEq (Lift-Der du)) (Lift-Der dA=))
Lift-Der (Conv {u = lam A₁ B₁ u} {A} {B} dA dB du dA=) =  ex.Conv (ex.coercTy1 (Lift-Der du)) (Lift-Der dB) (ex.coercTm (Lift-Der du)) (ex.TyTran (Lift-Der dA) (ex.coercEq (Lift-Der du)) (Lift-Der dA=))
Lift-Der (Conv {u = app A₁ B₁ u u₁} {A} {B} dA dB du dA=) =  ex.Conv (ex.coercTy1 (Lift-Der du)) (Lift-Der dB) (ex.coercTm (Lift-Der du)) (ex.TyTran (Lift-Der dA) (ex.coercEq (Lift-Der du)) (Lift-Der dA=))
-- ex.Conv (ex.coercTy1 (Lift-Der du)) (Lift-Der dB) (ex.coercTm (Lift-Der du)) (ex.TyTran (Lift-Der dA) (ex.coercEq (Lift-Der du)) (Lift-Der dA=))
Lift-Der (ConvEq dj dj₁ dj₂) = {!!}
Lift-Der UU = {!!}
Lift-Der UUCong = {!!}
Lift-Der (El dj) = {!!}
Lift-Der (ElCong dj) = {!!}
Lift-Der (Pi dj dj₁) = {!!}
Lift-Der (PiCong dj dj₁ dj₂) = {!!}
Lift-Der (Lam dj dj₁ dj₂) = {!!}
Lift-Der (LamCong dj dj₁ dj₂ dj₃) = {!!}
Lift-Der (App dj dj₁ dj₂ dj₃) = ex.Conv (ex.SubstTy (Lift-Der dj₁) {!!}) {!!}(ex.App (Lift-Der dj) (Lift-Der dj₁) (Lift-Der dj₂) (Lift-Der dj₃)) {!!}
Lift-Der (AppCong dj dj₁ dj₂ dj₃ dj₄) = {!!}
Lift-Der (BetaPi dj dj₁ dj₂ dj₃) = {!!}
Lift-Der (EtaPi dj dj₁ dj₂) = {!!}
