{-# OPTIONS --rewriting --prop --allow-unsolved-metas #-}

open import common renaming (Unit to metaUnit)
open import normal
import ex
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)
open import translation

liftTy : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : TyExpr n) → ex.TyExpr n
liftTm : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : ex.TyExpr n) → (u : TmExpr n) → ex.TmExpr n

liftTy Γ (uu) = ex.uu
liftTy Γ (el v) = ex.el (liftTm Γ (ex.uu) v)
liftTy Γ (pi A A₁) = ex.pi (liftTy Γ A ) (liftTy (Γ ex., (liftTy Γ A)) A₁) 
-- liftTy (suc zero) Γ (uu) <m = ex.uu
-- liftTy (suc m) Γ (el v) <m = ex.el (ex.coerc (ex.getTy (liftCtx Γ) (liftTm m Γ v (suc-ref-< <m))) (ex.uu) (liftTm (m) Γ v (suc-ref-< <m)))
-- liftTy (suc m) Γ (pi A A₁) <m = ex.pi (liftTy (m) Γ A {!!}) (liftTy m (Γ , A) A₁ {!!})

liftTm Γ C (var x) = ex.coerc (ex.getTy Γ (ex.var x)) C (ex.var x)
liftTm Γ C (lam A B u) = ex.coerc (ex.pi (liftTy Γ A) (liftTy (Γ ex., (liftTy Γ A)) B)) C (ex.lam (liftTy Γ A) (liftTy (Γ ex., (liftTy Γ A)) B) (liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) u))
liftTm Γ C (app A B u u₁) = ex.coerc (ex.substTy (liftTy (Γ ex., liftTy Γ A) B) (liftTm Γ (liftTy Γ A) u₁)) C (ex.app (liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) (liftTm Γ (liftTy Γ (pi A B)) u) (liftTm Γ (liftTy Γ A) u₁))


{- Lifting to define liftMorTriv. Only for rewriting!! -}
liftTyRew : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : TyExpr n) → ex.TyExpr n
liftTmRew : {n : ℕ} → (Γ : (ex.Ctx n)) → (u : TmExpr n) → ex.TmExpr n

liftTyRew Γ (uu) = ex.uu
liftTyRew Γ (el v) = ex.el (liftTm Γ (ex.uu) v)
liftTyRew Γ (pi A A₁) = ex.pi (liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) A₁)

liftTmRew Γ (var x) = ex.var x
liftTmRew Γ (lam A B u) = ex.lam (liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) (liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) u) 
liftTmRew Γ (app A B u u₁) = ex.app (liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) (liftTm Γ (liftTy Γ (pi A B)) u) (liftTm Γ (liftTy Γ A) u₁)

-- liftMorRew Γ (δ , u) =  liftMorRew Γ δ ex., liftTmRew Γ u

{- note that liftMorRew is simply not well defined, when Conversion is involved -}

{- This lifting is only allowed to be used, when if a variable, the last rule used was NOT conversion, it is needed to make commutation of substitution strict. -}
liftTyTriv : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : TyExpr n) → ex.TyExpr n
liftTmTriv : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : ex.TyExpr n) → (u : TmExpr n) → ex.TmExpr n

liftTyTriv Γ (uu) = ex.uu
liftTyTriv Γ (el v) = ex.el (liftTm Γ (ex.uu) v)
liftTyTriv Γ (pi A A₁) = ex.pi (liftTy Γ A ) (liftTy (Γ ex., (liftTy Γ A)) A₁) 

liftTmTriv Γ C (var x) = ex.var x
liftTmTriv Γ C u = liftTm Γ C u

liftCtx : {n : ℕ} → (Γ : Ctx n) → ex.Ctx n
liftCtx ◇ = ex.◇
liftCtx (Γ , A) = liftCtx Γ ex., liftTy (liftCtx Γ) A

{- morphism lifting needs coercions. Aim: Define lifting that preserves wellformed-ness -}
liftMor : {n m : ℕ} → ex.Ctx n → ex.Ctx m → Mor n m → ex.Mor n m
liftMor Γ Δ ◇ = ex.◇
liftMor Γ (Δ ex., A) (δ , u) =  liftMor Γ Δ δ ex., liftTm Γ (A ex.[ liftMor Γ Δ δ ]Ty) u

liftJdg : Judgment → ex.Judgment
liftJdg (Γ ⊢ x) = liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) x
liftJdg (Γ ⊢ x :> x₁) = liftCtx Γ ⊢ₑ liftTm (liftCtx Γ) (liftTy (liftCtx Γ) x₁) x :> liftTy (liftCtx Γ) x₁
liftJdg (Γ ⊢ x == x₁) = liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) x == liftTy (liftCtx Γ) x₁
liftJdg (Γ ⊢ x == x₁ :> x₂) = liftCtx Γ ⊢ₑ (liftTm (liftCtx Γ) (liftTy (liftCtx Γ) x₂) x) ==
                    (liftTm (liftCtx Γ) (liftTy (liftCtx Γ) x₂) x₁) :> liftTy (liftCtx Γ) x₂

{- Morphism for rewriting, only thing that happens: all variables are not coerced-}
liftMorRew : {n m : ℕ} → ex.Ctx n → ex.Ctx m → Mor n m → ex.Mor n m
liftMorRew Γ ex.◇ ◇ = ex.◇
liftMorRew Γ (Δ ex., A) (δ , u) = liftMorRew Γ Δ δ ex., liftTmRew Γ u
-- liftMorRew Γ (Δ ex., A) (δ , var x) = liftMorRew Γ Δ δ ex., ex.var x
-- liftMorRew Γ (Δ ex., A) (δ , lam A₁ B u) = liftMorRew Γ Δ δ ex., ex.lam (liftTy Γ A₁) (liftTy (Γ ex., liftTy Γ A₁) B) (liftTm (Γ ex., liftTy Γ A₁) (liftTy (Γ ex., liftTy Γ A₁) B) u)
-- liftMorRew Γ (Δ ex., A) (δ , app A₁ B u u₁) = liftMorRew Γ Δ δ ex., ex.app (liftTy Γ A₁) (liftTy (Γ ex., liftTy Γ A₁) B) (liftTm Γ (liftTy Γ (pi A₁ B)) u) (liftTm Γ (liftTy Γ A₁) u₁)

getLHSRew : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : ex.TyExpr m} {δ : Mor n m} {u : TmExpr n} → ex.getLHS (liftMorRew Γ (Δ ex., A) (δ , u)) ≡ liftMorRew Γ Δ δ
getLHSRew {u = var x} = refl
getLHSRew {u = lam A B u} = refl
getLHSRew {u = app A B u u₁} = refl

liftMorRew-to-liftTy : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (C : ex.TyExpr n) (x : Fin m) (δ : Mor n m) → ex.coerc (ex.getTy Γ ((ex.var x) ex.[ liftMorRew Γ Δ δ ]Tm)) C ((ex.var x) ex.[ liftMorRew Γ Δ δ ]Tm) ≡ liftTm Γ C ((var x) [ δ ]Tm)
liftMorRew-to-liftTy Γ (Δ ex., A) B last (δ , var x) = refl
liftMorRew-to-liftTy Γ (Δ ex., A) B last (δ , lam A₁ B₁ u) = refl
liftMorRew-to-liftTy Γ (Δ ex., A) B last (δ , app A₁ B₁ u u₁) = refl
liftMorRew-to-liftTy Γ (Δ ex., A) B (prev x) (δ , var x₁) = liftMorRew-to-liftTy Γ Δ B x δ
liftMorRew-to-liftTy Γ (Δ ex., A) B (prev x) (δ , lam A₁ B₁ u) = liftMorRew-to-liftTy Γ Δ B x δ
liftMorRew-to-liftTy Γ (Δ ex., A) B (prev x) (δ , app A₁ B₁ u u₁) = liftMorRew-to-liftTy Γ Δ B x δ

{- not sure what type expression to pass to liftTm. Should not really matter I guess, maybe getTy? -}
strip-liftTy : (Γ : ex.Ctx n) → (A : TyExpr n) → || liftTy Γ A ||Ty ≡ A
strip-liftTm : (Γ : ex.Ctx n) → (A : ex.TyExpr n) → (v : TmExpr n) → || liftTm Γ A v ||Tm ≡ v

strip-liftTy Γ (uu) = refl
strip-liftTy Γ (el v) = ap (el) (strip-liftTm Γ (ex.uu) v)
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

weakenTy'-liftTy k Γ B (uu) = refl
weakenTy'-liftTy k Γ B (el v) = ex.ap-el-Ty (weakenTm'-liftTm k Γ B (ex.uu) v)
weakenTy'-liftTy k Γ B (pi A A₁) rewrite weakenTy'-liftTy k Γ B A | weakenTy'-liftTy (prev k) (Γ ex., (liftTy Γ A)) B A₁ = refl

weakenTm'-liftTm last Γ A C (var x) = refl
weakenTm'-liftTm (prev k) (Γ ex., A₁) A C (var last) = ex.ap-coerc-Tm (! ex.weakenTy-weakenTy) refl refl
weakenTm'-liftTm (prev k) (Γ ex., A₁) A C (var (prev x)) = ex.ap-coerc-Tm ((ap (λ z → ex.weakenTy (ex.getTy (ex.weakenCtx k Γ A) (ex.var z))) (weakenVar-weakenVar k x)
                                  ∙ ap (λ z → ex.weakenTy z) (! (ex.weakenTy'-getTy k Γ (ex.var x) A)))
                                  ∙ ! ex.weakenTy-weakenTy) refl (ap (λ z → ex.var (prev z)) (weakenVar-weakenVar k x))
weakenTm'-liftTm k Γ A C (lam A₁ B u) rewrite weakenTy'-liftTy k Γ A A₁ |  weakenTy'-liftTy (prev k) (Γ ex., liftTy Γ A₁) A B =  ex.ap-coerc-Tm (ex.ap-pi-Ty refl (refl)) refl (ex.ap-lam-Tm refl refl (weakenTm'-liftTm (prev k) (Γ ex., liftTy Γ A₁) A (liftTy (Γ ex., liftTy Γ A₁) B) u ))
weakenTm'-liftTm k Γ A C (app A₁ B u u₁) rewrite weakenTy'-liftTy k Γ A A₁ | weakenTy'-liftTy (prev k) (Γ ex., liftTy Γ A₁) A B | weakenTm'-liftTm k Γ A (liftTy Γ (pi A₁ B)) u | weakenTm'-liftTm k Γ A (liftTy Γ A₁) u₁ =  ex.ap-coerc-Tm (! ex.weakenTy-substTy) refl (ex.ap-app-Tm refl refl refl refl)

weakenTm-liftTm : (Γ : ex.Ctx n) (A B : ex.TyExpr n) (u : TmExpr n) → liftTm (ex.weakenCtx last Γ A) (ex.weakenTy' last B) (weakenTm' last u) ≡ ex.weakenTm' last (liftTm Γ B u)
weakenTm-liftTm Γ A B u = weakenTm'-liftTm last Γ A B u

weakenTy-liftTy : (Γ : ex.Ctx n) (B : ex.TyExpr n) (A : TyExpr n) → liftTy (ex.weakenCtx last Γ B) (weakenTy' last A) ≡ ex.weakenTy' last (liftTy Γ A)
weakenTy-liftTy Γ B A = weakenTy'-liftTy last Γ B A

weakenMor-liftMor : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : ex.TyExpr n) (δ : Mor n m) → liftMor (Γ ex., A) Δ (weakenMor δ) ≡ ex.weakenMor (liftMor Γ Δ δ)
weakenMor-liftMor Γ ex.◇ A ◇ = refl
weakenMor-liftMor Γ (Δ ex., A₁) A (δ , u) rewrite weakenMor-liftMor Γ Δ A δ | ! (ex.weaken[]Ty A₁ (liftMor Γ Δ δ) last) | weakenTm-liftTm Γ A (A₁ ex.[ liftMor Γ Δ δ ]Ty) u = refl

weakenMor+-liftMor : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : ex.TyExpr m) (δ : Mor n m) → ex.Derivable (Δ ⊢ₑ A) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → (Γ ex., A ex.[ liftMor Γ Δ δ ]Ty ) ex.⊢ liftMor (Γ ex., A ex.[ liftMor Γ Δ δ ]Ty) (Δ ex., A) (weakenMor+ δ ) == ex.weakenMor+ (liftMor Γ Δ δ) ∷> (Δ ex., A)
weakenMor+-liftMor Γ Δ A δ dA dδ rewrite weakenMor-liftMor Γ Δ (A ex.[ liftMor Γ Δ δ ]Ty) δ | ! (ex.weaken[]Ty A (liftMor Γ Δ δ) last) = ex.WeakMorEq (ex.MorRefl dδ) ex., ex.congTmEqTy ( (ex.weaken[]Ty A (liftMor Γ Δ δ) last)) {!!}
-- (ex.CoercRefl (ex.VarLast (ex.SubstTy dA dδ)))
{- weakening for rewriting Lifting -}

weakenTm'-liftTmRew : (k : Fin (suc n)) (Γ : ex.Ctx n) (A : ex.TyExpr (n -F' k)) (u : TmExpr n) → liftTmRew (ex.weakenCtx k Γ A) (weakenTm' k u) ≡ ex.weakenTm' k (liftTmRew Γ u)
weakenTy'-liftTyRew : (k : Fin (suc n)) (Γ : ex.Ctx n) (B : ex.TyExpr (n -F' k)) (A : TyExpr n) → liftTyRew (ex.weakenCtx k Γ B) (weakenTy' k A) ≡ ex.weakenTy' k (liftTyRew Γ A)

weakenTy'-liftTyRew k Γ B (uu) = refl
weakenTy'-liftTyRew k Γ B (el v) = ex.ap-el-Ty {!!}
-- ex.ap-el-Ty refl
-- (weakenTm'-liftTmRew k Γ B v)
weakenTy'-liftTyRew k Γ B (pi A A₁) rewrite weakenTy'-liftTyRew k Γ B A = {!!}
-- ex.ap-pi-Ty refl ( weakenTy'-liftTyRew (prev k) (Γ ex., (liftTyRew Γ A)) B A₁)
weakenTm'-liftTmRew k Γ B u = {!!}

weakenMor-liftMorRew : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : ex.TyExpr n) (δ : Mor n m) → liftMorRew (Γ ex., A) Δ (weakenMor δ) ≡ ex.weakenMor (liftMorRew Γ Δ δ)
weakenMor-liftMorRew Γ ex.◇ A ◇ = refl
weakenMor-liftMorRew Γ (Δ ex., A) B (δ , var x) = ex.Mor+= (weakenMor-liftMorRew Γ Δ B δ) refl
weakenMor-liftMorRew Γ (Δ ex., A) B (δ , lam A₁ B₁ u) rewrite weakenTy'-liftTy last Γ B A₁ = ex.Mor+= (weakenMor-liftMorRew Γ Δ B δ) (ex.ap-lam-Tm refl (weakenTy'-liftTy (prev last) (Γ ex., liftTy Γ A₁) B B₁) (ap (λ x → liftTm ((Γ ex., B) ex., ex.weakenTy (liftTy Γ A₁)) x (weakenTm' (prev last) u)) (weakenTy'-liftTy (prev last) (Γ ex., liftTy Γ A₁) B B₁)
                       ∙ (weakenTm'-liftTm (prev last) (Γ ex., liftTy Γ A₁) B (liftTy (Γ ex., liftTy Γ A₁) B₁) u)))
weakenMor-liftMorRew Γ (Δ ex., A) B (δ , app A₁ B₁ u u₁) = {!!}
-- ex.Mor+= (weakenMor-liftMorRew Γ A δ) (weakenTm'-liftTmRew last Γ A u)

weakenMor+liftMorRew : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : ex.TyExpr m) (δ : Mor n m) → liftMorRew (Γ ex., A ex.[ liftMorRew Γ Δ δ ]Ty) (Δ ex., A) (weakenMor+ δ) ≡ ex.weakenMor+ (liftMorRew Γ Δ δ)
weakenMor+liftMorRew Γ ex.◇ A ◇ = refl
weakenMor+liftMorRew Γ (Δ ex., A₁) A (δ , u) = ex.Mor+= (weakenMor-liftMorRew Γ (Δ ex., A₁) (A ex.[ liftMorRew Γ (Δ ex., A₁) (δ , u) ]Ty) (δ , u)) refl

coercTy-liftTy : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {B : TyExpr (suc m)} {δ : Mor n m} → ex.Derivable (Δ ⊢ₑ liftTy Δ A) → ex.Derivable ((Δ ex., liftTy Δ A) ⊢ₑ liftTy (Δ ex., liftTy Δ A) B) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → (Γ ex., liftTy Γ (A [ δ ]Ty)) ex.⊢ liftMor (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) (weakenMor+ δ) ∷> (Δ ex., liftTy Δ A) → 
                 ex.Derivable ((Γ ex., (liftTy Δ A ex.[ liftMor Γ Δ δ ]Ty)) ⊢ₑ liftTy (Δ ex., liftTy Δ A) B ex.[ ex.weakenMor+ (liftMor Γ Δ δ) ]Ty == ex.coercTy (liftTy (Γ ex., liftTy Γ (A [ δ ]Ty)) (B [ weakenMor+ δ ]Ty)) (liftTy Γ (A [ δ ]Ty)) (liftTy Δ A ex.[ liftMor Γ Δ δ ]Ty))

coercTy-liftTy dA dB dδ dδ+ = {!ex.SubstTyMorEq dB (ex.WeakMor+ dA dδ)!}
-- ex.Mor+= (ex.Mor+= (weakenMor-liftMorRew Γ A δ) (weakenTm'-liftTmRew last Γ A u)) refl
------
{- get rhs of a context with a dummy for emtpy context -}
pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

getRHSCtx : {n : ℕ} → Ctx n → TyExpr (pred n)
getRHSCtx ◇ = uu
getRHSCtx (Γ , A) = A

{- Only for Rewriting, not well defined. Approach where liftMor is modified -}
[]-liftTyRew : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : TyExpr m) → (δ : Mor n m) → ex.Derivable ( Δ ⊢ₑ liftTy Δ A) → Γ ex.⊢ liftMorRew Γ Δ δ ∷> Δ → (liftTy Δ A) ex.[ liftMorRew Γ Δ δ ]Ty ≡ liftTy Γ (A [ δ ]Ty)

[]-liftTmRew : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → ex.Derivable (Δ ⊢ₑ liftTm Δ B u :> B) → Γ ex.⊢ liftMorRew Γ Δ δ ∷> Δ → (liftTm Δ B u) ex.[ liftMorRew Γ Δ δ ]Tm ≡ liftTm Γ (B ex.[ liftMorRew Γ Δ δ ]Ty) (u [ δ ]Tm)

[]-liftTyRew Γ Δ (uu) δ dA' dδ' = {!!}
[]-liftTyRew Γ Δ (el v) δ dA' dδ' = {!!}
[]-liftTyRew Γ Δ (pi A B) δ (ex.Pi dA dB) dδ' = ex.ap-pi-Ty ([]-liftTyRew Γ Δ A δ dA dδ') ( ap (λ x → liftTy ((Δ ex., liftTy Δ A)) B ex.[ x ]Ty) (! (weakenMor+liftMorRew Γ Δ (liftTy Δ A) δ))
               ∙  ap (λ x → liftTy (Δ ex., liftTy Δ A) B ex.[ liftMorRew (Γ ex., x) Δ (weakenMor δ) ex., ex.var last ]Ty) ([]-liftTyRew Γ Δ A δ dA dδ')
               ∙ []-liftTyRew (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) B (weakenMor+ δ) dB (ex.congMor (ex.Ctx+= refl ([]-liftTyRew Γ Δ A δ dA dδ')) refl ( (! (weakenMor+liftMorRew Γ Δ (liftTy Δ (A)) δ))
                              ∙ ap (λ x → liftMorRew (Γ ex., x) Δ (weakenMor δ) ex., ex.var last) ([]-liftTyRew Γ Δ A δ dA dδ')) ( ex.WeakMor+ dA dδ')))

[]-liftTmRew Γ (ex._,_ {_} Δ A) B (var last) (δ , var x) (ex.Conv {Γ = .(Δ ex., A)} du' du'' du''' du'''') (dδ' ex., x₁) =  ex.ap-coerc-Tm (ex.weakenTyInsert A (liftMorRew Γ Δ δ) (ex.var x) ∙ ! (ex.getTy=Ty x₁)) refl refl
[]-liftTmRew Γ (Δ ex., C) B (var last) (δ , lam A B₁ u) (ex.Conv {Γ = .(Δ ex., C)} dwC dB du dB=) (dδ' ex., x) =  ex.ap-coerc-Tm ((ex.getTy-[]Ty (ex.var last) (dδ' ex., x)) ∙ refl) refl (ex.ap-lam-Tm refl refl refl)
[]-liftTmRew Γ (Δ ex., C) B (var last) (δ , app A B₁ u v) (ex.Conv {Γ = .(Δ ex., C)} dC dB du dB=) (dδ' ex., x) = ex.ap-coerc-Tm ( ex.getTy-[]Ty (ex.var last) (dδ' ex., x)) refl refl

[]-liftTmRew Γ (Δ ex., A) B (var (prev x)) (δ , var y) (ex.Conv {Γ = .(Δ ex., A)} dA dB du dB=) (dδ' ex., dx) =   ex.ap-coerc-Tm (ex.weakenTyInsert (ex.getTy Δ (ex.var x)) (liftMorRew Γ Δ δ) (ex.var y) ∙ ex.getTy-[]Ty (ex.var x) dδ') refl refl
                       ∙ liftMorRew-to-liftTy Γ Δ (B ex.[ liftMorRew Γ Δ δ ex., ex.var y ]Ty) x δ
[]-liftTmRew Γ (Δ ex., A) B (var (prev x)) (δ , lam A₁ B₁ u) (ex.Conv {Γ = .(Δ ex., A)} du' du'' du''' du'''') (dδ' ex., dx) =  ex.ap-coerc-Tm (ex.weakenTyInsert (ex.getTy Δ (ex.var x)) (liftMorRew Γ Δ δ) _ ∙ ex.getTy-[]Ty (ex.var x) dδ') refl refl ∙ liftMorRew-to-liftTy Γ Δ (B ex.[ liftMorRew Γ Δ δ ex., _ ]Ty) x δ
[]-liftTmRew Γ (ex._,_ {_} Δ A) B (var (prev x)) (δ , app A₁ B₁ u u₁) (ex.Conv {Γ = .(Δ ex., A)} du' du'' du''' du'''') (dδ' ex., dx) =  ex.ap-coerc-Tm (ex.weakenTyInsert (ex.getTy Δ (ex.var x)) (liftMorRew Γ Δ δ) _ ∙ ex.getTy-[]Ty (ex.var x) dδ') refl refl ∙ liftMorRew-to-liftTy Γ Δ (B ex.[ liftMorRew Γ Δ δ ex., _ ]Ty) x δ

[]-liftTmRew Γ Δ C (lam A B u) δ (ex.Conv dPi dC (ex.Lam dA dB du) dC=) dδ' = ex.ap-coerc-Tm ([]-liftTyRew Γ Δ (pi A B) δ dPi dδ') refl
             (ex.ap-lam-Tm
               ([]-liftTyRew Γ Δ A δ dA dδ')
               ( ap (λ x → liftTy ((Δ ex., liftTy Δ A)) B ex.[ x ]Ty) (! (weakenMor+liftMorRew Γ Δ (liftTy Δ A) δ))
               ∙  ap (λ x → liftTy (Δ ex., liftTy Δ A) B ex.[ liftMorRew (Γ ex., x) Δ (weakenMor δ) ex., ex.var last ]Ty) ([]-liftTyRew Γ Δ A δ dA dδ')
               ∙ []-liftTyRew (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) B (weakenMor+ δ) dB (ex.congMor (ex.Ctx+= refl ([]-liftTyRew Γ Δ A δ dA dδ')) refl ( (! (weakenMor+liftMorRew Γ Δ (liftTy Δ (A)) δ))
                              ∙ ap (λ x → liftMorRew (Γ ex., x) Δ (weakenMor δ) ex., ex.var last) ([]-liftTyRew Γ Δ A δ dA dδ')) ( ex.WeakMor+ dA dδ')))
               {!!})
[]-liftTmRew Γ Δ B (app A B₁ u u₁) δ du' dδ' = {!!}

{- actual substitution commutes judgmentally-}
-- liftTm Γ (B ex. [liftMorRew Γ Δ δ ]Ty) (u [ δ ]Tm) ≡ liftTmRew Γ 

liftMor-liftMorRew : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → ex.Derivable (Γ ⊢ₑ liftTm Γ (B ex.[ liftMor Γ Δ δ ]Ty) (u [ δ ]Tm) == ex.coerc (B ex.[ liftMorRew Γ Δ δ ]Ty) (B ex.[ liftMor Γ Δ δ ]Ty) (liftTm Γ (B ex.[ liftMorRew Γ Δ δ ]Ty) (u [ δ ]Tm)) :> (B ex.[ liftMor Γ Δ δ ]Ty))

liftMor-liftMorRew Γ Δ B u δ = {!!}

[]-liftTy : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : TyExpr m) → (δ : Mor n m) → ex.Derivable ( Δ ⊢ₑ liftTy Δ A) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → ex.Derivable (Γ ⊢ₑ (liftTy Δ A) ex.[ liftMor Γ Δ δ ]Ty == liftTy Γ (A [ δ ]Ty))

[]-liftTm : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → ex.Derivable (Δ ⊢ₑ liftTm Δ B u :> B) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → ex.Derivable (Γ ⊢ₑ (liftTm Δ B u) ex.[ liftMor Γ Δ δ ]Tm == liftTm Γ (B ex.[ liftMor Γ Δ δ ]Ty) (u [ δ ]Tm) :> B ex.[ liftMor Γ Δ δ ]Ty)

[]-liftTy Γ Δ (uu) δ dA dδ = ex.UUCong
[]-liftTy Γ Δ (el v) δ dA dδ = ex.ElCong {!!}
[]-liftTy Γ Δ (pi A B) δ (ex.Pi dA dB) dδ = ex.PiCong (ex.SubstTy dA dδ) {! ex.SubstTy dA dδ!} (ex.SubstTy dB (ex.WeakMor+ dA dδ)) {!ex.SubstTy dB (ex.WeakMor+ dA dδ)!} ([]-liftTy Γ Δ A δ dA dδ) {!!}

[]-liftTm Γ Δ B (var x) δ (ex.Conv du du₁ du₂ du₃) dδ = {!!}
[]-liftTm Γ Δ B (lam A B₁ u) δ du dδ = {!!}
[]-liftTm Γ Δ B (app A B₁ u u₁) δ du dδ = {!!}

-- []-liftTyRew : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : TyExpr m) → (δ : Mor n m) → ex.Derivable ( Δ ⊢ₑ liftTy Δ A) → Γ ex.⊢ liftMorRew Γ δ ∷> Δ → (liftTy Δ A) ex.[ liftMorRew Γ δ ]Ty ≡ liftTy Γ (A [ δ ]Ty)
-- 
-- []-liftTmRew : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → ex.Derivable (Δ ⊢ₑ liftTm Δ B u :> B) → Γ ex.⊢ liftMorRew Γ δ ∷> Δ → (liftTm Δ B u) ex.[ liftMorRew Γ δ ]Tm ≡ liftTm Γ (B ex.[ liftMorRew Γ δ ]Ty) (u [ δ ]Tm)
-- 
-- []-liftTyRew Γ Δ (uu) δ dA' dδ' = {!!}
-- []-liftTyRew Γ Δ (el v) δ dA' dδ' = {!!}
-- []-liftTyRew Γ Δ (pi A B) δ (ex.Pi dA' dA'') dδ' = ex.ap-pi-Ty ([]-liftTyRew Γ Δ A δ dA' dδ') (ap (λ x → liftTy ((Δ ex., liftTy Δ A)) B ex.[ x ]Ty) (! (weakenMor+liftMorRew Γ (liftTy Γ (A [ δ ]Ty)) δ))
--                        ∙ []-liftTyRew (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) B (weakenMor+ δ) dA'' (ex.congMor (ex.Ctx+= refl ([]-liftTyRew Γ Δ A δ dA' dδ')) refl (! (weakenMor+liftMorRew Γ (liftTy Γ (A [ δ ]Ty)) δ)) ( ex.WeakMor+ dA' dδ')))
-- 
-- []-liftTmRew Γ .(Δ ex., A) B (var last) (δ , var x) (ex.Conv {Γ = (Δ ex., A)} dwA dB du dB=) (dδ' ex., x₁) = ex.ap-coerc-Tm (ex.weakenTyInsert A (liftMorRew Γ δ) (ex.var x) ∙ ! (ex.getTy=Ty Γ (ex.var x) x₁)) refl refl
-- []-liftTmRew Γ .(Δ ex., C) B (var last) (δ , lam A B₁ u) (ex.Conv {Γ = Δ ex., C} dwC dB du dB=) (dδ' ex., x) = ex.ap-coerc-Tm ((ex.getTy-[]Ty Γ (Δ ex., C) (liftMorRew Γ (δ , lam A B₁ u)) (ex.var last) (dδ' ex., x)) ∙ {!!}) refl (ex.ap-lam-Tm {!refl!} {!!} {!!})
-- []-liftTmRew Γ Δ B (var last) (δ , app A B₁ u u₁) du' dδ' = {!!}
-- []-liftTmRew Γ Δ B (var (prev x)) (δ , u) du' dδ' = {!!}
-- []-liftTmRew Γ Δ B (lam A B₁ u) δ du' dδ' = {!!}
-- []-liftTmRew Γ Δ B (app A B₁ u u₁) δ du' dδ' = {!!}

{- Als not valid judgmentally, here the issue is that we cannot assume by induction hyp that B ≡ B' but only B == B'. But then we cannot use ConvEq-}


{- Only for Rewriting, not well defined. Approach where liftTy is modified-}
[]-liftTyTriv : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : TyExpr m) → (δ : Mor n m) → ex.Derivable ( Δ ⊢ₑ liftTy Δ A) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → (liftTy Δ A) ex.[ liftMor Γ Δ δ ]Ty ≡ liftTy Γ (A [ δ ]Ty)

[]-liftTmTriv : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → ex.Derivable (Δ ⊢ₑ liftTmTriv Δ B u :> B) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → (liftTmTriv Δ B u) ex.[ liftMor Γ Δ δ ]Tm ≡ liftTm Γ (B ex.[ liftMor Γ Δ δ ]Ty) (u [ δ ]Tm)

-- []-liftTm : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → ex.Derivable (Δ ⊢ₑ liftTm Δ B u :> B) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → ex.Derivable (Γ ex.⊢ (liftTm Δ B u) ex.[ liftMor Γ Δ δ ]Tm == liftTm Γ (B ex.[ liftMor Γ Δ δ ]Ty) (u [ δ ]Tm) :> B ex.[ liftMor Γ Δ δ ]Ty )

-- []-liftTm : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (u' : ex.TmExpr m) → (δ : Mor n m) (δ' : ex.Mor n m) → ex.Derivable (Δ ⊢ₑ u' :> B) → Γ ex.⊢ δ' ∷> Δ → || Γ ||Ctx ⊢ δ ∷> || Δ ||Ctx → (|| u' ||Tm ≡ u) → || δ' ||Mor ≡ δ → (liftTm Δ B u) ex.[ δ' ]Tm ≡ liftTm Γ (B ex.[ δ' ]Ty) (u [ δ ]Tm)

[]-liftTyTriv Γ Δ (uu) δ dA dδ' = refl
[]-liftTyTriv Γ Δ (el v) δ (ex.El dA) dδ' = {!!}
-- ex.ap-el-Ty refl ([]-liftTmTriv Γ Δ (ex.uu) v δ dA dδ')
[]-liftTyTriv Γ Δ (pi A B) δ dA dδ' = {!!}

[]-liftTmTriv (Γ ex., A₁) (Δ ex., A) .(ex.weakenTy' last A) (var last) (δ , var last) (ex.VarLast du') (dδ' ex., x) = ex.ap-coerc-Tm refl (! (ex.weakenTyInsert A (liftMor (Γ ex., A₁) Δ δ) _)) refl
[]-liftTmTriv (Γ ex., A₁) (Δ ex., A) .(ex.weakenTy' last A) (var last) (δ , var (prev x)) (ex.VarLast du') dδ' = ex.ap-coerc-Tm refl (! (ex.weakenTyInsert A (liftMor (Γ ex., A₁) Δ δ) _)) refl
[]-liftTmTriv Γ (Δ ex., A) .(ex.weakenTy' last A) (var last) (δ , lam A₁ B₁ u) (ex.VarLast du') dδ' = ex.ap-coerc-Tm refl (! (ex.weakenTyInsert A (liftMor Γ Δ δ) _)) refl
[]-liftTmTriv Γ (Δ ex., A) .(ex.weakenTy' last A) (var last) (δ , app A₁ B₁ u u₁) (ex.VarLast du') dδ' = ex.ap-coerc-Tm refl (! (ex.weakenTyInsert A (liftMor Γ Δ δ) _)) refl 
[]-liftTmTriv Γ .(Δ ex., B) .(ex.weakenTy' last _) (var (prev x)) (δ , u) (ex.VarPrev {Γ = Δ} {B = B} {A = A} du' du'') (dδ' ex., x₁) = []-liftTmTriv Γ Δ A (var x) δ du'' dδ' ∙
                                           ! (ap (λ z → (liftTm Γ z (x [ δ ]Var))) (ex.weakenTyInsert A (liftMor Γ Δ δ) _))
-- ex.getTy-[]Ty Γ Δ (liftMor Γ Δ (δ , u)) (ex.var x) dδ'
[]-liftTmTriv Γ Δ B (lam A B₁ u) δ (ex.Conv (ex.Pi dA dB₁) dB du dA=) dδ' = ex.ap-coerc-Tm (ex.ap-pi-Ty ( []-liftTyTriv Γ Δ A δ dA dδ') {! []-liftTyTriv (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) B₁ (weakenMor+ δ) dB₁!}) {!!} {!!}
-- ex.ap-coerc-Tm (ex.ap-pi-Ty ([]-liftTyTriv Γ Δ A δ dA dδ') {![]-liftTyTriv (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTyTriv Δ A) B₁ (weakenMor+ δ) dB₁!}) {!!} {!!}
[]-liftTmTriv Γ Δ B (app A B₁ u u₁) δ du' dδ' = {!!}
-- ex.ap-coerc-Tm (ex.ap-pi-Ty ([]-liftTy Γ ex.◇ A ◇ ex.◇ refl tt tt) ([]-liftTy (Γ ex., liftTy Γ (A [ ◇ ]Ty)) (ex.◇ ex., liftTy ex.◇ A) B₁ (weakenMor+ ◇) (ex.weakenMor+ ex.◇) refl (tt , ex.congTmTy!
--                           ([]-liftTy (Γ ex., liftTy Γ (A [ ◇ ]Ty)) ex.◇ A (weakenMor ◇) (ex.weakenMor ex.◇) refl tt tt ∙
--                           ap (λ z → liftTy (Γ ex., liftTy Γ (A [ ◇ ]Ty)) z) (! (weaken[]Ty A ◇ last)) ∙
--                           weakenTy-liftTy Γ (liftTy Γ (A [ ◇ ]Ty)) (A [ ◇ ]Ty)) (ex.VarLast {!!}))
--                           {!!})) {!!} {!!}
-- []-liftTy : (Γ : ex.Ctx n) (Δ : ex.Ctx m) {A : TyExpr m} (δ : Mor n m) → ex.Derivable (Γ ⊢ₑ (liftTy Δ A) ex.[ (liftMor Γ Δ δ) ]Ty == liftTy Γ (A [ δ ]Ty))

-- []-liftTm : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → (liftTm Δ B u) ex.[ (liftMor Γ Δ δ) ]Tm ≡ liftTm Γ (B ex.[ liftMor Γ Δ δ ]Ty) (u [ δ ]Tm)

-- []-liftTy Γ Δ {uu} δ = refl
-- []-liftTy Γ Δ {el v} δ = ex.ap-el-Ty {!!} {!!}
-- -- ex.ap-el-Ty refl ([]-liftTm Γ Δ (uu) v δ)
-- []-liftTy Γ Δ {pi A A₁} δ rewrite ! (weakenMor-liftMor Γ Δ (liftTy Γ (A [ δ ]Ty)) δ) = {!!}
-- ex.ap-pi-Ty ([]-liftTy Γ Δ δ) ([]-liftTy (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) (weakenMor δ , var last))

-- []-liftTm (Γ ex., A₁) (Δ ex., A) B (var last) (δ , var last) = ex.ap-coerc-Tm {!!} {!!} {!!}
-- []-liftTm Γ (Δ ex., A) B (var last) (δ , var (prev x)) = {!!}
-- []-liftTm Γ (Δ ex., A) B (var last) (δ , lam A₁ B₁ u) = ex.ap-coerc-Tm {!!} {!!} {!!}
-- []-liftTm Γ (Δ ex., A) B (var last) (δ , app A₁ B₁ u u₁) = {!!}

-- []-substTy : {Γ : ex.Ctx n} (A : ex.TyExpr n) (B : TyExpr (suc n)) (u : TmExpr n) → ex.substTy (liftTy (Γ ex., A) B) (ex.coerc (ex.getTy Γ (liftTm Γ u)) A (liftTm Γ u)) ≡ liftTy Γ (substTy B u)
-- []-substTm : {Γ : ex.Ctx n} (A : ex.TyExpr n) (u : TmExpr (suc n)) (u₁ : TmExpr n) → ex.substTm (liftTm (Γ ex., A) u) (ex.coerc (ex.getTy Γ (liftTm Γ u)) A (liftTm Γ u)) ≡ liftTy Γ (substTy B u)
-- []-substTy {Γ = Γ ex., A₁} A (uu) (var last) = refl
-- []-substTy {Γ = Γ ex., A₁} A (el v) (var last) = ex.ap-el-Ty refl (ex.ap-coerc-Tm {!!} refl {!!})
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

idmor-unstrip : {Γ : ex.Ctx n} → ex.⊢ Γ → Γ ex.⊢ liftMor Γ Γ (idMor n) == ex.idMor n ∷> Γ
idMorDerivableLift : {Γ : ex.Ctx n} →  ex.⊢ Γ → (Γ ex.⊢ liftMor Γ Γ (idMor n) ∷> Γ)

idMorDerivableLift {Γ = .ex.◇} ex.tt = ex.tt
idMorDerivableLift {Γ = .(_ ex., _)} ( ex._,_ {Γ = Γ} {A = A} dΓ x)
                  = ex.congMor refl refl (! (weakenMor-liftMor _ _ _ (idMor _))) (ex.WeakMor (idMorDerivableLift dΓ))
               ex., ex.congTm (ex.weaken[]Ty A _ last ∙ ! (ap (λ x → A ex.[ x ]Ty) (weakenMor-liftMor Γ Γ A (idMor _))))
                              (ex.ap-coerc-Tm refl
                                              ((ex.weaken[]Ty A _ last ∙ ! (ap (λ x → A ex.[ x ]Ty) (weakenMor-liftMor Γ Γ A (idMor _)))))
                                              refl)
                              (ex.Conv (ex.WeakTy x) (ex.WeakTy (ex.SubstTy x (idMorDerivableLift dΓ))) (ex.VarLast x) (ex.WeakTyEq (ex.congTyEq (ex.[idMor]Ty A) refl (ex.SubstTyMorEq x (ex.idMorDerivable dΓ) (idMorDerivableLift dΓ) (ex.MorSymm dΓ dΓ (idmor-unstrip dΓ)) (idmor-unstrip dΓ))))) 

-- All these Lemmas need the derivability of liftings to be concluded.
idmor-unstrip {Γ = ex.◇} dΓ = ex.tt
idmor-unstrip {Γ = Γ ex., A} (dΓ ex., x)
                 rewrite ! (! (ex.weaken[]Ty A (ex.idMor _) last) ∙ ap (λ x → ex.weakenTy x) (ex.[idMor]Ty A))
                      = ex.congMorEq refl refl (! (weakenMor-liftMor Γ Γ A (idMor _))) refl (ex.WeakMorEq (idmor-unstrip dΓ)) ex., ex.TmRefl (ex.Conv
                                   (ex.congTy ( ! (ap (λ x → ex.weakenTy x) (ex.[idMor]Ty A)) ∙ (ex.weaken[]Ty A (ex.idMor _) last)) (ex.WeakTy x))
                                   (ex.congTy (((ex.weaken[]Ty A _ last)) ∙ ! (ap (λ x → A ex.[ x ]Ty) (weakenMor-liftMor Γ Γ A (idMor _)))) (ex.WeakTy (ex.SubstTy x (idMorDerivableLift dΓ))))
                                   (ex.congTm (! (ap (λ x → ex.weakenTy x) (ex.[idMor]Ty A)) ∙ (ex.weaken[]Ty A (ex.idMor _) last)) refl (ex.VarLast x))
                                   (ex.congTyEq ( ! (! (ex.weaken[]Ty A (ex.idMor _) last) ∙ ap (λ x → ex.weakenTy x) (ex.[idMor]Ty A)))
                                           (ex.weaken[]Ty A (liftMor Γ Γ (idMor _)) last ∙ ! (ap (λ x → A ex.[ x ]Ty) (weakenMor-liftMor Γ Γ A (idMor _))))
                                           (ex.WeakTyEq (ex.congTyEq (ex.[idMor]Ty A) refl (ex.SubstTyMorEq x (ex.idMorDerivable dΓ) (idMorDerivableLift dΓ) (ex.MorSymm dΓ dΓ (idmor-unstrip dΓ)) (idmor-unstrip dΓ)) ))))
-- ex.congTmEq
--                                   (ex.ap-coerc-Tm (! (ex.weaken[]Ty A (ex.idMor _) last) ∙ ap (λ x → ex.weakenTy x) (ex.[idMor]Ty A)) refl refl)
--                                   refl
--                                   refl

-- {!ex.WeakMor+Eq x (ex.idMorDerivable dΓ) (idmor-unstrip Γ dΓ)!}

unstrip-[]Ty : (Γ : Ctx n) (Δ : Ctx m) (A : TyExpr m) → (δ : Mor n m) → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) (A [ δ ]Ty))
unstrip-[]Ty Γ Δ uu δ dA dδ = ex.UU
unstrip-[]Ty Γ Δ (el v) δ dA dδ = ex.El {!!}
unstrip-[]Ty Γ Δ (pi A B) δ (Pi dA dB) dδ = ex.Pi {!!} {!!}

[]Ty-unstrip : (Γ : Ctx n) (Δ : Ctx m) (A : TyExpr m) → (δ : Mor n m) → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → ex.Derivable (liftCtx Γ ⊢ₑ (liftTy (liftCtx Δ) A) ex.[ liftMor (liftCtx Γ) (liftCtx Δ) δ ]Ty)
[]Ty-unstrip Γ Δ A δ dA dδ = {!SubstTy dA dδ!}

unstrip-[]Tm : (Γ : Ctx n) (Δ : Ctx m) (A : TyExpr m) (u : TmExpr m) → (δ : Mor n m) → Derivable (Δ ⊢ u :> A) → Γ ⊢ δ ∷> Δ → ex.Derivable (liftCtx Γ ⊢ₑ liftTm (liftCtx Γ) (liftTy (liftCtx Γ) (A [ δ ]Ty)) (u [ δ ]Tm) :> liftTy (liftCtx Γ) (A [ δ ]Ty))
unstrip-[]Tm Γ Δ A u δ du dδ = {!!}

[]Ty-lift : (Γ : Ctx n) (Δ : Ctx m) (A : TyExpr m) → (δ : Mor n m) → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → ex.Derivable (liftCtx Γ ⊢ₑ (liftTy (liftCtx Δ) A) ex.[ liftMor (liftCtx Γ) (liftCtx Δ) δ ]Ty == liftTy (liftCtx Γ) (A [ δ ]Ty))

[]Tm-lift : (Γ : Ctx n) (Δ : Ctx m) (B : TyExpr m) (u : TmExpr m) (δ : Mor n m) → Derivable (Δ ⊢ u :> B) → Γ ⊢ δ ∷> Δ
  → ex.Derivable (liftCtx Γ ⊢ₑ (liftTm (liftCtx Δ) (liftTy (liftCtx Δ) B) u) ex.[ liftMor (liftCtx Γ) (liftCtx Δ) δ ]Tm
                     == ex.coerc ((liftTy (liftCtx Δ) B) ex.[ liftMor (liftCtx Γ) (liftCtx Δ) δ ]Ty)
                              (liftTy (liftCtx Γ) (B [ δ ]Ty))
                              (liftTm (liftCtx Γ) ((liftTy (liftCtx Δ) B) ex.[ liftMor (liftCtx Γ) (liftCtx Δ) δ ]Ty) (u [ δ ]Tm)) :> (liftTy (liftCtx Γ) (B [ δ ]Ty)))

[]Ty-lift Γ Δ (uu) δ dA dδ = ex.TyRefl ex.UU
[]Ty-lift Γ Δ (el (var x)) δ dA dδ = ex.ElCong {!!}
[]Ty-lift Γ Δ (el (lam A B v)) δ dA dδ = ex.ElCong {!!}
[]Ty-lift Γ Δ (el (app A B v v₁)) δ dA dδ = ex.ElCong {!!}
[]Ty-lift Γ Δ (pi B B₁) δ dA dδ = {!!}
[]Tm-lift = {!!}

substTy-lift : {n : ℕ} (Γ : Ctx n) (A : TyExpr n) (B : TyExpr (suc n)) → (u : TmExpr n) → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ u :> A) → ⊢ Γ 
  → ex.Derivable (liftCtx Γ ⊢ₑ ex.substTy (liftTy (liftCtx Γ ex., liftTy (liftCtx Γ) A) B) (liftTm (liftCtx Γ) (liftTy (liftCtx Γ) A) u) == liftTy (liftCtx Γ) (substTy B u))

substTm-lift : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {B' : ex.TyExpr (suc n)} {v : TmExpr (suc n)} → {u : TmExpr n} → {u' : ex.TmExpr n} → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ v :> B) → Derivable (Γ ⊢ u :> A) → ⊢ Γ 
  → ex.Derivable (liftCtx Γ ⊢ₑ ex.substTm (liftTm (liftCtx Γ ex., liftTy (liftCtx Γ) A) B' v) (liftTm (liftCtx Γ) (liftTy (liftCtx Γ) A) u) == liftTm (liftCtx Γ) (ex.substTy B' u') (substTm v u) :> ex.substTy B' u')

substTy-lift {n} Γ A .(uu) u dA UU du dΓ = {!!}
substTy-lift {n} Γ A .(el _) u dA (El dB) du dΓ = ex.ElCong {!!}
substTy-lift {n} Γ A .(pi _ _) u dA (Pi dB dB₁) du dΓ = {!!}

substTm-lift = {!!}

-- ex.TyTran
--                                            ([]Ty-unstrip (Γ) (Γ , A) B (idMor n , u) dB (idMorDerivable dΓ , congTmTy! ([idMor]Ty A) (du)))
--                                            {!idmor-unstrip!}
--                                            ([]Ty-lift Γ (Γ , A) B (idMor n , u) dB (idMorDerivable dΓ , congTmTy! ([idMor]Ty A) (du)))

Lift-Der : {jdg : Judgment} → ⊢ snd (getCtx jdg) → Derivable (jdg) → ex.Derivable (liftJdg jdg)
Lift-Der (dΓ , dA) (VarLast {Γ = Γ} {A = A} dj) 
                  rewrite weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) A
                  = ex.Conv
                    (ex.WeakTy (Lift-Der dΓ dj))
                    ( ex.WeakTy (Lift-Der dΓ dj)) ( ex.VarLast (Lift-Der dΓ dj))
                    (ex.TyRefl (ex.WeakTy (Lift-Der dΓ dj)))
Lift-Der (dΓ , dA) (VarPrev {Γ = Γ} {B = B} {A = A} dA dk) 
                     = ex.congTm (! (weakenTy-liftTy (liftCtx Γ) (liftTy (liftCtx Γ) B) A)) (ex.ap-coerc-Tm refl (! (weakenTy-liftTy _ _ _)) refl) (ex.WeakTm (Lift-Der dΓ dk))
Lift-Der (dΓ , dA) (VarLastCong {Γ = Γ} {A = A} dj) =
                      ex.ConvEq (ex.WeakTy (Lift-Der dΓ dj))
                                (ex.TmRefl (ex.VarLast (Lift-Der dΓ dj)))
                                (ex.congTyEq refl (! (weakenTy-liftTy (liftCtx Γ) (liftTy (liftCtx Γ) A) A))
                                (ex.TyRefl (ex.WeakTy (Lift-Der dΓ dj))))
-- ex.getTy (ex.var k) == ex.getTy (ex.var k')
Lift-Der (dΓ , dB) (VarPrevCong {Γ = Γ} {B = B} {A = A} dj dj₁)
         = ex.congTmEq (ex.ap-coerc-Tm refl (! (weakenTy-liftTy _ _ A)) refl)
                       (ex.ap-coerc-Tm refl (! (weakenTy-liftTy _ _ A)) refl)
                       (! (weakenTy-liftTy _ _ A))
                       (ex.WeakTmEq (Lift-Der dΓ dj₁))
Lift-Der dΓ (TySymm dj) = ex.TySymm (Lift-Der dΓ dj)
Lift-Der dΓ (TyTran dj dj₁ dj₂) = {!!}
Lift-Der dΓ (TmSymm dj) = {!!}
Lift-Der dΓ (TmTran dv du= dv=) = ex.TmTran (Lift-Der dΓ dv) (Lift-Der dΓ du=) (Lift-Der dΓ dv=)
Lift-Der dΓ (Conv {u = var x} {A} {B} dA dB du dA=) =  ex.Conv (ex.coercInvTy1 (Lift-Der dΓ du)) (Lift-Der dΓ dB) (ex.coercInvTm (Lift-Der dΓ du)) (ex.TyTran (Lift-Der dΓ dA) (ex.coercInvEq (Lift-Der dΓ du)) (Lift-Der dΓ dA=))
Lift-Der dΓ (Conv {u = lam A₁ B₁ u} {A} {B} dA dB du dA=) =  ex.Conv (ex.coercInvTy1 (Lift-Der dΓ du)) (Lift-Der dΓ dB) (ex.coercInvTm (Lift-Der dΓ du)) (ex.TyTran (Lift-Der dΓ dA) (ex.coercInvEq (Lift-Der dΓ du)) (Lift-Der dΓ dA=))
Lift-Der dΓ (Conv {u = app A₁ B₁ u u₁} {A} {B} dA dB du dA=) =  ex.Conv (ex.coercInvTy1 (Lift-Der dΓ du)) (Lift-Der dΓ dB) (ex.coercInvTm (Lift-Der dΓ du)) (ex.TyTran (Lift-Der dΓ dA) (ex.coercInvEq (Lift-Der dΓ du)) (Lift-Der dΓ dA=))
-- ex.Conv (ex.coercInvTy1 (Lift-Der du)) (Lift-Der dB) (ex.coercInvTm (Lift-Der du)) (ex.TyTran (Lift-Der dA) (ex.coercInvEq (Lift-Der du)) (Lift-Der dA=))
Lift-Der dΓ (ConvEq dj dj₁ dj₂) = {!!}
Lift-Der dΓ UU = ex.UU
Lift-Der dΓ UUCong = ex.UUCong
Lift-Der dΓ (El dv) = ex.El (Lift-Der dΓ dv)
Lift-Der dΓ (ElCong dv=) = ex.ElCong (Lift-Der dΓ dv=)
Lift-Der dΓ (Pi dA dB) = ex.Pi (Lift-Der dΓ dA) (Lift-Der (dΓ , dA) dB)
Lift-Der dΓ (PiCong dA dA= dB=) = ex.PiCong (Lift-Der dΓ dA) {!!} {!!} {!!} {!!} {!!}
Lift-Der dΓ (Lam dj dj₁ dj₂) = ex.Conv {!!} {!!} {!!} {!!}
Lift-Der dΓ (LamCong dj dj₁ dj₂ dj₃) = {!ex.LamCong!}
Lift-Der dΓ (App {Γ = Γ} {A = A} {B = B} {f = f} {a = a} dA dB df da)
                 = ex.Conv (ex.SubstTy (Lift-Der (dΓ , dA) dB) {!idMorDerivable dΓ!})
                           {!!}
                           (ex.App (Lift-Der dΓ dA) (Lift-Der (dΓ , dA) dB) (Lift-Der dΓ df) (Lift-Der dΓ da))
                           (substTy-lift Γ A B a dA dB da dΓ)
Lift-Der dΓ (AppCong dj dj₁ dj₂ dj₃ dj₄) = {!ex.!}
Lift-Der dΓ (BetaPi dj dj₁ dj₂ dj₃) = {!ex.BetaPi!}
Lift-Der dΓ (EtaPi dj dj₁ dj₂) = {!!}
