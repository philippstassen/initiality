{-# OPTIONS --rewriting --prop --allow-unsolved-metas #-}

open import common renaming (Unit to metaUnit)
open import normal
import ex
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)
open import translation
---------
---- The mutual definition of liftTm and liftTm1 makes the induction hypothesis much better readable.
--------
liftTy1 : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : TyExpr n) → ex.TyExpr n
liftTm1 : {n : ℕ} → (Γ : (ex.Ctx n)) → (u : TmExpr n) → ex.TmExpr n
liftTm : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : ex.TyExpr n) → (u : TmExpr n) → ex.TmExpr n

liftTy1 Γ (uu) = ex.uu
liftTy1 Γ (el v) = ex.el (liftTm Γ (ex.uu) v)
liftTy1 Γ (pi A A₁) = ex.pi (liftTy1 Γ A) (liftTy1 (Γ ex., liftTy1 Γ A) A₁)

liftTm1 Γ (var x) = ex.var x
liftTm1 Γ (lam A B u) = ex.lam (liftTy1 Γ A)
                              (liftTy1 (Γ ex., liftTy1 Γ A) B)
                              (liftTm (Γ ex., liftTy1 Γ A) (liftTy1 (Γ ex., liftTy1 Γ A) B) u)
liftTm1 Γ (app A B u u₁) = ex.app (liftTy1 Γ A)
                                  (liftTy1 (Γ ex., liftTy1 Γ A) B)
                                  (liftTm Γ (liftTy1 Γ (pi A B)) u)
                                  (liftTm Γ (liftTy1 Γ A) u₁)

liftTm Γ A u = ex.coerc (ex.getTy Γ (liftTm1 Γ u)) A (liftTm1 Γ u)

liftTy : {n : ℕ} → (Γ : (ex.Ctx n)) → (A : TyExpr n) → ex.TyExpr n

liftTy Γ A = liftTy1 Γ A

-- liftTy Γ (uu) = ex.uu
-- liftTy Γ (el v) = ex.el (liftTm Γ (ex.uu) v)
-- liftTy Γ (pi A A₁) = ex.pi (liftTy Γ A ) (liftTy (Γ ex., (liftTy Γ A)) A₁) 
-- 
-- liftTm Γ C (var x) = ex.coerc (ex.getTy Γ (ex.var x)) C (ex.var x)
-- liftTm Γ C (lam A B u) = ex.coerc (ex.pi (liftTy Γ A) (liftTy (Γ ex., (liftTy Γ A)) B)) C (ex.lam (liftTy Γ A) (liftTy (Γ ex., (liftTy Γ A)) B) (liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) u))
-- liftTm Γ C (app A B u u₁) = ex.coerc (ex.substTy (liftTy (Γ ex., liftTy Γ A) B) (liftTm Γ (liftTy Γ A) u₁)) C (ex.app (liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) (liftTm Γ (liftTy Γ (pi A B)) u) (liftTm Γ (liftTy Γ A) u₁))

-- liftTm1 Γ (lam A B u) = ex.lam (liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) (liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) u)

-- liftMorRew Γ (δ , u) =  liftMorRew Γ δ ex., liftTm1 Γ u

{- note that liftMorRew is simply not well defined, when Conversion is involved -}

{- This lifting is only allowed to be used, when if a variable, the last rule used was NOT conversion, it is needed to make commutation of substitution strict. -}

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
liftMorRew Γ (Δ ex., A) (δ , u) = liftMorRew Γ Δ δ ex., liftTm1 Γ u
-- liftMorRew Γ (Δ ex., A) (δ , var x) = liftMorRew Γ Δ δ ex., ex.var x
-- liftMorRew Γ (Δ ex., A) (δ , lam A₁ B u) = liftMorRew Γ Δ δ ex., ex.lam (liftTy Γ A₁) (liftTy (Γ ex., liftTy Γ A₁) B) (liftTm (Γ ex., liftTy Γ A₁) (liftTy (Γ ex., liftTy Γ A₁) B) u)
-- liftMorRew Γ (Δ ex., A) (δ , app A₁ B u u₁) = liftMorRew Γ Δ δ ex., ex.app (liftTy Γ A₁) (liftTy (Γ ex., liftTy Γ A₁) B) (liftTm Γ (liftTy Γ (pi A₁ B)) u) (liftTm Γ (liftTy Γ A₁) u₁)

getLHSRew : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : ex.TyExpr m} {δ : Mor n m} {u : TmExpr n} → ex.getLHS (liftMorRew Γ (Δ ex., A) (δ , u)) ≡ liftMorRew Γ Δ δ
getLHSRew {u = var x} = refl
getLHSRew {u = lam A B u} = refl
getLHSRew {u = app A B u u₁} = refl

-- liftMorRew-to-liftTy : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (C : ex.TyExpr n) (x : Fin m) (δ : Mor n m) → ex.coerc (ex.getTy Γ ((ex.var x) ex.[ liftMorRew Γ Δ δ ]Tm)) C ((ex.var x) ex.[ liftMorRew Γ Δ δ ]Tm) ≡ liftTm Γ C ((var x) [ δ ]Tm)
-- liftMorRew-to-liftTy Γ (Δ ex., A) B last (δ , var x) = refl
-- liftMorRew-to-liftTy Γ (Δ ex., A) B last (δ , lam A₁ B₁ u) = refl
-- liftMorRew-to-liftTy Γ (Δ ex., A) B last (δ , app A₁ B₁ u u₁) = refl
-- liftMorRew-to-liftTy Γ (Δ ex., A) B (prev x) (δ , var x₁) = liftMorRew-to-liftTy Γ Δ B x δ
-- liftMorRew-to-liftTy Γ (Δ ex., A) B (prev x) (δ , lam A₁ B₁ u) = liftMorRew-to-liftTy Γ Δ B x δ
-- liftMorRew-to-liftTy Γ (Δ ex., A) B (prev x) (δ , app A₁ B₁ u u₁) = liftMorRew-to-liftTy Γ Δ B x δ

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

weakenMor-liftᵈ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : ex.TyExpr n} {δ : Mor n m}
                  → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                  → (Γ ex., A) ex.⊢ liftMor (Γ ex., A) Δ (weakenMor δ) ∷> Δ
weakenMor-liftᵈ dδ = ex.congMor refl refl (! (weakenMor-liftMor _ _ _ _)) (ex.WeakMor dδ)
-- (ex.CoercRefl (ex.VarLast (ex.SubstTy dA dδ)))
{- weakening for rewriting Lifting -}

weakenTm'-liftTm1 : (k : Fin (suc n)) (Γ : ex.Ctx n) (A : ex.TyExpr (n -F' k)) (u : TmExpr n) → liftTm1 (ex.weakenCtx k Γ A) (weakenTm' k u) ≡ ex.weakenTm' k (liftTm1 Γ u)
weakenTy'-liftTy1 : (k : Fin (suc n)) (Γ : ex.Ctx n) (B : ex.TyExpr (n -F' k)) (A : TyExpr n) → liftTy1 (ex.weakenCtx k Γ B) (weakenTy' k A) ≡ ex.weakenTy' k (liftTy1 Γ A)

weakenTy'-liftTy1 k Γ B (uu) = refl
weakenTy'-liftTy1 k Γ B (el v) = ex.ap-el-Ty {!!}
-- ex.ap-el-Ty refl
-- (weakenTm'-liftTm1 k Γ B v)
weakenTy'-liftTy1 k Γ B (pi A A₁) rewrite weakenTy'-liftTy1 k Γ B A = {!!}
-- ex.ap-pi-Ty refl ( weakenTy'-liftTy1 (prev k) (Γ ex., (liftTy1 Γ A)) B A₁)
weakenTm'-liftTm1 k Γ B u = {!!}

-- weakenMor-liftMorRew : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : ex.TyExpr n) (δ : Mor n m) → liftMorRew (Γ ex., A) Δ (weakenMor δ) ≡ ex.weakenMor (liftMorRew Γ Δ δ)
-- weakenMor-liftMorRew Γ ex.◇ A ◇ = refl
-- weakenMor-liftMorRew Γ (Δ ex., A) B (δ , var x) = ex.Mor+= (weakenMor-liftMorRew Γ Δ B δ) refl
-- weakenMor-liftMorRew Γ (Δ ex., A) B (δ , lam A₁ B₁ u) rewrite weakenTy'-liftTy last Γ B A₁ = ex.Mor+= (weakenMor-liftMorRew Γ Δ B δ) (ex.ap-lam-Tm refl (weakenTy'-liftTy (prev last) (Γ ex., liftTy Γ A₁) B B₁) (ap (λ x → liftTm ((Γ ex., B) ex., ex.weakenTy (liftTy Γ A₁)) x (weakenTm' (prev last) u)) (weakenTy'-liftTy (prev last) (Γ ex., liftTy Γ A₁) B B₁)
--                        ∙ (weakenTm'-liftTm (prev last) (Γ ex., liftTy Γ A₁) B (liftTy (Γ ex., liftTy Γ A₁) B₁) u)))
-- weakenMor-liftMorRew Γ (Δ ex., A) B (δ , app A₁ B₁ u u₁) = {!!}
-- -- ex.Mor+= (weakenMor-liftMorRew Γ A δ) (weakenTm'-liftTm1 last Γ A u)
-- 
-- weakenMor+liftMorRew : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : ex.TyExpr m) (δ : Mor n m) → liftMorRew (Γ ex., A ex.[ liftMorRew Γ Δ δ ]Ty) (Δ ex., A) (weakenMor+ δ) ≡ ex.weakenMor+ (liftMorRew Γ Δ δ)
-- weakenMor+liftMorRew Γ ex.◇ A ◇ = refl
-- weakenMor+liftMorRew Γ (Δ ex., A₁) A (δ , u) = ex.Mor+= (weakenMor-liftMorRew Γ (Δ ex., A₁) (A ex.[ liftMorRew Γ (Δ ex., A₁) (δ , u) ]Ty) (δ , u)) refl

coercTy-liftTy : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {B : TyExpr (suc m)} {δ : Mor n m} → ex.Derivable (Δ ⊢ₑ liftTy Δ A) → ex.Derivable ((Δ ex., liftTy Δ A) ⊢ₑ liftTy (Δ ex., liftTy Δ A) B) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → (Γ ex., liftTy Γ (A [ δ ]Ty)) ex.⊢ liftMor (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) (weakenMor+ δ) ∷> (Δ ex., liftTy Δ A) → 
                 ex.Derivable ((Γ ex., (liftTy Δ A ex.[ liftMor Γ Δ δ ]Ty)) ⊢ₑ liftTy (Δ ex., liftTy Δ A) B ex.[ ex.weakenMor+ (liftMor Γ Δ δ) ]Ty == ex.coercTy (liftTy (Γ ex., liftTy Γ (A [ δ ]Ty)) (B [ weakenMor+ δ ]Ty)) (liftTy Γ (A [ δ ]Ty)) (liftTy Δ A ex.[ liftMor Γ Δ δ ]Ty))

coercTy-liftTy dA dB dδ dδ+ = {!ex.SubstTyMorEq dB (ex.WeakMor+ dA dδ)!}
-- ex.Mor+= (ex.Mor+= (weakenMor-liftMorRew Γ A δ) (weakenTm'-liftTm1 last Γ A u)) refl
------
{- get rhs of a context with a dummy for emtpy context -}
pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

getRHSCtx : {n : ℕ} → Ctx n → TyExpr (pred n)
getRHSCtx ◇ = uu
getRHSCtx (Γ , A) = A

--------------------------
------------------ Commutation of substitution in a similar style as Guillaume
--------------------------
[]-liftTy1 : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} → {δ : Mor n m}
             → ex.⊢ Γ → ex.⊢ Δ 
             → ex.Derivable ( Δ ⊢ₑ liftTy1 Δ A)
             → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
             → ex.Derivable (Γ ⊢ₑ liftTy1 Γ (A [ δ ]Ty))

[]-liftTm1 : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {u : TmExpr m} {δ : Mor n m}
             → ex.⊢ Γ → ex.⊢ Δ 
             → ex.Derivable (Δ ⊢ₑ liftTm1 Δ u :> ex.getTy Δ (liftTm1 Δ u))
             → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
             → ex.Derivable (Γ ⊢ₑ liftTm1 Γ (u [ δ ]Tm) :> ex.getTy Γ (liftTm1 Γ (u [ δ ]Tm)))

[]-liftTy1⁼ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} → {δ : Mor n m}
             → ex.⊢ Γ → ex.⊢ Δ 
             → ex.Derivable ( Δ ⊢ₑ liftTy1 Δ A)
             → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
             → ex.Derivable (Γ ⊢ₑ (liftTy1 Δ A) ex.[ liftMor Γ Δ δ ]Ty == liftTy1 Γ (A [ δ ]Ty))

[]-liftTm1⁼ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {u : TmExpr m} {δ : Mor n m}
             → ex.⊢ Γ → ex.⊢ Δ 
             → ex.Derivable (Δ ⊢ₑ liftTm1 Δ u :> ex.getTy Δ (liftTm1 Δ u))
             → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
             → ex.Derivable (Γ ⊢ₑ (liftTm1 Δ u) ex.[ liftMor Γ Δ δ ]Tm ==
                                  ex.coerc (ex.getTy Γ (liftTm1 Γ (u [ δ ]Tm)))
                                           ((ex.getTy Δ (liftTm1 Δ u)) ex.[ liftMor Γ Δ δ ]Ty)
                                           (liftTm1 Γ (u [ δ ]Tm))
                                                                          :> (ex.getTy Δ (liftTm1 Δ u)) ex.[ liftMor Γ Δ δ ]Ty)

[]-liftTm1⁼! : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {u : TmExpr m} {δ : Mor n m}
             → ex.⊢ Γ → ex.⊢ Δ 
             → ex.Derivable (Δ ⊢ₑ liftTm1 Δ u :> ex.getTy Δ (liftTm1 Δ u))
             → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
             → ex.Derivable (Γ ⊢ₑ ex.coerc ((ex.getTy Δ (liftTm1 Δ u)) ex.[ liftMor Γ Δ δ ]Ty)
                                           (ex.getTy Γ (liftTm1 Γ (u [ δ ]Tm)))
                                           ((liftTm1 Δ u) ex.[ liftMor Γ Δ δ ]Tm)
                               ==
                                           (liftTm1 Γ (u [ δ ]Tm))
                               :> (ex.getTy Γ (liftTm1 Γ (u [ δ ]Tm))))

[]-liftTm2 : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {u : TmExpr m} {δ : Mor n m}
             → ex.⊢ Γ → ex.⊢ Δ 
             → ex.Derivable (Δ ⊢ₑ liftTy1 Δ A) 
             → ex.Derivable (Δ ⊢ₑ liftTm Δ (liftTy1 Δ A) u :> liftTy1 Δ A)
             → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
             → ex.Derivable (Γ ⊢ₑ liftTm Γ (liftTy1 Γ (A [ δ ]Ty)) (u [ δ ]Tm) :> (liftTy1 Γ (A [ δ ]Ty)))

[]-liftTm2⁼ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {u : TmExpr m} {δ : Mor n m}
             → ex.⊢ Γ → ex.⊢ Δ 
             → ex.Derivable (Δ ⊢ₑ liftTy1 Δ A) 
             → ex.Derivable (Δ ⊢ₑ liftTm Δ (liftTy1 Δ A) u :> liftTy1 Δ A)
             → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
             → ex.Derivable (Γ ⊢ₑ (liftTm Δ (liftTy1 Δ A) u) ex.[ liftMor Γ Δ δ ]Tm ==
                                  ex.coerc (liftTy1 Γ (A [ δ ]Ty))
                                           (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty)
                                           (liftTm Γ (liftTy1 Γ (A [ δ ]Ty)) (u [ δ ]Tm))
                                                                          :> (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))
---------
--- Equality of Types corrolary
-----------
getTy-[]-lift : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {u : TmExpr m} {δ : Mor n m} → ex.⊢ Γ → ex.⊢ Δ → ex.Derivable (Δ ⊢ₑ liftTm1 Δ u :> ex.getTy Δ (liftTm1 Δ u))
                   → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                   → ex.Derivable (Γ ⊢ₑ ex.getTy Γ (liftTm1 Γ (u [ δ ]Tm)))
getTy-[]-lift {u = u} {δ} dΓ dΔ du dδ = ex.coercInvTy1 (ex.TmEqTm2 dΓ ([]-liftTm1⁼ dΓ dΔ du dδ))
-- getTy-[]-lift {Γ = Γ} {Δ ex., A} (var last) (δ , v) du (dδ ex., dv) = ex.coercInvTy1 dv
-- getTy-[]-lift {Γ = Γ} {Δ ex., A} (var (prev x)) (δ , v) du (dδ ex., dv) = getTy-[]-lift (var x) δ (ex.VarPrevInvTm du) dδ
-- getTy-[]-lift {Γ = Γ} {Δ} (lam A B u) δ du dδ = {!!}
-- getTy-[]-lift {Γ = Γ} {Δ} (app A B u u₁) δ du dδ = {!ex.SubstTy!}

getTy-[]-lift⁼ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {u : TmExpr m} {δ : Mor n m}
                   → ex.⊢ Γ → ex.⊢ Δ 
                   → ex.Derivable (Δ ⊢ₑ liftTm1 Δ u :> ex.getTy Δ (liftTm1 Δ u))
                   → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                   → ex.Derivable (Γ ⊢ₑ ex.getTy Γ (liftTm1 Γ (u [ δ ]Tm)) == (ex.getTy Δ (liftTm1 Δ u)) ex.[ liftMor Γ Δ δ ]Ty)
getTy-[]-lift⁼ {Γ = Γ} {Δ} {u} {δ} dΓ dΔ du dδ = ex.coercInvEq (ex.TmEqTm2 dΓ ([]-liftTm1⁼ dΓ dΔ du dδ))

getTy-[]-lift⁼! : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {u : TmExpr m} {δ : Mor n m}
                   → ex.⊢ Γ → ex.⊢ Δ 
                   → ex.Derivable (Δ ⊢ₑ liftTm1 Δ u :> ex.getTy Δ (liftTm1 Δ u))
                   → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                   → ex.Derivable (Γ ⊢ₑ (ex.getTy Δ (liftTm1 Δ u)) ex.[ liftMor Γ Δ δ ]Ty == ex.getTy Γ (liftTm1 Γ (u [ δ ]Tm)))
getTy-[]-lift⁼! {Γ = Γ} {Δ} {u} {δ} dΓ dΔ du dδ = ex.TySymm (ex.coercInvEq (ex.TmEqTm2 dΓ ([]-liftTm1⁼ dΓ dΔ du dδ)))



--------------
---------- Weakening extension also needs to be simultaneously
-------------

weakenMor+-liftᵈ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {δ : Mor n m}
                 → ex.⊢ Γ → ex.⊢ Δ 
                 → ex.Derivable (Δ ⊢ₑ liftTy1 Δ A) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                 → (Γ ex., liftTy1 Γ (A [ δ ]Ty)) ex.⊢ liftMor (Γ ex., liftTy1 Γ (A [ δ ]Ty)) (Δ ex., liftTy1 Δ A) (weakenMor+ δ) ∷> (Δ ex., liftTy1 Δ A)
weakenMor+-liftᵈ {Γ = Γ} {Δ} {A} {δ} dΓ dΔ dA dδ rewrite weakenMor-liftMor Γ Δ (liftTy1 Γ (A [ δ ]Ty)) δ = ex.WeakMor dδ ex., ex.Conv (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                        (ex.congTy (ex.weaken[]Ty _ _ _) (ex.WeakTy (ex.SubstTy dA dδ)))
                                        (ex.VarLast ([]-liftTy1 dΓ dΔ dA dδ))
                                        (ex.congTyEq refl (ex.weaken[]Ty _ _ _) (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))))

weakenMor+-lift⁼ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {δ : Mor n m}
                   → ex.⊢ Γ → ex.⊢ Δ 
                   → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                   → ex.Derivable (Δ ⊢ₑ liftTy1 Δ A) 
                   → (Γ ex., (liftTy1 Γ (A [ δ ]Ty)))
                       ex.⊢ liftMor (Γ ex., (liftTy1 Γ (A [ δ ]Ty)))
                                     (Δ ex., liftTy1 Δ A)
                                     (weakenMor+ δ )
                       == ex.weakenMor (liftMor Γ Δ δ) ex.,
                                       liftTm
                                          (Γ ex., liftTy1 Γ (A [ δ ]Ty))
                                          (ex.weakenTy ((liftTy1 Δ A) ex.[ liftMor Γ Δ δ ]Ty))
                                          (var last) ∷> (Δ ex., liftTy1 Δ A)

weakenMor+-lift⁼ {Γ = Γ} {Δ} {A} {δ} dΓ dΔ dδ dA rewrite weakenMor-liftMor Γ Δ (liftTy1 Γ (A [ δ ]Ty)) δ | ! (ex.weaken[]Ty (liftTy1 Δ A) (liftMor Γ Δ δ) last) = ex.MorRefl (ex.WeakMor dδ ex., ex.congTmTy (ex.weaken[]Ty _ _ _) (ex.Conv (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ)) (ex.WeakTy (ex.SubstTy dA dδ)) (ex.VarLast ([]-liftTy1 dΓ dΔ dA dδ)) (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))))
--                     ex.WeakMorEq {!!} ex., ex.congTmEqTy ( (ex.weaken[]Ty (liftTy1 Δ A) (liftMor Γ Δ δ) last))
--                            (ex.congTmEq refl (ex.ap-coerc-Tm (ex.weaken[]Ty _ _ _) (ex.weaken[]Ty _ _ _) refl) refl
--                                     (ex.TmSymm (ex.CoercTrans (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ)) (ex.WeakTy (ex.SubstTy dA dδ)) (ex.WeakTy (ex.SubstTy dA dδ)) ([]-liftTm1 {!!} {!!} {!!} {!!}) {!!} {!!})
--                                    ))

getTy-coercTy-lift : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {u : TmExpr (suc m)} {δ : Mor n m}
                 → ex.⊢ Γ → ex.⊢ Δ 
                 → ex.Derivable (Δ ⊢ₑ liftTy1 Δ A) 
                 → ex.Derivable ((Δ ex., liftTy1 Δ A) ⊢ₑ liftTm1 (Δ ex., liftTy1 Δ A) u :> ex.getTy (Δ ex., liftTy1 Δ A) (liftTm1 (Δ ex., liftTy1 Δ A) u))
                 → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                 → ex.Derivable ((Γ ex., (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty)) ⊢ₑ
                             ex.getTy (Δ ex., liftTy1 Δ A) (liftTm1 (Δ ex., liftTy1 Δ A) u) ex.[ ex.weakenMor (liftMor Γ Δ δ) ex., ex.coerc (ex.weakenTy' last (liftTy1 Γ (A [ δ ]Ty)))
                                                                                                                                  (ex.weakenTy' last (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))
                                                                                                                                  (ex.coerc (ex.weakenTy' last (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))
                                                                                                                                            (ex.weakenTy' last (liftTy1 Γ (A [ δ ]Ty)))
                                                                                                                                            (ex.var last)) ]Ty
                               == ex.coercTy (ex.getTy (Γ ex., liftTy1 Γ (A [ δ ]Ty))
                                             (liftTm1 (Γ ex., liftTy1 Γ (A [ δ ]Ty)) (u [ weakenMor+ δ ]Tm)))
                                             (liftTy1 Γ (A [ δ ]Ty)) (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))
getTy-coercTy-lift {n = n} {Γ = Γ} {Δ} {A} {u} {δ} dΓ dΔ dA du dδ = ex.congTyEq (! (ex.ap[]Ty refl
                                                                                           (ex.Mor+= ((ap (ex.weakenMor) (! (ex.[idMor]Mor _)) ∙ ex.weaken[]Mor _ _ _) ∙ ! (ex.weakenMorInsert _ _ _)) refl
                                                                                           ∙ ex.Mor+= (ex.ap[]Mor (! (weakenMor-liftMor _ _ _ δ))
                                                                                                                         refl)
                                                                                                      (ex.ap-coerc-Tm ((ap (ex.weakenTy) (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _) ∙ ! (ex.weakenTyInsert (liftTy1 Γ (A [ δ ]Ty)) _ _))
                                                                                                                      ((ap (ex.weakenTy) (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _) ∙ ! (ex.weakenTyInsert (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty) _ _) ∙ ex.ap[]Ty (ex.weaken[]Ty _ _ _ ∙ ex.ap[]Ty refl (! (weakenMor-liftMor _ _ _ δ) )) refl)
                                                                                                                      refl) )
                                                                                            ∙ ! (ex.[]Ty-assoc (ex.weakenMor' last (ex.idMor _) ex., ex.coerc (ex.weakenTy' last (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty)) (ex.weakenTy' last (liftTy1 Γ (A [ δ ]Ty))) (ex.var last)) _ _) ))
                                                                                refl
                                                                                (ex.CoercTyEq dΓ (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)) (ex.TySymm (getTy-[]-lift⁼ (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) du (weakenMor+-liftᵈ dΓ dΔ dA dδ))))
----------------------
---------- Lemmas for Morphism Extension
----------------------
Mor+-[]-liftTyᵈ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {B : TyExpr (suc m)} {δ : Mor n m}
               → ex.⊢ Γ → ex.⊢ Δ 
               → ex.Derivable ( Δ ⊢ₑ liftTy1 Δ A)
               → ex.Derivable ((Δ ex., liftTy1 Δ A) ⊢ₑ liftTy1 (Δ ex., liftTy1 Δ A) B)
               → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
               → ex.Derivable ((Γ ex., (liftTy1 Γ (A [ δ ]Ty))) ⊢ₑ liftTy1 (Γ ex., liftTy1 Γ (A [ δ ]Ty)) (B [ weakenMor+ δ ]Ty))

Mor+-[]-liftTmᵈ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {u : TmExpr (suc m)} {δ : Mor n m}
                → ex.⊢ Γ → ex.⊢ Δ 
                → ex.Derivable ( Δ ⊢ₑ liftTy1 Δ A)
                → ex.Derivable ((Δ ex., liftTy1 Δ A) ⊢ₑ liftTm1 (Δ ex., liftTy1 Δ A) u :> ex.getTy (Δ ex., liftTy1 Δ A) (liftTm1 (Δ ex., liftTy1 Δ A) u))
                → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                → ex.Derivable ((Γ ex., (liftTy Δ A) ex.[ liftMor Γ Δ δ ]Ty) ⊢ₑ
                   ex.coercTm (liftTm1 (Γ ex., liftTy Γ (A [ δ ]Ty)) (u [ weakenMor+ δ ]Tm))
                              (liftTy1 Γ (A [ δ ]Ty))
                              ((liftTy1 Δ A) ex.[ liftMor Γ Δ δ ]Ty)
                :> ex.coercTy (ex.getTy (Γ ex., liftTy1 Γ (A [ δ ]Ty))
                                        (liftTm1 (Γ ex., liftTy1 Γ (A [ δ ]Ty)) (u [ weakenMor+ δ ]Tm)))
                              (liftTy1 Γ (A [ δ ]Ty))
                              (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))



Mor+-[]-liftTy⁼ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {B : TyExpr (suc m)} {δ : Mor n m}
               → ex.⊢ Γ → ex.⊢ Δ 
               → ex.Derivable ( Δ ⊢ₑ liftTy1 Δ A)
               → ex.Derivable ((Δ ex., liftTy1 Δ A) ⊢ₑ liftTy1 (Δ ex., liftTy1 Δ A) B)
               → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
               → ex.Derivable ((Γ ex., (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty)) ⊢ₑ liftTy1 (Δ ex., liftTy1 Δ A) B ex.[ ex.weakenMor+ (liftMor Γ Δ δ) ]Ty
                            == ex.coercTy (liftTy1 (Γ ex., liftTy1 Γ (A [ δ ]Ty)) (B [ weakenMor+ δ ]Ty))
                                          (liftTy1 Γ (A [ δ ]Ty))
                                          (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))

Mor+-[]-liftTm⁼ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {u : TmExpr (suc m)} {δ : Mor n m}
                → ex.⊢ Γ → ex.⊢ Δ 
                → ex.Derivable ( Δ ⊢ₑ liftTy1 Δ A)
                → ex.Derivable ((Δ ex., liftTy1 Δ A) ⊢ₑ liftTm1 (Δ ex., liftTy1 Δ A) u :> ex.getTy (Δ ex., liftTy1 Δ A) (liftTm1 (Δ ex., liftTy1 Δ A) u))
                → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                → ex.Derivable ((Γ ex., (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty)) ⊢ₑ
                ex.coerc (ex.getTy (Δ ex., liftTy1 Δ A) (liftTm1 (Δ ex., liftTy1 Δ A) u) ex.[ ex.weakenMor+ (liftMor Γ Δ δ) ]Ty)
                         (ex.coercTy (ex.getTy (Γ ex., liftTy1 Γ (A [ δ ]Ty)) (liftTm1 (Γ ex., liftTy1 Γ (A [ δ ]Ty)) (u [ weakenMor+ δ ]Tm))) 
                                     (liftTy1 Γ (A [ δ ]Ty))
                                     (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))
                         ((liftTm1 (Δ ex., liftTy1 Δ A) u) ex.[ ex.weakenMor+ (liftMor Γ Δ δ) ]Tm)
                == ex.coercTm (liftTm1 (Γ ex., liftTy Γ (A [ δ ]Ty)) (u [ weakenMor+ δ ]Tm))
                              (liftTy1 Γ (A [ δ ]Ty))
                              ((liftTy1 Δ A) ex.[ liftMor Γ Δ δ ]Ty)
                :> ex.coercTy (ex.getTy (Γ ex., liftTy1 Γ (A [ δ ]Ty))
                                        (liftTm1 (Γ ex., liftTy1 Γ (A [ δ ]Ty)) (u [ weakenMor+ δ ]Tm)))
                              (liftTy1 Γ (A [ δ ]Ty))
                              (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))

Mor+-[]-liftTyᵈ {Γ = Γ} {Δ} {A} {B} {δ} dΓ dΔ dA dB dδ = []-liftTy1 (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) dB (weakenMor+-liftᵈ dΓ dΔ dA dδ)

Mor+-[]-liftTy⁼ {Γ = Γ} {Δ} {A} {B} {δ} dΓ dΔ dA dB dδ =
                (ex.TyTran
                (ex.congTy (ex.ap[]Ty 
                             (ex.ap[]Ty refl
                               (ex.Mor+= (! (weakenMor-liftMor Γ Δ _ δ))
                                 (ex.ap-coerc-Tm refl
                                    (ex.weaken[]Ty _ _ _ ∙ ex.ap[]Ty refl (! (weakenMor-liftMor Γ Δ _ δ)))
                                    refl)))
                           refl)
                   (ex.CoercTy dΓ ([]-liftTy1 dΓ dΔ dA dδ)
                       (ex.SubstTy dA dδ)
                       (ex.SubstTy dB (ex.WeakMor+coerc dA ([]-liftTy1 dΓ dΔ dA dδ) dδ (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))))
                       (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))))
                   (ex.congTyEq refl
                        (ex.ap[]Ty refl
                          (ex.Mor+= (((ap (λ x → ex.weakenMor x) (! (ex.[idMor]Mor _)) ∙ ex.weaken[]Mor _ _ _) ∙ ! (ex.weakenMorInsert _ _ _)) ∙ (ex.ap[]Mor (! (weakenMor-liftMor Γ Δ _ δ)) refl))
                             (ex.ap-coerc-Tm ((ap (λ x → ex.weakenTy x) (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _) ∙ ! (ex.weakenTyInsert _ _ _))
                               (((((! (ex.weaken[]Ty _ _ _) ∙ ap (λ x → ex.weakenTy x) (! (ex.[idMor]Ty _))) ∙ ex.weaken[]Ty _ _ _) ∙ ! (ex.weakenTyInsert _ _ _)) ∙ (ex.ap[]Ty (ex.weaken[]Ty _ _ _) refl)) ∙ (ex.ap[]Ty (ex.ap[]Ty refl ( (! (weakenMor-liftMor Γ Δ _ δ)))) refl))
                               refl) )
                           ∙ ! (ex.[]Ty-assoc _ _ _))
                        ((ex.SubstTyMorEq1
                            (dΓ ex., ex.SubstTy dA dδ)
                            (dΔ ex., dA)
                            dB
                            (ex.WeakMorEq
                               (ex.MorRefl dδ)
                              ex.,
                               ex.TmTran
                                 {!!}
                                 (ex.TmTran
                                   (ex.Conv
                                     (ex.WeakTy (ex.SubstTy dA dδ))
                                     {!!}
                                     (ex.VarLast {!!})
                                     {!!})
                                   (ex.congTmEq refl
                                      (ex.ap-coerc-Tm refl (ex.weaken[]Ty _ _ _) refl)
                                      (ex.weaken[]Ty _ _ _)
                                      (ex.CoercRefl! (ex.VarLast (ex.SubstTy dA dδ))))
                                   (ex.TmSymm
                                     (ex.CoercTrans
                                       (ex.WeakTy (ex.SubstTy dA dδ))
                                       (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                       (ex.congTy (ex.weaken[]Ty _ _ _) (ex.WeakTy (ex.SubstTy dA dδ)))
                                       (ex.VarLast (ex.SubstTy dA dδ))
                                       (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ))
                                       (ex.congTyEq refl (ex.weaken[]Ty _ _ _) (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))) )))
                                  (ex.TmSymm
                                    (ex.CoercTrans
                                      {!!}
                                      {!!}
                                      {!!}
                                      (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ)) (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ)) (ex.VarLast (ex.SubstTy dA dδ)) (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                      (ex.congTyEq refl (ex.weaken[]Ty _ _ _) (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))))
                                      (ex.congTyEq (ex.weaken[]Ty _ _ _) (ex.weaken[]Ty _ _ _) (ex.TyRefl (ex.WeakTy (ex.SubstTy dA dδ)))) ))))) )
                             (ex.CoercTyEq dΓ (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)) ([]-liftTy1⁼ (dΓ ex., {!!}) (dΔ ex., dA) dB (weakenMor+-liftᵈ dΓ dΔ dA dδ))))

Mor+-[]-liftTmᵈ dΓ dΔ dA du dδ = ex.CoercTm dΓ {!!} {!!} ([]-liftTm1 {!!} (dΔ ex., dA) du {!!}) {!!}

Mor+-[]-liftTm⁼ {n = n} {Γ = Γ} {Δ} {A} {u} {δ} dΓ dΔ dA du dδ =
                ex.TmTran (ex.Conv (ex.SubstTy (ex.SubstTy (ex.TmTy (dΔ ex., dA) du)
                                                           (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                               (ex.WeakMor (ex.idMorDerivable dΓ) ex., ex.congTmTy (ap (ex.weakenTy) (! (ex.[idMor]Ty _)) ∙ (ex.weaken[]Ty _ _ _))
                                                                                                   (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                        (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                        (ex.VarLast (ex.SubstTy dA dδ))
                                                                                                        (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))))
                                   (ex.CoercTy dΓ ([]-liftTy1 dΓ dΔ dA dδ)
                                               (ex.SubstTy dA dδ)
                                               (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ)
                                                              (dΔ ex., dA)
                                                              du
                                                              (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                               (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                   (ex.CoercTm dΓ ([]-liftTy1 dΓ dΔ dA dδ)
                                                  (ex.SubstTy dA dδ)
                                                  (ex.SubstTm du
                                                  (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                  (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                   (ex.CoercTyEq dΓ (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))
                                                 (ex.TySymm (getTy-[]-lift⁼ (dΓ ex., []-liftTy1 dΓ dΔ dA dδ)
                                                                            (dΔ ex., dA)
                                                                            du
                                                                            (weakenMor+-liftᵈ dΓ dΔ dA dδ)))))
                          ((ex.congTmEq refl
                                        BigRewrite
                                        refl
                                       (ex.TmTran (ex.Conv (ex.SubstTy (ex.TmTy (dΔ ex., dA) du)
                                                           (ex.WeakMor dδ ex., ex.congTmTy (ex.weaken[]Ty _ _ _)
                                                                                           (ex.Conv (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                    (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                    (ex.Conv
                                                                                                            (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                            (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                            (ex.VarLast (ex.SubstTy dA dδ))
                                                                                                            (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                                                                                    (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))))))
                                                           (ex.CoercTy dΓ
                                                                       ([]-liftTy1 dΓ dΔ dA dδ)
                                                                       (ex.SubstTy dA dδ)
                                                                       (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) du (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                                       (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                                           (ex.Conv (ex.SubstTy (ex.TmTy (dΔ ex., dA) du) (ex.WeakMor+ dA dδ))
                                                                    (ex.SubstTy (ex.TmTy (dΔ ex., dA) du)
                                                                                (ex.WeakMor dδ ex., ex.congTmTy (ex.weaken[]Ty _ _ _)
                                                                                                    (ex.Conv (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                             (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                             (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                                   (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                                   (ex.VarLast (ex.SubstTy dA dδ))
                                                                                                                   (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                                                                                             (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))))))
                                                                    (ex.SubstTm du (ex.WeakMor+ dA dδ))
                                                                    (getTy-substMor dΓ dΔ dA du dδ))
                                                           (getTy-coercTy-lift dΓ dΔ dA du dδ))
                                                   (ex.TmSymm (ex.CoercTrans (ex.SubstTy (ex.TmTy (dΔ ex., dA) du) (ex.WeakMor+ dA dδ))
                                                                                   (ex.TyEqTy1 (dΓ ex., ex.SubstTy dA dδ) (getTy-coercTy-lift dΓ dΔ dA du dδ))
                                                                                   (ex.TyEqTy2 (dΓ ex., ex.SubstTy dA dδ) (getTy-coercTy-lift dΓ dΔ dA du dδ))
                                                                                   (ex.SubstTm du (ex.WeakMor+ dA dδ))
                                                                                   (getTy-substMor dΓ dΔ dA du dδ)
                                                                                   (getTy-coercTy-lift dΓ dΔ dA du dδ)))
                                                              (ex.ConvEq (ex.SubstTy (ex.TmTy (dΔ ex., dA) du)
                                                                         (ex.WeakMor dδ ex., ex.congTmTy (ex.weaken[]Ty _ _ _)
                                                                                                         (ex.Conv (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                                  (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                                  (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                                     (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                                     (ex.VarLast (ex.SubstTy dA dδ))
                                                                                                                     (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                                                                                                                  ( ex.TySymm (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ))))))
                                                                         (ex.TmSymm (ex.SubstTmMorEq1 (dΓ ex., ex.SubstTy dA dδ)
                                                                                          (dΔ ex., dA)
                                                                                          du
                                                                                          (ex.MorRefl (ex.WeakMor dδ)
                                                                                                  ex., ex.congTmEq refl
                                                                                                             (ex.ap-coerc-Tm (ex.weaken[]Ty _ _ _)
                                                                                                                  (ex.weaken[]Ty _ _ _)
                                                                                                                  refl)
                                                                                                             (ex.weaken[]Ty _ _ _)
                                                                                                             (ex.CoercTrans (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                                            (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                                            (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                                            (ex.VarLast (ex.SubstTy dA dδ))
                                                                                                                            (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ))
                                                                                                                            (ex.TySymm (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))))))
                                                                         (getTy-coercTy-lift dΓ dΔ dA du dδ)))) )
                         (ex.SubstTmEq ([]-liftTm1⁼! (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) du (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                       (ex.WeakMor (ex.idMorDerivable dΓ) ex., ex.congTmTy (ap (ex.weakenTy) (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _)
                                                                                           (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                    (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                    (ex.VarLast (ex.SubstTy dA dδ))
                                                                                                    (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))))
                                    where
                                    getTy-substMor :  {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {u : TmExpr (suc m)} {δ : Mor n m}
                                                     → ex.⊢ Γ → ex.⊢ Δ 
                                                     → ex.Derivable ( Δ ⊢ₑ liftTy1 Δ A)
                                                     → ex.Derivable ((Δ ex., liftTy1 Δ A) ⊢ₑ liftTm1 (Δ ex., liftTy1 Δ A) u :> ex.getTy (Δ ex., liftTy1 Δ A) (liftTm1 (Δ ex., liftTy1 Δ A) u))
                                                     → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ

                                                     → ex.Derivable ((Γ ex., (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty)) ⊢ₑ ex.getTy (Δ ex., liftTy1 Δ A) (liftTm1 (Δ ex., liftTy1 Δ A) u) ex.[ ex.weakenMor+ (liftMor Γ Δ δ) ]Ty
                                                       == (ex.getTy (Δ ex., liftTy1 Δ A) (liftTm1 (Δ ex., liftTy1 Δ A) u)
                                                          ex.[ ex.weakenMor (liftMor Γ Δ δ) ex., ex.coerc (ex.weakenTy' last (liftTy1 Γ (A [ δ ]Ty)))
                                                                                                          (ex.weakenTy' last (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))
                                                                                                          (ex.coerc (ex.weakenTy' last (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))
                                                                                                                    (ex.weakenTy' last (liftTy1 Γ (A [ δ ]Ty)))
                                                                                                                    (ex.var last)) ]Ty))
                                    getTy-substMor {Γ = Γ} {Δ} {A} {u} {δ} dΓ dΔ dA du dδ = ex.SubstTyMorEq1 (dΓ ex., ex.SubstTy dA dδ)
                                                                                                             (dΔ ex., dA)
                                                                                                             (ex.TmTy (dΔ ex., dA) du)
                                                                                                             (ex.MorSymm (dΓ ex., ex.SubstTy dA dδ)
                                                                                                                         (dΔ ex., dA)
                                                                                                                         (ex.WeakMorEq (ex.MorRefl dδ) ex., ex.congTmEq refl
                                                                                                                                                                  (ex.ap-coerc-Tm (ex.weaken[]Ty _ _ _) (ex.weaken[]Ty _ _ _) refl)
                                                                                                                                                                  (ex.weaken[]Ty _ _ _)
                                                                                                                                                                  (ex.CoercTrans (ex.WeakTy (ex.SubstTy dA dδ)) (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ)) (ex.WeakTy (ex.SubstTy dA dδ)) (ex.VarLast (ex.SubstTy dA dδ)) (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)) (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))))))
                                    BigRewrite = (ex.ap-coerc-Tm
                                                      (ex.ap[]Ty refl
                                                                 (ex.Mor+= (((ap (ex.weakenMor) (! (ex.[idMor]Mor _))
                                                                                 ∙ ex.weaken[]Mor _ _ _) ∙ ! (ex.weakenMorInsert _ _ _))
                                                                                 ∙ ex.ap[]Mor (! (weakenMor-liftMor Γ Δ (liftTy Γ (A [ δ ]Ty)) δ)) refl)
                                                                           (ex.ap-coerc-Tm ((ap (ex.weakenTy) (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _) ∙ (! (ex.weakenTyInsert _ _ _)))
                                                                                           (((ap (ex.weakenTy) (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _) ∙ ! (ex.weakenTyInsert _ _ _))
                                                                                                    ∙ ex.ap[]Ty (ex.weaken[]Ty _ _ _ ∙ ex.ap[]Ty refl
                                                                                                                                                 (! (weakenMor-liftMor Γ Δ
                                                                                                                                                                       (liftTy Γ (A [ δ ]Ty)) δ)))
                                                                                                      refl )
                                                                                           refl) )
                                                                      ∙ ! (ex.[]Ty-assoc _ _ _))
                                                      refl
                                                      (ex.ap[]Tm {u = (liftTm1 (Δ ex., liftTy1 Δ A) u)} refl
                                                            (ex.Mor+= ((ap (ex.weakenMor) (! (ex.[idMor]Mor _))
                                                                                 ∙ ex.weaken[]Mor _ _ _)
                                                                        ∙ ! (ex.weakenMorInsert _ _ _))
                                                            refl ∙ ex.Mor+= (ex.ap[]Mor (! (weakenMor-liftMor Γ Δ (liftTy Γ (A [ δ ]Ty)) δ))
                                                                                        refl)
                                                                            (ex.ap-coerc-Tm (ap (ex.weakenTy) (! (ex.[idMor]Ty _))
                                                                                                ∙ ex.weaken[]Ty _ _ _
                                                                                                ∙ ! (ex.weakenTyInsert (liftTy Γ (A [ δ ]Ty)) _ _))
                                                                                            (((ap (ex.weakenTy) (! (ex.[idMor]Ty _))
                                                                                                                ∙ ex.weaken[]Ty _ _ _ )
                                                                                                  ∙ ! ( ex.weakenTyInsert _ _ _) )
                                                                                                  ∙ ex.ap[]Ty (ex.weaken[]Ty _ _ _ ∙ ex.ap[]Ty refl
                                                                                                                                               (! (weakenMor-liftMor Γ Δ (liftTy Γ (A [ δ ]Ty)) δ)))
                                                                                                              refl)
                                                                                            refl))
                                                            ∙ ! (ex.[]Tm-assoc _ _ (liftTm1 (Δ ex., liftTy1 Δ A) u)) ) )


---------------------- []-liftTm1⁼! (dΓ ex., ?) (dΔ ex., dA) du (weakenMor+-liftᵈ dΓ dΔ dA dδ)
----- Proofs
----------------------
[]-liftTy1 {A = uu} {δ} dΓ dΔ dA dδ = ex.UU
[]-liftTy1 {A = (el v)} {δ} dΓ dΔ (ex.El dv) dδ = ex.El
              (ex.Conv
                       (getTy-[]-lift dΓ dΔ (ex.coercInvTm dv) dδ)
                       ex.UU
                       ([]-liftTm1 dΓ dΔ (ex.coercInvTm dv) dδ)
                       (ex.TyTran (ex.SubstTy (ex.coercInvTy1 dv) dδ) (getTy-[]-lift⁼ dΓ dΔ (ex.coercInvTm dv) dδ) (ex.SubstTyEq (ex.coercInvEq dv)dδ)))
[]-liftTy1 {A = (pi A A₁)} {δ} dΓ dΔ (ex.Pi dA dB) dδ = ex.Pi ([]-liftTy1 dΓ dΔ dA dδ) ([]-liftTy1 (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) dB (weakenMor+-liftᵈ dΓ dΔ dA dδ))

[]-liftTm1 {u = var last} {δ , v} dΓ (dΔ ex., dA) (ex.VarLast du) (dδ ex., dv) = ex.coercInvTm dv
[]-liftTm1 {u = var (prev x)} {δ , v} dΓ (dΔ ex., dA) du (dδ ex., dv) = []-liftTm1 dΓ dΔ (ex.VarPrevInvTm du) dδ 
-- again VarPrev is not able to unify
[]-liftTm1 {u = lam A B f} {δ} dΓ dΔ (ex.Lam dA dB df) dδ = ex.Lam ([]-liftTy1 dΓ dΔ dA dδ) (Mor+-[]-liftTyᵈ dΓ dΔ dA dB dδ) ([]-liftTm2 (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) dB df (weakenMor+-liftᵈ dΓ dΔ dA dδ))
[]-liftTm1 {u = app A B u u₁} {δ} dΓ dΔ (ex.App dA dB df da) dδ = ex.App ([]-liftTy1 dΓ dΔ dA dδ) (Mor+-[]-liftTyᵈ dΓ dΔ dA dB dδ) ([]-liftTm2 dΓ dΔ (ex.Pi dA dB) df dδ) ([]-liftTm2 dΓ dΔ dA da dδ)

[]-liftTy1⁼ {Γ = Γ} {Δ} {uu} {δ} dΓ dΔ dA dδ = ex.UUCong
[]-liftTy1⁼ {Γ = Γ} {Δ} {(el v)} {δ} dΓ dΔ (ex.El dA) dδ = ex.ElCong (ex.TmTran
                               (ex.Conv (ex.SubstTy (ex.coercInvTy1 dA) dδ) ex.UU
                                        (ex.Conv (getTy-[]-lift dΓ dΔ (ex.coercInvTm dA) dδ)
                                                 (ex.SubstTy (ex.coercInvTy1 dA) dδ)
                                                 ([]-liftTm1 dΓ dΔ (ex.coercInvTm dA) dδ)
                                                 (getTy-[]-lift⁼ dΓ dΔ (ex.coercInvTm dA) dδ))
                                                 (ex.SubstTyEq (ex.coercInvEq dA) dδ))
                               (ex.ConvEq (ex.SubstTy (ex.coercInvTy1 dA) dδ)
                                          ([]-liftTm1⁼ dΓ dΔ (ex.coercInvTm dA) dδ)
                                          (ex.coercInvEq (ex.SubstTm dA dδ)))
                                          (ex.CoercTrans
                                            (getTy-[]-lift dΓ dΔ (ex.coercInvTm dA) dδ)
                                            (ex.SubstTy (ex.Derivable-getTy (ex.coercInvTm dA) dΔ) dδ)
                                            ex.UU
                                            ([]-liftTm1 dΓ dΔ (ex.coercInvTm dA) dδ)
                                            (getTy-[]-lift⁼ dΓ dΔ (ex.coercInvTm dA) dδ)
                                            (ex.SubstTyEq (ex.coercInvEq dA) dδ)
                                            ))
[]-liftTy1⁼ {Γ = Γ} {Δ} {(pi A B)} {δ} dΓ dΔ (ex.Pi dA dB) dδ =
                    ex.PiCong (ex.SubstTy dA dδ)
                              ([]-liftTy1 dΓ dΔ dA dδ)
                              (ex.SubstTy dB (ex.WeakMor+ dA dδ))
                              ([]-liftTy1 (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) dB (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                              ([]-liftTy1⁼ dΓ dΔ dA dδ)
                              (Mor+-[]-liftTy⁼ dΓ dΔ dA dB dδ)

[]-liftTm1⁼ {Γ = Γ} {Δ ex., A} {var last} {δ , u} dΓ (dΔ ex., x₁) (ex.VarLast du) (dδ ex., x) = ex.congTmEq refl (ex.ap-coerc-Tm refl (! (ex.weakenTyInsert _ _ _)) refl) (! (ex.weakenTyInsert _ _ _)) (ex.TmRefl x)
[]-liftTm1⁼ {Γ = Γ} {(Δ ex., A)} {var (prev x)} {δ , u} dΓ (dΔ ex., dA) du (dδ ex., x₁) = ex.congTmEq refl (ex.ap-coerc-Tm refl (! (ex.weakenTyInsert _ _ _)) refl) (! (ex.weakenTyInsert  _ _ _)) ([]-liftTm1⁼ dΓ dΔ (ex.VarPrevInvTm du) dδ)
-- here again agda cannot pattern match on du (I do not understand why).
-- I am surprised that Agda lets me apply the induction hypothesis on ex.VarPrevInvTm without termination checking failing.
[]-liftTm1⁼ {Γ = Γ} {Δ} {lam A B u} {δ} dΓ dΔ (ex.Lam dA dB df) dδ =
            ex.LamCong
               {!!}
               {!!}
               {!!}
               {!!}
               {!!}
               {!!}
               {!!}
               {!!}
               (ex.TmTran (ex.Conv (ex.CoercTy dΓ ([]-liftTy1 dΓ dΔ dA dδ)
                                         (ex.SubstTy dA dδ)
                                         (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                         {!!})
                              {!!}
                              (Mor+-[]-liftTmᵈ {!!} {!!} {!!} {!!} {!!})
                              (ex.TySymm {! Mor+-[]-liftTy⁼ dΓ dΔ dA ? dδ!}))
                   (ex.TmTran (ex.Conv {!!}
                                  {!!}
                                  (ex.Conv (ex.SubstTy (ex.coercInvTy1 df) (ex.WeakMor+ dA dδ)) (ex.CoercTy dΓ
                                                      {!!}
                                                      {!!}
                                                      (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                      {!!})
                                           (ex.SubstTm (ex.coercInvTm df) (ex.WeakMor+ dA dδ))
                                           {!This one needs an extra function!})
                                  (ex.TySymm {!!}))
                       (ex.TmSymm (ex.CoercTrans {!!} {!!} {!!} {!!} {!!} (ex.TySymm {!!})))
                       (ex.ConvEq (ex.CoercTy dΓ
                                       ([]-liftTy1 dΓ dΔ dA dδ)
                                       (ex.SubstTy dA dδ)
                                       (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                       {!!})
                            (Mor+-[]-liftTm⁼ dΓ dΔ dA (ex.coercInvTm df) dδ)
                            (ex.TySymm {!!})))
                   (ex.TmSymm (ex.CoercTrans
                                     (ex.SubstTy (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                 (ex.WeakMor (ex.idMorDerivable dΓ) ex., ex.congTmTy (ap (ex.weakenTy) (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _) (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ)) (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ)) (ex.VarLast (ex.SubstTy dA dδ)) (ex.WeakTyEq {!!}))))
                                     {!!}
                                     {!!}
                                     (ex.CoercTm dΓ ([]-liftTy1 dΓ dΔ dA dδ) (ex.SubstTy dA dδ) ([]-liftTm1 (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ)) {!!})
                                     (ex.CoercTyEq dΓ (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)) {!ex.coercInvEq df!})
                                     (ex.TySymm (Mor+-[]-liftTy⁼ dΓ dΔ dA dB dδ)))))
[]-liftTm1⁼ {Γ = Γ} {Δ} {app A B f a} {δ} dΓ dΔ (ex.App dA dB df da) dδ =
     ex.congTmEq refl (ex.ap-coerc-Tm refl (! (ex.[]Ty-substTy {B = liftTy1 (Δ ex., liftTy1 Δ A) B} {δ = liftMor Γ Δ δ})) refl) (! (ex.[]Ty-substTy {B = liftTy1 (Δ ex., liftTy1 Δ A) B} {δ = liftMor Γ Δ δ}))
       (ex.AppCong
          (ex.SubstTy dA dδ)
          ([]-liftTy1 dΓ dΔ dA dδ)
          (ex.SubstTy dB (ex.WeakMor+ dA dδ ))
          (Mor+-[]-liftTyᵈ dΓ dΔ dA dB dδ)
          (ex.SubstTm df dδ)
          ([]-liftTm2 dΓ dΔ (ex.Pi dA dB) df dδ)
          (ex.SubstTm da dδ)
          ([]-liftTm2 dΓ dΔ dA da dδ)
          ([]-liftTy1⁼ dΓ dΔ dA dδ)
          (Mor+-[]-liftTy⁼ dΓ dΔ dA dB dδ)
          ([]-liftTm2⁼ dΓ dΔ (ex.Pi dA dB) df dδ)
          ([]-liftTm2⁼ dΓ dΔ dA da dδ))


[]-liftTm1⁼! dΓ dΔ du dδ = {!!}
-----------------
----- As a corollary we get the full commutation also with outermost coercion
----------------
[]-liftTm2 dΓ dΔ dA du dδ = ex.Conv (getTy-[]-lift dΓ dΔ (ex.coercInvTm du) dδ)
                                    ([]-liftTy1 dΓ dΔ dA dδ)
                                    ([]-liftTm1 dΓ dΔ (ex.coercInvTm du) dδ)
                                    (ex.TyTran
                                         (ex.SubstTy dA dδ)
                                         (ex.TyTran (ex.SubstTy (ex.coercInvTy1 du) dδ)
                                             (getTy-[]-lift⁼ dΓ dΔ (ex.coercInvTm du) dδ)
                                             (ex.SubstTyEq (ex.coercInvEq du) dδ))
                                             ([]-liftTy1⁼ dΓ dΔ (ex.coercInvTy2 du) dδ))

[]-liftTm2⁼ dΓ dΔ dA du dδ = {!!}

------------------------------------------------------------------------
-- []-liftTy1⁼ Γ Δ (uu) δ dA' dδ' = {!!}
-- []-liftTy1⁼ Γ Δ (el v) δ dA' dδ' = {!!}
-- []-liftTy1⁼ Γ Δ (pi A B) δ (ex.Pi dA dB) dδ' = ex.ap-pi-Ty ([]-liftTy1⁼ Γ Δ A δ dA dδ') ( ap (λ x → liftTy ((Δ ex., liftTy Δ A)) B ex.[ x ]Ty) (! (weakenMor+liftMorRew Γ Δ (liftTy Δ A) δ))
--                ∙  ap (λ x → liftTy (Δ ex., liftTy Δ A) B ex.[ liftMorRew (Γ ex., x) Δ (weakenMor δ) ex., ex.var last ]Ty) ([]-liftTy1⁼ Γ Δ A δ dA dδ')
--                ∙ []-liftTy1⁼ (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) B (weakenMor+ δ) dB (ex.congMor (ex.Ctx+= refl ([]-liftTy1⁼ Γ Δ A δ dA dδ')) refl ( (! (weakenMor+liftMorRew Γ Δ (liftTy Δ (A)) δ))
--                               ∙ ap (λ x → liftMorRew (Γ ex., x) Δ (weakenMor δ) ex., ex.var last) ([]-liftTy1⁼ Γ Δ A δ dA dδ')) ( ex.WeakMor+ dA dδ')))
-- 
-- []-liftTm1⁼ Γ (ex._,_ {_} Δ A) B (var last) (δ , var x) (ex.Conv {Γ = .(Δ ex., A)} du' du'' du''' du'''') (dδ' ex., x₁) =  ex.ap-coerc-Tm (ex.weakenTyInsert A (liftMorRew Γ Δ δ) (ex.var x) ∙ ! (ex.getTy=Ty x₁)) refl refl
-- []-liftTm1⁼ Γ (Δ ex., C) B (var last) (δ , lam A B₁ u) (ex.Conv {Γ = .(Δ ex., C)} dwC dB du dB=) (dδ' ex., x) =  ex.ap-coerc-Tm ((ex.getTy-[]Ty (ex.var last) (dδ' ex., x)) ∙ refl) refl (ex.ap-lam-Tm refl refl refl)
-- []-liftTm1⁼ Γ (Δ ex., C) B (var last) (δ , app A B₁ u v) (ex.Conv {Γ = .(Δ ex., C)} dC dB du dB=) (dδ' ex., x) = ex.ap-coerc-Tm ( ex.getTy-[]Ty (ex.var last) (dδ' ex., x)) refl refl
-- 
-- []-liftTm1⁼ Γ (Δ ex., A) B (var (prev x)) (δ , var y) (ex.Conv {Γ = .(Δ ex., A)} dA dB du dB=) (dδ' ex., dx) =   ex.ap-coerc-Tm (ex.weakenTyInsert (ex.getTy Δ (ex.var x)) (liftMorRew Γ Δ δ) (ex.var y) ∙ ex.getTy-[]Ty (ex.var x) dδ') refl refl
--                        ∙ liftMorRew-to-liftTy Γ Δ (B ex.[ liftMorRew Γ Δ δ ex., ex.var y ]Ty) x δ
-- []-liftTm1⁼ Γ (Δ ex., A) B (var (prev x)) (δ , lam A₁ B₁ u) (ex.Conv {Γ = .(Δ ex., A)} du' du'' du''' du'''') (dδ' ex., dx) =  ex.ap-coerc-Tm (ex.weakenTyInsert (ex.getTy Δ (ex.var x)) (liftMorRew Γ Δ δ) _ ∙ ex.getTy-[]Ty (ex.var x) dδ') refl refl ∙ liftMorRew-to-liftTy Γ Δ (B ex.[ liftMorRew Γ Δ δ ex., _ ]Ty) x δ
-- []-liftTm1⁼ Γ (ex._,_ {_} Δ A) B (var (prev x)) (δ , app A₁ B₁ u u₁) (ex.Conv {Γ = .(Δ ex., A)} du' du'' du''' du'''') (dδ' ex., dx) =  ex.ap-coerc-Tm (ex.weakenTyInsert (ex.getTy Δ (ex.var x)) (liftMorRew Γ Δ δ) _ ∙ ex.getTy-[]Ty (ex.var x) dδ') refl refl ∙ liftMorRew-to-liftTy Γ Δ (B ex.[ liftMorRew Γ Δ δ ex., _ ]Ty) x δ
-- 
-- []-liftTm1⁼ Γ Δ C (lam A B u) δ (ex.Conv dPi dC (ex.Lam dA dB du) dC=) dδ' = ex.ap-coerc-Tm ([]-liftTy1⁼ Γ Δ (pi A B) δ dPi dδ') refl
--              (ex.ap-lam-Tm
--                ([]-liftTy1⁼ Γ Δ A δ dA dδ')
--                ( ap (λ x → liftTy ((Δ ex., liftTy Δ A)) B ex.[ x ]Ty) (! (weakenMor+liftMorRew Γ Δ (liftTy Δ A) δ))
--                ∙  ap (λ x → liftTy (Δ ex., liftTy Δ A) B ex.[ liftMorRew (Γ ex., x) Δ (weakenMor δ) ex., ex.var last ]Ty) ([]-liftTy1⁼ Γ Δ A δ dA dδ')
--                ∙ []-liftTy1⁼ (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) B (weakenMor+ δ) dB (ex.congMor (ex.Ctx+= refl ([]-liftTy1⁼ Γ Δ A δ dA dδ')) refl ( (! (weakenMor+liftMorRew Γ Δ (liftTy Δ (A)) δ))
--                               ∙ ap (λ x → liftMorRew (Γ ex., x) Δ (weakenMor δ) ex., ex.var last) ([]-liftTy1⁼ Γ Δ A δ dA dδ')) ( ex.WeakMor+ dA dδ')))
--                {!!})
-- []-liftTm1⁼ Γ Δ B (app A B₁ u u₁) δ du' dδ' = {!!}

{- actual substitution commutes judgmentally-}
-- liftTm Γ (B ex. [liftMorRew Γ Δ δ ]Ty) (u [ δ ]Tm) ≡ liftTm1 Γ 

-- liftMor-liftMorRew : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → ex.Derivable (Γ ⊢ₑ liftTm Γ (B ex.[ liftMor Γ Δ δ ]Ty) (u [ δ ]Tm) == ex.coerc (B ex.[ liftMorRew Γ Δ δ ]Ty) (B ex.[ liftMor Γ Δ δ ]Ty) (liftTm Γ (B ex.[ liftMorRew Γ Δ δ ]Ty) (u [ δ ]Tm)) :> (B ex.[ liftMor Γ Δ δ ]Ty))
-- 
-- liftMor-liftMorRew Γ Δ B u δ = {!!}

[]-liftTy : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : TyExpr m) → (δ : Mor n m) → ex.Derivable ( Δ ⊢ₑ liftTy Δ A) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → ex.Derivable (Γ ⊢ₑ (liftTy Δ A) ex.[ liftMor Γ Δ δ ]Ty == liftTy Γ (A [ δ ]Ty))

[]-liftTm : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → ex.Derivable (Δ ⊢ₑ liftTm Δ B u :> B) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → ex.Derivable (Γ ⊢ₑ (liftTm Δ B u) ex.[ liftMor Γ Δ δ ]Tm == liftTm Γ (B ex.[ liftMor Γ Δ δ ]Ty) (u [ δ ]Tm) :> B ex.[ liftMor Γ Δ δ ]Ty)

[]-liftTy Γ Δ (uu) δ dA dδ = ex.UUCong
[]-liftTy Γ Δ (el v) δ dA dδ = ex.ElCong {!!}
[]-liftTy Γ Δ (pi A B) δ (ex.Pi dA dB) dδ = ex.PiCong (ex.SubstTy dA dδ) {! ex.SubstTy dA dδ!} (ex.SubstTy dB (ex.WeakMor+ dA dδ)) {!ex.SubstTy dB (ex.WeakMor+ dA dδ)!} ([]-liftTy Γ Δ A δ dA dδ) {!!}

[]-liftTm Γ Δ B (var x) δ (ex.Conv du du₁ du₂ du₃) dδ = {!!}
[]-liftTm Γ Δ B (lam A B₁ u) δ du dδ = {!!}
[]-liftTm Γ Δ B (app A B₁ u u₁) δ du dδ = {!!}

-- []-liftTy1⁼ : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : TyExpr m) → (δ : Mor n m) → ex.Derivable ( Δ ⊢ₑ liftTy Δ A) → Γ ex.⊢ liftMorRew Γ δ ∷> Δ → (liftTy Δ A) ex.[ liftMorRew Γ δ ]Ty ≡ liftTy Γ (A [ δ ]Ty)
-- 
-- []-liftTm1⁼ : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → ex.Derivable (Δ ⊢ₑ liftTm Δ B u :> B) → Γ ex.⊢ liftMorRew Γ δ ∷> Δ → (liftTm Δ B u) ex.[ liftMorRew Γ δ ]Tm ≡ liftTm Γ (B ex.[ liftMorRew Γ δ ]Ty) (u [ δ ]Tm)
-- 
-- []-liftTy1⁼ Γ Δ (uu) δ dA' dδ' = {!!}
-- []-liftTy1⁼ Γ Δ (el v) δ dA' dδ' = {!!}
-- []-liftTy1⁼ Γ Δ (pi A B) δ (ex.Pi dA' dA'') dδ' = ex.ap-pi-Ty ([]-liftTy1⁼ Γ Δ A δ dA' dδ') (ap (λ x → liftTy ((Δ ex., liftTy Δ A)) B ex.[ x ]Ty) (! (weakenMor+liftMorRew Γ (liftTy Γ (A [ δ ]Ty)) δ))
--                        ∙ []-liftTy1⁼ (Γ ex., liftTy Γ (A [ δ ]Ty)) (Δ ex., liftTy Δ A) B (weakenMor+ δ) dA'' (ex.congMor (ex.Ctx+= refl ([]-liftTy1⁼ Γ Δ A δ dA' dδ')) refl (! (weakenMor+liftMorRew Γ (liftTy Γ (A [ δ ]Ty)) δ)) ( ex.WeakMor+ dA' dδ')))
-- 
-- []-liftTm1⁼ Γ .(Δ ex., A) B (var last) (δ , var x) (ex.Conv {Γ = (Δ ex., A)} dwA dB du dB=) (dδ' ex., x₁) = ex.ap-coerc-Tm (ex.weakenTyInsert A (liftMorRew Γ δ) (ex.var x) ∙ ! (ex.getTy=Ty Γ (ex.var x) x₁)) refl refl
-- []-liftTm1⁼ Γ .(Δ ex., C) B (var last) (δ , lam A B₁ u) (ex.Conv {Γ = Δ ex., C} dwC dB du dB=) (dδ' ex., x) = ex.ap-coerc-Tm ((ex.getTy-[]Ty Γ (Δ ex., C) (liftMorRew Γ (δ , lam A B₁ u)) (ex.var last) (dδ' ex., x)) ∙ {!!}) refl (ex.ap-lam-Tm {!refl!} {!!} {!!})
-- []-liftTm1⁼ Γ Δ B (var last) (δ , app A B₁ u u₁) du' dδ' = {!!}
-- []-liftTm1⁼ Γ Δ B (var (prev x)) (δ , u) du' dδ' = {!!}
-- []-liftTm1⁼ Γ Δ B (lam A B₁ u) δ du' dδ' = {!!}
-- []-liftTm1⁼ Γ Δ B (app A B₁ u u₁) δ du' dδ' = {!!}

-- []-liftTm : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (δ : Mor n m) → ex.Derivable (Δ ⊢ₑ liftTm Δ B u :> B) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → ex.Derivable (Γ ex.⊢ (liftTm Δ B u) ex.[ liftMor Γ Δ δ ]Tm == liftTm Γ (B ex.[ liftMor Γ Δ δ ]Ty) (u [ δ ]Tm) :> B ex.[ liftMor Γ Δ δ ]Ty )

-- []-liftTm : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (B : ex.TyExpr m) (u : TmExpr m) (u' : ex.TmExpr m) → (δ : Mor n m) (δ' : ex.Mor n m) → ex.Derivable (Δ ⊢ₑ u' :> B) → Γ ex.⊢ δ' ∷> Δ → || Γ ||Ctx ⊢ δ ∷> || Δ ||Ctx → (|| u' ||Tm ≡ u) → || δ' ||Mor ≡ δ → (liftTm Δ B u) ex.[ δ' ]Tm ≡ liftTm Γ (B ex.[ δ' ]Ty) (u [ δ ]Tm)

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
getTy-liftTy : {n : ℕ} (Γ : Ctx n) (u : TmExpr n) → ex.getTy (liftCtx Γ) (liftTm1 (liftCtx Γ) u) ≡ liftTy (liftCtx Γ) (getTy Γ u)
getTy-liftTy (Γ , A) (var last) = {!!}
getTy-liftTy (Γ , A) (var (prev x)) = {!!}
getTy-liftTy Γ (lam A B u) = refl
getTy-liftTy Γ (app A B u u₁) = {!u₁!}

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
