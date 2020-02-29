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
weakenTm'-liftTm (prev k) (Γ ex., A₁) A C (var (prev x)) = ex.ap-coerc-Tm ((ap (λ z → ex.weakenTy (ex.getTy (ex.weakenCtx k Γ A) (ex.var z)))
                                                                               (weakenVar-weakenVar k x) ∙ ap (λ z → ex.weakenTy z) (! (ex.weakenTy'-getTy k Γ (ex.var x) A)))
                                                                                                         ∙ ! ex.weakenTy-weakenTy)
                                                                          refl
                                                                          (ap (λ z → ex.var (prev z))
                                                                              (weakenVar-weakenVar k x))
weakenTm'-liftTm k Γ A C (lam A₁ B u) rewrite weakenTy'-liftTy k Γ A A₁ |  weakenTy'-liftTy (prev k) (Γ ex., liftTy Γ A₁) A B
                                      =  ex.ap-coerc-Tm (ex.ap-pi-Ty refl refl)
                                                        refl
                                                        (ex.ap-lam-Tm refl refl (weakenTm'-liftTm (prev k) (Γ ex., liftTy Γ A₁) A (liftTy (Γ ex., liftTy Γ A₁) B) u ))
weakenTm'-liftTm k Γ A C (app A₁ B u u₁) rewrite weakenTy'-liftTy k Γ A A₁ | weakenTy'-liftTy (prev k) (Γ ex., liftTy Γ A₁) A B
                                               | weakenTm'-liftTm k Γ A (liftTy Γ (pi A₁ B)) u | weakenTm'-liftTm k Γ A (liftTy Γ A₁) u₁
                                      =  ex.ap-coerc-Tm (! ex.weakenTy-substTy) refl (ex.ap-app-Tm refl refl refl refl)

weakenTm-liftTm : (Γ : ex.Ctx n) (A B : ex.TyExpr n) (u : TmExpr n) → liftTm (ex.weakenCtx last Γ A) (ex.weakenTy' last B) (weakenTm' last u) ≡ ex.weakenTm' last (liftTm Γ B u)
weakenTm-liftTm Γ A B u = weakenTm'-liftTm last Γ A B u

weakenTy-liftTy : (Γ : ex.Ctx n) (B : ex.TyExpr n) (A : TyExpr n) → liftTy (ex.weakenCtx last Γ B) (weakenTy' last A) ≡ ex.weakenTy' last (liftTy Γ A)
weakenTy-liftTy Γ B A = weakenTy'-liftTy last Γ B A

weakenCtx-liftCtx : (k : Fin (suc n)) (Γ : Ctx n) (B : TyExpr (n -F' k)) → ex.weakenCtx k (liftCtx Γ) (liftTy (liftCtx (cutCtx k Γ)) B) ≡ liftCtx (weakenCtx k Γ B)
weakenCtx-liftCtx last Γ B = refl
weakenCtx-liftCtx (prev k) (Γ , A) B = ex.Ctx+= (weakenCtx-liftCtx k Γ B)
                                                (! (ap (λ x → liftTy x _) (! (weakenCtx-liftCtx k Γ B))
                                                ∙ weakenTy'-liftTy k (liftCtx Γ) (liftTy (liftCtx (cutCtx k Γ)) B) A))

weakenMor-liftMor : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : ex.TyExpr n) (δ : Mor n m) → liftMor (Γ ex., A) Δ (weakenMor δ) ≡ ex.weakenMor (liftMor Γ Δ δ)
weakenMor-liftMor Γ ex.◇ A ◇ = refl
weakenMor-liftMor Γ (Δ ex., A₁) A (δ , u) rewrite weakenMor-liftMor Γ Δ A δ | ! (ex.weaken[]Ty A₁ (liftMor Γ Δ δ) last) | weakenTm-liftTm Γ A (A₁ ex.[ liftMor Γ Δ δ ]Ty) u = refl

----------------------------------
---------- Lemmas that apply these syntactic equalities to derivations
-----------------------------------
weakenTy-liftᵈ : {k : Fin (suc n)} (Γ : Ctx n) (B : TyExpr (n -F' k)) (A : TyExpr n)
                → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) A)
                → ex.Derivable (liftCtx (weakenCtx k Γ B) ⊢ₑ liftTy (liftCtx (weakenCtx k Γ B)) (weakenTy' k A))
weakenTy-liftᵈ {k = k} Γ B A dA = ex.congTyCtx (weakenCtx-liftCtx k Γ B)
                                               (ex.congTy (! (ap (λ x → liftTy x _) (! (weakenCtx-liftCtx k Γ B)) ∙ weakenTy'-liftTy k (liftCtx Γ) (liftTy (liftCtx (cutCtx k Γ)) B) A))
                                                          (ex.WeakTy dA))

weakenTy-lift⁼ : {k : Fin (suc n)} (Γ : Ctx n) (B : TyExpr (n -F' k)) (A : TyExpr n)
                → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) A)
                → ex.Derivable (liftCtx (weakenCtx k Γ B) ⊢ₑ ex.weakenTy' k (liftTy (liftCtx Γ) A) == liftTy (liftCtx (weakenCtx k Γ B)) (weakenTy' k A))
weakenTy-lift⁼ {k = k} Γ B A dA = ex.congTyEq (ap (λ x → liftTy x _) (! (weakenCtx-liftCtx k Γ B)) ∙ weakenTy'-liftTy k (liftCtx Γ) (liftTy (liftCtx (cutCtx k Γ)) B) A )
                                  refl
                                  (ex.TyRefl (weakenTy-liftᵈ Γ B A dA))


weakenTm'-liftᵈ : (k : Fin (suc n)) {Γ : Ctx n} (B : TyExpr (n -F' k)) {A : TyExpr n} {u : TmExpr n}
               → ex.Derivable (liftCtx Γ ⊢ₑ liftTm (liftCtx Γ) (liftTy (liftCtx Γ) A) u :> liftTy (liftCtx Γ) A)
               → ex.Derivable (liftCtx (weakenCtx k Γ B) ⊢ₑ liftTm (liftCtx (weakenCtx k Γ B)) (liftTy (liftCtx (weakenCtx k Γ B)) (weakenTy' k A)) (weakenTm' k u)
                                         :> liftTy (liftCtx (weakenCtx k Γ B)) (weakenTy' k A))
weakenTm'-liftᵈ k B dA = {!!}

weakenTm-liftᵈ : {Γ : ex.Ctx n} (B : ex.TyExpr n) {A : TyExpr n} {u : TmExpr n}
               → ex.Derivable (Γ ⊢ₑ liftTm Γ (liftTy Γ A) u :> liftTy Γ A)
               → ex.Derivable ((Γ ex., B) ⊢ₑ liftTm (Γ ex., B) (liftTy (Γ ex., B) (weakenTy A)) (weakenTm u) :> liftTy (Γ ex., B) (weakenTy A))
weakenTm-liftᵈ {Γ = Γ} B {A} {u} dA = ex.congTm (! (weakenTy-liftTy Γ B A))
                                                (! (weakenTm-liftTm Γ B (liftTy Γ A) u) ∙  ap (λ x → liftTm (Γ ex., B) x _) (! (weakenTy-liftTy Γ B A)) )
                                                (ex.WeakTm dA)

weakenMor-liftᵈ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : ex.TyExpr n} {δ : Mor n m}
                  → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                  → (Γ ex., A) ex.⊢ liftMor (Γ ex., A) Δ (weakenMor δ) ∷> Δ
weakenMor-liftᵈ dδ = ex.congMor refl refl (! (weakenMor-liftMor _ _ _ _)) (ex.WeakMor dδ)

--------------------------------
---------- Weakening commutation for lifting without outermost coercion. The very same arguments again.
-------------------------------
weakenTm'-liftTm1 : (k : Fin (suc n)) (Γ : ex.Ctx n) (A : ex.TyExpr (n -F' k)) (u : TmExpr n) → liftTm1 (ex.weakenCtx k Γ A) (weakenTm' k u) ≡ ex.weakenTm' k (liftTm1 Γ u)
weakenTy'-liftTy1 : (k : Fin (suc n)) (Γ : ex.Ctx n) (B : ex.TyExpr (n -F' k)) (A : TyExpr n) → liftTy1 (ex.weakenCtx k Γ B) (weakenTy' k A) ≡ ex.weakenTy' k (liftTy1 Γ A)

weakenTy'-liftTy1 k Γ B (uu) = refl
weakenTy'-liftTy1 k Γ B (el v) = ex.ap-el-Ty (ex.ap-coerc-Tm ( (ex.ap-getTy refl (weakenTm'-liftTm1 k Γ B v) ∙ ! (ex.weakenTy'-getTy k Γ (liftTm1 Γ v) B))) refl (weakenTm'-liftTm1 k Γ B v))
weakenTy'-liftTy1 k Γ B (pi A A₁) rewrite weakenTy'-liftTy1 k Γ B A = ex.ap-pi-Ty refl (weakenTy'-liftTy (prev k) (Γ ex., liftTy Γ A) B A₁)

weakenTm'-liftTm1 k Γ B (var x) = ap (ex.var) (weakenVar-weakenVar k x)
weakenTm'-liftTm1 k Γ B (lam A B₁ u) = ex.ap-lam-Tm (weakenTy'-liftTy k Γ B A)
                                                    (ap (λ x → liftTy1 x (weakenTy' (prev k) B₁))
                                                        (ex.Ctx+= refl
                                                                  (weakenTy'-liftTy k Γ B A))
                                                        ∙ weakenTy'-liftTy (prev k) (Γ ex., liftTy Γ A) B B₁)
                                                    (ex.ap-coerc-Tm (ex.ap-getTy (ex.Ctx+= refl
                                                                                           (weakenTy'-liftTy k Γ B A))
                                                                                  ((ap ((λ x → liftTm1 x (weakenTm' (prev k) u)))
                                                                                        (ex.Ctx+= refl
                                                                                                  (weakenTy'-liftTy k Γ B A))
                                                                                        ∙ (weakenTm'-liftTm1 (prev k) (Γ ex., liftTy Γ A) B u)))
                                                                         ∙ ! (ex.weakenTy'-getTy (prev k) (Γ ex., liftTy1 Γ A) (liftTm1 (Γ ex., liftTy1 Γ A) u) B) )
                                                                    (ap (λ x → liftTy x (weakenTy' (prev k) B₁))
                                                                        (ex.Ctx+= refl (weakenTy'-liftTy k Γ B A))
                                                                      ∙ weakenTy'-liftTy (prev k) (Γ ex., liftTy Γ A) B B₁)
                                                                    (ap (λ x → liftTm1 x (weakenTm' (prev k) u))
                                                                        (ex.Ctx+= refl (weakenTy'-liftTy k Γ B A))
                                                                      ∙ (weakenTm'-liftTm1 (prev k) (Γ ex., liftTy Γ A) B u)))
weakenTm'-liftTm1 k Γ B (app A B₁ u u₁) = ex.ap-app-Tm (weakenTy'-liftTy k Γ B A)
                                                       (ap (λ x → liftTy1 x (weakenTy' (prev k) B₁))
                                                        (ex.Ctx+= refl
                                                                  (weakenTy'-liftTy k Γ B A))
                                                        ∙ weakenTy'-liftTy (prev k) (Γ ex., liftTy Γ A) B B₁)
                                                       (ex.ap-coerc-Tm ((ex.ap-getTy refl (weakenTm'-liftTm1 k Γ B u) ∙ ! (ex.weakenTy'-getTy k Γ (liftTm1 Γ u) B)))
                                                                       (weakenTy'-liftTy k Γ B (pi A B₁))
                                                                       (weakenTm'-liftTm1 k Γ B u))
                                                       (ex.ap-coerc-Tm (ex.ap-getTy refl (weakenTm'-liftTm1 k Γ B u₁) ∙ ! (ex.weakenTy'-getTy k Γ (liftTm1 Γ u₁) B))
                                                                       (weakenTy'-liftTy1 k Γ B A)
                                                                       (weakenTm'-liftTm1 k Γ B u₁))

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

[]-liftTy1⁼ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} → {δ : Mor n m}
             → ex.⊢ Γ → ex.⊢ Δ 
             → ex.Derivable ( Δ ⊢ₑ liftTy1 Δ A)
             → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
             → ex.Derivable (Γ ⊢ₑ (liftTy1 Δ A) ex.[ liftMor Γ Δ δ ]Ty == liftTy1 Γ (A [ δ ]Ty))


[]-liftTm1 : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {u : TmExpr m} {δ : Mor n m}
             → ex.⊢ Γ → ex.⊢ Δ 
             → ex.Derivable (Δ ⊢ₑ liftTm1 Δ u :> ex.getTy Δ (liftTm1 Δ u))
             → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
             → ex.Derivable (Γ ⊢ₑ liftTm1 Γ (u [ δ ]Tm) :> ex.getTy Γ (liftTm1 Γ (u [ δ ]Tm)))

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

getTy-coercTy-lemma : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {u : TmExpr (suc m)} {δ : Mor n m}
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
getTy-coercTy-lemma {n = n} {Γ = Γ} {Δ} {A} {u} {δ} dΓ dΔ dA du dδ = ex.congTyEq (! (ex.ap[]Ty refl
                                                                                           (ex.Mor+= ((ap (ex.weakenMor) (! (ex.[idMor]Mor _)) ∙ ex.weaken[]Mor _ _ _)
                                                                                                          ∙ ! (ex.weakenMorInsert _ _ _)
                                                                                                          ∙ (ex.ap[]Mor (! (weakenMor-liftMor _ _ _ δ)) refl))
                                                                                                          (ex.ap-coerc-Tm ((ap (ex.weakenTy) (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _)
                                                                                                                               ∙ ! (ex.weakenTyInsert (liftTy1 Γ (A [ δ ]Ty)) _ _))
                                                                                                                          ((ap (ex.weakenTy) (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _)
                                                                                                                               ∙ ! (ex.weakenTyInsert (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty) _ _)
                                                                                                                               ∙ ex.ap[]Ty (ex.weaken[]Ty _ _ _
                                                                                                                                                  ∙ ex.ap[]Ty refl
                                                                                                                                                              (! (weakenMor-liftMor _ _ _ δ) ))
                                                                                                                                            refl)
                                                                                                                          refl) )
                                                                                            ∙ ! (ex.[]Ty-assoc _ _ _) ))
                                                                                refl
                                                                                (ex.CoercTyEq dΓ
                                                                                              (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))
                                                                                              (ex.TySymm (getTy-[]-lift⁼ (dΓ ex., []-liftTy1 dΓ dΔ dA dδ)
                                                                                                                         (dΔ ex., dA)
                                                                                                                         du
                                                                                                                         (weakenMor+-liftᵈ dΓ dΔ dA dδ) )))

getTy-coercTy-lift : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {u : TmExpr (suc m)} {δ : Mor n m}
                 → ex.⊢ Γ → ex.⊢ Δ 
                 → ex.Derivable (Δ ⊢ₑ liftTy1 Δ A) 
                 → ex.Derivable ((Δ ex., liftTy1 Δ A) ⊢ₑ liftTm1 (Δ ex., liftTy1 Δ A) u :> ex.getTy (Δ ex., liftTy1 Δ A) (liftTm1 (Δ ex., liftTy1 Δ A) u))
                 → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ
                 → ex.Derivable ((Γ ex., (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty)) ⊢ₑ
                             ex.getTy (Δ ex., liftTy1 Δ A) (liftTm1 (Δ ex., liftTy1 Δ A) u) ex.[ ex.weakenMor+ (liftMor Γ Δ δ) ]Ty
                               == ex.coercTy (ex.getTy (Γ ex., liftTy1 Γ (A [ δ ]Ty))
                                             (liftTm1 (Γ ex., liftTy1 Γ (A [ δ ]Ty)) (u [ weakenMor+ δ ]Tm)))
                                             (liftTy1 Γ (A [ δ ]Ty)) (liftTy1 Δ A ex.[ liftMor Γ Δ δ ]Ty))

getTy-coercTy-lift {Γ = Γ} {Δ} {A} {u} {δ} dΓ dΔ dA du dδ = ex.TySymm (ex.TyTran (ex.SubstTy (ex.TmTy (dΔ ex., dA) du)
                                                                                             (ex.WeakMor dδ ex., ex.congTmTy (ex.weaken[]Ty _ _ _)
                                                                                                                             (ex.Conv (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                                                      (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                                                      (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ))
                                                                                                                                              (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                                                                                                              (ex.VarLast (ex.SubstTy dA dδ))
                                                                                                                                              (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                                                                                                                              (ex.TySymm (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ))))))
                                                                                 (ex.TySymm (getTy-coercTy-lemma dΓ dΔ dA du dδ) )
                                                                                 (ex.SubstTyMorEq1 (dΓ ex., ex.SubstTy dA dδ)
                                                                                                   (dΔ ex., dA)
                                                                                                   (ex.TmTy (dΔ ex., dA) du)
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
                                 (ex.Conv (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                          (ex.SubstTy dA (ex.WeakMor dδ))
                                          (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ))
                                                   (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                                   (ex.VarLast (ex.SubstTy dA dδ))
                                                   (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                          (ex.congTyEq refl (ex.weaken[]Ty _ _ _) (ex.TySymm (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))))
                                 (ex.TmTran
                                   (ex.Conv
                                     (ex.WeakTy (ex.SubstTy dA dδ))
                                     (ex.SubstTy dA (ex.WeakMor dδ))
                                     (ex.VarLast (ex.SubstTy dA dδ))
                                     ( ex.congTyEq refl (ex.weaken[]Ty _ _ _) (ex.WeakTyEq (ex.TyRefl (ex.SubstTy dA dδ))) ))
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
                                      (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ))
                                      (ex.SubstTy dA (ex.WeakMor dδ))
                                      (ex.SubstTy dA (ex.WeakMor dδ))
                                      (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ)) (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ)) (ex.VarLast (ex.SubstTy dA dδ)) (ex.WeakTyEq ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                      (ex.congTyEq refl (ex.weaken[]Ty _ _ _) (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))))
                                      (ex.congTyEq (ex.weaken[]Ty _ _ _) (ex.weaken[]Ty _ _ _) (ex.TyRefl (ex.WeakTy (ex.SubstTy dA dδ)))) ))))) )
                             (ex.CoercTyEq dΓ (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)) ([]-liftTy1⁼ (dΓ ex.,  []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) dB (weakenMor+-liftᵈ dΓ dΔ dA dδ))))

Mor+-[]-liftTmᵈ dΓ dΔ dA du dδ = ex.CoercTm dΓ
                                            ([]-liftTy1 dΓ dΔ dA dδ)
                                            (ex.SubstTy dA dδ)
                                            ([]-liftTm1 ( dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) du (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                            (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))

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
                                                           (getTy-coercTy-lemma dΓ dΔ dA du dδ))
                                                   (ex.TmSymm (ex.CoercTrans (ex.SubstTy (ex.TmTy (dΔ ex., dA) du) (ex.WeakMor+ dA dδ))
                                                                                   (ex.TyEqTy1 (dΓ ex., ex.SubstTy dA dδ) (getTy-coercTy-lemma dΓ dΔ dA du dδ))
                                                                                   (ex.TyEqTy2 (dΓ ex., ex.SubstTy dA dδ) (getTy-coercTy-lemma dΓ dΔ dA du dδ))
                                                                                   (ex.SubstTm du (ex.WeakMor+ dA dδ))
                                                                                   (getTy-substMor dΓ dΔ dA du dδ)
                                                                                   (getTy-coercTy-lemma dΓ dΔ dA du dδ)))
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
                                                                         (getTy-coercTy-lemma dΓ dΔ dA du dδ)))) )
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
               (ex.SubstTy dA dδ)
               ( []-liftTy1 dΓ dΔ dA dδ)
               (ex.SubstTy dB (ex.WeakMor+ dA dδ))
               ([]-liftTy1 (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) dB (weakenMor+-liftᵈ dΓ dΔ dA dδ))
               (ex.Conv (ex.SubstTy (ex.coercInvTy1 df)
                                    ((ex.WeakMor+ dA dδ)))
                        (ex.SubstTy dB ( (ex.WeakMor+ dA dδ)))
                        (ex.SubstTm (ex.coercInvTm df) (ex.WeakMor+ dA dδ))
                        (ex.SubstTyEq (ex.coercInvEq df) ( (ex.WeakMor+ dA dδ))))
               ([]-liftTm2 (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) dB df (weakenMor+-liftᵈ dΓ dΔ dA dδ))
               ( []-liftTy1⁼ dΓ dΔ dA dδ)
               (Mor+-[]-liftTy⁼ dΓ dΔ dA dB dδ)
               (ex.TmTran (ex.Conv (ex.CoercTy dΓ ([]-liftTy1 dΓ dΔ dA dδ)
                                         (ex.SubstTy dA dδ)
                                         (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                         (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                              (ex.SubstTy dB (ex.WeakMor+ dA dδ))
                              (Mor+-[]-liftTmᵈ dΓ dΔ dA (ex.coercInvTm df) dδ)
                              (ex.TySymm ( ex.TyTran (ex.SubstTy (ex.coercInvTy1 df) (ex.WeakMor+ dA dδ))
                                                     (ex.SubstTyEq (ex.TySymm (ex.coercInvEq df)) (ex.WeakMor+ dA dδ))
                                                     (getTy-coercTy-lift dΓ dΔ dA (ex.coercInvTm df) dδ))))
                   (ex.TmTran (ex.Conv (ex.CoercTy dΓ
                                                   ([]-liftTy1 dΓ dΔ dA dδ)
                                                   (ex.SubstTy dA dδ)
                                                   (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                   (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                  (ex.SubstTy dB ((ex.WeakMor+ dA dδ)))
                                  (ex.Conv (ex.SubstTy (ex.coercInvTy1 df) (ex.WeakMor+ dA dδ)) (ex.CoercTy dΓ
                                                      ( []-liftTy1 dΓ dΔ dA dδ)
                                                      (ex.SubstTy dA dδ)
                                                      (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                      (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                           (ex.SubstTm (ex.coercInvTm df) (ex.WeakMor+ dA dδ))
                                           (getTy-coercTy-lift dΓ dΔ dA (ex.coercInvTm df) dδ ))
                                  (ex.TySymm ( ex.TyTran (ex.SubstTy (ex.coercInvTy1 df) (ex.WeakMor+ dA dδ))
                                                     (ex.SubstTyEq (ex.TySymm (ex.coercInvEq df)) (ex.WeakMor+ dA dδ))
                                                     (getTy-coercTy-lift dΓ dΔ dA (ex.coercInvTm df) dδ))))
                       (ex.TmSymm (ex.CoercTrans (ex.SubstTy (ex.coercInvTy1 df) (ex.WeakMor+ dA dδ))
                                                             ( ex.CoercTy dΓ ([]-liftTy1 dΓ dΔ dA dδ)
                                                                          (ex.SubstTy dA dδ)
                                                                          (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                                          (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                                             (ex.SubstTy dB (ex.WeakMor+ dA dδ))
                                                             (ex.SubstTm (ex.coercInvTm df) (ex.WeakMor+ dA dδ))
                                                             (getTy-coercTy-lift dΓ dΔ dA (ex.coercInvTm df) dδ)
                                                             (ex.TySymm (ex.TyTran (ex.SubstTy (ex.coercInvTy1 df) (ex.WeakMor+ dA dδ))
                                                     (ex.SubstTyEq (ex.TySymm (ex.coercInvEq df)) (ex.WeakMor+ dA dδ))
                                                     (getTy-coercTy-lift dΓ dΔ dA (ex.coercInvTm df) dδ)))))
                       (ex.ConvEq (ex.CoercTy dΓ
                                       ([]-liftTy1 dΓ dΔ dA dδ)
                                       (ex.SubstTy dA dδ)
                                       (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                       (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                            (Mor+-[]-liftTm⁼ dΓ dΔ dA (ex.coercInvTm df) dδ)
                            (ex.TySymm ( ex.TyTran (ex.SubstTy (ex.coercInvTy1 df) (ex.WeakMor+ dA dδ))
                                                     (ex.SubstTyEq (ex.TySymm (ex.coercInvEq df)) (ex.WeakMor+ dA dδ))
                                                     (getTy-coercTy-lift dΓ dΔ dA (ex.coercInvTm df) dδ)))))
                   (ex.TmSymm (ex.CoercTrans
                                     (ex.SubstTy (getTy-[]-lift (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                 (ex.WeakMor (ex.idMorDerivable dΓ) ex., ex.congTmTy (ap (ex.weakenTy) (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _) (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ)) (ex.WeakTy ([]-liftTy1 dΓ dΔ dA dδ)) (ex.VarLast (ex.SubstTy dA dδ)) (ex.WeakTyEq ( []-liftTy1⁼ dΓ dΔ dA dδ)))))
                                     (ex.CoercTy dΓ
                                                 ( []-liftTy1 dΓ dΔ dA dδ)
                                                 (ex.SubstTy dA dδ)
                                                 ([]-liftTy1 (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) dB (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                 (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                     (ex.SubstTy dB (ex.WeakMor+ dA dδ))
                                     (ex.CoercTm dΓ ([]-liftTy1 dΓ dΔ dA dδ)
                                                    (ex.SubstTy dA dδ)
                                                    ([]-liftTm1 (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                    (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                     (ex.CoercTyEq dΓ (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ))
                                                   (ex.TyTran (ex.SubstTy dB (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                              (ex.TyTran (ex.SubstTy (ex.coercInvTy1 df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                                         (getTy-[]-lift⁼ (dΓ ex., []-liftTy1 dΓ dΔ dA dδ ) (dΔ ex., dA) (ex.coercInvTm df) (weakenMor+-liftᵈ dΓ dΔ dA dδ))
                                                                         (ex.SubstTyEq (ex.coercInvEq df) (weakenMor+-liftᵈ dΓ dΔ dA dδ)))
                                                              ([]-liftTy1⁼ (dΓ ex., []-liftTy1 dΓ dΔ dA dδ) (dΔ ex., dA) dB (weakenMor+-liftᵈ dΓ dΔ dA dδ))))
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


[]-liftTm1⁼! dΓ dΔ du dδ = ex.TmTran (ex.Conv (ex.SubstTy (ex.TmTy dΔ du) dδ)
                                              (getTy-[]-lift dΓ dΔ du dδ)
                                              (ex.Conv ( getTy-[]-lift dΓ dΔ du dδ)
                                                       (ex.SubstTy (ex.TmTy dΔ du) dδ)
                                                       ([]-liftTm1 dΓ dΔ du dδ)
                                                       (getTy-[]-lift⁼ dΓ dΔ du dδ))
                                              ( ex.TySymm (getTy-[]-lift⁼ dΓ dΔ du dδ)))
                                     (ex.ConvEq (ex.SubstTy (ex.TmTy dΔ du) dδ) ([]-liftTm1⁼ dΓ dΔ du dδ) (ex.TySymm (getTy-[]-lift⁼ dΓ dΔ du dδ)))
                                     (ex.TmTran (ex.Conv ( getTy-[]-lift dΓ dΔ du dδ)
                                                         ( getTy-[]-lift dΓ dΔ du dδ)
                                                         ([]-liftTm1 dΓ dΔ du dδ)
                                                         (ex.TyRefl (getTy-[]-lift dΓ dΔ du dδ)))
                                                (ex.CoercTrans (getTy-[]-lift dΓ dΔ du dδ)
                                                               (ex.SubstTy (ex.TmTy dΔ du) dδ)
                                                               (getTy-[]-lift dΓ dΔ du dδ)
                                                               ([]-liftTm1 dΓ dΔ du dδ)
                                                               (getTy-[]-lift⁼ dΓ dΔ du dδ)
                                                               (ex.TySymm (getTy-[]-lift⁼ dΓ dΔ du dδ)))
                                                (ex.CoercRefl ([]-liftTm1 dΓ dΔ du dδ)))
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

[]-liftTm2⁼ dΓ dΔ dA du dδ = ex.TmTran (ex.Conv (ex.SubstTy (ex.coercInvTy1 du) dδ)
                                                (ex.SubstTy dA dδ)
                                                (ex.Conv (getTy-[]-lift dΓ dΔ (ex.coercInvTm du) dδ)
                                                         (ex.SubstTy (ex.coercInvTy1 du) dδ)
                                                         ([]-liftTm1 dΓ dΔ (ex.coercInvTm du) dδ)
                                                         ((getTy-[]-lift⁼ dΓ dΔ (ex.coercInvTm du) dδ)))
                                                (ex.SubstTyEq (ex.coercInvEq du) dδ))
                                       (ex.ConvEq (ex.SubstTy (ex.coercInvTy1 du) dδ) ([]-liftTm1⁼ dΓ dΔ (ex.coercInvTm du) dδ) (ex.SubstTyEq (ex.coercInvEq du) dδ))
                                       (ex.TmTran (ex.Conv (getTy-[]-lift dΓ dΔ (ex.coercInvTm du) dδ)
                                                           (ex.SubstTy dA dδ)
                                                           ([]-liftTm1 dΓ dΔ (ex.coercInvTm du) dδ)
                                                           ((ex.TyTran (ex.SubstTy (ex.coercInvTy1 du) dδ)
                                                                                       (getTy-[]-lift⁼ dΓ dΔ (ex.coercInvTm du) dδ)
                                                                                       (ex.SubstTyEq (ex.coercInvEq du) dδ))))
                                                  (ex.CoercTrans (getTy-[]-lift dΓ dΔ (ex.coercInvTm du) dδ)
                                                                 (ex.SubstTy (ex.coercInvTy1 du) dδ)
                                                                 (ex.SubstTy dA dδ)
                                                                 ([]-liftTm1 dΓ dΔ (ex.coercInvTm du) dδ)
                                                                 (getTy-[]-lift⁼ dΓ dΔ (ex.coercInvTm du) dδ)
                                                                 (ex.SubstTyEq (ex.coercInvEq du) dδ))
                                                  (ex.TmSymm (ex.CoercTrans ( getTy-[]-lift dΓ dΔ (ex.coercInvTm du) dδ)
                                                                            ([]-liftTy1 dΓ dΔ dA dδ )
                                                                            (ex.SubstTy dA dδ)
                                                                            ( []-liftTm1 dΓ dΔ (ex.coercInvTm du) dδ)
                                                                            (ex.TyTran (ex.SubstTy (ex.coercInvTy1 du) dδ)
                                                                                       (getTy-[]-lift⁼ dΓ dΔ (ex.coercInvTm du) dδ)
                                                                                       (ex.TyTran (ex.SubstTy dA dδ)
                                                                                                  (ex.SubstTyEq (ex.coercInvEq du) dδ)
                                                                                                  ([]-liftTy1⁼ dΓ dΔ dA dδ)))
                                                                            (ex.TySymm ([]-liftTy1⁼ dΓ dΔ dA dδ)))))

------------------------------------------------------------------------
----------------- Some Lemmas about identity morphisms are needed
-------------------------------------------------------------------
idmor-lift⁼ : {Γ : ex.Ctx n} → ex.⊢ Γ → Γ ex.⊢ liftMor Γ Γ (idMor n) == ex.idMor n ∷> Γ
idMorDerivableLift : {Γ : ex.Ctx n} →  ex.⊢ Γ → (Γ ex.⊢ liftMor Γ Γ (idMor n) ∷> Γ)

idMorDerivableLift {Γ = .ex.◇} ex.tt = ex.tt
idMorDerivableLift {Γ = .(_ ex., _)} ( ex._,_ {Γ = Γ} {A = A} dΓ x)
                  = ex.congMor refl refl (! (weakenMor-liftMor _ _ _ (idMor _))) (ex.WeakMor (idMorDerivableLift dΓ))
               ex., ex.congTm (ex.weaken[]Ty A _ last ∙ ! (ap (λ x → A ex.[ x ]Ty) (weakenMor-liftMor Γ Γ A (idMor _))))
                              (ex.ap-coerc-Tm refl
                                              ((ex.weaken[]Ty A _ last ∙ ! (ap (λ x → A ex.[ x ]Ty) (weakenMor-liftMor Γ Γ A (idMor _)))))
                                              refl)
                              (ex.Conv (ex.WeakTy x) (ex.WeakTy (ex.SubstTy x (idMorDerivableLift dΓ))) (ex.VarLast x) (ex.WeakTyEq (ex.congTyEq (ex.[idMor]Ty A) refl (ex.SubstTyMorEq x (ex.idMorDerivable dΓ) (idMorDerivableLift dΓ) (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ)) (idmor-lift⁼ dΓ))))) 

-- All these Lemmas need the derivability of liftings to be concluded.
idmor-lift⁼ {Γ = ex.◇} dΓ = ex.tt
idmor-lift⁼ {Γ = Γ ex., A} (dΓ ex., x)
                 rewrite ! (! (ex.weaken[]Ty A (ex.idMor _) last) ∙ ap (λ x → ex.weakenTy x) (ex.[idMor]Ty A))
                      = ex.congMorEq refl refl (! (weakenMor-liftMor Γ Γ A (idMor _))) refl (ex.WeakMorEq (idmor-lift⁼ dΓ)) ex., ex.TmRefl (ex.Conv
                                   (ex.congTy ( ! (ap (λ x → ex.weakenTy x) (ex.[idMor]Ty A)) ∙ (ex.weaken[]Ty A (ex.idMor _) last)) (ex.WeakTy x))
                                   (ex.congTy (((ex.weaken[]Ty A _ last)) ∙ ! (ap (λ x → A ex.[ x ]Ty) (weakenMor-liftMor Γ Γ A (idMor _)))) (ex.WeakTy (ex.SubstTy x (idMorDerivableLift dΓ))))
                                   (ex.congTm (! (ap (λ x → ex.weakenTy x) (ex.[idMor]Ty A)) ∙ (ex.weaken[]Ty A (ex.idMor _) last)) refl (ex.VarLast x))
                                   (ex.congTyEq ( ! (! (ex.weaken[]Ty A (ex.idMor _) last) ∙ ap (λ x → ex.weakenTy x) (ex.[idMor]Ty A)))
                                           (ex.weaken[]Ty A (liftMor Γ Γ (idMor _)) last ∙ ! (ap (λ x → A ex.[ x ]Ty) (weakenMor-liftMor Γ Γ A (idMor _))))
                                           (ex.WeakTyEq (ex.congTyEq (ex.[idMor]Ty A) refl (ex.SubstTyMorEq x (ex.idMorDerivable dΓ) (idMorDerivableLift dΓ) (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ)) (idmor-lift⁼ dΓ)) ))))

[idmor-lift]Ty : {Γ : ex.Ctx n} {A A' : ex.TyExpr n} → ex.⊢ Γ
             → ex.Derivable (Γ ⊢ₑ A == A')
             → ex.Derivable (Γ ⊢ₑ A == A' ex.[ liftMor Γ Γ (idMor n) ]Ty)
[idmor-lift]Ty dΓ dA= = ex.congTyEq (ex.[idMor]Ty _) refl (ex.SubstTyFullEq dΓ dΓ dA= (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ)))

substTy-liftTyᵈ : {n : ℕ} {Γ : ex.Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr n}
             → ex.⊢ Γ 
             → ex.Derivable (Γ ⊢ₑ liftTy1 Γ A)
             → ex.Derivable ((Γ ex., liftTy1 Γ A) ⊢ₑ liftTy1 (Γ ex., liftTy1 Γ A) B)
             → ex.Derivable (Γ ⊢ₑ liftTm Γ (liftTy1 Γ A) u :> (liftTy1 Γ A))  
             → ex.Derivable (Γ ⊢ₑ liftTy Γ (substTy B u))

substTy-liftTy⁼ : {n : ℕ} {Γ : ex.Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr n}
             → ex.⊢ Γ 
             → ex.Derivable (Γ ⊢ₑ liftTy1 Γ A)
             → ex.Derivable ((Γ ex., liftTy1 Γ A) ⊢ₑ liftTy1 (Γ ex., liftTy1 Γ A) B)
             → ex.Derivable (Γ ⊢ₑ liftTm Γ (liftTy1 Γ A) u :> (liftTy1 Γ A))  
             → ex.Derivable (Γ ⊢ₑ ex.substTy (liftTy (Γ ex., liftTy Γ A) B) (liftTm Γ (liftTy Γ A) u) == liftTy Γ (substTy B u))

substTm-liftTmᵈ : {n : ℕ} {Γ : ex.Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {v : TmExpr (suc n)} {u : TmExpr n}
             → ex.⊢ Γ
             → ex.Derivable (Γ ⊢ₑ liftTy Γ A)
             → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) v :> liftTy1 (Γ ex., liftTy Γ A) B)
             → ex.Derivable (Γ ⊢ₑ liftTm Γ (liftTy Γ A) u :> liftTy Γ A) 
             → ex.Derivable (Γ ⊢ₑ liftTm Γ (liftTy Γ (B [ idMor n , u ]Ty)) (substTm v u)
                               :> liftTy Γ (B [ idMor n , u ]Ty))

substTm-liftTm⁼ : {n : ℕ} {Γ : ex.Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {v : TmExpr (suc n)} {u : TmExpr n}
             → ex.⊢ Γ
             → ex.Derivable (Γ ⊢ₑ liftTy Γ A)
             → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) v :> liftTy1 (Γ ex., liftTy Γ A) B)
             → ex.Derivable (Γ ⊢ₑ liftTm Γ (liftTy Γ A) u :> liftTy Γ A) 
             → ex.Derivable (Γ ⊢ₑ ex.substTm ((liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) v)) (liftTm Γ (liftTy Γ A) u)
                               == liftTm Γ (ex.substTy (liftTy (Γ ex., liftTy Γ A) B) (liftTm Γ (liftTy Γ A) u)) (substTm v u)
                               :> (ex.substTy (liftTy (Γ ex., liftTy Γ A) B) (liftTm Γ (liftTy Γ A) u)))

substTy-liftTyᵈ dΓ dA dB du = ex.TyEqTy2 dΓ (substTy-liftTy⁼ dΓ dA dB du)

substTy-liftTy⁼ {Γ = Γ} {A} {B} {u} dΓ dA dB du = ex.TyTran (ex.SubstTy dB liftidMor)
                                                            (ex.SubstTyMorEq1 dΓ (dΓ ex., dA) dB
                                                                              (ex.MorSymm dΓ (dΓ ex., dA)
                                                                                          (idmor-lift⁼ dΓ ex., ex.TmSymm (ex.congTmEq (ex.ap-coerc-Tm (! (ex.[idMor]Ty _)) refl refl)
                                                                                                      refl refl
                                                                                                      (ex.CoercTrans (ex.coercInvTy1 du) dA
                                                                                                                     (ex.SubstTy dA (idMorDerivableLift dΓ)) (ex.coercInvTm du)
                                                                                                                     (ex.coercInvEq du) ([idmor-lift]Ty dΓ (ex.TyRefl dA)))))))
                                                            ([]-liftTy1⁼ dΓ (dΓ ex., dA) dB liftidMor)
                          where liftidMor : Γ ex.⊢ liftMor Γ Γ (idMor _) ex., liftTm Γ (liftTy Γ A ex.[ liftMor Γ Γ (idMor _) ]Ty) u ∷> (Γ ex., liftTy Γ A)
                                liftidMor = idMorDerivableLift dΓ ex., ex.Conv (ex.coercInvTy1 du) (ex.SubstTy dA (idMorDerivableLift dΓ))
                                                                               (ex.coercInvTm du) ([idmor-lift]Ty dΓ (ex.coercInvEq du))

substTm-liftTmᵈ dΓ dA dv du = []-liftTm2 dΓ (dΓ ex., dA) (ex.coercInvTy2 dv) dv (idMorDerivableLift dΓ ex., ex.Conv (ex.coercInvTy1 du)
                                                                                                                    (ex.SubstTy dA (idMorDerivableLift dΓ))
                                                                                                                    (ex.coercInvTm du)
                                                                                                                    ([idmor-lift]Ty dΓ (ex.coercInvEq du)))

substTm-liftTm⁼ {Γ = Γ} {A} {B} {v} {u} dΓ dA dv du = ex.TmTran (ex.Conv (ex.SubstTy (ex.coercInvTy2 dv) liftidMor)
                                                                         (ex.SubstTy (ex.coercInvTy2 dv) SUBSTMOR)
                                                                         (ex.SubstTm dv liftidMor)
                                                                         (ex.SubstTyMorEq1 dΓ (dΓ ex., dA) (ex.coercInvTy2 dv) liftidMorEq))
                                        (ex.SubstTmMorEq1 dΓ (dΓ ex., dA) dv (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ) ex., ex.TmSymm (ex.congTmEq (ex.ap-coerc-Tm refl (! (ex.[idMor]Ty _)) refl)
                                                                                                                                            refl (! (ex.[idMor]Ty _))
                                                                                                                               (ex.CoercTrans (ex.coercInvTy1 du)
                                                                                                                                              (ex.SubstTy dA (idMorDerivableLift dΓ)) dA
                                                                                                                                              (ex.coercInvTm du)
                                                                                                                                              ([idmor-lift]Ty dΓ (ex.coercInvEq du))
                                                                                                                                              (ex.TySymm ([idmor-lift]Ty dΓ (ex.TyRefl dA)))))))
                                        (ex.TmTran (ex.Conv (ex.SubstTy (ex.coercInvTy2 dv) liftidMor)
                                                            (ex.SubstTy (ex.coercInvTy2 dv) SUBSTMOR)
                                                            (ex.Conv (substTy-liftTyᵈ dΓ dA (ex.coercInvTy2 dv) du)
                                                                     (ex.SubstTy (ex.coercInvTy2 dv) liftidMor)
                                                                     (substTm-liftTmᵈ dΓ dA dv du)
                                                                     (ex.TySymm ([]-liftTy1⁼ dΓ (dΓ ex., dA) (ex.coercInvTy2 dv) liftidMor)))
                                                            (ex.SubstTyMorEq1 dΓ (dΓ ex., dA) (ex.coercInvTy2 dv) liftidMorEq))
                                                   (ex.ConvEq (ex.SubstTy (ex.coercInvTy2 dv) liftidMor)
                                                              ([]-liftTm2⁼ dΓ (dΓ ex., dA) (ex.coercInvTy2 dv) dv liftidMor)
                                                              (ex.SubstTyMorEq1 dΓ (dΓ ex., dA) (ex.coercInvTy2 dv) liftidMorEq))
                                                   (ex.TmTran (ex.Conv (substTy-liftTyᵈ dΓ dA (ex.coercInvTy2 dv) du) (ex.SubstTy (ex.coercInvTy2 dv) SUBSTMOR)
                                                                       ([]-liftTm2 dΓ (dΓ ex., dA) (ex.coercInvTy2 dv) dv liftidMor)
                                                                       (ex.TySymm (substTy-liftTy⁼ dΓ dA (ex.coercInvTy2 dv) du)))
                                                              (ex.CoercTrans (substTy-liftTyᵈ dΓ dA (ex.coercInvTy2 dv) du)
                                                                             (ex.SubstTy (ex.coercInvTy2 dv) liftidMor)
                                                                             (ex.SubstTy (ex.coercInvTy2 dv) SUBSTMOR)
                                                                             (substTm-liftTmᵈ dΓ dA dv du )
                                                                             (ex.TySymm ([]-liftTy1⁼ dΓ (dΓ ex., dA) (ex.coercInvTy2 dv) liftidMor))
                                                                             (ex.SubstTyMorEq1 dΓ (dΓ ex., dA) (ex.coercInvTy2 dv) liftidMorEq))
                                                              (ex.CoercTrans (getTy-[]-lift dΓ (dΓ ex., dA) (ex.coercInvTm dv) liftidMor)
                                                                             (substTy-liftTyᵈ dΓ dA (ex.coercInvTy2 dv) du )
                                                                             (ex.SubstTy (ex.coercInvTy2 dv) SUBSTMOR)
                                                                             (ex.coercInvTm (substTm-liftTmᵈ dΓ dA dv du))
                                                                             (ex.TyTran (ex.SubstTy (ex.coercInvTy1 dv) liftidMor)
                                                                                        (getTy-[]-lift⁼ dΓ (dΓ ex., dA) (ex.coercInvTm dv) liftidMor)
                                                                                        (ex.TyTran (ex.SubstTy (ex.coercInvTy2 dv) liftidMor)
                                                                                                   (ex.SubstTyEq (ex.coercInvEq dv) liftidMor)
                                                                                                   ([]-liftTy1⁼ dΓ (dΓ ex., dA) (ex.coercInvTy2 dv) liftidMor)))
                                                                             (ex.TySymm (substTy-liftTy⁼ dΓ dA (ex.coercInvTy2 dv) du)))))

                         where
                               SUBSTMOR : Γ ex.⊢ ex.idMor _ ex., liftTm Γ (liftTy Γ A) u ∷> (Γ ex., liftTy Γ A)
                               SUBSTMOR = ex.idMorDerivable dΓ ex., ex.congTmTy (! (ex.[idMor]Ty _)) du
                               liftidMor : Γ ex.⊢ liftMor Γ Γ (idMor _) ex., liftTm Γ (liftTy Γ A ex.[ liftMor Γ Γ (idMor _) ]Ty) u ∷> (Γ ex., liftTy Γ A)
                               liftidMor = idMorDerivableLift dΓ ex., ex.Conv (ex.coercInvTy1 du)
                                                                              (ex.SubstTy dA (idMorDerivableLift dΓ))
                                                                              (ex.coercInvTm du)
                                                                              ([idmor-lift]Ty dΓ (ex.coercInvEq du))

                               liftidMorEq : Γ ex.⊢ liftMor Γ Γ (idMor _) ex., liftTm Γ (liftTy Γ A ex.[ liftMor Γ Γ (idMor _) ]Ty) u 
                                                 == ex.idMor _ ex., liftTm Γ (liftTy Γ A) u
                                                  ∷> (Γ ex., liftTy Γ A) 
                               liftidMorEq = idmor-lift⁼ dΓ ex., ex.TmSymm (ex.congTmEq (ex.ap-coerc-Tm (! (ex.[idMor]Ty _)) refl refl)
                                                                                        refl refl
                                                                                        (ex.CoercTrans (ex.coercInvTy1 du) dA (ex.SubstTy dA (idMorDerivableLift dΓ)) (ex.coercInvTm du)
                                                                                                       (ex.coercInvEq du) ([idmor-lift]Ty dΓ (ex.TyRefl dA))))
coercTy-liftᵈ : {Γ : ex.Ctx n} {A A' : TyExpr n} {B : TyExpr (suc n)}
          → ex.⊢ Γ
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A == liftTy Γ A')
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTy (Γ ex., liftTy Γ A) B)
          → ex.Derivable ((Γ ex., liftTy Γ A') ⊢ₑ liftTy (Γ ex., liftTy Γ A') B)
coercTy-liftᵈ dΓ dA= dB = ex.congTy (ap (liftTy _) ([idMor]Ty _))
                                    ([]-liftTy1 (dΓ ex., dA') (dΓ ex., dA) dB (weakenMor-liftᵈ (idMorDerivableLift dΓ)
                                                                              ex.,  ex.Conv (ex.WeakTy (ex.TyEqTy2 dΓ dA=))
                                                                                            (ex.SubstTy (ex.TyEqTy1 dΓ dA=) (weakenMor-liftᵈ (idMorDerivableLift dΓ)))
                                                                                            (ex.VarLast (ex.TyEqTy2 dΓ dA=))
                                                                                            (ex.congTyEq refl
                                                                                                         (ex.weaken[]Ty _ _ _ ∙ ex.ap[]Ty refl (! (weakenMor-liftMor _ _ _ _)))
                                                                                                         (ex.WeakTyEq ([idmor-lift]Ty dΓ (ex.TySymm dA=))))))
                     where
                     dA = ex.TyEqTy1 dΓ dA=
                     dA' = ex.TyEqTy2 dΓ dA=

coercTy-lift⁼ : {Γ : ex.Ctx n} {A A' : TyExpr n} {B : TyExpr (suc n)}
          → ex.⊢ Γ
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A == liftTy Γ A')
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTy (Γ ex., liftTy Γ A) B)
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTy (Γ ex., liftTy Γ A) B == ex.coercTy (liftTy (Γ ex., liftTy Γ A') B) (liftTy Γ A') (liftTy Γ A))
coercTy-lift⁼ {Γ = Γ} {A} {A'} {B = B} dΓ dA= dB
               = ex.TySymm (ex.congTyEq refl
                                        (ap (liftTy (Γ ex., (liftTy Γ A))) ([idMor]Ty _))
                                        (ex.TyTran (ex.SubstTy dB' (weakenMor-liftᵈ (idMorDerivableLift dΓ) ex., ex.Conv (ex.WeakTy dA)
                                                                                                                        (ex.SubstTy dA' (weakenMor-liftᵈ (idMorDerivableLift dΓ)))
                                                                                                                        (ex.VarLast dA)
                                                                                                                        (ex.congTyEq refl
                                                                                                                                    (ex.weaken[]Ty (liftTy Γ A') _ last
                                                                                                                                      ∙ ex.ap[]Ty refl (! (weakenMor-liftMor Γ Γ _ _)))
                                                                                                                                    (ex.TyTran (ex.WeakTy (ex.congTy (ap (liftTy Γ)
                                                                                                                                                                         (! ([idMor]Ty _)))
                                                                                                                                                                     dA'))
                                                                                                                                               (ex.congTyEq refl
                                                                                                                                                            (ap (λ x → ex.weakenTy (liftTy Γ x))
                                                                                                                                                                (! ([idMor]Ty _)))
                                                                                                                                                            (ex.WeakTyEq dA=))
                                                                                                                                               (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ
                                                                                                                                                                      dΓ
                                                                                                                                                                      dA'
                                                                                                                                                                      (idMorDerivableLift dΓ))))))))
                                                   (ex.SubstTyMorEq1 (dΓ ex., dA)
                                                                     (dΓ ex., dA')
                                                                     dB'
                                                                     (ex.congMorEq refl refl refl
                                                                                   (! (weakenMor-liftMor Γ Γ (liftTy Γ A) _))
                                                                                   (ex.WeakMorEq (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ)))
                                                                            ex., ex.congTmEq refl
                                                                                             (ex.ap-coerc-Tm refl
                                                                                                             (ap ex.weakenTy (! (ex.[idMor]Ty _ )) ∙ ex.weaken[]Ty _ _ _)
                                                                                                             refl)
                                                                                             (ap ex.weakenTy (! (ex.[idMor]Ty _ )) ∙ ex.weaken[]Ty _ _ _)
                                                                                             (ex.TmSymm (ex.CoercTrans (ex.WeakTy dA)
                                                                                                                       (ex.SubstTy dA' (weakenMor-liftᵈ (idMorDerivableLift dΓ) ))
                                                                                                                       (ex.WeakTy dA')
                                                                                                                       (ex.VarLast dA)
                                                                                                                       ((ex.congTyEq refl
                                                                                                                                    (ex.weaken[]Ty (liftTy Γ A') _ last
                                                                                                                                      ∙ ex.ap[]Ty refl (! (weakenMor-liftMor Γ Γ _ _)))
                                                                                                                                    (ex.TyTran (ex.WeakTy (ex.congTy (ap (liftTy Γ)
                                                                                                                                                                         (! ([idMor]Ty _)))
                                                                                                                                                                     dA'))
                                                                                                                                               (ex.congTyEq refl
                                                                                                                                                            (ap (λ x → ex.weakenTy (liftTy Γ x))
                                                                                                                                                                (! ([idMor]Ty _)))
                                                                                                                                                            (ex.WeakTyEq dA=))
                                                                                                                                               (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ
                                                                                                                                                                       dΓ
                                                                                                                                                                       dA'
                                                                                                                                                                       (idMorDerivableLift dΓ)))))))
                                                                                                                       (ex.congTyEq (ex.weaken[]Ty _ _ _
                                                                                                                                         ∙ ex.ap[]Ty refl (! (weakenMor-liftMor Γ Γ _ _)))
                                                                                                                                    (ap (λ x → ex.weakenTy (liftTy1 Γ x))
                                                                                                                                        ([idMor]Ty _))
                                                                                                                                    (ex.TySymm (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ
                                                                                                                                                                   dΓ
                                                                                                                                                                   dA'
                                                                                                                                                                   (idMorDerivableLift dΓ))))))))))
                                                   (([]-liftTy1⁼ (dΓ ex., dA)
                                                     (dΓ ex., dA')
                                                     dB'
                                                     (ex.congMor refl
                                                                 refl
                                                                 (! (weakenMor-liftMor Γ Γ (liftTy Γ A) _))
                                                                 (ex.WeakMor (idMorDerivableLift dΓ)) ex., ex.Conv (ex.WeakTy dA)
                                                                                                                   (ex.SubstTy dA' (weakenMor-liftᵈ (idMorDerivableLift dΓ)))
                                                                                                                   (ex.VarLast dA)
                                                                                                                   (((ex.congTyEq refl
                                                                                                                                 (ex.weaken[]Ty (liftTy Γ A') _ last
                                                                                                                                   ∙ ex.ap[]Ty refl (! (weakenMor-liftMor Γ Γ _ _)))
                                                                                                                                 (ex.TyTran (ex.WeakTy (ex.congTy (ap (liftTy Γ)
                                                                                                                                                                      (! ([idMor]Ty _)))
                                                                                                                                                                  dA'))
                                                                                                                                            (ex.congTyEq refl
                                                                                                                                                         (ap (λ x → ex.weakenTy (liftTy Γ x))
                                                                                                                                                             (! ([idMor]Ty _)))
                                                                                                                                                         (ex.WeakTyEq dA=))
                                                                                                                                            (ex.WeakTyEq (ex.TySymm ([]-liftTy1⁼ dΓ
                                                                                                                                                              dΓ
                                                                                                                                                              dA'
                                                                                                                                                              (idMorDerivableLift dΓ)))))))))))))
                                        where
                                        dA = ex.TyEqTy1 dΓ dA=
                                        dA' = ex.TyEqTy2 dΓ dA=
                                        dB' = coercTy-liftᵈ dΓ dA= dB


coercTm-liftᵈ : {Γ : ex.Ctx n} {A A' : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
          → ex.⊢ Γ
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A == liftTy Γ A')
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) u :> liftTy (Γ ex., liftTy Γ A) B)
          → ex.Derivable ((Γ ex., liftTy Γ A') ⊢ₑ liftTm (Γ ex., liftTy Γ A') (liftTy (Γ ex., liftTy Γ A') B) u :> liftTy (Γ ex., liftTy Γ A') B)

coercTm1-liftᵈ : {Γ : ex.Ctx n} {A A' : TyExpr n} {u : TmExpr (suc n)}
          → ex.⊢ Γ
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A == liftTy Γ A')
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTm1 (Γ ex., liftTy Γ A) u :> ex.getTy (Γ ex., liftTy Γ A) (liftTm1 (Γ ex., liftTy Γ A) u))
          → ex.Derivable ((Γ ex., liftTy Γ A') ⊢ₑ liftTm1 (Γ ex., liftTy Γ A') u :> ex.getTy (Γ ex., liftTy Γ A') (liftTm1 (Γ ex., liftTy Γ A') u))

coercTm1-liftᵈ {Γ = Γ} {A} {A'} {u} dΓ dA= du = ex.congTm (ex.ap-getTy {u' = liftTm1 _ u} refl (ap (liftTm1 _) ([idMor]Tm u)))
                                                          (ap (liftTm1 _) ([idMor]Tm u))
                                                           ([]-liftTm1 (dΓ ex., (ex.TyEqTy2 dΓ dA=))
                                                                     (dΓ ex., (ex.TyEqTy1 dΓ dA=))
                                                                     du
                                                                     (weakenMor-liftᵈ (idMorDerivableLift dΓ) ex., ex.Conv (ex.WeakTy (ex.TyEqTy2 dΓ dA=))
                                                                                                              (ex.SubstTy (ex.TyEqTy1 dΓ dA=) (weakenMor-liftᵈ (idMorDerivableLift dΓ)))
                                                                                                              (ex.VarLast (ex.TyEqTy2 dΓ dA=))
                                                                                                              (ex.congTyEq refl
                                                                                                                           (ex.weaken[]Ty _ _ _ ∙ ex.ap[]Ty refl (! (weakenMor-liftMor Γ Γ _ _)))
                                                                                                                           (ex.WeakTyEq ([idmor-lift]Ty dΓ (ex.TySymm dA=))))))

coercTm-liftᵈ {Γ = Γ} {A} {A'} {B} {u} dΓ dA= du = ex.congTm (ap (liftTy (Γ ex., liftTy Γ A')) ([idMor]Ty B))
                                                             (ap (λ x → liftTm _ (liftTy _ x) _) ([idMor]Ty B)
                                                            ∙ ap (liftTm _ _) ([idMor]Tm u))
                                    ([]-liftTm2 (dΓ ex., (ex.TyEqTy2 dΓ dA=))
                                                (dΓ ex., (ex.TyEqTy1 dΓ dA=))
                                                (ex.TmTy (dΓ ex., ex.TyEqTy1 dΓ dA=) du)
                                                du
                                                (weakenMor-liftᵈ (idMorDerivableLift dΓ) ex., ex.Conv (ex.WeakTy (ex.TyEqTy2 dΓ dA=))
                                                                                                      (ex.SubstTy (ex.TyEqTy1 dΓ dA=) (weakenMor-liftᵈ (idMorDerivableLift dΓ)))
                                                                                                      (ex.VarLast (ex.TyEqTy2 dΓ dA=))
                                                                                                      (ex.congTyEq refl
                                                                                                                   (ex.weaken[]Ty _ _ _ ∙ ex.ap[]Ty refl (! (weakenMor-liftMor Γ Γ _ _)))
                                                                                                                   (ex.WeakTyEq ([idmor-lift]Ty dΓ (ex.TySymm dA=))))))   

----------------------------
---- Lemmas needed for CoercTm Equality Statements. They will also be useful in the lifting
----------------------------
coercTy-getTy-liftᵈ : {Γ : ex.Ctx n} {A A' : TyExpr n} {u : TmExpr (suc n)}
          → ex.⊢ Γ
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A == liftTy Γ A')
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTm1 (Γ ex., liftTy Γ A) u :> ex.getTy (Γ ex., liftTy Γ A) (liftTm1 (Γ ex., liftTy Γ A) u))
          → ex.Derivable ((Γ ex., liftTy Γ A') ⊢ₑ ex.getTy (Γ ex., liftTy Γ A') (liftTm1 (Γ ex., liftTy Γ A') u))
coercTy-getTy-liftᵈ {Γ = Γ} {A} {A'} {u} dΓ dA= du = ex.congTy (ex.ap-getTy {u' = liftTm1 (Γ ex., liftTy Γ A') u} refl (ap (liftTm1 _) ([idMor]Tm _)) )
                                                              (getTy-[]-lift (dΓ ex., dA') (dΓ ex., dA) du
                                                                             (weakenMor-liftᵈ (idMorDerivableLift dΓ) ex., ex.Conv (ex.WeakTy dA')
                                                                                                                    (ex.SubstTy dA (weakenMor-liftᵈ (idMorDerivableLift dΓ)))
                                                                                                                    (ex.VarLast dA')
                                                                                                                    (ex.congTyEq refl (ex.weaken[]Ty _ _ _
                                                                                                                                      ∙ ex.ap[]Ty refl (! (weakenMor-liftMor _ _ _ _)))
                                                                                                                                 (ex.WeakTyEq ([idmor-lift]Ty dΓ (ex.TySymm dA=)))) ))
                              where
                              dA = ex.TyEqTy1 dΓ dA=
                              dA' = ex.TyEqTy2 dΓ dA=
coercTy-getTy-lift⁼ :  {Γ : ex.Ctx n} {A A' : TyExpr n} {u : TmExpr (suc n)}
          → ex.⊢ Γ
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A == liftTy Γ A')
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTm1 (Γ ex., liftTy Γ A) u :> ex.getTy (Γ ex., liftTy Γ A) (liftTm1 (Γ ex., liftTy Γ A) u))
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ ex.getTy (Γ ex., liftTy Γ A) (liftTm1 (Γ ex., liftTy Γ A) u)
                                              == ex.coercTy (ex.getTy (Γ ex., liftTy Γ A') (liftTm1 (Γ ex., liftTy Γ A') u)) (liftTy Γ A') (liftTy Γ A))
coercTy-getTy-lift⁼ {Γ = Γ} {A} {A'} {u} dΓ dA= du
                       = ex.TyTran (ex.SubstTy (ex.TmTy (dΓ ex., dA') du') (ex.WeakMor (idMorDerivableLift dΓ) ex.,  ex.congTmTy (ex.weaken[]Ty _ _ _)
                                                                                                                             (ex.Conv (ex.WeakTy dA)
                                                                                                                             (ex.WeakTy (ex.SubstTy dA' (idMorDerivableLift dΓ)) )
                                                                                                                             (ex.VarLast dA)
                                                                                                                             (ex.congTyEq (ap ex.weakenTy (ex.[idMor]Ty _)) refl
                                                                                                                                          (ex.WeakTyEq (ex.SubstTyFullEq dΓ dΓ dA=
                                                                                                                                                         (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ))))))))
                                   (ex.congTyEq (ex.ap-getTy {Γ' = Γ ex., liftTy Γ A} {u' = liftTm1 (Γ ex., liftTy Γ A) u}
                                                             refl (ap (λ x → liftTm1 (Γ ex., liftTy Γ A) x) ([idMor]Tm u)))
                                                (ex.ap[]Ty refl (ex.Mor+= (weakenMor-liftMor Γ Γ _ _)
                                                                          (ex.ap-coerc-Tm refl (ex.ap[]Ty refl
                                                                                                          (weakenMor-liftMor Γ Γ _ _) ∙ ! (ex.weaken[]Ty _ _ _))
                                                                                          refl)))
                                                (getTy-[]-lift⁼ (dΓ ex., dA) (dΓ ex., dA') du'
                                                                (weakenMor-liftᵈ (idMorDerivableLift dΓ)
                                                                            ex., ex.Conv (ex.WeakTy dA)
                                                                                         (ex.SubstTy dA' (weakenMor-liftᵈ (idMorDerivableLift dΓ)))
                                                                                         (ex.VarLast dA)
                                                                                         (ex.congTyEq (ap ex.weakenTy (ex.[idMor]Ty _))
                                                                                                      (ex.weaken[]Ty _ _ _ ∙ ex.ap[]Ty refl
                                                                                                                          (! (weakenMor-liftMor Γ Γ _ _)))
                                                                                                      (ex.WeakTyEq (ex.SubstTyFullEq dΓ dΓ dA=
                                                                                                                       (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ))))))))
                                   (ex.SubstTyMorEq1 (dΓ ex., dA) (dΓ ex., dA') (ex.TmTy (dΓ ex., dA') du')
                                                     (ex.WeakMorEq (idmor-lift⁼ dΓ) ex.,
                                                                   ex.congTmEq refl (ex.ap-coerc-Tm (ap ex.weakenTy (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _)
                                                                                                    (ex.weaken[]Ty _ _ _)
                                                                                                    refl)
                                                                               (ex.weaken[]Ty _ _ _)
                                                                               (ex.TmSymm (ex.CoercTrans (ex.WeakTy dA) (ex.WeakTy dA')
                                                                                                         (ex.WeakTy (ex.SubstTy dA' (idMorDerivableLift dΓ)))
                                                                                                         (ex.VarLast dA) (ex.WeakTyEq dA=)
                                                                                                         (ex.WeakTyEq (ex.congTyEq (ex.[idMor]Ty _) refl
                                                                                                                                   (ex.SubstTyMorEq1 dΓ dΓ dA'
                                                                                                                                                     (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ)))))))))
                                   where
                                   dA = ex.TyEqTy1 dΓ dA=
                                   dA' = ex.TyEqTy2 dΓ dA=
                                   du' = coercTm1-liftᵈ dΓ dA= du

coercTm1-lift⁼ : {Γ : ex.Ctx n} {A A' : TyExpr n} {u : TmExpr (suc n)}
          → ex.⊢ Γ
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A)
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A')
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A == liftTy Γ A')
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTm1 (Γ ex., liftTy Γ A) u :> ex.getTy (Γ ex., liftTy Γ A) (liftTm1 (Γ ex., liftTy Γ A) u))
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ (ex.coercTm (liftTm1 (Γ ex., liftTy Γ A') u) (liftTy Γ A') (liftTy Γ A))
                                                                      == ex.coerc (ex.getTy (Γ ex., liftTy Γ A) (liftTm1 (Γ ex., liftTy Γ A) u))
                                                                                  (ex.coercTy (ex.getTy (Γ ex., liftTy Γ A') (liftTm1 (Γ ex., liftTy Γ A') u)) (liftTy Γ A') (liftTy Γ A))
                                                                                  (liftTm1 (Γ ex., liftTy Γ A) u)
                                                                      :> ex.coercTy (ex.getTy (Γ ex., liftTy Γ A') (liftTm1 (Γ ex., liftTy Γ A') u)) (liftTy Γ A') (liftTy Γ A))

coercTm1-lift⁼ {Γ = Γ} {A} {A'} {u} dΓ dA dA' dA= du
               = ex.congTmEq refl
                     refl
                     refl
                     (ex.TmTran (ex.Conv (ex.SubstTy (ex.Derivable-getTy (coercTm1-liftᵈ dΓ dA= du) (dΓ ex., dA')) Morphism1)
                                         (ex.CoercTy dΓ dA' dA (ex.Derivable-getTy (coercTm1-liftᵈ dΓ dA= du) (dΓ ex., dA')) (ex.TySymm dA=))
                                         (ex.SubstTm (coercTm1-liftᵈ dΓ dA= du) Morphism1)
                                         (ex.SubstTyMorEq1 (dΓ ex., dA) (dΓ ex., dA') (ex.TmTy (dΓ ex., dA') (coercTm1-liftᵈ dΓ dA= du)) (ex.MorSymm (dΓ ex., dA) (dΓ ex., dA') Morphism1Eq)))
                         (ex.SubstTmMorEq1 (dΓ ex., dA)
                                           (dΓ ex., dA')
                                           (coercTm1-liftᵈ dΓ dA= du)
                                           Morphism1Eq)
                         (ex.TmTran (ex.Conv (ex.SubstTy (ex.Derivable-getTy (coercTm1-liftᵈ dΓ dA= du) (dΓ ex., dA')) Morphism1)
                                             (ex.CoercTy dΓ dA' dA (ex.TmTy (dΓ ex., dA') (coercTm1-liftᵈ dΓ dA= du)) (ex.TySymm dA=))
                                             (ex.Conv (ex.TmTy (dΓ ex., dA) du)
                                                      (ex.SubstTy (ex.TmTy (dΓ ex., dA') (coercTm1-liftᵈ dΓ dA= du)) Morphism1)
                                                      du
                                                      (ex.TyTran (ex.CoercTy dΓ dA' dA (ex.TmTy (dΓ ex., dA') (coercTm1-liftᵈ dΓ dA= du)) (ex.TySymm dA=))
                                                                 (coercTy-getTy-lift⁼ dΓ dA= du)
                                                                 (ex.SubstTyMorEq1 (dΓ ex., dA) (dΓ ex., dA') (ex.TmTy (dΓ ex., dA') (coercTm1-liftᵈ dΓ dA= du)) Morphism1Eq)))
                                             (ex.SubstTyMorEq1 (dΓ ex., dA) (dΓ ex., dA') (ex.TmTy (dΓ ex., dA') (coercTm1-liftᵈ dΓ dA= du)) (ex.MorSymm (dΓ ex., dA) (dΓ ex., dA') Morphism1Eq)))
                                    (ex.ConvEq (ex.SubstTy (ex.TmTy (dΓ ex., dA') (coercTm1-liftᵈ dΓ dA= du)) Morphism1)
                                               (ex.congTmEq (ex.ap[]Tm {u = liftTm1 (Γ ex., liftTy Γ A') u} refl (ex.Mor+= (weakenMor-liftMor Γ Γ _ _)
                                                              (ex.ap-coerc-Tm refl (ex.ap[]Ty refl (weakenMor-liftMor Γ Γ _ _) ∙ ! (ex.weaken[]Ty _ _ _)) refl)))
                                                   (ex.ap-coerc-Tm (ex.ap-getTy {Γ = Γ ex., liftTy Γ A} refl (ap (liftTm1 _) ([idMor]Tm u)))
                                                                   (ex.ap[]Ty refl (ex.Mor+= (weakenMor-liftMor Γ Γ _ _)
                                                                                             (ex.ap-coerc-Tm refl
                                                                                                        (ex.ap[]Ty refl (weakenMor-liftMor Γ Γ _ _)
                                                                                                                   ∙ ! (ex.weaken[]Ty _ _ _))
                                                                                                        refl)))
                                                                   (ap (liftTm1 _) ([idMor]Tm _)))
                                                   (ex.ap[]Ty refl (ex.Mor+= (weakenMor-liftMor Γ Γ _ _)
                                                                                             (ex.ap-coerc-Tm refl
                                                                                                        (ex.ap[]Ty refl (weakenMor-liftMor Γ Γ _ _)
                                                                                                                   ∙ ! (ex.weaken[]Ty _ _ _))
                                                                                                        refl)))
                                                   ([]-liftTm1⁼ (dΓ ex., dA) (dΓ ex., dA') (coercTm1-liftᵈ dΓ dA= du)
                                                                (weakenMor-liftᵈ (idMorDerivableLift dΓ) ex., ex.Conv (ex.WeakTy dA)
                                                                                                 (ex.SubstTy dA'
                                                                                                 (weakenMor-liftᵈ (idMorDerivableLift dΓ)))
                                                                                                 (ex.VarLast dA)
                                                                                                 (ex.congTyEq (ap (ex.weakenTy) (ex.[idMor]Ty _))
                                                                                                         (ex.weaken[]Ty _ _ _
                                                                                                           ∙ ex.ap[]Ty refl (! (weakenMor-liftMor Γ Γ _ _)))
                                                                                                         (ex.WeakTyEq (ex.SubstTyFullEq dΓ dΓ dA= (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ))))))))
                                               (ex.SubstTyMorEq1 (dΓ ex., dA) (dΓ ex., dA') (ex.Derivable-getTy (coercTm1-liftᵈ dΓ dA= du) (dΓ ex., dA'))
                                                   (ex.WeakMorEq (idmor-lift⁼ dΓ) ex., ex.congTmEq refl
                                                                                           (ex.ap-coerc-Tm (ap ex.weakenTy (! (ex.[idMor]Ty _))
                                                                                                ∙ ex.weaken[]Ty _ _ _)
                                                                                                (ex.weaken[]Ty _ _ _) refl)
                                                                                           (ex.weaken[]Ty _ _ _)
                                                                                           (ex.TmSymm (ex.CoercTrans (ex.WeakTy dA)
                                                                                                (ex.WeakTy dA')
                                                                                                (ex.WeakTy (ex.SubstTy dA' (idMorDerivableLift dΓ)))
                                                                                                (ex.VarLast dA)
                                                                                                (ex.WeakTyEq dA=)
                                                                                                (ex.WeakTyEq (ex.congTyEq (ex.[idMor]Ty _) refl
                                                                                                                 (ex.SubstTyMorEq1 dΓ dΓ dA' (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ))))))))))
                                    (ex.CoercTrans (ex.Derivable-getTy du (dΓ ex., dA))
                                                   (ex.SubstTy (ex.Derivable-getTy (coercTm1-liftᵈ dΓ dA= du) (dΓ ex., dA'))
                                                               Morphism1)
                                                   (ex.CoercTy dΓ dA' dA (ex.Derivable-getTy (coercTm1-liftᵈ dΓ dA= du) (dΓ ex., dA')) (ex.TySymm dA=))
                                                   du
                                                   (ex.TyTran (ex.CoercTy dΓ dA' dA (ex.Derivable-getTy (coercTm1-liftᵈ dΓ dA= du) (dΓ ex., dA')) (ex.TySymm dA=))
                                                              (coercTy-getTy-lift⁼ dΓ dA= du)
                                                              (ex.SubstTyMorEq1 (dΓ ex., dA) (dΓ ex., dA') (ex.Derivable-getTy (coercTm1-liftᵈ dΓ dA= du) (dΓ ex., dA'))
                                                              (ex.WeakMorEq (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ))
                                                                     ex., ex.congTmEq refl (ex.ap-coerc-Tm (ex.weaken[]Ty _ _ _) (ap ex.weakenTy (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _) refl)
                                                                                      (ap ex.weakenTy (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _)
                                                                                      (ex.TmSymm (ex.CoercTrans (ex.WeakTy dA) (ex.WeakTy (ex.SubstTy dA' (idMorDerivableLift dΓ)))
                                                                                                                (ex.WeakTy dA') (ex.VarLast dA)
                                                                                                                (ex.WeakTyEq (ex.congTyEq (ex.[idMor]Ty _) refl
                                                                                                                                  (ex.SubstTyFullEq dΓ dΓ dA= (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ)))))
                                                                                                                (ex.WeakTyEq (ex.congTyEq refl (ex.[idMor]Ty _)
                                                                                                                             (ex.SubstTyMorEq1 dΓ dΓ dA' (idmor-lift⁼ dΓ)))))) )))
                                                   (ex.SubstTyMorEq1 (dΓ ex., dA)
                                                                     (dΓ ex., dA')
                                                                     (ex.Derivable-getTy (coercTm1-liftᵈ dΓ dA= du) (dΓ ex., dA'))
                                                                     (ex.WeakMorEq (idmor-lift⁼ dΓ) ex., ex.congTmEq refl
                                                                                                 (ex.ap-coerc-Tm (ap ex.weakenTy (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _)
                                                                                                                 (ex.weaken[]Ty _ _ _) refl)
                                                                                                 (ex.weaken[]Ty _ _ _)
                                                                                                 (ex.TmSymm (ex.CoercTrans (ex.WeakTy dA)
                                                                                                                           (ex.WeakTy dA')
                                                                                                                           (ex.WeakTy (ex.SubstTy dA' (idMorDerivableLift dΓ)))
                                                                                                                           (ex.VarLast dA)
                                                                                                                           (ex.WeakTyEq dA=)
                                                                                                                           (ex.WeakTyEq (ex.congTyEq (ex.[idMor]Ty _) refl
                                                                                                                                            (ex.SubstTyMorEq1 dΓ dΓ dA' (ex.MorSymm dΓ dΓ
                                                                                                                                                                     (idmor-lift⁼ dΓ))))))))))))
                                              where
                                              Morphism1 : (Γ ex., liftTy Γ A) ex.⊢ ex.weakenMor (liftMor Γ Γ (idMor _)) ex., ex.coerc (ex.weakenTy (liftTy Γ A))
                                                                                                                                 (ex.weakenTy' last (liftTy1 Γ A' ex.[ liftMor Γ Γ (idMor _) ]Ty))
                                                                                                                                 (ex.var last)
                                                                                 ∷> (Γ ex., liftTy Γ A')

                                              Morphism1 = ex.WeakMor (idMorDerivableLift dΓ) ex., ex.congTmTy (ex.weaken[]Ty _ _ _)
                                                                                                                    (ex.Conv (ex.WeakTy dA)
                                                                                                                             (ex.WeakTy (ex.SubstTy dA' (idMorDerivableLift dΓ)) )
                                                                                                                             (ex.VarLast dA)
                                                                                                                             (ex.congTyEq (ap ex.weakenTy (ex.[idMor]Ty _)) refl
                                                                                                                                          (ex.WeakTyEq (ex.SubstTyFullEq dΓ dΓ dA=
                                                                                                                                                         (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ))))))
                                              Morphism1Eq : (Γ ex., liftTy Γ A) ex.⊢ ex.weakenMor (ex.idMor _) ex., ex.coerc (ex.weakenTy (liftTy Γ A)) (ex.weakenTy (liftTy Γ A')) (ex.var last)
                                                                                   == ex.weakenMor (liftMor Γ Γ (idMor _)) ex., ex.coerc (ex.weakenTy (liftTy Γ A))
                                                                                                                                   (ex.weakenTy' last (liftTy1 Γ A' ex.[ liftMor Γ Γ (idMor _) ]Ty))
                                                                                                                                   (ex.var last)
                                                                                   ∷> (Γ ex., liftTy Γ A')
                                                                                                          
                                              Morphism1Eq = ex.WeakMorEq (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ))
                                                          ex., ex.congTmEq refl
                                                                      (ex.ap-coerc-Tm (ex.weaken[]Ty _ _ _)
                                                                                      (ap ex.weakenTy (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _)
                                                                                      refl)
                                                                      (ap ex.weakenTy (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _)
                                                                      (ex.TmSymm (ex.CoercTrans (ex.WeakTy dA) (ex.WeakTy (ex.SubstTy dA' (idMorDerivableLift dΓ))) (ex.WeakTy dA') (ex.VarLast dA)
                                                                                                (ex.WeakTyEq (ex.congTyEq (ex.[idMor]Ty _) refl
                                                                                                                          (ex.SubstTyFullEq dΓ dΓ dA= (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ)))))
                                                                                                (ex.WeakTyEq (ex.congTyEq refl (ex.[idMor]Ty _) (ex.SubstTyMorEq1 dΓ dΓ dA' (idmor-lift⁼ dΓ))))))

coercTm-lift⁼ : {Γ : ex.Ctx n} {A A' : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
          → ex.⊢ Γ
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A == liftTy Γ A')
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) u :> liftTy (Γ ex., liftTy Γ A) B)
          → ex.Derivable ((Γ ex., liftTy Γ A) ⊢ₑ liftTm (Γ ex., liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) u
                                                                      == ex.coerc (ex.coercTy (liftTy (Γ ex., liftTy Γ A') B) (liftTy Γ A') (liftTy Γ A))
                                                                                  (liftTy (Γ ex., liftTy Γ A) B)
                                                                                  (ex.coercTm (liftTm (Γ ex., liftTy Γ A') (liftTy (Γ ex., liftTy Γ A') B) u)
                                                                                              (liftTy Γ A')
                                                                                              (liftTy Γ A))
                                                                      :> (liftTy (Γ ex., liftTy Γ A) B))

coercTm-lift⁼ dΓ dA= du = ex.TmTran (ex.Conv (ex.coercInvTy1 du) dB
                                             (ex.Conv (ex.CoercTy dΓ dA' dA (ex.coercInvTy1 du') (ex.TySymm dA=))
                                                      (ex.coercInvTy1 du)
                                                      (ex.CoercTm dΓ dA' dA (ex.coercInvTm du') (ex.TySymm dA=))
                                                      (ex.TySymm (coercTy-getTy-lift⁼ dΓ dA= (ex.coercInvTm du))))
                                                      (ex.coercInvEq du))
                                    (ex.ConvEq (ex.coercInvTy1 du)
                                               (ex.coercSymm (dΓ ex., dA) (ex.TmSymm (coercTm1-lift⁼ dΓ (ex.TyEqTy1 dΓ dA=) (ex.TyEqTy2 dΓ dA=) dA= (ex.coercInvTm du))))
                                               (ex.coercInvEq du))
                                    (ex.TmTran (ex.Conv (ex.CoercTy dΓ dA' dA (ex.coercInvTy1 du') (ex.TySymm dA=))
                                                        dB
                                                        (ex.CoercTm dΓ dA' dA (ex.coercInvTm du') (ex.TySymm dA=))
                                                                    (ex.TyTran (ex.CoercTy dΓ dA' dA dB' (ex.TySymm dA=))
                                                                               (ex.CoercTyEq dΓ (ex.TySymm dA=) (ex.coercInvEq du'))
                                                                               (ex.TySymm (coercTy-lift⁼ dΓ dA= dB))))
                                               (ex.CoercTrans (ex.CoercTy dΓ dA' dA (ex.coercInvTy1 du') (ex.TySymm dA=))
                                                              (ex.coercInvTy1 du)
                                                              (ex.TmTy (dΓ ex., dA) du)
                                                              (ex.CoercTm dΓ dA' dA (ex.coercInvTm du') (ex.TySymm dA=))
                                                              (ex.TySymm (coercTy-getTy-lift⁼ dΓ dA= (ex.coercInvTm du)) )
                                                              (ex.coercInvEq du))
                                               (ex.TmSymm (ex.CoercTrans (ex.SubstTy (ex.coercInvTy1 du') COERCMOR)
                                                                         (ex.CoercTy dΓ dA' dA dB' (ex.TySymm dA=))
                                                                         dB
                                                                         (ex.SubstTm (ex.coercInvTm du') COERCMOR)
                                                                         (ex.CoercTyEq dΓ (ex.TySymm dA=) (ex.coercInvEq du'))
                                                                         (ex.TySymm (coercTy-lift⁼ dΓ dA= dB)))))
                        where
                        dA = ex.TyEqTy1 dΓ dA=
                        dA' = ex.TyEqTy2 dΓ dA=
                        du' = coercTm-liftᵈ dΓ dA= du 
                        dB = ex.coercInvTy2 du
                        dB' = ex.coercInvTy2 du'
                        COERCMOR = ex.WeakMor (ex.idMorDerivable dΓ) ex., ex.congTmTy (ap ex.weakenTy (! (ex.[idMor]Ty _)) ∙ ex.weaken[]Ty _ _ _)
                                                                                      (ex.Conv (ex.WeakTy dA) (ex.WeakTy dA') (ex.VarLast dA) (ex.WeakTyEq dA=))
---------------------------------------------------------
--------------- Perhaps necessary Context conversion results
---------------------------------------------------------

liftTyCtxEq : {Γ Γ' : ex.Ctx n} {A : TyExpr n} 
          → ex.⊢ Γ → ex.⊢ Γ' → ex.⊢ Γ == Γ' 
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A)
          → ex.Derivable (Γ' ⊢ₑ liftTy Γ' A)
          → ex.Derivable (Γ ⊢ₑ liftTy Γ A == ex.coercCtxTy Γ' Γ (liftTy Γ' A))

liftTm1CtxEq : {Γ Γ' : ex.Ctx n} {u : TmExpr n}
          → ex.⊢ Γ → ex.⊢ Γ' → ex.⊢ Γ == Γ'
          → ex.Derivable (Γ ⊢ₑ liftTm1 Γ u :> ex.getTy Γ (liftTm1 Γ u))
          → ex.Derivable (Γ' ⊢ₑ liftTm1 Γ' u :> ex.getTy Γ' (liftTm1 Γ' u))
          → ex.Derivable (Γ ⊢ₑ liftTm1 Γ u == ex.coerc (ex.coercCtxTy Γ' Γ (ex.getTy Γ' (liftTm1 Γ' u)))
                                                        (ex.getTy Γ (liftTm1 Γ u))
                                                        (ex.coercCtxTm Γ' Γ (liftTm1 Γ' u)) :> ex.getTy Γ (liftTm1 Γ u))

getTyCtxEq : {Γ Γ' : ex.Ctx n} {u : TmExpr n}
          → ex.⊢ Γ → ex.⊢ Γ' → ex.⊢ Γ == Γ'
          → ex.Derivable (Γ ⊢ₑ liftTm1 Γ u :> ex.getTy Γ (liftTm1 Γ u))
          → ex.Derivable (Γ' ⊢ₑ liftTm1 Γ' u :> ex.getTy Γ' (liftTm1 Γ' u))
          → ex.Derivable (Γ ⊢ₑ ex.getTy Γ (liftTm1 Γ u) == ex.coercCtxTy Γ' Γ (ex.getTy Γ' (liftTm1 Γ' u)))

liftTyCtxEq {A = uu} dΓ dΓ' dΓ= dA1 dA2 = ex.UUCong
liftTyCtxEq {A = el v} dΓ dΓ' dΓ= dA1 dA1 = ex.ElCong {!!}
liftTyCtxEq {Γ = Γ} {Γ'} {A = pi A B} dΓ dΓ' dΓ= (ex.Pi dA dB) (ex.Pi dA' dB') = ex.PiCong {!!}
                                                    {!!}
                                                    {!!}
                                                    {!!}
                                                    (liftTyCtxEq dΓ dΓ' dΓ= dA dA')
                                                    (ex.congTyEq refl
                                                                 (ex.ap[]Ty refl (ex.Mor+= ((ap ex.weakenMor (! (ex.[idMor]Mor _)) ∙ ex.weaken[]Mor _ _ _)
                                                                                                ∙ ! (ex.weakenMorInsert (ex.ConvMor Γ Γ') _ _))
                                                                                           (ex.ap-coerc-Tm refl (! (ex.weaken[]Ty _ _ _)) refl))
                                                                                  ∙ ! (ex.[]Ty-assoc _ _ (liftTy1 (Γ' ex., liftTy Γ' A) B)))
                                                                 (liftTyCtxEq (dΓ ex., dA)
                                                                              (dΓ' ex., dA')
                                                                              (dΓ= ex., liftTyCtxEq dΓ dΓ' dΓ= dA dA')
                                                                              dB
                                                                              dB'))

liftTm1CtxEq {Γ = Γ ex., A} {Γ' ex., A'} {var last} (dΓ ex., dA) (dΓ' ex., dA') (dΓ= ex., dA=) du du'
                            = ex.congTmEq refl
                                          (ex.ap-coerc-Tm (ex.weaken[]Ty _ _ _ ∙ ! (ex.weakenTyInsert A' _ _))
                                                          refl
                                                          (ex.ap-coerc-Tm refl
                                                                          (ex.weaken[]Ty _ _ _)
                                                                          refl))
                                          refl
                                          (ex.TmTran {!!}
                                                     {!!}
                                                     (ex.TmSymm (ex.CoercTrans (ex.WeakTy dA)
                                                                               (ex.WeakTy (ex.SubstTy dA' (ex.ConvMor-Derivable dΓ dΓ' dΓ=)))
                                                                               (ex.WeakTy dA)
                                                                               (ex.VarLast dA)
                                                                               (ex.WeakTyEq dA=)
                                                                               (ex.WeakTyEq (ex.TySymm dA=)))))
liftTm1CtxEq {u = var (prev x)} dΓ dΓ' dΓ= du du' = {!!}
liftTm1CtxEq {u = lam A B u} dΓ dΓ' dΓ= du du' = {!!}
liftTm1CtxEq {u = app A B u u₁} dΓ dΓ' dΓ= du du' = {!!}

getTyCtxEq dΓ dΓ' dΓ= du du' = {!!}

----------------------------------------------------------
------------ Main Theorem
----- In any case the proof idea is to use the same explicit version of the rule (case distinction over rules), and then make the outermost coercions work.
----- To make the outermost coercions work is the more difficult part. 
----------------------------------------------------------

Lift-Der : {jdg : Judgment} → ex.⊢ liftCtx (snd (getCtx jdg)) → Derivable (jdg) → ex.Derivable (liftJdg jdg)

Lift-TyEq : {Γ Γ' : Ctx n} {A A' : TyExpr n}
          → ex.⊢ liftCtx Γ
          → ex.⊢ liftCtx Γ'
          → ex.⊢ liftCtx Γ == liftCtx Γ'
          → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) A)
          → ex.Derivable (liftCtx Γ' ⊢ₑ liftTy (liftCtx Γ') A')
          → Derivable (Γ ⊢ A == A')
          → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) A == ex.coercCtxTy (liftCtx Γ') (liftCtx Γ) (liftTy (liftCtx Γ') A'))

Lift-TyEq-Triv : {Γ : Ctx n} {A A' : TyExpr n}
          → ex.⊢ liftCtx Γ
          → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) A)
          → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) A')
          → Derivable (Γ ⊢ A == A')
          → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) A == liftTy (liftCtx Γ) A')

Lift-TyEq-Ext : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)}
         → ex.⊢ liftCtx Γ
         → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) A)
         → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) A')
         → ex.Derivable ((liftCtx (Γ , A)) ⊢ₑ liftTy (liftCtx (Γ , A)) B)
         → ex.Derivable ((liftCtx (Γ , A')) ⊢ₑ liftTy (liftCtx (Γ , A')) B')
         → Derivable (Γ ⊢ A == A')
         → Derivable ((Γ , A) ⊢ B == B')
         → ex.Derivable ((liftCtx Γ ex., (liftTy (liftCtx Γ) A)) ⊢ₑ liftTy (liftCtx Γ ex., liftTy (liftCtx Γ) A) B' == ex.coercTy (liftTy (liftCtx Γ ex., liftTy (liftCtx Γ) A') B') (liftTy (liftCtx Γ) A') (liftTy (liftCtx Γ) A))

Lift-TyEq-Ext {B' = B'} dΓ dA dA' dB dB' dA= dB= = {!B'!}

Lift-Der (dΓ ex., dA) (VarLast {Γ = Γ} {A = A} dj) 
                  rewrite weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) A
                  = ex.Conv
                    (ex.WeakTy (Lift-Der dΓ dj))
                    ( ex.WeakTy (Lift-Der dΓ dj)) ( ex.VarLast (Lift-Der dΓ dj))
                    (ex.TyRefl (ex.WeakTy (Lift-Der dΓ dj)))
Lift-Der (dΓ ex., dA) (VarPrev {Γ = Γ} {B = B} {A = A} dA dk) 
                     = ex.congTm (! (weakenTy-liftTy (liftCtx Γ) (liftTy (liftCtx Γ) B) A)) (ex.ap-coerc-Tm refl (! (weakenTy-liftTy _ _ _)) refl) (ex.WeakTm (Lift-Der dΓ dk))
Lift-Der (dΓ ex., dA) (VarLastCong {Γ = Γ} {A = A} dj) =
                      ex.ConvEq (ex.WeakTy (Lift-Der dΓ dj))
                                (ex.TmRefl (ex.VarLast (Lift-Der dΓ dj)))
                                (ex.congTyEq refl (! (weakenTy-liftTy (liftCtx Γ) (liftTy (liftCtx Γ) A) A))
                                (ex.TyRefl (ex.WeakTy (Lift-Der dΓ dj))))
-- ex.getTy (ex.var k) == ex.getTy (ex.var k')
Lift-Der (dΓ ex., dB) (VarPrevCong {Γ = Γ} {B = B} {A = A} dj dj₁)
         = ex.congTmEq (ex.ap-coerc-Tm refl (! (weakenTy-liftTy _ _ A)) refl)
                       (ex.ap-coerc-Tm refl (! (weakenTy-liftTy _ _ A)) refl)
                       (! (weakenTy-liftTy _ _ A))
                       (ex.WeakTmEq (Lift-Der dΓ dj₁))
Lift-Der dΓ (TySymm dj) = ex.TySymm (Lift-Der dΓ dj)
Lift-Der dΓ (TyTran dj dj₁ dj₂) = ex.TyTran (Lift-Der dΓ dj) (Lift-Der dΓ dj₁) (Lift-Der dΓ dj₂)
Lift-Der dΓ (TmSymm dj) = ex.TmSymm (Lift-Der dΓ dj)
Lift-Der dΓ (TmTran dv du= dv=) = ex.TmTran (Lift-Der dΓ dv) (Lift-Der dΓ du=) (Lift-Der dΓ dv=)
Lift-Der dΓ (Conv {u = var x} {A} {B} dA dB du dA=) =  ex.Conv (ex.coercInvTy1 (Lift-Der dΓ du)) (Lift-Der dΓ dB) (ex.coercInvTm (Lift-Der dΓ du)) (ex.TyTran (Lift-Der dΓ dA) (ex.coercInvEq (Lift-Der dΓ du)) (Lift-Der dΓ dA=))
Lift-Der dΓ (Conv {u = lam A₁ B₁ u} {A} {B} dA dB du dA=) =  ex.Conv (ex.coercInvTy1 (Lift-Der dΓ du)) (Lift-Der dΓ dB) (ex.coercInvTm (Lift-Der dΓ du)) (ex.TyTran (Lift-Der dΓ dA) (ex.coercInvEq (Lift-Der dΓ du)) (Lift-Der dΓ dA=))
Lift-Der dΓ (Conv {u = app A₁ B₁ u u₁} {A} {B} dA dB du dA=) =  ex.Conv (ex.coercInvTy1 (Lift-Der dΓ du)) (Lift-Der dΓ dB) (ex.coercInvTm (Lift-Der dΓ du)) (ex.TyTran (Lift-Der dΓ dA) (ex.coercInvEq (Lift-Der dΓ du)) (Lift-Der dΓ dA=))
-- ex.Conv (ex.coercInvTy1 (Lift-Der du)) (Lift-Der dB) (ex.coercInvTm (Lift-Der du)) (ex.TyTran (Lift-Der dA) (ex.coercInvEq (Lift-Der du)) (Lift-Der dA=))
Lift-Der dΓ (ConvEq dA du= dA=) = ex.TmTran (ex.Conv dA-Lift dB-Lift du-Lift dA=-Lift)
                                            (ex.TmSymm (ex.CoercTrans (ex.coercInvTy1 du-Lift) dA-Lift dB-Lift (ex.coercInvTm du-Lift) (ex.coercInvEq du-Lift) dA=-Lift))
                                            (ex.TmTran (ex.Conv dA-Lift dB-Lift du'-Lift dA=-Lift)
                                                       (ex.ConvEq dA-Lift du=-Lift dA=-Lift)
                                                       (ex.CoercTrans (ex.coercInvTy1 du'-Lift) dA-Lift dB-Lift (ex.coercInvTm du'-Lift) (ex.coercInvEq du'-Lift) dA=-Lift))
                                where
                                dA-Lift = Lift-Der dΓ dA
                                du-Lift = ex.TmEqTm1 dΓ (Lift-Der dΓ du=)
                                du'-Lift = ex.TmEqTm2 dΓ (Lift-Der dΓ du=)
                                dB-Lift = ex.TyEqTy2 dΓ (Lift-Der dΓ dA=)
                                du=-Lift = Lift-Der dΓ du=
                                dA=-Lift = Lift-Der dΓ dA=
Lift-Der dΓ UU = ex.UU
Lift-Der dΓ UUCong = ex.UUCong
Lift-Der dΓ (El dv) = ex.El (Lift-Der dΓ dv)
Lift-Der dΓ (ElCong dv=) = ex.ElCong (Lift-Der dΓ dv=)
Lift-Der dΓ (Pi dA dB) = ex.Pi (Lift-Der dΓ dA) (Lift-Der (dΓ ex., (Lift-Der dΓ dA)) dB)
Lift-Der dΓ (PiCong dA dA= dB=) = ex.PiCong (Lift-Der dΓ dA)
                                            dA'-Lift
                                            dB-Lift
                                            (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift)
                                            dA=-Lift
                                            (ex.TyTran dB'-Lift
                                                       (Lift-Der (dΓ ex., Lift-Der dΓ dA) dB=)
                                                       (coercTy-lift⁼ dΓ (Lift-Der dΓ dA=) dB'-Lift))
                                    where
                                    dA-Lift = Lift-Der dΓ dA
                                    dA'-Lift = ex.TyEqTy2 dΓ (Lift-Der dΓ dA=)
                                    dB-Lift = ex.TyEqTy1 (dΓ ex., dA-Lift) (Lift-Der (dΓ ex., dA-Lift) dB=)
                                    dB'-Lift = ex.TyEqTy2 (dΓ ex., dA-Lift) (Lift-Der (dΓ ex., dA-Lift) dB=)
                                    dA=-Lift = Lift-Der dΓ dA=
                                    dB=-Lift = Lift-Der (dΓ ex., dA-Lift) dB=
Lift-Der dΓ (Lam dA dB du) = ex.Conv (ex.Pi dA-Lift dB-Lift)
                                     (ex.Pi dA-Lift dB-Lift)
                                     (ex.Lam dA-Lift dB-Lift du-Lift)
                                     (ex.TyRefl (ex.Pi dA-Lift dB-Lift))
                                    where
                                    dA-Lift = Lift-Der dΓ dA
                                    dB-Lift = Lift-Der (dΓ ex., dA-Lift) dB
                                    du-Lift = Lift-Der (dΓ ex., dA-Lift) du
Lift-Der dΓ (LamCong dA dA= dB= du=) = ex.TmTran (ex.Lam dA-Lift dB-Lift du-Lift)
                                                 (ex.CoercRefl (ex.Lam dA-Lift dB-Lift du-Lift))
                                                 (ex.LamCong dA-Lift
                                                             dA'-Lift
                                                             dB-Lift
                                                             (coercTy-liftᵈ dΓ (Lift-Der dΓ dA=) dB'-Lift)
                                                             du-Lift
                                                             (ex.Conv (coercTy-getTy-liftᵈ dΓ (Lift-Der dΓ dA=) (ex.coercInvTm du'-Lift))
                                                                      (coercTy-liftᵈ dΓ (Lift-Der dΓ dA=) dB'-Lift)
                                                                      (ex.coercInvTm (coercTm-liftᵈ dΓ (Lift-Der dΓ dA=) du'-Lift))
                                                                      (ex.TyTran (ex.CoercTy dΓ dA-Lift dA'-Lift dB-Lift (Lift-Der dΓ dA=))
                                                                                 (ex.TyTran (ex.CoercTy dΓ dA-Lift dA'-Lift (ex.coercInvTy1 du'-Lift) (Lift-Der dΓ dA=))
                                                                                            (coercTy-getTy-lift⁼ dΓ (ex.TySymm (Lift-Der dΓ dA=))
                                                                                                                 (coercTm1-liftᵈ dΓ (Lift-Der dΓ dA=) (ex.coercInvTm du'-Lift)))
                                                                                            (ex.CoercTyEq dΓ (Lift-Der dΓ dA=) (ex.coercInvEq du'-Lift)))
                                                                                 (ex.TyTran (ex.CoercTy dΓ dA-Lift dA'-Lift dB'-Lift (Lift-Der dΓ dA=)) 
                                                                                            (ex.CoercTyEq dΓ (Lift-Der dΓ dA=) (Lift-Der (dΓ ex., dA-Lift) dB=))
                                                                                            (ex.TySymm (coercTy-lift⁼ dΓ (ex.TySymm (Lift-Der dΓ dA=)) (coercTy-liftᵈ dΓ (Lift-Der dΓ dA=) dB'-Lift))))))
                                                             (Lift-Der dΓ dA=)
                                                             (ex.TyTran dB'-Lift
                                                                        (Lift-Der (dΓ ex., Lift-Der dΓ dA) dB=)
                                                                        (coercTy-lift⁼ dΓ (Lift-Der dΓ dA=) dB'-Lift))
                                                             (ex.TmTran du'-Lift
                                                                        (Lift-Der (dΓ ex., dA-Lift) du=)
                                                                        (ex.TmTran (ex.Conv (ex.CoercTy dΓ dA'-Lift dA-Lift (coercTy-liftᵈ dΓ dA=-Lift dB-Lift) (ex.TySymm dA=-Lift))
                                                                                            dB-Lift
                                                                                            (ex.CoercTm dΓ dA'-Lift dA-Lift (coercTm-liftᵈ dΓ dA=-Lift du'-Lift) (ex.TySymm dA=-Lift))
                                                                                            (ex.TySymm (coercTy-lift⁼ dΓ dA=-Lift dB-Lift)))
                                                                                   (coercTm-lift⁼ dΓ (Lift-Der dΓ dA=) du'-Lift)
                                                                                   (ex.TmTran (ex.Conv (ex.CoercTy dΓ dA'-Lift dA-Lift (ex.coercInvTy1 (coercTm-liftᵈ dΓ dA=-Lift du'-Lift))
                                                                                                                   (ex.TySymm dA=-Lift))
                                                                                                       dB-Lift
                                                                                                       (ex.CoercTm dΓ dA'-Lift dA-Lift (ex.coercInvTm (coercTm-liftᵈ dΓ dA=-Lift du'-Lift))
                                                                                                                   (ex.TySymm dA=-Lift))
                                                                                                       (ex.TyTran (ex.coercInvTy1 du'-Lift)
                                                                                                                  (ex.TySymm (coercTy-getTy-lift⁼ dΓ dA=-Lift (ex.coercInvTm du'-Lift)) )
                                                                                                                  (ex.coercInvEq du'-Lift)))
                                                                                       (ex.CoercTrans (ex.CoercTy dΓ dA'-Lift dA-Lift
                                                                                                                  (ex.coercInvTy1 (coercTm-liftᵈ dΓ (Lift-Der dΓ dA=) du'-Lift))
                                                                                                                  (ex.TySymm dA=-Lift))
                                                                                                      (ex.CoercTy dΓ dA'-Lift dA-Lift (coercTy-liftᵈ dΓ (Lift-Der dΓ dA=) dB-Lift)
                                                                                                                  (ex.TySymm (Lift-Der dΓ dA=)))
                                                                                                      dB-Lift
                                                                                                      (ex.CoercTm dΓ dA'-Lift dA-Lift
                                                                                                                  (ex.coercInvTm (coercTm-liftᵈ dΓ (Lift-Der dΓ dA=) du'-Lift))
                                                                                                                  (ex.TySymm dA=-Lift))
                                                                                                      (ex.CoercTyEq dΓ (ex.TySymm (Lift-Der dΓ dA=))
                                                                                                                    (ex.TyTran (ex.CoercTy dΓ dA-Lift dA'-Lift (ex.coercInvTy1 du'-Lift)
                                                                                                                                      (Lift-Der dΓ dA=))
                                                                                                                    (coercTy-getTy-lift⁼ dΓ (ex.TySymm (Lift-Der dΓ dA=))
                                                                                                                              (ex.coercInvTm (coercTm-liftᵈ dΓ (Lift-Der dΓ dA=) du'-Lift)))
                                                                                                                              (ex.TyTran (ex.CoercTy dΓ dA-Lift dA'-Lift dB-Lift (Lift-Der dΓ dA=) )
                                                                                                                                          (ex.CoercTyEq dΓ (Lift-Der dΓ dA=)
                                                                                                                                                        (ex.coercInvEq du'-Lift))
                                                                                                                                    (ex.TySymm (coercTy-lift⁼ dΓ (ex.TySymm (Lift-Der dΓ dA=))
                                                                                                                                        (coercTy-liftᵈ dΓ (Lift-Der dΓ dA=) dB-Lift))))))
                                                                                                      (ex.TySymm (coercTy-lift⁼ dΓ (Lift-Der dΓ dA=) dB-Lift) ))
                                                                                       (ex.TmSymm (ex.CoercTrans (ex.CoercTy dΓ dA'-Lift dA-Lift
                                                                                                                             (coercTy-getTy-liftᵈ dΓ (Lift-Der dΓ dA=) (ex.coercInvTm du'-Lift))
                                                                                                                             (ex.TySymm dA=-Lift))
                                                                                                 (ex.CoercTy dΓ dA'-Lift dA-Lift
                                                                                                             (coercTy-liftᵈ dΓ (Lift-Der dΓ dA=) dB'-Lift)
                                                                                                             (ex.TySymm (Lift-Der dΓ dA=)))
                                                                                                 dB-Lift
                                                                                                 (ex.CoercTm dΓ dA'-Lift dA-Lift (ex.coercInvTm (coercTm-liftᵈ dΓ (Lift-Der dΓ dA=) du'-Lift))
                                                                                                             (ex.TySymm dA=-Lift))
                                                                                                 (ex.CoercTyEq dΓ (ex.TySymm (Lift-Der dΓ dA=))
                                                                                                               (ex.TyTran (ex.CoercTy dΓ dA-Lift dA'-Lift (ex.coercInvTy1 du'-Lift)
                                                                                                                                      (Lift-Der dΓ dA=))
                                                                                                                    (coercTy-getTy-lift⁼ dΓ (ex.TySymm (Lift-Der dΓ dA=))
                                                                                                                               (ex.coercInvTm (coercTm-liftᵈ dΓ dA=-Lift du'-Lift)))
                                                                                                                    (ex.TyTran (ex.CoercTy dΓ dA-Lift dA'-Lift dB'-Lift dA=-Lift)
                                                                                                                         (ex.CoercTyEq dΓ (Lift-Der dΓ dA=)
                                                                                                                                       (ex.TyTran dB-Lift
                                                                                                                                                  (ex.coercInvEq du'-Lift)
                                                                                                                                                  (Lift-Der (dΓ ex., dA-Lift) dB=)))
                                                                                                                         (ex.TySymm (coercTy-lift⁼ dΓ (ex.TySymm dA=-Lift)
                                                                                                                                    (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift))))))
                                                                                                 (ex.TyTran dB'-Lift
                                                                                                            (ex.TySymm (coercTy-lift⁼ dΓ dA=-Lift dB'-Lift))
                                                                                                            (ex.TySymm (Lift-Der (dΓ ex., dA-Lift) dB=)))))))))
                                    where
                                    dA-Lift = Lift-Der dΓ dA
                                    dA'-Lift = ex.TyEqTy2 dΓ (Lift-Der dΓ dA=)
                                    dB-Lift = ex.TyEqTy1 (dΓ ex., dA-Lift) (Lift-Der (dΓ ex., dA-Lift) dB=)
                                    dB'-Lift = ex.TyEqTy2 (dΓ ex., dA-Lift) (Lift-Der (dΓ ex., dA-Lift) dB=)
                                    du-Lift = ex.TmEqTm1 (dΓ ex., dA-Lift) (Lift-Der (dΓ ex., dA-Lift) du=)
                                    du'-Lift = ex.TmEqTm2 (dΓ ex., dA-Lift) (Lift-Der (dΓ ex., dA-Lift) du=)
                                    dA=-Lift = Lift-Der dΓ dA=
Lift-Der dΓ (App {Γ = Γ} {A = A} {B = B} {f = f} {a = a} dA dB df da)
                  = ex.Conv (ex.SubstTy (Lift-Der (dΓ ex., (Lift-Der dΓ dA)) dB)
                                        (ex.idMorDerivable dΓ ex., ex.congTmTy (! (ex.[idMor]Ty _)) (Lift-Der dΓ da)))
                            ([]-liftTy1 dΓ
                                        (dΓ ex., Lift-Der dΓ dA)
                                        (Lift-Der (dΓ ex., Lift-Der dΓ dA) dB)
                                        (idMorDerivableLift dΓ ex., ex.Conv (ex.coercInvTy1 (Lift-Der dΓ da))
                                                                            (ex.SubstTy (Lift-Der dΓ dA) (idMorDerivableLift dΓ))
                                                                            (ex.coercInvTm (Lift-Der dΓ da))
                                                                            (ex.TyTran (Lift-Der dΓ dA)
                                                                                       (ex.coercInvEq (Lift-Der dΓ da))
                                                                                       (ex.congTyEq (ex.[idMor]Ty _) refl
                                                                                                    (ex.SubstTyMorEq1 dΓ
                                                                                                                      dΓ
                                                                                                                      (Lift-Der dΓ dA)
                                                                                                                      (ex.MorSymm dΓ dΓ (idmor-lift⁼ dΓ)))))))
                            (ex.App (Lift-Der dΓ dA) (Lift-Der (dΓ ex., (Lift-Der dΓ dA)) dB) (Lift-Der dΓ df) (Lift-Der dΓ da))
                            (substTy-liftTy⁼ dΓ (Lift-Der dΓ dA) (Lift-Der (dΓ ex., Lift-Der dΓ dA) dB) (Lift-Der dΓ da))
Lift-Der dΓ (AppCong {Γ = Γ} {A = A} {A' = A'} {a = a} {a' = a'} dA dA= dB= df= da=)
            = ex.TmTran (ex.Conv (ex.SubstTy dB-Lift SUBSTMOR)
                                 (substTy-liftTyᵈ dΓ dA-Lift dB-Lift da-Lift)
                                 (ex.Conv (ex.SubstTy (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift) COERCMOR)
                                          (ex.SubstTy dB-Lift SUBSTMOR)
                                          (ex.App dA'-Lift
                                                  (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift)
                                                  (ex.Conv (ex.coercInvTy1 df'-Lift) (ex.Pi dA'-Lift (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift)) (ex.coercInvTm df'-Lift)
                                                           (ex.TyTran (ex.Pi dA-Lift dB-Lift) (ex.coercInvEq df'-Lift)
                                                                      (ex.PiCong dA-Lift dA'-Lift dB-Lift (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift) dA=-Lift
                                                                                 (ex.TyTran dB'-Lift dB=-Lift (coercTy-lift⁼ dΓ dA=-Lift dB'-Lift)))))
                                                  (ex.Conv (ex.coercInvTy1 da'-Lift) dA'-Lift (ex.coercInvTm da'-Lift)
                                                                           (ex.TyTran dA-Lift (ex.coercInvEq da'-Lift) dA=-Lift)))
                                          (ex.TySymm (ex.SubstTyFullEqExt dΓ
                                                                          dΓ
                                                                          dA=-Lift
                                                                          (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift)
                                                                          (ex.TyTran dB'-Lift dB=-Lift (coercTy-lift⁼ dΓ dA=-Lift dB'-Lift))
                                                                          (ex.MorRefl (ex.idMorDerivable dΓ))
                                                                          (ex.congTmEq refl (ex.ap-coerc-Tm (! (ex.[idMor]Ty _)) (! (ex.[idMor]Ty _)) refl) (! (ex.[idMor]Ty _))
                                                                                       (ex.TmTran da'-Lift da=-Lift (ex.TmSymm (ex.CoercTrans (ex.coercInvTy1 da'-Lift) dA'-Lift dA-Lift
                                                                                                                                              (ex.coercInvTm da'-Lift)
                                                                                                                                              (ex.TyTran dA-Lift (ex.coercInvEq da'-Lift) dA=-Lift)
                                                                                                                                              (ex.TySymm dA=-Lift))))))))
                                 (substTy-liftTy⁼ dΓ dA-Lift dB-Lift da-Lift))
                        (ex.ConvEq (ex.SubstTy dB-Lift SUBSTMOR)
                                   (ex.AppCong dA-Lift
                                               dA'-Lift
                                               dB-Lift
                                               (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift)
                                               df-Lift
                                               (ex.Conv (ex.coercInvTy1 df'-Lift)
                                                        (ex.Pi dA'-Lift (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift))
                                                        (ex.coercInvTm df'-Lift)
                                                        (ex.TyTran (ex.Pi dA-Lift dB-Lift) (ex.coercInvEq df'-Lift)
                                                                   (ex.PiCong dA-Lift dA'-Lift dB-Lift (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift) dA=-Lift
                                                                              (ex.TyTran dB'-Lift dB=-Lift (coercTy-lift⁼ dΓ dA=-Lift dB'-Lift)))))
                                               da-Lift
                                               (ex.Conv (ex.coercInvTy1 da'-Lift) dA'-Lift (ex.coercInvTm da'-Lift) (ex.TyTran dA-Lift (ex.coercInvEq da'-Lift) dA=-Lift))
                                               dA=-Lift
                                               (ex.TyTran dB'-Lift dB=-Lift (coercTy-lift⁼ dΓ dA=-Lift dB'-Lift))
                                               (ex.TmTran df'-Lift df=-Lift
                                                          (ex.TmSymm (ex.CoercTrans (ex.coercInvTy1 df'-Lift)
                                                                                    (ex.Pi dA'-Lift (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift)) (ex.Pi dA-Lift dB-Lift)
                                                                                    (ex.coercInvTm df'-Lift)
                                                                                    (ex.TyTran (ex.Pi dA-Lift dB-Lift) (ex.coercInvEq df'-Lift)
                                                                                               (ex.PiCong dA-Lift dA'-Lift dB-Lift (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift)
                                                                                                          dA=-Lift (ex.TyTran dB'-Lift (dB=-Lift) (coercTy-lift⁼ dΓ dA=-Lift dB'-Lift))))
                                                                                               (ex.PiCong dA'-Lift dA-Lift (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift)
                                                                                                          dB-Lift (ex.TySymm dA=-Lift)
                                                                                                          (ex.TyTran (coercTy-liftᵈ dΓ dA=-Lift dB-Lift)
                                                                                                                     (ex.TyTran (ex.CoercTy dΓ dA-Lift dA'-Lift dB'-Lift dA=-Lift)
                                                                                                                                (coercTy-lift⁼ dΓ (ex.TySymm dA=-Lift)
                                                                                                                                               (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift))
                                                                                                                                (ex.TyTran (ex.CoercTy dΓ dA-Lift dA'-Lift dB-Lift dA=-Lift)
                                                                                                                                           (ex.CoercTyEq dΓ dA=-Lift (ex.TySymm dB=-Lift))
                                                                                                                                           (ex.coercTySymm dΓ dA=-Lift
                                                                                                                                                           (coercTy-liftᵈ dΓ dA=-Lift dB-Lift)
                                                                                                                                                           (coercTy-lift⁼ dΓ dA=-Lift dB-Lift))))
                                                                                                                  (coercTy-lift⁼ dΓ (ex.TySymm dA=-Lift) (coercTy-liftᵈ dΓ dA=-Lift dB-Lift)))))))
                                               (ex.TmTran da'-Lift da=-Lift (ex.TmSymm (ex.CoercTrans (ex.coercInvTy1 da'-Lift) dA'-Lift dA-Lift (ex.coercInvTm da'-Lift)
                                                                                                   (ex.TyTran dA-Lift (ex.coercInvEq da'-Lift) dA=-Lift) (ex.TySymm dA=-Lift)))))
                                   (substTy-liftTy⁼ dΓ dA-Lift dB-Lift da-Lift))
                        (ex.CoercTrans (ex.SubstTy (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift) COERCMOR)
                                       (ex.SubstTy dB-Lift SUBSTMOR)
                                       (substTy-liftTyᵈ dΓ dA-Lift dB-Lift da-Lift)
                                       (ex.App dA'-Lift (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift) (ex.Conv (ex.coercInvTy1 df'-Lift)
                                                                                                      (ex.Pi dA'-Lift (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift))
                                                                                                      (ex.coercInvTm df'-Lift)
                                                                                                      (ex.TyTran (ex.Pi dA-Lift dB-Lift) (ex.coercInvEq df'-Lift)
                                                                                                                 (ex.PiCong dA-Lift dA'-Lift dB-Lift (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift) dA=-Lift
                                                                                                                            (ex.TyTran dB'-Lift dB=-Lift (coercTy-lift⁼ dΓ dA=-Lift dB'-Lift)))))
                                       (ex.Conv (ex.coercInvTy1 da'-Lift) dA'-Lift (ex.coercInvTm da'-Lift) (ex.TyTran dA-Lift (ex.coercInvEq da'-Lift) dA=-Lift)))
                                       (ex.SubstTyFullEqExt dΓ dΓ (ex.TySymm dA=-Lift) dB-Lift
                                                            (ex.TyTran (ex.CoercTy dΓ dA-Lift dA'-Lift dB'-Lift dA=-Lift)
                                                                       (coercTy-lift⁼ dΓ (ex.TySymm dA=-Lift) (coercTy-liftᵈ dΓ dA=-Lift dB'-Lift)) (ex.CoercTyEq dΓ dA=-Lift (ex.TySymm dB=-Lift)))
                                                            (ex.MorRefl (ex.idMorDerivable dΓ))
                                                            (ex.congTmEq refl (ex.ap-coerc-Tm (! (ex.[idMor]Ty _)) (! (ex.[idMor]Ty _)) refl) (! (ex.[idMor]Ty _))
                                                                         (ex.TmTran (ex.Conv dA-Lift dA'-Lift da'-Lift dA=-Lift )
                                                                                    (ex.TmSymm (ex.CoercTrans (ex.coercInvTy1 da'-Lift) dA-Lift dA'-Lift (ex.coercInvTm da'-Lift)
                                                                                                              (ex.coercInvEq da'-Lift) dA=-Lift))
                                                                                    (ex.ConvEq dA-Lift (ex.TmSymm da=-Lift) dA=-Lift))))
                                       (substTy-liftTy⁼ dΓ dA-Lift dB-Lift da-Lift))
                         where
                         dA-Lift = Lift-Der dΓ dA
                         dA'-Lift = ex.TyEqTy2 dΓ (Lift-Der dΓ dA=)
                         dB-Lift = ex.TyEqTy1 (dΓ ex., dA-Lift) (Lift-Der (dΓ ex., dA-Lift) dB=)
                         dB'-Lift = ex.TyEqTy2 (dΓ ex., dA-Lift) (Lift-Der (dΓ ex., dA-Lift) dB=)
                         df-Lift = ex.TmEqTm1 dΓ (Lift-Der dΓ df=)
                         df'-Lift = ex.TmEqTm2 dΓ (Lift-Der dΓ df=)
                         da-Lift = ex.TmEqTm1 dΓ (Lift-Der dΓ da=)
                         da'-Lift = ex.TmEqTm2 dΓ (Lift-Der dΓ da=)
                         dA=-Lift = Lift-Der dΓ dA=
                         dB=-Lift = Lift-Der (dΓ ex., dA-Lift) dB=
                         df=-Lift = Lift-Der dΓ df=
                         da=-Lift = Lift-Der dΓ da=
                         COERCMOR : liftCtx Γ ex.⊢ ex.idMor _ ex., ex.coerc (ex.getTy (liftCtx Γ) (liftTm1 (liftCtx Γ) a')) (liftTy (liftCtx Γ) A') (liftTm1 (liftCtx Γ) a')
                                                 ∷> (liftCtx Γ ex., liftTy (liftCtx Γ) A')
                         COERCMOR = ex.idMorDerivable dΓ ex., ex.congTmTy (! (ex.[idMor]Ty _))
                                                                          (ex.Conv (ex.coercInvTy1 da'-Lift) dA'-Lift
                                                                                   (ex.coercInvTm da'-Lift) (ex.TyTran dA-Lift (ex.coercInvEq da'-Lift) dA=-Lift))
                         SUBSTMOR : liftCtx Γ ex.⊢ ex.idMor _ ex., liftTm (liftCtx Γ) (liftTy (liftCtx Γ) A) a ∷> (liftCtx Γ ex., liftTy (liftCtx Γ) A)
                         SUBSTMOR = ex.idMorDerivable dΓ ex., ex.congTmTy (! (ex.[idMor]Ty _)) da-Lift
Lift-Der dΓ (BetaPi {Γ = Γ} {A} {B} {u} {a} dA dB du da) = ex.TmTran (ex.Conv (ex.SubstTy dB-Lift SUBSTMOR)
                                                      (substTy-liftTyᵈ dΓ dA-Lift dB-Lift da-Lift)
                                                      (ex.App dA-Lift dB-Lift (ex.coercInvTm df-Lift) da-Lift)
                                                      (substTy-liftTy⁼ dΓ dA-Lift dB-Lift da-Lift))
                                             (ex.ConvEq (ex.SubstTy dB-Lift SUBSTMOR)
                                                        (ex.TmTran (ex.Conv (ex.SubstTy dB-Lift SUBSTMOR)
                                                                            (ex.SubstTy dB-Lift SUBSTMOR)
                                                                            (ex.App dA-Lift dB-Lift (ex.coercInvTm df-Lift) da-Lift)
                                                                            (ex.TyRefl (ex.SubstTy dB-Lift SUBSTMOR)))
                                                                   (ex.AppCong dA-Lift dA-Lift dB-Lift dB-Lift df-Lift (ex.coercInvTm df-Lift) da-Lift da-Lift (ex.TyRefl dA-Lift)
                                                                               (coercTy-lift⁼ dΓ (ex.TyRefl dA-Lift) dB-Lift)
                                                                               (ex.TmRefl df-Lift)
                                                                               (ex.TmSymm (ex.CoercTrans (ex.coercInvTy1 da-Lift) dA-Lift dA-Lift
                                                                                                         (ex.coercInvTm da-Lift) (ex.coercInvEq da-Lift) (ex.TyRefl dA-Lift))))
                                                                   (ex.CoercRefl (ex.App dA-Lift dB-Lift (ex.coercInvTm df-Lift) da-Lift)))
                                                        (substTy-liftTy⁼ dΓ dA-Lift dB-Lift da-Lift))
                                             (ex.TmTran (ex.Conv (ex.SubstTy dB-Lift SUBSTMOR)
                                                                 (substTy-liftTyᵈ dΓ dA-Lift dB-Lift da-Lift)
                                                                 (ex.SubstTm du-Lift SUBSTMOR)
                                                                 (substTy-liftTy⁼ dΓ dA-Lift dB-Lift da-Lift))
                                                        (ex.ConvEq (ex.SubstTy dB-Lift SUBSTMOR)
                                                                   (ex.BetaPi dA-Lift dB-Lift du-Lift da-Lift)
                                                                   (substTy-liftTy⁼ dΓ dA-Lift dB-Lift da-Lift))
                                                        (ex.TmSymm (ex.TmTran (ex.Conv (ex.coercInvTy1 (substTm-liftTmᵈ dΓ dA-Lift du-Lift da-Lift))
                                                                              (substTy-liftTyᵈ dΓ dA-Lift dB-Lift da-Lift)
                                                                              (ex.Conv (ex.SubstTy dB-Lift SUBSTMOR)
                                                                                       (ex.coercInvTy1 (substTm-liftTmᵈ dΓ dA-Lift du-Lift da-Lift))
                                                                                       (ex.SubstTm du-Lift SUBSTMOR)
                                                                                       (ex.TyTran (substTy-liftTyᵈ dΓ dA-Lift dB-Lift da-Lift)
                                                                                                  (substTy-liftTy⁼ dΓ dA-Lift dB-Lift da-Lift)
                                                                                                  (ex.TySymm (ex.coercInvEq (substTm-liftTmᵈ dΓ dA-Lift du-Lift da-Lift)))))
                                                                               (ex.coercInvEq (substTm-liftTmᵈ dΓ dA-Lift du-Lift da-Lift)))
                                                                         (ex.ConvEq (ex.coercInvTy1 (substTm-liftTmᵈ dΓ dA-Lift du-Lift da-Lift))
                                                                                    (ex.coercSymm dΓ (ex.TmSymm (substTm-liftTm⁼ dΓ dA-Lift du-Lift da-Lift)))
                                                                                    (ex.coercInvEq (substTm-liftTmᵈ dΓ dA-Lift du-Lift da-Lift) ) )
                                                                         (ex.CoercTrans (ex.SubstTy dB-Lift SUBSTMOR)
                                                                                        (ex.coercInvTy1 (substTm-liftTmᵈ dΓ dA-Lift du-Lift da-Lift))
                                                                                        (substTy-liftTyᵈ dΓ dA-Lift dB-Lift da-Lift)
                                                                                        (ex.SubstTm du-Lift SUBSTMOR)
                                                                                        (ex.TyTran (substTy-liftTyᵈ dΓ dA-Lift dB-Lift da-Lift)
                                                                                                   (substTy-liftTy⁼ dΓ dA-Lift dB-Lift da-Lift)
                                                                                                   (ex.TySymm (ex.coercInvEq (substTm-liftTmᵈ dΓ dA-Lift du-Lift da-Lift))))
                                                                                        (ex.coercInvEq (substTm-liftTmᵈ dΓ dA-Lift du-Lift da-Lift))) )))
                                 where
                                 dA-Lift = Lift-Der dΓ dA
                                 dB-Lift = Lift-Der (dΓ ex., dA-Lift) dB
                                 du-Lift = Lift-Der (dΓ ex., dA-Lift) du
                                 da-Lift = Lift-Der dΓ da
                                 df-Lift = ex.Conv (ex.Pi dA-Lift dB-Lift) (ex.Pi dA-Lift dB-Lift) (ex.Lam dA-Lift dB-Lift du-Lift) (ex.TyRefl (ex.Pi dA-Lift dB-Lift))
                                 SUBSTMOR : liftCtx Γ ex.⊢ ex.idMor _ ex., liftTm (liftCtx Γ) (liftTy1 (liftCtx Γ) A) a ∷> (liftCtx Γ ex., liftTy (liftCtx Γ) A)
                                 SUBSTMOR = ex.idMorDerivable dΓ ex., ex.congTmTy (! (ex.[idMor]Ty _)) da-Lift
Lift-Der dΓ (EtaPi {n = n} {Γ = Γ} {A} {B} {f} dA dB df)
            = ex.TmTran (ex.Lam dA-Lift dB-Lift (ex.congTmTy (ex.weakenTyInsert' (prev last) (liftTy (liftCtx (Γ , A)) B) (ex.idMor (suc n)) (ex.var last) ∙ ex.[idMor]Ty _)
                                                (ex.App (ex.WeakTy dA-Lift) (ex.WeakTy dB-Lift) (ex.WeakTm df-Lift) (ex.VarLast dA-Lift))))
                        (ex.EtaPi dA-Lift dB-Lift df-Lift)
                        (ex.LamCong dA-Lift dA-Lift dB-Lift dB-Lift
                                    (ex.congTm (ex.weakenTyInsert' (prev last) (liftTy _ B) (ex.idMor (suc n)) (ex.var last) ∙ ex.[idMor]Ty _)
                                               refl
                                               (ex.App (ex.WeakTy dA-Lift) (ex.WeakTy dB-Lift) (ex.WeakTm df-Lift) (ex.VarLast dA-Lift)))
                                    ((ex.congTm (ap (liftTy _) (weakenTyInsert' (prev last) B (idMor (suc n)) (var last) ∙ [idMor]Ty B))
                                                (ap (λ x → liftTm _ (liftTy _ x) (app (weakenTy A) (weakenTy' (prev last) B) (weakenTm f) (var last)))
                                                    (weakenTyInsert' (prev last) B (idMor (suc n)) (var last) ∙ [idMor]Ty B))
                                                dapp-Lift))
                                    (ex.TyRefl dA-Lift)
                                    (coercTy-lift⁼ dΓ (ex.TyRefl dA-Lift) dB-Lift)
                        (ex.TmTran (ex.congTm (ap (liftTy (liftCtx (Γ , A))) (weakenTyInsert' (prev last) B (idMor (suc n)) (var last) ∙ [idMor]Ty _))
                                              refl (ex.Conv (ex.SubstTy (weakenTy-liftᵈ (Γ , A) A B dB-Lift) (ex.idMorDerivable (dΓ ex., dA-Lift)
                                                                                                        ex., ex.congTmTy (! (ex.[idMor]Ty _)) (ex.Conv (ex.WeakTy dA-Lift)
                                                                                                                                        (weakenTy-liftᵈ Γ A A dA-Lift)
                                                                                                                                        (ex.VarLast dA-Lift)
                                                                                                                                        (weakenTy-lift⁼ Γ A A dA-Lift))))
                                                            (ex.congTy (ap (liftTy (liftCtx (Γ , A))) (! (weakenTyInsert' (prev last) B (idMor (suc n)) (var last) ∙ [idMor]Ty _)))
                                                                       dB-Lift)
                                                            (ex.coercInvTm dapp-Lift)
                                                            (ex.congTyEq (! (ex.weakenTyInsert' (prev last) (liftTy (liftCtx (Γ , A)) B)
                                                                                                (ex.weakenMor (ex.idMor n) ex., liftTm (liftCtx (Γ , A))
                                                                                                                                (liftTy (liftCtx (Γ , A)) (weakenTy A))
                                                                                                                                (var last))
                                                                                                (ex.var last))
                                                                        ∙ ex.ap[]Ty {B = liftTy (liftCtx ((Γ , A) , weakenTy A)) (weakenTy' (prev last) B)}
                                                                                    (! (weakenTy'-liftTy (prev last) (liftCtx (Γ , A)) (liftTy (liftCtx Γ) A) B)
                                                                                  ∙ ap (λ x → liftTy (liftCtx (Γ , A) ex., x) (weakenTy' (prev last) B))
                                                                                       (! (weakenTy-liftTy (liftCtx Γ) (liftTy (liftCtx Γ) A) A)) ) refl)
                                                                         (ex.[idMor]Ty _
                                                                         ∙ ap (liftTy (liftCtx (Γ , A))) (! (weakenTyInsert' (prev last) B (idMor (suc n)) (var last) ∙ [idMor]Ty _)))
                                                                         (ex.SubstTyMorEq1 (dΓ ex., dA-Lift) (dΓ ex., dA-Lift) dB-Lift
                                                                                           (ex.MorRefl (ex.WeakMor (ex.idMorDerivable dΓ))
                                                                                       ex., ex.congTmEq refl (ex.ap-coerc-Tm (! (ex.[idMor]Ty _)
                                                                                                                               ∙ ex.weakenTyInsert (liftTy _ A) (ex.weakenMor (ex.idMor n))
                                                                                                                                                   (ex.var last))
                                                                                                                             ((weakenTy-liftTy (liftCtx Γ) (liftTy _ A) A
                                                                                                                             ∙ ap ex.weakenTy (! (ex.[idMor]Ty _))) ∙ ex.weaken[]Ty _ _ _)
                                                                                                                             refl)
                                                                                                        ((weakenTy-liftTy (liftCtx Γ) (liftTy _ A) A
                                                                                                        ∙ ap ex.weakenTy (! (ex.[idMor]Ty _))) ∙ ex.weaken[]Ty _ _ _)
                                                                                                        (ex.TmRefl (ex.Conv (ex.WeakTy dA-Lift) (weakenTy-liftᵈ Γ A A dA-Lift)
                                                                                                                            (ex.VarLast dA-Lift) (weakenTy-lift⁼ Γ A A dA-Lift))))))))
                                   (ex.congTmEq refl
                                                ((ex.ap-coerc-Tm refl
                                                       (ex.weakenTyInsert' (prev last) (liftTy _ B) (ex.idMor (suc n)) (ex.var last)
                                                       ∙ ex.[idMor]Ty _
                                                       ∙ ap (liftTy _) (! (weakenTyInsert' (prev last) B (idMor (suc n)) (var last) ∙ [idMor]Ty _)))
                                                                refl))
                                                  (ex.weakenTyInsert' (prev last) (liftTy _ B) (ex.idMor (suc n)) (ex.var last) ∙ ex.[idMor]Ty _)
                                   ((ex.AppCong ((ex.WeakTy dA-Lift)) ((weakenTy-liftᵈ Γ A A dA-Lift)) ((ex.WeakTy dB-Lift))
                                               ((weakenTy-liftᵈ (Γ , A) A B dB-Lift)) (ex.WeakTm df-Lift)
                                               (weakenTm-liftᵈ (liftTy _ A) df-Lift)
                                               (ex.VarLast dA-Lift)
                                               (ex.Conv (ex.WeakTy dA-Lift) (weakenTy-liftᵈ Γ A A dA-Lift) (ex.VarLast dA-Lift) (weakenTy-lift⁼ Γ A A dA-Lift))
                                               (weakenTy-lift⁼ Γ A A dA-Lift)
                                               (ex.congTyCtxEq (ex.Ctx+= refl (weakenTy-liftTy (liftCtx Γ) (liftTy _ A) A))
                                                               (ap (λ x → liftTy x (weakenTy' (prev last) B))
                                                                   (ex.Ctx+= refl (weakenTy-liftTy (liftCtx Γ) (liftTy _ A) A))
                                                                ∙ weakenTy'-liftTy (prev last) (liftCtx Γ ex., liftTy (liftCtx Γ) A) (liftTy (liftCtx Γ) A) B )
                                                               (ap (ex.coercTy _ _) (weakenTy-liftTy (liftCtx Γ) (liftTy (liftCtx Γ) A) A))
                                                               (coercTy-lift⁼ (dΓ ex., dA-Lift) (ex.TyRefl (weakenTy-liftᵈ Γ A A dA-Lift))
                                                                              (weakenTy-liftᵈ (Γ , A) A B dB-Lift)))
                                               (ex.TmSymm (ex.congTmEq (ex.ap-coerc-Tm (! (weakenTy-liftTy (liftCtx Γ) (liftTy (liftCtx Γ) A) (pi A B))) refl
                                                                          (ex.ap-coerc-Tm (ex.weakenTy-getTy (liftCtx Γ) (liftTm1 _ f) (liftTy (liftCtx Γ) A)
                                                                                          ∙ ex.ap-getTy {u = ex.weakenTm (liftTm1 (liftCtx Γ) f) } refl
                                                                                                        (! (weakenTm'-liftTm1 last (liftCtx Γ) (liftTy (liftCtx Γ) A) f)) )
                                                                                            (! (weakenTy-liftTy (liftCtx Γ) (liftTy (liftCtx Γ) A) (pi A B)))
                                                                                            (! (weakenTm'-liftTm1 last (liftCtx Γ) (liftTy (liftCtx Γ) A) f))))
                                                                       refl
                                                                       refl
                                                            (ex.CoercTrans (ex.WeakTy (ex.coercInvTy1 df-Lift))
                                                                           (ex.Pi (ex.WeakTy dA-Lift) (ex.WeakTy dB-Lift))
                                                                           (ex.WeakTy (ex.Pi dA-Lift dB-Lift))
                                                                           (ex.WeakTm (ex.coercInvTm df-Lift))
                                                                           (ex.WeakTyEq (ex.coercInvEq df-Lift))
                                                                           (ex.WeakTyEq (ex.TyRefl (ex.Pi dA-Lift dB-Lift))))))
                                               (ex.coercSymm (dΓ ex., dA-Lift) (ex.TmRefl (ex.Conv (ex.WeakTy dA-Lift)
                                                                                                   (weakenTy-liftᵈ Γ A A dA-Lift)
                                                                                                   (ex.VarLast dA-Lift)
                                                                                                   (weakenTy-lift⁼ Γ A A dA-Lift)))))))
                                   (ex.TmTran (ex.congTm (! (ap (liftTy _) (! (weakenTyInsert' (prev last) B (idMor _) (var last) ∙ [idMor]Ty B))))
                                                         (ex.ap-coerc-Tm refl refl refl)
                                                         (ex.Conv (ex.CoercTy dΓ dA-Lift dA-Lift (substTy-liftTyᵈ (dΓ ex., dA-Lift) (weakenTy-liftᵈ Γ A A dA-Lift)
                                                                                                                  (weakenTy-liftᵈ (Γ , A) A B dB-Lift)
                                                                                                                  (ex.Conv (ex.WeakTy dA-Lift) (weakenTy-liftᵈ Γ A A dA-Lift) (ex.VarLast dA-Lift)
                                                                                                                           (weakenTy-lift⁼ Γ A A dA-Lift)))
                                                                              (ex.TyRefl dA-Lift))
                                                                  (ex.congTy (ap (liftTy _) (! (weakenTyInsert' (prev last) B (idMor _) (var last) ∙ [idMor]Ty B)))
                                                                             dB-Lift)
                                                                  (ex.CoercTm dΓ dA-Lift dA-Lift dapp-Lift (ex.TyRefl dA-Lift))
                                                                  (ex.TySymm (coercTy-lift⁼ dΓ (ex.TyRefl dA-Lift)
                                                                             (ex.congTy (ap (liftTy _) (! (weakenTyInsert' (prev last) B (idMor _) (var last) ∙ [idMor]Ty B)))
                                                                                        dB-Lift)))))
                                              (ex.congTmEqTy (ap (liftTy _) (weakenTyInsert' (prev last) B (idMor _) (var last) ∙ [idMor]Ty B ))
                                                             (coercTm-lift⁼ dΓ (ex.TyRefl dA-Lift) dapp-Lift))
                                                             (ex.congTmEq (ex.ap-coerc-Tm (ap (λ x → ex.coercTy x _ _)
                                                                          (ap (liftTy _) (! (weakenTyInsert' (prev last) B (idMor _) (var last) ∙ [idMor]Ty B))))
                                                                          (ap (liftTy _) (! (weakenTyInsert' (prev last) B (idMor _) (var last) ∙ [idMor]Ty B)))
                                                                          ((ap (λ x → ex.coercTm (liftTm (liftCtx Γ ex., liftTy (liftCtx Γ) A) x (app (weakenTy A)
                                                                                                                                                      (weakenTy' (prev last) B)
                                                                                                                                                      (weakenTm f) (var last)) )
                                                                                                (liftTy1 (liftCtx Γ) A) (liftTy1 (liftCtx Γ) A))
                                                                              (ap (liftTy (liftCtx Γ ex., liftTy (liftCtx Γ) A))
                                                                                  (! (weakenTyInsert' (prev last) B (idMor _) (var last) ∙ [idMor]Ty B))))) )
                                                                          refl
                                                                          refl
                                                                          (ex.TmRefl (ex.Conv (ex.CoercTy dΓ dA-Lift dA-Lift dB-Lift (ex.TyRefl dA-Lift))
                                                                                     dB-Lift
                                                                                     (ex.CoercTm dΓ dA-Lift dA-Lift
                                                                                                 (ex.congTm (ap (liftTy _) (weakenTyInsert' (prev last) B (idMor _) _ ∙ [idMor]Ty _))
                                                                                                            (ex.ap-coerc-Tm refl
                                                                                                            (ap (liftTy _) (weakenTyInsert' (prev last) B (idMor _) _ ∙ [idMor]Ty _)) refl)
                                                                                                            dapp-Lift)
                                                                                                 (ex.TyRefl dA-Lift))
                                                                                      (ex.TySymm (coercTy-lift⁼ dΓ (ex.TyRefl dA-Lift) dB-Lift)))))) ))
                                 where
                                 dA-Lift = Lift-Der dΓ dA
                                 dB-Lift = Lift-Der (dΓ ex., dA-Lift) dB
                                 df-Lift = Lift-Der dΓ df
                                 dapp-Lift : ex.Derivable ((liftCtx (Γ , A)) ⊢ₑ liftTm (liftCtx (Γ , A))
                                                                                       (liftTy (liftCtx (Γ , A)) (substTy (weakenTy' (prev last) B) (var last)))
                                                                                       (app (weakenTy A) (weakenTy' (prev last) B) (weakenTm f) (var last))
                                                                             :> liftTy (liftCtx (Γ , A)) (substTy (weakenTy' (prev last) B) (var last)))
                                 dapp-Lift = ex.Conv ((ex.SubstTy (weakenTy-liftᵈ (Γ , A) A B dB-Lift)
                                                                  (ex.idMorDerivable (dΓ ex., dA-Lift)
                                                             ex., ex.congTmTy (! (ex.[idMor]Ty _))
                                                                              (ex.Conv (ex.WeakTy dA-Lift) (weakenTy-liftᵈ Γ A A dA-Lift) (ex.VarLast dA-Lift) (weakenTy-lift⁼ Γ A A dA-Lift)))))
                                                     (substTy-liftTyᵈ (dΓ ex., dA-Lift)
                                                                      (weakenTy-liftᵈ {k = last} Γ A A dA-Lift)
                                                                      ((weakenTy-liftᵈ {k = prev last} (Γ , A) A B dB-Lift))
                                                                      (ex.Conv (ex.WeakTy dA-Lift) (weakenTy-liftᵈ Γ A A dA-Lift) (ex.VarLast dA-Lift) (weakenTy-lift⁼ Γ A A dA-Lift)) )
                                                                      (ex.App (weakenTy-liftᵈ Γ A A dA-Lift )
                                                                              (weakenTy-liftᵈ {k = prev last} (Γ , A) A B dB-Lift)
                                                                              (weakenTm-liftᵈ (liftTy (liftCtx Γ) A) df-Lift)
                                                                              (ex.Conv (ex.WeakTy dA-Lift) (weakenTy-liftᵈ Γ A A dA-Lift) (ex.VarLast dA-Lift) (weakenTy-lift⁼ Γ A A dA-Lift)))
                                                     (ex.congTyEq refl
                                                                  (ex.ap[]Ty {A = liftTy _ (weakenTy' (prev last) B)} 
                                                                              (ap (λ x → liftTy x (weakenTy' (prev last) B))
                                                                                 (ex.Ctx+= refl (weakenTy-liftTy (liftCtx Γ) (liftTy (liftCtx Γ) A) A))
                                                                              ∙ weakenTy'-liftTy (prev last) (liftCtx (Γ , A)) (liftTy _ A) B)
                                                                              refl
                                                                    ∙ ex.weakenTyInsert' (prev last) (liftTy _ B) (ex.idMor (suc n)) (ex.var last)
                                                                    ∙ ex.[idMor]Ty _
                                                                    ∙ ap (liftTy _)  (! (weakenTyInsert' (prev last) B (idMor (suc n)) (var last) ∙ [idMor]Ty B)))
                                                                  (ex.SubstTyMorEq1 (dΓ ex., dA-Lift)
                                                                                    ((dΓ ex., dA-Lift) ex., weakenTy-liftᵈ Γ A A dA-Lift)
                                                                                    (weakenTy-liftᵈ (Γ , A) A B dB-Lift)
                                                                                    (ex.MorRefl (ex.idMorDerivable (dΓ ex., dA-Lift))
                                                                               ex., ex.congTmEq refl
                                                                                                (ex.ap-coerc-Tm (! (weakenTy-liftTy (liftCtx Γ) (liftTy _ A) A) ∙ ! (ex.[idMor]Ty _))
                                                                                                                (! (ex.[idMor]Ty _))
                                                                                                                refl)
                                                                                                (! (ex.[idMor]Ty _))
                                                                                                (ex.ConvEq (ex.WeakTy dA-Lift)
                                                                                                           (ex.TmRefl (ex.VarLast dA-Lift))
                                                                                                           (weakenTy-lift⁼ Γ A A dA-Lift)))))

Lift-TyEq dΓ dΓ' dΓ= dA dA' (TySymm dA=) = {!Lift-TyEq dΓ' dΓ (ex.CtxSymm dΓ=) dA'!}
Lift-TyEq dΓ dΓ' dΓ= dA dA' (TyTran dA= dA=₁ dA=₂) = {!!}
Lift-TyEq dΓ dΓ' dΓ= dA dA' UUCong = {!!}
Lift-TyEq dΓ dΓ' dΓ= dA dA' (ElCong dA=) = {!!}
Lift-TyEq dΓ dΓ' dΓ= dA dA' (PiCong dA= dA=₁ dA=₂) = {!!}


-- ex.TyTran {!!}
--                                                    (Lift-TyEq (dΓ ex., dA)
--                                                               (dΓ ex., dA')
--                                                               (ex.CtxRefl dΓ ex.,  Lift-TyEq-Triv dΓ dA dA' dA= )
--                                                               dB
--                                                               dB'
--                                                               dB=)
--                                                    (ex.SubstTyMorEq1 {!!}
--                                                                      {!!}
--                                                                      dB'
--                                                                      ({!!} ex., {!!})) 

Lift-TyEq-Triv dΓ dA dA' dA= = {!!}

Lift-Ctx : {Γ : Ctx n} → ⊢ Γ → ex.⊢ liftCtx Γ
Lift-Ctx tt = ex.tt
Lift-Ctx (dΓ , x) = Lift-Ctx dΓ ex., Lift-Der (Lift-Ctx dΓ) x

lift-left-Inv : {Γ : ex.Ctx n} → ex.⊢ Γ == liftCtx (|| Γ ||Ctx)
lift-left-Inv = {!!}

Lift-TyDer : {Γ : ex.Ctx n} {A : TyExpr n} → ex.⊢ Γ → Derivable (|| Γ ||Ctx ⊢ A ) → ex.Derivable (Γ ⊢ₑ liftTy Γ A == ex.coercCtxTy (liftCtx (|| Γ ||Ctx )) Γ (liftTy (liftCtx (|| Γ ||Ctx)) A))
Lift-TyDer dA = {!!}

Lift-TmDer : {Γ : ex.Ctx n} {u : TmExpr n} {A : TyExpr n}
           → ex.⊢ Γ
           → Derivable (|| Γ ||Ctx ⊢ u :> A)
           → ex.Derivable (Γ ⊢ₑ liftTm1 Γ u == ex.coerc (ex.getTy Γ (ex.coercCtxTm (liftCtx (|| Γ ||Ctx )) Γ (liftTm1 (liftCtx (|| Γ ||Ctx)) u)))
                                                        (ex.getTy Γ (liftTm1 Γ u))
                                                        (ex.coercCtxTm (liftCtx (|| Γ ||Ctx )) Γ (liftTm1 (liftCtx (|| Γ ||Ctx)) u)) :> ex.getTy Γ (liftTm1 Γ u))
Lift-TmDer dΓ du = {!!}
