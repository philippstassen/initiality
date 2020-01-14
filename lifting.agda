{-# OPTIONS --rewriting --prop --allow-unsolved-metas #-}

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

liftTm Γ (var x) = ex.var x
liftTm Γ (lam A B u) = ex.lam (liftTy Γ A) (liftTy (Γ ex., (liftTy Γ A)) B) (ex.coerc (ex.getTy (Γ ex., liftTy Γ A) (liftTm (Γ ex., liftTy Γ A) u)) (liftTy (Γ ex., liftTy Γ A) B) (liftTm (Γ ex., liftTy Γ A) u))

liftTm Γ (app A B u u₁) = ex.app (liftTy Γ A) (liftTy (Γ ex., liftTy Γ A) B) (ex.coerc (ex.getTy Γ (liftTm Γ u)) (liftTy Γ (pi A B)) (liftTm Γ u)) (ex.coerc (ex.getTy Γ (liftTm Γ u₁)) (liftTy Γ A) (liftTm Γ u₁))

liftCtx : {n : ℕ} → (Γ : Ctx n) → ex.Ctx n
liftCtx ◇ = ex.◇
liftCtx (Γ , A) = liftCtx Γ ex., liftTy (liftCtx Γ) A

{- morphism lifting needs coercions. Aim: Define lifting that preserves wellformed-ness -}
{- Does the morlifting need the outermost coercion ??? 
I does not need it, if substitution commutes with the lifting syntactically -}
liftMor : {n m : ℕ} → ex.Ctx n → ex.Ctx m → Mor n m → ex.Mor n m
liftMor Γ Δ ◇ = ex.◇
liftMor Γ (Δ ex., A) (δ , u) = liftMor Γ Δ δ ex., ex.coerc (ex.getTy Γ (liftTm Γ u)) (A ex.[ liftMor Γ Δ δ ]Ty) (liftTm Γ u)
-- liftMor Γ Δ δ ex., liftTm Γ u

liftJdg : Judgment → ex.Judgment
liftJdg (Γ ⊢ x) = liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) x
liftJdg (Γ ⊢ x :> x₁) = liftCtx Γ ⊢ₑ ex.coerc (ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) x)) (liftTy (liftCtx Γ) x₁) (liftTm (liftCtx Γ) x) :> liftTy (liftCtx Γ) x₁
liftJdg (Γ ⊢ x == x₁) = liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) x == liftTy (liftCtx Γ) x₁
liftJdg (Γ ⊢ u == v :> A)
        = liftCtx Γ ⊢ₑ ex.coerc
                   (ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) u))
                   (liftTy (liftCtx Γ) A)
                   (liftTm (liftCtx Γ) u)
                   == ex.coerc
                   (ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) v))
                   (liftTy (liftCtx Γ) A)
                   (liftTm (liftCtx Γ) v) :> liftTy (liftCtx Γ) A

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
weakenTm'-liftTm k Γ A (app A₁ B u u₁) rewrite weakenTy'-liftTy k Γ A A₁ | weakenTm'-liftTm k Γ A u | weakenTm'-liftTm k Γ A u₁ = ex.ap-app-Tm refl (weakenTy'-liftTy (prev k) (Γ ex., (liftTy Γ A₁)) A B) (ex.ap-coerc-Tm (! (ex.weakenTy'-getTy k Γ (liftTm Γ u) A)) (ex.ap-pi-Ty refl (weakenTy'-liftTy (prev k) (Γ ex., (liftTy Γ A₁)) A B)) refl) (ex.ap-coerc-Tm (! (ex.weakenTy'-getTy k Γ (liftTm Γ u₁) A)) refl refl)

weakenTm-liftTm : (Γ : ex.Ctx n) (A : ex.TyExpr n) (u : TmExpr n) → liftTm (ex.weakenCtx last Γ A) (weakenTm' last u) ≡ ex.weakenTm' last (liftTm Γ u)
weakenTm-liftTm Γ A u = weakenTm'-liftTm last Γ A u

weakenTy-liftTy : (Γ : ex.Ctx n) (B : ex.TyExpr n) (A : TyExpr n) → liftTy (ex.weakenCtx last Γ B) (weakenTy' last A) ≡ ex.weakenTy' last (liftTy Γ A)
weakenTy-liftTy Γ B A = weakenTy'-liftTy last Γ B A

weakenMor-liftMor : (Γ : ex.Ctx n) (Δ : ex.Ctx m) (A : ex.TyExpr n) (δ : Mor n m) → liftMor (Γ ex., A) Δ (weakenMor δ) ≡ ex.weakenMor (liftMor Γ Δ δ)
weakenMor-liftMor Γ ex.◇ A ◇ = refl
weakenMor-liftMor Γ (Δ ex., A₁) A (δ , u) rewrite weakenMor-liftMor Γ Δ A δ | ! (ex.weaken[]Ty A₁ (liftMor Γ Δ δ) last) | weakenTm-liftTm Γ A u = ex.Mor+= refl (ex.ap-coerc-Tm (! (ex.weakenTy-getTy Γ (liftTm Γ u) A)) refl refl)

weakenMor+-liftMor : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : ex.TyExpr m} {δ : Mor n m} → ex.Derivable (Δ ⊢ₑ A) → Γ ex.⊢ liftMor Γ Δ δ ∷> Δ → (Γ ex., A ex.[ liftMor Γ Δ δ ]Ty ) ex.⊢ liftMor (Γ ex., A ex.[ liftMor Γ Δ δ ]Ty) (Δ ex., A) (weakenMor+ δ ) == ex.weakenMor+ (liftMor Γ Δ δ) ∷> (Δ ex., A)
weakenMor+-liftMor {Γ = Γ} {Δ = Δ} {A = A} {δ = δ} dA dδ rewrite weakenMor-liftMor Γ Δ (A ex.[ liftMor Γ Δ δ ]Ty) δ | ! (ex.weaken[]Ty A (liftMor Γ Δ δ) last) = ex.WeakMorEq (ex.MorRefl dδ) ex., ex.congTmEqTy ( (ex.weaken[]Ty A (liftMor Γ Δ δ) last)) (ex.congTmEq refl (ex.ap-coerc-Tm (ex.weaken[]Ty _ _ _) (ex.weaken[]Ty _ _ _) refl) refl (ex.TmRefl (ex.Conv (ex.WeakTy (ex.SubstTy dA dδ)) (ex.WeakTy (ex.SubstTy dA dδ)) (ex.VarLast (ex.SubstTy dA dδ)) (ex.TyRefl (ex.WeakTy (ex.SubstTy dA dδ))))))

{- Identity Morphism is equal two the lifting of the identity morphism
Lifting of identity morphism is also derivable -}
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

unstrip-[]Ty : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} → {δ : Mor n m} → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → ex.Derivable (liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) (A [ δ ]Ty))
unstrip-[]Ty dA dδ = {!SubstTy dA dδ!}

[]Ty-unstrip : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} → {δ : Mor n m} → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → ex.Derivable (liftCtx Γ ⊢ₑ (liftTy (liftCtx Δ) A) ex.[ liftMor (liftCtx Γ) (liftCtx Δ) δ ]Ty)
[]Ty-unstrip dA dδ = {!SubstTy dA dδ!}

unstrip-[]Tm : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {u : TmExpr m} → {δ : Mor n m} → Derivable (Δ ⊢ u :> A) → Γ ⊢ δ ∷> Δ → ex.Derivable (liftCtx Γ ⊢ₑ liftTm (liftCtx Γ) (u [ δ ]Tm) :> liftTy (liftCtx Γ) (A [ δ ]Ty))
unstrip-[]Tm du dδ = {!!}

[]Ty-lift : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} → {δ : Mor n m} → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → ex.Derivable (liftCtx Γ ⊢ₑ (liftTy (liftCtx Δ) A) ex.[ liftMor (liftCtx Γ) (liftCtx Δ) δ ]Ty == liftTy (liftCtx Γ) (A [ δ ]Ty))

[]Tm-lift : {Γ : Ctx n} {Δ : Ctx m} {B : TyExpr m} {u : TmExpr m} {δ : Mor n m} → Derivable (Δ ⊢ u :> B) → Γ ⊢ δ ∷> Δ
  → ex.Derivable (liftCtx Γ ⊢ₑ ex.coerc
                          (ex.getTy (liftCtx Δ) (liftTm (liftCtx Δ) u) ex.[ liftMor (liftCtx Γ) (liftCtx Δ) δ ]Ty)
                          (liftTy (liftCtx Γ) (B [ δ ]Ty))
                          ((liftTm (liftCtx Δ) u) ex.[ liftMor (liftCtx Γ) (liftCtx Δ) δ ]Tm)
                     == ex.coerc
                          (ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) (u [ δ ]Tm)))
--                           ((liftTy (liftCtx Δ) B) ex.[ liftMor (liftCtx Γ) (liftCtx Δ) δ ]Ty)
                          (liftTy (liftCtx Γ) (B [ δ ]Ty))
                          (liftTm (liftCtx Γ) (u [ δ ]Tm)) :> (liftTy (liftCtx Γ) (B [ δ ]Ty)))

[]Ty-lift {A = uu i} dA dδ = ex.TyRefl ex.UU
[]Ty-lift {A = el i v} (El dv) dδ = ex.ElCong ([]Tm-lift dv dδ)
[]Ty-lift {A = pi A B} (Pi dA dB) dδ = ex.PiCong ([]Ty-unstrip dA dδ) (unstrip-[]Ty dA dδ) {![]Ty-unstrip dB (WeakMor+ dA dδ)!} {!!} ([]Ty-lift dA dδ) {!!}
[]Tm-lift = {!!}

substTy-lift : {n : ℕ} (Γ : Ctx n) (A : TyExpr n) (B : TyExpr (suc n)) → (u : TmExpr n) → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ u :> A) → ⊢ Γ 
  → ex.Derivable (liftCtx Γ ⊢ₑ ex.substTy (liftTy (liftCtx Γ ex., liftTy (liftCtx Γ) A) B) (liftTm (liftCtx Γ) u) == liftTy (liftCtx Γ) (substTy B u))

substTm-lift : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {B' : ex.TyExpr (suc n)} {v : TmExpr (suc n)} → {u : TmExpr n} → {u' : ex.TmExpr n} → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ v :> B) → Derivable (Γ ⊢ u :> A) → ⊢ Γ 
  → ex.Derivable (liftCtx Γ ⊢ₑ ex.substTm (liftTm (liftCtx Γ ex., liftTy (liftCtx Γ) A) v) (liftTm (liftCtx Γ) u) == liftTm (liftCtx Γ) (substTm v u) :> ex.substTy B' u')

substTy-lift {n} Γ A .(uu _) u dA UU du dΓ = {!!}
substTy-lift {n} Γ A .(el _ _) u dA (El dB) du dΓ = ex.ElCong {!!}
substTy-lift {n} Γ A .(pi _ _) u dA (Pi dB dB₁) du dΓ = {!!}

substTm-lift = {!!}
