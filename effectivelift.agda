{-# OPTIONS --rewriting --prop --allow-unsolved-metas #-}

-- open import Agda.Builtin.Bool
open import common renaming (Unit to metaUnit)
open import normal
import ex 
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)
open import relevant-syntx
open import relevant-rules
open import translation

liftTy : {n : ℕ} {Γ : Ctx n} → {A : TyExpr n} → (dA : Derivation (Γ ⊢ A)) → ex.TyExpr n
liftTm : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} → {u : TmExpr n} → (du : Derivation (Γ ⊢ u :> A)) → ex.TmExpr n

liftTy {A = .uu} UU = ex.uu
liftTy {A = .(el v)} (El {v = v} dv) = ex.el (liftTm dv)
liftTy {A = .(pi A B)} (Pi {A = A} {B} dA dB) = ex.pi (liftTy dA) (liftTy dB)

liftTm {A = .(weakenTy A)} {u = .(var last)} (VarLast {A = A} du) = ex.var last
----------
---VarPrev distinction when conversion is applied in hypothesis
---------
liftTm (VarPrev dA dk) = ex.weakenTm (liftTm dk)
-- liftTm (VarPrev dA (VarLast dl)) = ex.var (prev last)
-- liftTm (VarPrev {k = k} {A} du (Conv {A = A₀} {B = A} dA₀ dA dt dA=)) = ex.coerc (ex.weakenTy (liftTy dA₀)) (ex.weakenTy (liftTy dA)) (ex.var (prev k))
-- liftTm (VarPrev dA (VarPrev {k = k} dA₁ dk)) = {!ex.weakenTm (liftTm dk)!}
---------
---------
-- ex.var (prev k)
liftTm {A = .B} {u = .u} (Conv {u = u} {A = A} {B = B} dA dB du dA=) = ex.coerc (liftTy dA) (liftTy dB) (liftTm du)
liftTm {A = .(pi A B)} {u = .(lam A B u)} (Lam {A = A} {B} {u} dA dB du) = ex.lam (liftTy dA) (liftTy dB) (liftTm du)
liftTm {A = .(substTy B a)} {u = .(app A B f a)} (App {A = A} {B = B} {f = f} {a = a} dA dB df da) = ex.app (liftTy dA) (liftTy dB) (liftTm df) (liftTm da)

liftCtx : {n : ℕ} {Γ : Ctx n} → ⊢R Γ → ex.Ctx n
liftCtx {Γ = .◇} tt = ex.◇
liftCtx {Γ = .(Γ , A)} (_,_ {Γ = Γ} {A} dΓ dA) = liftCtx dΓ ex., liftTy dA

liftMor : {n m : ℕ} {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → Γ ⊢R δ ∷> Δ → ex.Mor n m
liftMor {δ = .◇} tt = ex.◇
liftMor {δ = .(δ , u)} (_,_ {δ = δ} {u} dδ du) = liftMor dδ ex., liftTm du

-- We are only lifting the small subset of well formed judgments
liftJdg : {n : ℕ} {jdg : Judgment} → ⊢R snd (getCtx jdg) → Derivation (jdg) → ex.Judgment
liftJdg {jdg = Γ ⊢ x} dΓ dj = liftCtx dΓ ex.⊢ liftTy dj
liftJdg {jdg = .(Γ , A) ⊢ .(var last) :> .(weakenTy' last A)} dΓ (VarLast {Γ = Γ} {A} dA) = liftCtx dΓ ex.⊢ liftTm (VarLast dA) :> ex.weakenTy (liftTy dA)
liftJdg {jdg = .(Γ , _) ⊢ .(var (prev k)) :> .(weakenTy' last A)} dΓ (VarPrev {Γ = Γ} {k = k} {A} dA dk) = {!!}
liftJdg {jdg = Γ ⊢ x :> x₁} dΓ (Conv dj dj₁ dj₂ dj₃) = {!!}
liftJdg {jdg = Γ ⊢ .(lam _ _ _) :> .(pi _ _)} dΓ (Lam dj dj₁ dj₂) = {!!}
liftJdg {jdg = Γ ⊢ .(app _ _ _ _) :> .(_ [ idMor _ , _ ]Ty)} dΓ (App dj dj₁ dj₂ dj₃) = {!!}
liftJdg {jdg = Γ ⊢ x == x₁} dΓ (TySymm dA dB dA=) = {!!}
liftJdg {jdg = Γ ⊢ x == x₁} dΓ (TyTran dA dB dC dA= dB= ) = {!!}
liftJdg {jdg = Γ ⊢ .uu == .uu} dΓ UUCong = {!!}
liftJdg {jdg = Γ ⊢ .(el _) == .(el _)} dΓ (ElCong dj) = {!!}
liftJdg {jdg = Γ ⊢ .(pi _ _) == .(pi _ _)} dΓ (PiCong dj dj₁ dj₂) = {!!}
liftJdg {jdg = Γ ⊢ x == x₁ :> x₂} dΓ dj = {!!}

{- weakenVar and ex.weakenVar are the same -}
weakenVar-weakenVar : (k : Fin (suc n)) → (x : Fin n) → weakenVar' k x ≡ ex.weakenVar' k x
weakenVar-weakenVar last x = refl
weakenVar-weakenVar (prev k) last = refl
weakenVar-weakenVar (prev k) (prev x) = ap prev (weakenVar-weakenVar k x)

weakenTy'-liftTy : {k : Fin (suc n)} {Γ : Ctx n} {A : TyExpr n} {T : TyExpr (n -F' k)} → (dA : Derivation (Γ ⊢ A)) → liftTy (WeakTyR {k = k} {T = T} dA) ≡ ex.weakenTy' k (liftTy dA)
weakenTm'-liftTm : {k : Fin (suc n)} {Γ : Ctx n} {A : TyExpr n} {u : TmExpr n} {T : TyExpr (n -F' k)} → (du : Derivation (Γ ⊢ u :> A)) → liftTm (WeakTmR {k = k} {T = T} du) ≡ ex.weakenTm' k (liftTm du)

weakenTy'-liftTy UU = refl
weakenTy'-liftTy (El dA) = {!!}
weakenTy'-liftTy (Pi dA dA₁) = ex.ap-pi-Ty (weakenTy'-liftTy dA) (weakenTy'-liftTy dA₁)

-- In proof relevant Derivations, Agda should identify proofs that are the same up to rewriting. This is immediate when using with abstraction instead of the congruence lemmas
weakenTm'-liftTm {k = last} (VarLast du) = refl
weakenTm'-liftTm {k = prev k} (VarLast {A = A} du) with weakenTy' (prev k) (weakenTy A) | weakenTy-weakenTy' {k = k} {A}
weakenTm'-liftTm {k = prev k} (VarLast du) | _ | reflR = refl

weakenTm'-liftTm {k = last} (VarPrev du du₁) = refl
weakenTm'-liftTm {k = prev k} (VarPrev {A = A} du du₁) 
                    with weakenTy' (prev k) (weakenTy A) | weakenTy-weakenTy' {k = k} {A}
... | .(weakenTy' last (weakenTy' k A)) | reflR = ap (λ x → ex.weakenTm x) (weakenTm'-liftTm du₁) ∙ ex.weakenTmCommutes _ _                  


-- weakenTm'-liftTm {k = prev k} (VarPrev {k = last} {A = .(weakenTy A)} dwA (VarLast {A = A} dA))
--                  with weakenTy' (prev k) (weakenTy (weakenTy A)) | weakenTy-weakenTy' {k = k} {weakenTy A}
-- weakenTm'-liftTm {_} {k = prev last} (VarPrev {B = _} {last} {.(weakenTy' last A)} dwA (VarLast {A = A} dA)) | _ | reflR = refl
-- weakenTm'-liftTm {_} {prev (prev k)} (VarPrev {B = _} {last} {.(weakenTy' last A)} dwA (VarLast {A = A} dA)) | _ | reflR = {!!}
-- 
-- weakenTm'-liftTm {k = prev k} (VarPrev du (VarPrev du₁ du₂)) = {!!}
-- weakenTm'-liftTm {k = prev k} (VarPrev {A = A} du (Conv du₁ du₂ du₃ du₄)) 
--                  with weakenTy' (prev k) (weakenTy A) | weakenTy-weakenTy' {k = k} {A}
-- ... | _ | reflR = ex.ap-coerc-Tm (ap (λ x → ex.weakenTy x) (weakenTy'-liftTy du₁) ∙ (! ex.weakenTy-weakenTy)) (ap (λ x → ex.weakenTy x) (weakenTy'-liftTy du₂) ∙ (! ex.weakenTy-weakenTy)) {!!}
-- weakenTm'-liftTm {k = prev k} (VarPrev {A = A} du du₁) with weakenTy' (prev k) (weakenTy A) | weakenTy-weakenTy' {k = k} {A}
-- weakenTm'-liftTm {k = prev k} (VarPrev {k = l} du du₁) | _ | reflR rewrite weakenVar-weakenVar k l = refl

weakenTm'-liftTm (Conv dA dB du dA=) = ex.ap-coerc-Tm {!weakenTy'-liftTy dA!} {!!} {!!}
weakenTm'-liftTm (Lam dA dB du) = ex.ap-lam-Tm {!!} (weakenTy'-liftTy dB) {!!}
weakenTm'-liftTm {k = k} (App {B = B} {a = a} dA dB df da)
                      with weakenTy' k (substTy B a) | weakenTy-substTy' {k = k} {B} {a}
weakenTm'-liftTm {k = k} (App {B = B} {a = a} dA dB df da) | _ | reflR = ex.ap-app-Tm (weakenTy'-liftTy dA) (weakenTy'-liftTy dB) (weakenTm'-liftTm df) (weakenTm'-liftTm da)

weakenMor-liftMor : {Γ : Ctx n} {Δ : Ctx m} {T : TyExpr n} {δ : Mor n m} (dδ : Γ ⊢R δ ∷> Δ) → liftMor (WeakMorR {Γ = Γ} {Δ} {T} {δ} dδ) ≡ ex.weakenMor (liftMor dδ)

weakenMor-liftMor tt = refl
weakenMor-liftMor (dδ , du) = ex.Mor+= (weakenMor-liftMor dδ) (WeakTmEq+Rewrite du)
                  where
                    WeakTmEq+Rewrite : {Γ : Ctx n} {A : TyExpr m} {T : TyExpr n} {δ : Mor n m} {u : TmExpr n} (du : Derivation (Γ ⊢ u :> A [ δ ]Ty)) → liftTm (WeakTm+Rewrite {Γ = Γ} {A} {T} {δ} {u} du) ≡ ex.weakenTm (liftTm du)
                    WeakTmEq+Rewrite {A = A} {δ = δ} du with (A [ weakenMor δ ]Ty) | (weaken[]TyR A δ last) 
                    WeakTmEq+Rewrite du                        | _ | reflR = weakenTm'-liftTm du

weakenMor+-liftMor : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} → (dA : Derivation (Δ ⊢ A)) → (dδ : Γ ⊢R δ ∷> Δ) → liftMor (WeakMorR+ dA dδ) ≡ ex.weakenMor+ (liftMor dδ)
weakenMor+-liftMor dA dδ = ex.Mor+= (weakenMor-liftMor dδ) (MorEq+Rewrite dA dδ)
                   where
                   MorEq+Rewrite : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} → (dA : Derivation (Δ ⊢ A)) → (dδ : Γ ⊢R δ ∷> Δ) → liftTm (WeakMor+Rewrite (SubstTyR dA dδ)) ≡ ex.var last
                   MorEq+Rewrite {Γ = Γ} {Δ} {δ} {A} dA dδ with A [ weakenMor δ ]Ty | weaken[]TyR A δ last
                   MorEq+Rewrite {Γ = Γ} {Δ} {δ} {A} dA dδ | .(weakenTy' last (A [ δ ]Ty)) | reflR = refl

-----------------
---- Substitution commutes with lifting
----------------
liftVar-Var : {k : Fin n} {Γ : Ctx n} {B : TyExpr n} {A : TyExpr n} → (dA : Derivation (Γ ⊢ A)) → (dk : Derivation (Γ ⊢ var k :> A)) → liftTm (VarPrev {B = B} dA dk) ≡ ex.weakenTm (liftTm dk)
liftVar-Var dA (VarLast dk) = refl
liftVar-Var dA (VarPrev dB dk) = refl
liftVar-Var dA (Conv dk dk₁ dk₂ dk₃) = refl

substTy-liftTy : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} (dA : Derivation (Δ ⊢ A)) (dδ : Γ ⊢R δ ∷> Δ) → liftTy (SubstTyR dA dδ) ≡ (liftTy dA) ex.[ liftMor dδ ]Ty
substTm-liftTm : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} {u : TmExpr m} (du : Derivation (Δ ⊢ u :> A)) (dδ : Γ ⊢R δ ∷> Δ) → liftTm (SubstTmR du dδ) ≡ (liftTm du) ex.[ liftMor dδ ]Tm

substTy-liftTy UU dδ = refl
substTy-liftTy (El dA) dδ = {!!}
substTy-liftTy (Pi dA dB) dδ = ex.ap-pi-Ty (substTy-liftTy dA dδ) (substTy-liftTy dB (WeakMorR+ dA dδ) ∙ ap (λ x → liftTy dB ex.[ x ]Ty) (weakenMor+-liftMor dA dδ))

substTm-liftTm {δ = δ , u}(VarLast {A = A} dA) (dδ , x) 
                with A [ δ ]Ty | weakenTyInsertR A δ u
...    | .(weakenTy' last A [ δ , u ]Ty) | reflR = refl
substTm-liftTm {δ = δ , u} (VarPrev {A = A} dA dk) (dδ , x)
            with weakenTy' last A [ δ , u ]Ty | !R (weakenTyInsertR A δ u)
...                            | .(A [ δ ]Ty) | reflR = substTm-liftTm dk dδ ∙ ! (ex.weakenTmInsert (liftTm dk) (liftMor dδ) (liftTm x))
substTm-liftTm (Conv dA dB du dA=) dδ = ex.ap-coerc-Tm (substTy-liftTy dA dδ) (substTy-liftTy dB dδ) (substTm-liftTm du dδ)
substTm-liftTm (Lam dA dB du) dδ = ex.ap-lam-Tm {!!} {!!} {!!}
substTm-liftTm {δ = δ} {u = app A B f a} (App dA dB df da) dδ 
            with (substTy B a) [ δ ]Ty | []Ty-substTyR {B = B} {a} {δ}
...  | .((B [ weakenMor' last δ , var last ]Ty) [ idMor _ , (a [ δ ]Tm) ]Ty) | reflR
              = ex.ap-app-Tm (substTy-liftTy dA dδ) (substTy-liftTy dB (WeakMorR+ dA dδ) ∙ ap (λ x → liftTy dB ex.[ x ]Ty) (weakenMor+-liftMor dA dδ)) (substTm-liftTm df dδ) (substTm-liftTm da dδ)
