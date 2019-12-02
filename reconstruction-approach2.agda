{-# OPTIONS --rewriting --prop #-}

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

ap-liftTy : {Γ Δ : ex.Ctx n} {A B : TyExpr n} → Γ ≡ Δ → A ≡ B → liftTy Γ A ≡ liftTy Δ B
ap-liftTy refl refl = refl
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
liftMor Γ (Δ ex., A) (δ , u) =  liftMor Γ Δ δ ex., liftTm Γ u
-- liftMor δ Γ ex., coerc (ex.getTy Γ (liftTm Γ u)) liftTm Γ u

liftJdg : Judgment → ex.Judgment
liftJdg (Γ ⊢ x) = liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) x
liftJdg (Γ ⊢ x :> x₁) = liftCtx Γ ⊢ₑ ex.coerc (ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) x)) (liftTy (liftCtx Γ) x₁) (liftTm (liftCtx Γ) x) :> liftTy (liftCtx Γ) x₁
liftJdg (Γ ⊢ x == x₁) = liftCtx Γ ⊢ₑ liftTy (liftCtx Γ) x == liftTy (liftCtx Γ) x₁
liftJdg (Γ ⊢ x == x₁ :> x₂) = liftCtx Γ ⊢ₑ ex.coerc (ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) x)) (liftTy (liftCtx Γ) x₂) (liftTm (liftCtx Γ) x) ==
                             ex.coerc (ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) x₁)) (liftTy (liftCtx Γ) x₂) (liftTm (liftCtx Γ) x₁) :> liftTy (liftCtx Γ) x₂

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

{- substitution does not commute with lifting, since getTy and substitution do not commute (see syntx explicit -}
ap-lift-Mor+ : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {B : TyExpr (suc m)} {δ : Mor n m} → (liftTy Δ A) ex.[ (liftMor Γ Δ δ) ]Ty ≡ liftTy Γ (A [ δ ]Ty) → liftTy (Δ ex., liftTy Δ A) B ex.[ ex.weakenMor+ (liftMor Γ Δ δ) ]Ty ≡ liftTy (Γ ex., (liftTy Γ (A [ δ ]Ty))) (B [ weakenMor+ δ ]Ty)
ap-lift-Mor+ {Γ = Γ} {ex.◇} {A} {uu i} {◇} eq = refl
ap-lift-Mor+ {Γ = Γ} {ex.◇} {A} {el i v} {◇} eq = ex.ap-el-Ty refl (ex.ap-coerc-Tm {!!} {!!} {!!})
ap-lift-Mor+ {Γ = Γ} {ex.◇} {A} {pi B B₁} {◇} eq = {!!}
ap-lift-Mor+ {Γ = Γ} {Δ ex., A₁} {A} {uu i} {δ} eq = refl
ap-lift-Mor+ {Γ = Γ} {Δ ex., A₁} {A} {el i v} {δ} eq = ex.ap-el-Ty refl (ex.ap-coerc-Tm {!!} {!!} {!!})
ap-lift-Mor+ {Γ = Γ} {Δ ex., A₁} {A} {pi B B₁} {δ} eq = {!!}

[]-liftTy : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {A : TyExpr m} {δ : Mor n m} → (liftTy Δ A) ex.[ (liftMor Γ Δ δ) ]Ty ≡ liftTy Γ (A [ δ ]Ty)
[]-liftTm : {Γ : ex.Ctx n} {Δ : ex.Ctx m} {u : TmExpr m} {δ : Mor n m} → (liftTm Δ u) ex.[ (liftMor Γ Δ δ) ]Tm ≡ liftTm Γ (u [ δ ]Tm)

[]-liftTy {Γ = Γ} {Δ} {uu i} {δ} = refl
[]-liftTy {Γ = ex.◇} {ex.◇} {el i (lam A B v)} {δ = ◇} = ex.ap-el-Ty refl (ex.ap-coerc-Tm (ex.ap-pi-Ty []-liftTy []-liftTy) refl (ex.ap-lam-Tm []-liftTy []-liftTy (ex.ap-coerc-Tm {!ex.ap-getTy (ex.Ctx+= {Γ = ex.◇} refl (ap-liftTy {Γ = ex.◇} refl (! ([idMor]Ty A)))) ([]-liftTm {Γ = ex.◇ ex., liftTy ex.◇ (A [ ◇ ]Ty)} {Δ = ex.◇ ex., liftTy ex.◇ A} {u = v} {δ = weakenMor+ ◇}) !} {!!} {!!}))) where
[]-liftTy {Γ = ex.◇} {ex.◇} {el i (app A B v v₁)} {δ} = {!!}
[]-liftTy {Γ = ex.◇} {Δ ex., A} {el i v} {δ} = {!!}
[]-liftTy {Γ = Γ ex., A} {Δ} {el i v} {δ} = {!!}
[]-liftTy {Γ = Γ} {Δ} {pi A A₁} {δ} = {!!}

[]-liftTm {Γ = Γ} {Δ ex., A} {var last} {δ , u} = refl
[]-liftTm {Γ = Γ} {Δ ex., A} {var (prev x)} {δ , u} = {!!}
[]-liftTm {Γ = Γ} {Δ} {lam A B u} {δ} = {!!}
[]-liftTm {Γ = Γ} {Δ} {app A B u u₁} {δ} = {!!}

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
getTy-liftTy : {n : ℕ} (Γ : Ctx n) (u : TmExpr n) → ex.getTy (liftCtx Γ) (liftTm (liftCtx Γ) u) ≡ liftTy (liftCtx Γ) (getTy Γ u)
getTy-liftTy (Γ , A) (var last) = ! (weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) A)
getTy-liftTy (Γ , A) (var (prev x)) rewrite getTy-liftTy Γ (var x) = ! (weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) (getTy Γ (var x)))
getTy-liftTy ◇ (lam A B (var x)) = refl
getTy-liftTy (Γ , A₁) (lam A B (var x)) = refl
getTy-liftTy ◇ (lam A B (lam A₁ B₁ u)) = refl
getTy-liftTy (Γ , A₂) (lam A B (lam A₁ B₁ u)) = refl
getTy-liftTy ◇ (lam A B (app A₁ B₁ u u₁)) = refl
getTy-liftTy (Γ , A₂) (lam A B (app A₁ B₁ u u₁)) = refl
getTy-liftTy ◇ (app A B u u₁) = {!!}
getTy-liftTy (Γ , A₁) (app A B u u₁) = {!!}

Lift-Der : {jdg : Judgment} → Derivable (jdg) → ex.Derivable (liftJdg jdg)
Lift-Der (VarLast {Γ = Γ} {A = A} dj) rewrite weakenTy'-liftTy last (liftCtx Γ) (liftTy (liftCtx Γ) A) A = ex.Conv (ex.WeakTy (Lift-Der dj)) (ex.WeakTy (Lift-Der dj)) (ex.VarLast (Lift-Der dj)) (ex.TyRefl (ex.WeakTy (Lift-Der dj)))
Lift-Der (VarPrev dj dj₁) = {!!}
Lift-Der (VarLastCong dj) = {!!}
Lift-Der (VarPrevCong dj dj₁) = {!!}
Lift-Der (TySymm dj) = {!!}
Lift-Der (TyTran dj dj₁ dj₂) = {!!}
Lift-Der (TmSymm dj) = {!!}
Lift-Der (TmTran dj dj₁ dj₂) = {!!}
Lift-Der (Conv {u = u} {A = A} {B = B} dA dB du dA=) = ex.Conv (ex.coercTy1 (Lift-Der du)) (Lift-Der dB) (ex.coercTm (Lift-Der du)) (ex.TyTran (Lift-Der dA) (ex.coercEq (Lift-Der du)) (Lift-Der dA=))
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
