{-# OPTIONS --rewriting --prop --without-K #-}

open import common renaming (Unit to metaUnit)
open import normal
import ex 
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)
open import translation

{- feels like I also need to put a coerc in the beginning, to translate a derivation that uses as final step Conversion, this would not be trackable anymore probably, possibly it can be fixed later in the derivation translation by hand -}
{-
+-it : List ℕ → ℕ
+-it [] = zero
+-it (n ∷ ns) = (+-it ns) + n

sizeTy' : TyExpr n → List ℕ
sizeTm' : TmExpr n → List ℕ

sizeTy : TyExpr n → ℕ
sizeTy A = suc (+-it (sizeTy' A))

sizeTm : TmExpr n → ℕ
sizeTm u = suc (+-it (sizeTm' u))

sizeTy' (uu i) = []
sizeTy' (el i v) = sizeTm v ∷ []
sizeTy' (pi A B) = sizeTy A ∷ (sizeTy A + sizeTy B) ∷ []

sizeTm' (var _) = []

sizeTm' (lam A B u) = sizeTy A ∷ (sizeTy A + sizeTy B) ∷ (sizeTy A + sizeTm u) ∷ []
sizeTm' (app A B f a) = sizeTy A ∷ (sizeTy A + sizeTy B) ∷ sizeTm f ∷ sizeTm a ∷ []

sizeCtx : Ctx n → ℕ
sizeCtx ◇ = 0
sizeCtx (Γ , A) = sizeCtx Γ + sizeTy A

sizeMor : Mor n m → ℕ
sizeMor {m = 0} ◇ = 0
sizeMor {m = suc m} (δ , u) = sizeTm u + sizeMor δ
-}

-- sizeTy : TyExpr n → ℕ
-- sizeTm : TmExpr n → ℕ

-- sizeTy (uu i) = zero
-- sizeTy (el i v) = suc (sizeTm v)
-- sizeTy (pi A A₁) = suc (sizeTy A + sizeTy A₁)
-- sizeTm (var x) = zero
-- sizeTm (lam A B u) = suc (sizeTy A + sizeTy B + sizeTm u)
-- sizeTm (app A B u u₁) = suc (sizeTy A + sizeTy B + sizeTm u + sizeTm u₁)

-- sizeCtx : Ctx n → ℕ
-- sizeCtx ◇ = zero
-- sizeCtx (Γ , A) = sizeCtx Γ + sizeTy A

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

lift-weakenTy : {Γ : ex.Ctx n} {A : TyExpr n} → liftTy (Γ ex., liftTy Γ A) (weakenTy A) ≡ ex.weakenTy (liftTy Γ A)
lift-weakenTy {Γ = Γ} {uu i} = refl
lift-weakenTy {Γ = Γ} {el i v} = {!!}
lift-weakenTy {Γ = Γ} {pi A A₁} = {!!}

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
