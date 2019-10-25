{-# OPTIONS --rewriting --prop --without-K #-}

open import common renaming (Unit to metaUnit)
open import normal
import ex 
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)

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

sizeTy : TyExpr n → ℕ
sizeTm : TmExpr n → ℕ

sizeTy (uu i) = zero
sizeTy (el i v) = suc (sizeTm v)
sizeTy (pi A A₁) = suc (sizeTy A + sizeTy A₁)
sizeTm (var x) = zero
sizeTm (lam A B u) = suc (sizeTy A + sizeTy B + sizeTm u)
sizeTm (app A B u u₁) = suc (sizeTy A + sizeTy B + sizeTm u + sizeTm u₁)

sizeCtx : Ctx n → ℕ
sizeCtx ◇ = zero
sizeCtx (Γ , A) = sizeCtx Γ + sizeTy A

constrTy : {n : ℕ} → (m : ℕ) → (Γ : Ctx n) → (A : TyExpr n) → ((sizeTy A) + (sizeCtx Γ)) < m → ex.TyExpr n
constrTm : {n : ℕ} → (m : ℕ) → (Γ : Ctx n) → (u : TmExpr n) → (sizeTm u + sizeCtx Γ) < m → ex.TmExpr n
constrCtx : {n : ℕ} → (m : ℕ) → (Γ : Ctx n) → sizeCtx Γ < m → ex.Ctx n

constrTy (suc m) Γ (uu i) <m = ex.uu i
constrTy (suc m) Γ (el i v) <m = ex.el i (ex.coerc (ex.getTy (constrCtx m Γ {!!}) (constrTm m Γ v (suc-ref-< <m))) (ex.uu i) (constrTm (m) Γ v (suc-ref-< <m)) )
constrTy (suc m) Γ (pi A A₁) <m = ex.pi (constrTy m Γ A (<-+m^2 {! !} {!!} {!!} {!!} {!!})) (constrTy m (Γ , A) A₁ {!!})
-- constrTy (suc zero) Γ (uu i) <m = ex.uu i
-- constrTy (suc m) Γ (el i v) <m = ex.el i (ex.coerc (ex.getTy (constrCtx Γ) (constrTm m Γ v (suc-ref-< <m))) (ex.uu i) (constrTm (m) Γ v (suc-ref-< <m)))
-- constrTy (suc m) Γ (pi A A₁) <m = ex.pi (constrTy (m) Γ A {!!}) (constrTy m (Γ , A) A₁ {!!})

constrTm m Γ u <m = {!!}
{- 
constrTy zero Γ (uu i) = ex.uu i
constrTy Γ (el i v) = ex.el i (ex.coerc (ex.getTy (constrCtx Γ) (constrTm Γ v)) (ex.uu i) (constrTm Γ v))
constrTy Γ (pi A A₁) = ex.pi (constrTy Γ A) (constrTy (Γ , A) A₁)

constrTm Γ (var x) = ex.var x
constrTm Γ (lam A B u) = ex.lam (constrTy Γ A) (constrTy (Γ , A) B) (ex.coerc (ex.getTy (constrCtx (Γ , A)) (constrTm (Γ , A) u)) (constrTy (Γ , A) B) (constrTm (Γ , A) u))
constrTm Γ (app A B u u₁) = ex.app (constrTy Γ A) (constrTy (Γ , A) B) (ex.coerc (ex.getTy (constrCtx Γ) (constrTm Γ u)) (constrTy Γ (pi A B)) (constrTm Γ u)) (ex.coerc (ex.getTy (constrCtx Γ) (constrTm Γ u₁)) (constrTy Γ A) (constrTm Γ u₁))
-}
{- Circularity: Ctx n needs Type n, which itself already uses Ctx (n+1) -}
constrCtx m ◇ <m = ex.◇
constrCtx (m) (Γ , A) <m = constrCtx m Γ (<-+m (sizeCtx Γ) (sizeTy A) m <m) ex., constrTy (suc (sizeTy A + sizeCtx Γ)) Γ A <-refl
