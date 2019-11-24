{-# OPTIONS --rewriting --prop --without-K #-}

-- open import Agda.Builtin.Bool
open import common renaming (Unit to metaUnit)
open import normal
import ex 
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)
open import translation

-- data ⊥ : Set where
-- 
-- data _+ₜ_ (A : Prop) (B : Prop) : Set where
--   inl : A → A +ₜ B
--   inr : B → A +ₜ B
-- 
-- Nif_then_else_ : {n m : ℕ} → ((n < m) +ₜ (m < n)) → ℕ → ℕ → ℕ
-- Nif_then_else_ (inl x) n m = n
-- Nif_then_else_ (inr x) n m = m
-- 
-- _<≡_ : ℕ → ℕ → Set
-- n <≡ m = (n < m) +ₜ (n ≡ m)
-- 
-- max : List ℕ → ℕ
-- max [] = zero
-- max (x ∷ l) = if x  <ₙ max l then max l else x

getCtx : Judgment → ΣSS ℕ Ctx 
getCtx ( _⊢_ {n = n} Γ x) = (n , Γ)
getCtx (_⊢_:>_ {n = n} Γ x x₁) = n , Γ
getCtx (_⊢_==_ {n = n} Γ x x₁) = n , Γ
getCtx (_⊢_==_:>_ {n = n} Γ x x₁ x₂) = n , Γ


{- in practice, we will fix m to be (suc SizeDer (t)). No matter what m, the terms should be equal in the end-}
constrTy : {n : ℕ} {Γ : ex.Ctx n} → (A : TyExpr n) → ⊢ || Γ ||Ctx → (dA : Derivation (|| Γ ||Ctx ⊢ A)) → ex.TyExpr n
constrTm : {n : ℕ} {Γ : ex.Ctx n} {A : TyExpr n} → (u : TmExpr n) → ⊢ || Γ ||Ctx → Derivation (|| Γ ||Ctx ⊢ u :> A) → ex.TmExpr n

constrTy (uu i) dΓ UU = ex.uu i
constrTy (el i v) dΓ (El dA) = ex.el i (constrTm v dΓ dA)
constrTy (pi A B) dΓ (Pi dA dB) = ex.pi (constrTy A dΓ dA) (constrTy B {!!} {!!})
-- constrTy (uu i) ctx UU = ex.uu i
-- constrTy (el i v) ctx (El dA) = ex.el i (constrTm v ctx dA)
-- constrTy (pi A A₁) ctx  (Pi dA dA₁) = ex.pi (constrTy A ctx dA) (constrTy A₁ (ctx , dA) dA₁)

constrTm u dΓ du = {!!}

constrCtx : {n : ℕ} → (Γ : Ctx n) → ⊢ Γ → ex.Ctx n
constrCtx Γ dΓ = {!!}

constrMor : {n m : ℕ} {Γ : Ctx n} {Δ : Ctx m} → (δ : Mor n m) → ⊢ Γ → Γ ⊢ δ ∷> Δ → ex.Mor n m
constrMor δ dΓ dδ = {!!}

-- constrTmComm-weakenTm' : {Γ : Ctx n} {u : TmExpr n} {k : Fin (suc n)} {T : TyExpr (n -F' k)} {A : TyExpr n} → (dΓ : ⊢ Γ) → (dT : Derivation (cutCtx k Γ ⊢ T)) → (du : Derivation (Γ ⊢ u :> A)) → constrTm (weakenTm' k u) (WeakCtx {k = k} {Γ = Γ} {T = T} dΓ dT) (WeakTm' {k = k} {Γ = Γ} {T = T} du) <-refl ≡R ex.weakenTm' k (constrTm (suc (SizeDer du)) u dΓ du <-refl)
-- constrTmComm-weakenTm' dΓ du du₁ = {!!}
-- 
-- constrMorComm-weakenMor : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr n} {δ : Mor n m} → (dΓ : ⊢R Γ) → (dA : Derivation (Γ ⊢ A)) → (dδ : Γ ⊢R δ ∷> Δ) → constrMor (weakenMor (δ)) (dΓ , dA) (WeakMorR dδ) ≡ ex.weakenMor (constrMor δ dΓ dδ)
-- constrMorComm-weakenMor {Γ = Γ} {Δ = ◇} {A} {◇} dΓ dA dδ = refl
-- constrMorComm-weakenMor {Γ = Γ} {Δ , A₁} {A} {δ , u} dΓ dA dδ = ex.Mor+= {!constrMorComm-weakenMor ?!} {!!}
-- -- ex.Mor+= (constrMorComm-weakenMor dΓ dA (fst dδ)) {!!} ∙ {!!}
-- -- (ap (λ dj → constrTm (suc (SizeDer (dj))) (weakenTm' last u) (dΓ , dA) dj <-refl) {a = congTmTyR (weaken[]TyR A₁ δ last) (WeakTm' (snd dδ))} {!!} ∙ {!!})
-- -- rewrite CongTmR {Γ = Γ , A} {A = weakenTy' last (A₁ [ δ ]Ty) } {B = A₁ [ weakenMor' last δ ]Ty} {u = weakenTm' last u} reflR (weaken[]TyR A₁ δ last) reflR
-- 
-- idMorisidMor : {n : ℕ} {Γ : Ctx n} → (dΓ : ⊢R Γ) → constrMor (idMor n) dΓ (idMorDerivableR dΓ) ≡ ex.idMor n
-- idMorisidMor {zero} dΓ = refl
-- idMorisidMor {suc n} {Γ = Γ , A} dΓ = ex.Mor+= {!idMorisidMor ?!} {!!}
-- 
-- 
-- constrSubstMor : {n m : ℕ} {Γ : Ctx n} {A : TyExpr n} {u : TmExpr n} → Derivation (Γ ⊢ u :> A) → ⊢R Γ → Γ ⊢R (idMor n , u) ∷> (Γ , A)
-- constrSubstMor {A = A} u dΓ = idMorDerivableR dΓ , congTmTyR! ([idMor]TyR A) u
-- 
-- {- this definition assumes that idMor is mapped to ex.idMor which is only up to ≡ corerct -}
-- constrSubstTy : {Γ : Ctx n} → {A : TyExpr n} → {B : TyExpr (suc n)} → {u : TmExpr n} → ⊢R Γ → Derivation (Γ ⊢ u :> A) → Derivation ((Γ , A) ⊢ B) → ex.TyExpr n
-- constrSubstTy {B = B} dΓ du dB = ex.substTy (constrTy (suc (SizeDer dB)) B (dΓ , TmTyR dΓ du) dB <-refl) {!!}

{- Case distinction of derivations might have been unnecessary, see the last judgment cases -}
constrJdg : (j : Judgment) → ( ⊢ (snd (getCtx j))) → Derivation (j) → ex.Judgment
constrJdg j dΓ dj = {!!}
-- constrJdg (Γ ⊢ (uu i)) ctx UU = (constrCtx Γ ctx) ex.⊢ ex.uu i
-- constrJdg (Γ ⊢ (el i v)) ctx (El dj) = (constrCtx Γ ctx) ex.⊢ constrTy (suc (SizeDer (El dj))) (el i v) ctx (El dj) (<-refl)
-- constrJdg (Γ ⊢ (pi A B)) ctx (Pi dj dj₁) =  (constrCtx Γ ctx) ex.⊢ constrTy (suc (SizeDer (Pi dj dj₁))) (pi A B) ctx (Pi dj dj₁) (<-refl)
-- constrJdg ((Γ , A) ⊢ (var last) :> .(weakenTy' last A)) ctx (VarLast dj) = (constrCtx (Γ , A) ctx) ⊢ₑ ex.var last :> ex.weakenTy (constrTy (suc (SizeDer dj)) A (fst ctx) dj (<-refl))
-- constrJdg ((Γ , A) ⊢ (var (prev k)) :> .(weakenTy' last _)) ctx (VarPrev dj dj₁) =  (constrCtx (Γ , _) ctx) ⊢ₑ ex.var (prev k) :> ex.weakenTy (constrTy (suc (SizeDer dj)) _ (fst ctx) (dj) (<-refl))
-- constrJdg (Γ ⊢ x :> x₁) ctx (Conv dj dj₁ dj₂) = constrCtx Γ ctx ⊢ₑ constrTm (suc (SizeDer (Conv dj dj₁ dj₂))) x ctx (Conv dj dj₁ dj₂) <-refl :> constrTy (suc (SizeDer (TyEqTy2R ctx dj₂))) x₁ ctx ( TyEqTy2R ctx dj₂) <-refl 
-- constrJdg (Γ ⊢ (lam A B u) :> (pi A B)) ctx (Lam dj dj₁ dj₂) = constrCtx Γ ctx ⊢ₑ constrTm (suc (SizeDer (Lam dj dj₁ dj₂))) (lam A B u) ctx (Lam dj dj₁ dj₂) <-refl :> constrTy (suc (SizeDer (Pi dj dj₁))) (pi A B) ctx (Pi dj dj₁) <-refl
-- constrJdg (Γ ⊢ (app A B u v) :> .(substTy B v)) ctx (App dj dj₁ dj₂ dj₃) = constrCtx Γ ctx ⊢ₑ constrTm (suc (SizeDer (App dj dj₁ dj₂ dj₃))) (app A B u v) ctx (App dj dj₁ dj₂ dj₃) <-refl :> {!!}
-- -- constrTy {!!} {!!} {!!} {!!} {!!}
-- constrJdg (Γ ⊢ x == x₁) ctx dj = constrCtx Γ ctx ⊢ₑ constrTy (suc (SizeDer dj)) x ctx (TyEqTy1R ctx dj) (SizeTyEqTy1R ctx dj <-refl) ==  constrTy (suc (SizeDer dj)) x₁ ctx (TyEqTy2R ctx dj) (SizeTyEqTy2R ctx dj <-refl)
-- constrJdg (Γ ⊢ x == x₁ :> x₂) ctx dj = constrCtx Γ ctx ⊢ₑ constrTm (suc (SizeDer dj)) x ctx (TmEqTm1R ctx dj) (SizeTmEqTm1R ctx dj <-refl) ==  constrTm (suc (SizeDer dj)) x₁ ctx (TmEqTm2R ctx dj) (SizeTmEqTm2R ctx dj <-refl) :> constrTy {!!} x₂ ctx {!!} {!!}

DerToEx : {j : Judgment} → ( ctx : ⊢ (snd (getCtx j))) → (dj : Derivation j) → (ex.Derivation (constrJdg j ctx dj))
DerToEx dj ctx = {!!}

{- proof that stripping after constructing gives you back where you started from -}

CtxisCtx : (Γ : Ctx n) → (dΓ : ⊢ Γ) → || (constrCtx Γ dΓ) ||Ctx ≡ Γ
CtxisCtx Γ dΓ = {!!}

JudgisJudg : (jdg : Judgment) → ( dΓ : ⊢ (snd (getCtx jdg))) → (dj : Derivation jdg) → || (constrJdg jdg dΓ dj) || ≡ jdg
JudgisJudg (Γ ⊢ .(uu _)) dΓ UU = {!!}
JudgisJudg (Γ ⊢ .(el _ _)) dΓ (El dj) = {!!}
JudgisJudg (Γ ⊢ .(pi _ _)) dΓ (Pi dj dj₁) = {!!}
JudgisJudg (Γ ⊢ x :> x₁) dΓ dj = {!!}
JudgisJudg (Γ ⊢ x == x₁) dΓ dj = {!!}
JudgisJudg (Γ ⊢ x == x₁ :> x₂) dΓ dj = {!!}
