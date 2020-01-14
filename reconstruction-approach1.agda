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

data ⊥ : Set where

data _+ₜ_ (A : Prop) (B : Prop) : Set where
  inl : A → A +ₜ B
  inr : B → A +ₜ B

Nif_then_else_ : {n m : ℕ} → ((n < m) +ₜ (m < n)) → ℕ → ℕ → ℕ
Nif_then_else_ (inl x) n m = n
Nif_then_else_ (inr x) n m = m

_<≡_ : ℕ → ℕ → Set
n <≡ m = (n < m) +ₜ (n ≡ m)

max : List ℕ → ℕ
max [] = zero
max (x ∷ l) = if x  <ₙ max l then max l else x

SizeDer : {jdg : Judgment} → Derivation (jdg) → ℕ
SizeDer (VarLast dj) = suc (SizeDer (dj))
SizeDer (VarPrev dj dj₁) = suc (SizeDer (dj) + SizeDer (dj₁))
SizeDer (VarLastCong dj) = suc (SizeDer dj)
SizeDer (VarPrevCong dj dj₁) =  suc (SizeDer (dj) + SizeDer (dj₁))
SizeDer (TySymm dj) =  suc (SizeDer dj)
SizeDer (TyTran dj dj₁ dj₂) =  suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂))
SizeDer (TmSymm dj) =  suc (SizeDer dj)
SizeDer (TmTran dj dj₁ dj₂) =  suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂))
SizeDer (Conv dj dj₁ dj₂) = suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂))
SizeDer (ConvEq dj dj₁ dj₂) =  suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂))
SizeDer UU = zero
SizeDer UUCong = zero
SizeDer (El dj) =  suc (SizeDer dj)
SizeDer (ElCong dj) =  suc (SizeDer dj)
SizeDer (Pi dj dj₁) =  suc (SizeDer (dj) + SizeDer (dj₁))
SizeDer (PiCong dj dj₁ dj₂) =  suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂))
SizeDer (Lam dj dj₁ dj₂) =  suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂))
SizeDer (LamCong dj dj₁ dj₂ dj₃) =  suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂) + SizeDer (dj₃))
SizeDer (App dj dj₁ dj₂ dj₃) =  suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂) + SizeDer (dj₃))
SizeDer (AppCong dj dj₁ dj₂ dj₃ dj₄) =  suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂) + SizeDer (dj₃) + SizeDer (dj₄))
SizeDer (BetaPi dj dj₁ dj₂ dj₃) =  suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂) + SizeDer (dj₃))
SizeDer (EtaPi dj dj₁ dj₂) = suc (SizeDer (dj) + SizeDer (dj₁) + SizeDer (dj₂))

congRespSize : {jdg : Judgment} → (dj : Derivation (jdg)) {dj₁ : Derivation (jdg)} → dj ≡ dj₁ → SizeDer dj ≡ SizeDer dj₁
congRespSize dj refl = refl

SizeTyEqTy1R : {A B : TyExpr n} {Γ : Ctx n} {m : ℕ} → (dΓ : ⊢R Γ) → (dA= : Derivation (Γ ⊢ A == B)) → SizeDer (dA=) < m → SizeDer (TyEqTy1R dΓ dA=) < m
SizeTyEqTy2R : {A B : TyExpr n} {Γ : Ctx n} → (dΓ : ⊢R Γ) → (dA= : Derivation (Γ ⊢ A == B)) → SizeDer (dA=) < m → SizeDer (TyEqTy2R dΓ dA=) < m
SizeTmEqTm1R : {u v : TmExpr n} {A : TyExpr n} {Γ : Ctx n} {m : ℕ} → (dΓ : ⊢R Γ) → (du= : Derivation (Γ ⊢ u == v :> A)) → SizeDer (du=) < m → SizeDer (TmEqTm1R dΓ du=) < m
SizeTmEqTm2R : {u v : TmExpr n} {A : TyExpr n} {Γ : Ctx n} {m : ℕ} → (dΓ : ⊢R Γ) → (du= : Derivation (Γ ⊢ u == v :> A)) → SizeDer (du=) < m → SizeDer (TmEqTm2R dΓ du=) < m

SizeTyEqTy1R {m = m} dΓ (TySymm dA=) <m = SizeTyEqTy2R dΓ dA= (<-+m' 1 (SizeDer dA=) m <m)
SizeTyEqTy1R {m = m} dΓ (TyTran dA= dA=₁ dA=₂) <m = SizeTyEqTy1R dΓ dA=₁ (<-+m^21 (SizeDer dA=) (SizeDer dA=₁) (SizeDer dA=₂) m (<-+m' 1 (SizeDer dA= + SizeDer dA=₁ + SizeDer dA=₂) m <m)) 
SizeTyEqTy1R {m = suc m} dΓ UUCong <m = suc-pos m
SizeTyEqTy1R {m = m} dΓ (ElCong dA=) <m = {!!}
SizeTyEqTy1R {m = m} dΓ (PiCong dA= dA=₁ dA=₂) <m = {!!}

SizeTyEqTy2R {m = m} dΓ (TySymm dA=) <m =  SizeTyEqTy1R dΓ dA= (<-+m' 1 (SizeDer dA=) m <m)
SizeTyEqTy2R {m = m} dΓ (TyTran dA= dA=₁ dA=₂) <m = {!!}
SizeTyEqTy2R {m = m} dΓ UUCong <m = {!!}
SizeTyEqTy2R {m = m} dΓ (ElCong dA=) <m = {!!}
SizeTyEqTy2R {m = m} dΓ (PiCong dA= dA=₁ dA=₂) <m = {!!}

SizeTmEqTm1R {m = m} dΓ (VarLastCong du=) <m = {!!}
SizeTmEqTm1R {m = m} dΓ (VarPrevCong du= du=₁) <m = {!!}
SizeTmEqTm1R {m = m} dΓ (TmSymm du=) <m = {!!}
SizeTmEqTm1R {m = m} dΓ (TmTran du= du=₁ du=₂) <m = {!!}
SizeTmEqTm1R {m = m} dΓ (ConvEq du= du=₁ du=₂) <m = {!!}
SizeTmEqTm1R {m = m} dΓ (LamCong du= du=₁ du=₂ du=₃) <m = {!!}
SizeTmEqTm1R {m = m} dΓ (AppCong du= du=₁ du=₂ du=₃ du=₄) <m = {!!}
SizeTmEqTm1R {m = m} dΓ (BetaPi du= du=₁ du=₂ du=₃) <m = {!!}
SizeTmEqTm1R {m = m} dΓ (EtaPi du= du=₁ du=₂) <m = {!!}
SizeTmEqTm2R {m = m} dΓ du= <m = {!!}

embedTy : {n : ℕ} → TyExpr n → ex.TyExpr n
embedTm : {n : ℕ} → TmExpr n → ex.TmExpr n

embedTy (uu) = ex.uu
embedTy (el v) = ex.el (embedTm v)
embedTy (pi A A₁) = ex.pi (embedTy A) (embedTy A₁)

embedTm (var x) = ex.var x
embedTm (lam A B u) = ex.lam (embedTy A) (embedTy B) (embedTm u)
embedTm (app A B u u₁) = ex.app (embedTy A) (embedTy B) (embedTm u) (embedTm u₁)

{- in practice, we will fix m to be (suc SizeDer (t)). No matter what m, the terms should be equal in the end-}
liftTy : {n : ℕ} {Γ : Ctx n} → (m : ℕ) → (A : TyExpr n) → ⊢R Γ → (dA : Derivation (Γ ⊢ A)) → SizeDer (dA) < m → ex.TyExpr n
liftTm : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} → (m : ℕ) → (u : TmExpr n) → ⊢R Γ → (du : Derivation (Γ ⊢ u :> A)) → SizeDer (du) < m → ex.TmExpr n

liftTy zero A dΓ dA () 
liftTy (suc m) (uu) dΓ UU <m = ex.uu
liftTy (suc m) (el v) dΓ (El dA) <m = ex.el (liftTm m v dΓ dA (suc-ref-< <m))
liftTy (suc m) (pi A B) dΓ (Pi dA dB) <m = ex.pi (liftTy m A dΓ dA (<-+m (SizeDer dA) (SizeDer dB) m (suc-ref-< <m))) (liftTy m B (dΓ , dA) dB ( <-+m' (SizeDer dA) (SizeDer dB) m (suc-ref-< <m)))
-- liftTy (uu) ctx UU = ex.uu
-- liftTy (el v) ctx (El dA) = ex.el (liftTm v ctx dA)
-- liftTy (pi A A₁) ctx  (Pi dA dA₁) = ex.pi (liftTy A ctx dA) (liftTy A₁ (ctx , dA) dA₁)

{- Problem: Hopefully my treatment of the implicit variables is okay.
 PROBLEM: The type arguments of the coercion have the same "level" as the term we recurse on. So there might be an termination issue. For instance just an infinite coerc sequence 
 IDEA: Take derivationlength as parameter
-}
liftTm (suc m) (var last) dΓ (VarLast du) <m = ex.var last
liftTm (suc m) (var (prev k)) dΓ (VarPrev du du₁) <m = ex.var (prev k)
liftTm (suc m) u dΓ (Conv {A = A} {B = B} du du₁ du₂) <m = ex.coerc (liftTy m A dΓ du (<-+m^2 (SizeDer du) (SizeDer du₁) (SizeDer du₂) m (suc-ref-< <m)) ) (liftTy m B dΓ (TyEqTy2R dΓ du₂) (SizeTyEqTy2R dΓ du₂ (<-+m^22 (SizeDer du) (SizeDer du₁) (SizeDer du₂) m (suc-ref-< <m)))) (liftTm m u dΓ du₁ (<-+m^21 (SizeDer du) (SizeDer du₁) (SizeDer du₂) m (suc-ref-< <m)))
liftTm (suc m) (lam A B u) dΓ (Lam du du₁ du₂) <m = ex.lam (liftTy m A dΓ du (<-+m^2 _ _ _ m (suc-ref-< <m))) (liftTy m B (dΓ , du) du₁ (<-+m^21 (SizeDer du) (SizeDer du₁) (SizeDer du₂) m (suc-ref-< <m))) (liftTm m u (dΓ , du) du₂ (<-+m^22 (SizeDer du) (SizeDer du₁) (SizeDer du₂) m (suc-ref-< <m)))
liftTm (suc m) (app A B u x) dΓ (App du du₁ du₂ du₃) <m = ex.app (liftTy m A dΓ du ( <-+m^2 (SizeDer du) (SizeDer du₁) (SizeDer du₂) m (<-+m (SizeDer du + SizeDer du₁ + SizeDer du₂) (SizeDer du₃) m (suc-ref-< <m)))) (liftTy m B (dΓ , du) du₁ ( <-+m^21 (SizeDer du) (SizeDer du₁) (SizeDer du₂) m (<-+m (SizeDer du + SizeDer du₁ + SizeDer du₂) (SizeDer du₃) m (suc-ref-< <m)))) (liftTm m u dΓ du₂ ( <-+m^22 (SizeDer du) (SizeDer du₁) (SizeDer du₂) m (<-+m (SizeDer du + SizeDer du₁ + SizeDer du₂) (SizeDer du₃) m (suc-ref-< <m)))) (liftTm m x dΓ du₃ ( <-+m' (SizeDer du + SizeDer du₁ + SizeDer du₂) (SizeDer du₃) m (suc-ref-< <m)))
-- liftTm .(var last) dΓ (VarLast du) = {!!}
-- liftTm .(var (prev _)) dΓ (VarPrev du du₁) = {!!}
-- liftTm u dΓ (Conv {A = A} {B = B} du du₁ du₂) = ex.coerc (liftTy A dΓ du) (liftTy B dΓ (TyEqTy2R dΓ du₂)) {!!}
-- liftTm .(lam _ _ _) dΓ (Lam du du₁ du₂) = {!!}
-- liftTm .(app _ _ _ _) dΓ (App du du₁ du₂ du₃) = {!!}
{- liftTm (var .last) dΓ (VarLast du) = ex.var last
liftTm (var .(prev _)) dΓ (VarPrev {k = k} du du₁) = ex.var (prev k)
liftTm (var x) dΓ (Conv {A = A} {B = B} du du₁ du₂) = ex.coerc (liftTy A dΓ du) (liftTy B dΓ (TyEqTy2R dΓ du₂)) (ex.var x)
liftTm (lam A B u) dΓ (Conv {A = A₁} {B = A₂} du du₁ du₂) = ex.coerc (liftTy A₁ dΓ du) (liftTy A₂ dΓ (TyEqTy2R dΓ du₂)) {!!}
liftTm (lam A B u) ctx (Lam du du₁ du₂) = {!!}
liftTm (app A B u u₁) ctx du = {!!}
-}
liftCtx : {n : ℕ} → (Γ : Ctx n) → (dj : ⊢R Γ) → ex.Ctx n

liftCtx ◇ _ = ex.◇
liftCtx (Γ , (uu)) (fst₁ , UU) = (liftCtx Γ fst₁) ex., liftTy (suc 0) (uu) fst₁ UU (suc-pos 0) 
liftCtx (Γ , (el v)) (fst₁ , El snd₁) = (liftCtx Γ fst₁) ex., liftTy (suc (SizeDer (El snd₁))) (el v) fst₁ (El snd₁) <-refl 
liftCtx (Γ , (pi A B)) (fst₁ , Pi snd₁ snd₂) = (liftCtx Γ fst₁) ex., liftTy (suc (SizeDer (Pi snd₁ snd₂))) (pi A B) fst₁ (Pi snd₁ snd₂) <-refl
-- liftCtx (Γ , .(sig _ _)) (fst₁ , Sig snd₁ snd₂) = {!!}
-- liftCtx (Γ , .empty) (fst₁ , Empty) = {!!}
-- liftCtx (Γ , .unit) (fst₁ , Unit) = {!!}
-- liftCtx (Γ , .nat) (fst₁ , Nat) = {!!}
-- liftCtx (Γ , .(id _ _ _)) (fst₁ , Id' snd₁ snd₂ snd₃) = {!!}

liftMor : {n m : ℕ} {Γ : Ctx n} {Δ : Ctx m} → (δ : Mor n m) → ⊢R Γ → Γ ⊢R δ ∷> Δ → ex.Mor n m
liftMor ◇ dΓ dδ = ex.◇
liftMor {Γ = Γ} {Δ = Δ , A} (δ , u) dΓ dδ = (liftMor {Γ = Γ} {Δ = Δ} δ dΓ (fst dδ)) ex., liftTm (suc (SizeDer (snd dδ))) u dΓ (snd dδ) <-refl

liftTmComm-weakenTm' : {Γ : Ctx n} {u : TmExpr n} {k : Fin (suc n)} {T : TyExpr (n -F' k)} {A : TyExpr n} → (dΓ : ⊢R Γ) → (dT : Derivation (cutCtx k Γ ⊢ T)) → (du : Derivation (Γ ⊢ u :> A)) → liftTm (suc (SizeDer (WeakTm' du))) (weakenTm' k u) (WeakCtxR {k = k} {Γ = Γ} {T = T} dΓ dT) (WeakTm' {k = k} {Γ = Γ} {T = T} du) <-refl ≡R ex.weakenTm' k (liftTm (suc (SizeDer du)) u dΓ du <-refl)
liftTmComm-weakenTm' dΓ du du₁ = {!!}

liftMorComm-weakenMor : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr n} {δ : Mor n m} → (dΓ : ⊢R Γ) → (dA : Derivation (Γ ⊢ A)) → (dδ : Γ ⊢R δ ∷> Δ) → liftMor (weakenMor (δ)) (dΓ , dA) (WeakMorR dδ) ≡ ex.weakenMor (liftMor δ dΓ dδ)
liftMorComm-weakenMor {Γ = Γ} {Δ = ◇} {A} {◇} dΓ dA dδ = refl
liftMorComm-weakenMor {Γ = Γ} {Δ , A₁} {A} {δ , u} dΓ dA dδ = ex.Mor+= {!liftMorComm-weakenMor ?!} {!!}
-- ex.Mor+= (liftMorComm-weakenMor dΓ dA (fst dδ)) {!!} ∙ {!!}
-- (ap (λ dj → liftTm (suc (SizeDer (dj))) (weakenTm' last u) (dΓ , dA) dj <-refl) {a = congTmTyR (weaken[]TyR A₁ δ last) (WeakTm' (snd dδ))} {!!} ∙ {!!})
-- rewrite CongTmR {Γ = Γ , A} {A = weakenTy' last (A₁ [ δ ]Ty) } {B = A₁ [ weakenMor' last δ ]Ty} {u = weakenTm' last u} reflR (weaken[]TyR A₁ δ last) reflR

idMorisidMor : {n : ℕ} {Γ : Ctx n} → (dΓ : ⊢R Γ) → liftMor (idMor n) dΓ (idMorDerivableR dΓ) ≡ ex.idMor n
idMorisidMor {zero} dΓ = refl
idMorisidMor {suc n} {Γ = Γ , A} dΓ = ex.Mor+= {!idMorisidMor ?!} {!!}


liftSubstMor : {n m : ℕ} {Γ : Ctx n} {A : TyExpr n} {u : TmExpr n} → Derivation (Γ ⊢ u :> A) → ⊢R Γ → Γ ⊢R (idMor n , u) ∷> (Γ , A)
liftSubstMor {A = A} u dΓ = idMorDerivableR dΓ , congTmTyR! ([idMor]TyR A) u

{- this definition assumes that idMor is mapped to ex.idMor which is only up to ≡ corerct -}
liftSubstTy : {Γ : Ctx n} → {A : TyExpr n} → {B : TyExpr (suc n)} → {u : TmExpr n} → ⊢R Γ → Derivation (Γ ⊢ u :> A) → Derivation ((Γ , A) ⊢ B) → ex.TyExpr n
liftSubstTy {B = B} dΓ du dB = ex.substTy (liftTy (suc (SizeDer dB)) B (dΓ , TmTyR dΓ du) dB <-refl) {!!}

{- Case distinction of derivations might have been unnecessary, see the last judgment cases -}
liftJdg : (j : Judgment) → ( ⊢R (snd (getCtx j))) → Derivation (j) → ex.Judgment

liftJdg (Γ ⊢ (uu)) ctx UU = (liftCtx Γ ctx) ex.⊢ ex.uu
liftJdg (Γ ⊢ (el v)) ctx (El dj) = (liftCtx Γ ctx) ex.⊢ liftTy (suc (SizeDer (El dj))) (el v) ctx (El dj) (<-refl)
liftJdg (Γ ⊢ (pi A B)) ctx (Pi dj dj₁) =  (liftCtx Γ ctx) ex.⊢ liftTy (suc (SizeDer (Pi dj dj₁))) (pi A B) ctx (Pi dj dj₁) (<-refl)
liftJdg ((Γ , A) ⊢ (var last) :> .(weakenTy' last A)) ctx (VarLast dj) = (liftCtx (Γ , A) ctx) ⊢ₑ ex.var last :> ex.weakenTy (liftTy (suc (SizeDer dj)) A (fst ctx) dj (<-refl))
liftJdg ((Γ , A) ⊢ (var (prev k)) :> .(weakenTy' last _)) ctx (VarPrev dj dj₁) =  (liftCtx (Γ , _) ctx) ⊢ₑ ex.var (prev k) :> ex.weakenTy (liftTy (suc (SizeDer dj)) _ (fst ctx) (dj) (<-refl))
liftJdg (Γ ⊢ x :> x₁) ctx (Conv dj dj₁ dj₂) = liftCtx Γ ctx ⊢ₑ liftTm (suc (SizeDer (Conv dj dj₁ dj₂))) x ctx (Conv dj dj₁ dj₂) <-refl :> liftTy (suc (SizeDer (TyEqTy2R ctx dj₂))) x₁ ctx ( TyEqTy2R ctx dj₂) <-refl 
liftJdg (Γ ⊢ (lam A B u) :> (pi A B)) ctx (Lam dj dj₁ dj₂) = liftCtx Γ ctx ⊢ₑ liftTm (suc (SizeDer (Lam dj dj₁ dj₂))) (lam A B u) ctx (Lam dj dj₁ dj₂) <-refl :> liftTy (suc (SizeDer (Pi dj dj₁))) (pi A B) ctx (Pi dj dj₁) <-refl
liftJdg (Γ ⊢ (app A B u v) :> .(substTy B v)) ctx (App dj dj₁ dj₂ dj₃) = liftCtx Γ ctx ⊢ₑ liftTm (suc (SizeDer (App dj dj₁ dj₂ dj₃))) (app A B u v) ctx (App dj dj₁ dj₂ dj₃) <-refl :> {!!}
-- liftTy {!!} {!!} {!!} {!!} {!!}
liftJdg (Γ ⊢ x == x₁) ctx dj = liftCtx Γ ctx ⊢ₑ liftTy (suc (SizeDer dj)) x ctx (TyEqTy1R ctx dj) (SizeTyEqTy1R ctx dj <-refl) ==  liftTy (suc (SizeDer dj)) x₁ ctx (TyEqTy2R ctx dj) (SizeTyEqTy2R ctx dj <-refl)
liftJdg (Γ ⊢ x == x₁ :> x₂) ctx dj = liftCtx Γ ctx ⊢ₑ liftTm (suc (SizeDer dj)) x ctx (TmEqTm1R ctx dj) (SizeTmEqTm1R ctx dj <-refl) ==  liftTm (suc (SizeDer dj)) x₁ ctx (TmEqTm2R ctx dj) (SizeTmEqTm2R ctx dj <-refl) :> liftTy {!!} x₂ ctx {!!} {!!}

DerToEx : {j : Judgment} → ( ctx : ⊢R (snd (getCtx j))) → (dj : Derivation j) → (ex.Derivable (liftJdg j ctx dj))
DerToEx dj ctx = {!!}

{- proof that stripping after liftucting gives you back where you started from -}

CtxisCtx : (Γ : Ctx n) → (dΓ : ⊢R Γ) → || (liftCtx Γ dΓ) ||Ctx ≡ Γ
CtxisCtx Γ dΓ = {!!}

JudgisJudg : (jdg : Judgment) → ( dΓ : ⊢R (snd (getCtx jdg))) → (dj : Derivation jdg) → || (liftJdg jdg dΓ dj) || ≡ jdg
JudgisJudg (Γ ⊢ .(uu)) dΓ UU = {!!}
JudgisJudg (Γ ⊢ .(el _)) dΓ (El dj) = {!!}
JudgisJudg (Γ ⊢ .(pi _ _)) dΓ (Pi dj dj₁) = {!!}
JudgisJudg (Γ ⊢ x :> x₁) dΓ dj = {!!}
JudgisJudg (Γ ⊢ x == x₁) dΓ dj = {!!}
JudgisJudg (Γ ⊢ x == x₁ :> x₂) dΓ dj = {!!}
