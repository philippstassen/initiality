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

liftTy1 : {n : ℕ} {Γ : Ctx n} → {A : TyExpr n} → (lΓ : ex.Ctx n) → (dA : Derivation (Γ ⊢ A)) → ex.TyExpr n
liftTm1 : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} → {u : TmExpr n} → (dΓ : ex.Ctx n) → (du : Derivation (Γ ⊢ u :> A)) → ex.TmExpr n

liftTyEq1 : {n : ℕ} {Γ : Ctx n} → {A B : TyExpr n} → (Δ : ex.Ctx n) → (dA= : Derivation (Γ ⊢ A == B)) → ex.TyExpr n
liftTyEq2 : {n : ℕ} {Γ : Ctx n} → {A B : TyExpr n} → (Δ : ex.Ctx n) → (dA= : Derivation (Γ ⊢ A == B)) → ex.TyExpr n

liftTmEq1 : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → (Δ : ex.Ctx n) → (dA= : Derivation (Γ ⊢ u == v :> A)) → ex.TmExpr n
liftTmEq2 : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → (Δ : ex.Ctx n) → (dA= : Derivation (Γ ⊢ u == v :> A)) → ex.TmExpr n

liftTmTy : {n : ℕ} {Γ : Ctx n} → {A : TyExpr n} {u : TmExpr n} → (dΓ : ex.Ctx n) → (du : Derivation (Γ ⊢ u :> A)) → ex.TyExpr n

liftTy1 dΓ UU = ex.uu
liftTy1 dΓ (El dv) = ex.el (liftTm1 dΓ dv)
liftTy1 dΓ (Pi dA dA₁) = ex.pi (liftTy1 dΓ dA) (liftTy1 (dΓ ex., liftTy1 dΓ dA) dA₁)

liftTm1 (dΓ ex., dA) (VarLast du) = ex.var last
liftTm1 (dΓ ex., dB) (VarPrev {A = A} dA₁ dk) = ex.weakenTm (liftTm1 dΓ dk)
-- Here we need to influence the derivation in the induction hypothesis. So Type Argument is needed
liftTm1 dΓ (Conv {A = A} {B = B} dA dB₁ du dA=) = {!!}
liftTm1 dΓ (Lam dA dB du) = ex.lam (liftTy1 dΓ dA) (liftTy1 (dΓ ex., liftTy1 dΓ dA) dB) (liftTm1 (dΓ ex., liftTy1 dΓ dA) du)
-- for applying ind hypothesis you need derivation df' such that liftTmTy dΓ df ≡ liftTy1 dΓ df'.
liftTm1 dΓ (App dA dB df da) = ex.app {!!} {!!} (ex.coerc (liftTmTy dΓ df) (ex.pi (liftTy1 dΓ dA) (liftTy1 (dΓ ex., liftTy1 dΓ dA) dB)) (liftTm1 dΓ df)) {!ex.coerc (lift!}


liftTyEq1 Δ (TySymm dB dA dB=) = liftTyEq2 Δ dB=
liftTyEq1 Δ (TyTran dA dB dC dA= dB=) = liftTyEq1 Δ dA=
liftTyEq1 Δ UUCong = ex.uu
liftTyEq1 Δ (ElCong dv dv' dv=) = ex.el (liftTmEq1 Δ dv=)
liftTyEq1 Δ (PiCong dA dA' dB dB' dA= dB=) = {!!}

liftTyEq2 Δ (TySymm dB dA dB=) = {!liftTy1 Δ dA!}
liftTyEq2 Δ (TyTran dA= dA=₁ dA=₂ dA=₃ dA=₄) = {!!}
liftTyEq2 Δ UUCong = {!!}
liftTyEq2 Δ (ElCong dA= dA=₁ dA=₂) = {!!}
liftTyEq2 Δ (PiCong dA= dA=₁ dA=₂ dA=₃ dA=₄ dA=₅) = {!!}

liftTmEq1 Δ du= = {!!}

liftTmEq2 Δ du= = {!!}



liftTmTy (dΓ ex., dA) (VarLast du) = ex.weakenTy dA
liftTmTy (dΓ ex., dB) (VarPrev dA dk) = ex.weakenTy (liftTmTy dΓ dk)
liftTmTy dΓ (Conv du du₁ du₂ du₃) = {!!}
liftTmTy dΓ (Lam dA dB du) = ex.pi (liftTy1 dΓ dA ) (liftTmTy (dΓ ex., liftTy1 dΓ dA) du)
liftTmTy dΓ (App dA dB df da) = {!ex.substTy (liftTy1 dΓ dB) (liftTm1!}

liftCtx1 : {n : ℕ} {Γ : Ctx n} → ⊢R Γ → ex.Ctx n
liftCtx1 {Γ = .◇} tt = ex.◇
liftCtx1 {Γ = .(Γ , A)} (_,_ {Γ = Γ} {A} dΓ dA) = liftCtx1 dΓ ex., liftTy1 (liftCtx1 dΓ) dA

liftJdg1 : {jdg : Judgment} → ⊢R (snd (getCtx jdg)) → Derivation jdg → ex.Judgment
liftJdg1 {Γ ⊢ x} dΓ dj = {!!}
liftJdg1 {Γ ⊢ x :> x₁} dΓ dj = {!liftCtx1 dΓ ex.⊢ liftTm1 (liftCtx1 dΓ) (liftTyTm!}
liftJdg1 {Γ ⊢ x == x₁} dΓ dj = liftCtx1 dΓ ex.⊢ liftTyEq1 (liftCtx1 dΓ) dj == liftTyEq2 (liftCtx1 dΓ) dj
liftJdg1 {Γ ⊢ x == x₁ :> x₂} dΓ dj = {!!}

CanonicityTyEq : {Γ : Ctx n} {A B : TyExpr n} (dΓ : ⊢R Γ) (dA : Derivation (Γ ⊢ A)) (dB : Derivation (Γ ⊢ B)) (dA= : Derivation (Γ ⊢ A == B)) → ex.Derivable (liftCtx1 dΓ ⊢ₑ liftTy1 (liftCtx1 dΓ) dA == liftTy1 (liftCtx1 dΓ) dB)
CanonicityTmEq : {Γ : Ctx n} {u v : TmExpr n} {A A' A'' : TyExpr n} (dΓ : ⊢R Γ) (du : Derivation (Γ ⊢ u :> A)) (dv : Derivation (Γ ⊢ v :> A')) (du= : Derivation (Γ ⊢ u == v :> A'')) → (A ≡ A') → (A ≡ A'') → ex.Derivable (liftCtx1 dΓ ⊢ₑ liftTm1 (liftCtx1 dΓ) du == ex.coerc (liftTmTy (liftCtx1 dΓ) dv) (liftTmTy (liftCtx1 dΓ) du) (liftTm1 (liftCtx1 dΓ) dv) :> liftTmTy (liftCtx1 dΓ) du)

CanonicityTyEq dΓ dA dB (TySymm dA= dA=₁ dA=₂) = {!!}
CanonicityTyEq dΓ dA dB (TyTran dA= dA=₁ dA=₂ dA=₃ dA=₄) = {!!}
CanonicityTyEq dΓ UU UU UUCong = {!!}
CanonicityTyEq dΓ (El dv) (El dv') (ElCong dv₁ dv'₁ dv=) = {!!}
CanonicityTyEq dΓ (Pi dA dB) (Pi dA' dB') (PiCong dA₁ dA'₁ dB₁ dB'₁ dA= dB=) = {!!}
                  where
                  Coercer : {Γ : Ctx n} {A A' : TyExpr n} {B : TyExpr (suc n)} → ⊢R Γ → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ A') → Derivation ((Γ , A') ⊢ B) → Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B)
                  Coercer dΓ dA dA' dB dA= = {!SubstTyR dB ((idMorDerivableR dΓ) , Conv dA dA' (VarLast dA) dA=)!}

CanonicityTmEq (dΓ , x) (VarLast du) (VarLast dv) du= A'≡ A''≡ = {!!}
CanonicityTmEq (dΓ , x) (VarLast du) (VarPrev dv dv₁) du= A'≡ A''≡ = {!du=!}
CanonicityTmEq (dΓ , x) (VarLast du) (Conv dv dv₁ dv₂ dv₃) A'≡ A''≡ du= = {!!}
CanonicityTmEq (dΓ , x) (VarLast du) (Lam dv dv₁ dv₂) A'≡ A''≡ du= = {!!}
CanonicityTmEq (dΓ , x) (VarLast du) (App dv dv₁ dv₂ dv₃) A'≡ A''≡ du= = {!!}
CanonicityTmEq (dΓ , x) (VarPrev du du₁) (VarLast dv) A'≡ A''≡ du= = {!!}
CanonicityTmEq (dΓ , x) (VarPrev du du₁) (VarPrev dv dv₁) A'≡ A''≡ du= = {!!}
CanonicityTmEq (dΓ , x) (VarPrev du du₁) (Conv dv dv₁ dv₂ dv₃) A'≡ A''≡ du= = {!!}
CanonicityTmEq (dΓ , x) (VarPrev du du₁) (Lam dv dv₁ dv₂) A'≡ A''≡ du= = {!!}
CanonicityTmEq (dΓ , x) (VarPrev du du₁) (App dv dv₁ dv₂ dv₃) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (Conv du du₁ du₂ du₃) (VarLast dv) A'≡ refl du= = {!A'≡!}
CanonicityTmEq dΓ (Conv du du₁ du₂ du₃) (VarPrev dv dv₁) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (Conv du du₁ du₂ du₃) (Conv dv dv₁ dv₂ dv₃) A'≡ refl refl = {!A'≡!}
CanonicityTmEq dΓ (Conv du du₁ du₂ du₃) (Lam dv dv₁ dv₂) A'≡ refl du= = {!!}
CanonicityTmEq dΓ (Conv du du₁ du₂ du₃) (App dv dv₁ dv₂ dv₃) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (Lam du du₁ du₂) (VarLast dv) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (Lam du du₁ du₂) (VarPrev dv dv₁) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (Lam du du₁ du₂) (Conv dv dv₁ dv₂ dv₃) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (Lam du du₁ du₂) (Lam dv dv₁ dv₂) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (Lam du du₁ du₂) (App dv dv₁ dv₂ dv₃) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (App du du₁ du₂ du₃) (VarLast dv) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (App du du₁ du₂ du₃) (VarPrev dv dv₁) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (App du du₁ du₂ du₃) (Conv dv dv₁ dv₂ dv₃) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (App du du₁ du₂ du₃) (Lam dv dv₁ dv₂) A'≡ A''≡ du= = {!!}
CanonicityTmEq dΓ (App du du₁ du₂ du₃) (App dv dv₁ dv₂ dv₃) A'≡ A''≡ du= = {!!}

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

--------- The context cannot be lifted independently from the judgment. Since the lifting is derivation sensitive, we need to choose particular derivation to get a well typed judgment
liftCtx : {n : ℕ} {Γ : Ctx n} → ⊢R Γ → ex.Ctx n
liftCtx {Γ = .◇} tt = ex.◇
liftCtx {Γ = .(Γ , A)} (_,_ {Γ = Γ} {A} dΓ dA) = liftCtx dΓ ex., liftTy dA

liftMor : {n m : ℕ} {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → Γ ⊢R δ ∷> Δ → ex.Mor n m
liftMor {δ = .◇} tt = ex.◇
liftMor {δ = .(δ , u)} (_,_ {δ = δ} {u} dδ du) = liftMor dδ ex., liftTm du

---------------------------
---Judgment Lifting
---------------------------
-- We are only lifting the small subset of well formed judgments
-- If using metatheorems, beware: TmTy dApp will not reduce without further pattern matching
-- CAREFUL: Derivations of the same judgment do not coincide (see VarLast for instance)
liftJdg : {n : ℕ} {jdg : Judgment} → ⊢R snd (getCtx jdg) → Derivation (jdg) → ex.Judgment
liftJdg {jdg = Γ ⊢ x} dΓ dj = liftCtx dΓ ex.⊢ liftTy dj
liftJdg (dΓ , dA₁) (VarLast {Γ = Γ} {A} dA) = (liftCtx dΓ ex., liftTy dA) ex.⊢ liftTm (VarLast dA) :> ex.weakenTy (liftTy dA)
----------------------
---- We need to be careful with the choice of the Derivation to lift the typing
----------------------
liftJdg ((dΓ , dC) , dB) (VarPrev {Γ = Γ} {B} {k} {A} dA dk) =  liftCtx ((dΓ , dC) , dB) ex.⊢ liftTm (VarPrev {Γ = Γ} {B} dA dk) :> ex.weakenTy (liftTy (TmTyR (dΓ , dC) dk))
-- liftJdg ((dΓ , dA₁) , dB) (VarPrev {Γ = .(Γ , A)} {B} {.last} {.(weakenTy' last _)} dwA (VarLast {Γ = Γ} {A = A} dA)) =  liftCtx ((dΓ , dA) , dB) ex.⊢ liftTm (VarPrev {Γ = (Γ , A)} {B} (WeakTyR dA) (VarLast dA)) :> ex.weakenTy (ex.weakenTy (liftTy dA))
-- liftJdg ((dΓ , dA₁) , dB) (VarPrev {Γ = .(_ , _)} {B} {.(prev _)} {.(weakenTy' last _)} dwA (VarPrev {B = C} dA dk)) = {! liftCtx dΓ ex.⊢ liftTm (VarPrev {Γ = Γ} {B} dA dk) :> ex.weakenTy (liftTy dA)!}
-- liftJdg dΓ (VarPrev {Γ = Γ} {B} {k} {A} dA (Conv dk dk₁ dk₂ dk₃)) = {!!}
-- -- liftCtx dΓ ex.⊢ liftTm (VarPrev {Γ = Γ} {B} dA dk) :> ex.weakenTy (liftTy dA)

liftJdg {jdg = Γ ⊢ x :> x₁} dΓ (Conv dA dB du dA=) = liftCtx dΓ ex.⊢ ex.coerc (liftTy dA) (liftTy dB) (liftTm du) :> liftTy dB
liftJdg {jdg = Γ ⊢ .(lam _ _ _) :> .(pi _ _)} dΓ (Lam dA dB du) = liftCtx dΓ ex.⊢ liftTm (Lam dA dB du) :> liftTy (Pi dA dB)
liftJdg {jdg = Γ ⊢ .(app _ _ _ _) :> .(_ [ idMor _ , _ ]Ty)} dΓ (App {A = A} dA dB df da) = liftCtx dΓ ex.⊢ liftTm (App dA dB df da) :> liftTy (SubstTyR dB (idMorDerivableR dΓ , congTmTyR (!R ([idMor]TyR A)) da))
liftJdg {jdg = Γ ⊢ x == x₁} dΓ (TySymm dA dB dA=) = liftCtx dΓ ex.⊢ liftTy dB == liftTy dA
liftJdg {jdg = Γ ⊢ x == x₁} dΓ (TyTran dA dB dC dA= dB= ) = liftCtx dΓ ex.⊢ liftTy dA == liftTy dC
liftJdg {jdg = Γ ⊢ .uu == .uu} dΓ UUCong = liftCtx dΓ ex.⊢ ex.uu == ex.uu
liftJdg {jdg = Γ ⊢ .(el _) == .(el _)} dΓ (ElCong dv dv' df=) = liftCtx dΓ ex.⊢ liftTy (El dv) == liftTy (El dv')
liftJdg {jdg = Γ ⊢ .(pi _ _) == .(pi _ _)} dΓ (PiCong dA dA' dB dB' dA= dB=) = liftCtx dΓ ex.⊢ liftTy (Pi dA dB) == liftTy (Pi dA' dB')
---------------
---Tm Equality lift
-------------
liftJdg {jdg = .(_ , _) ⊢ .(var last) == .(var last) :> .(weakenTy' last _)} dΓ (VarLastCong {A = A} dA) = liftCtx dΓ ex.⊢ liftTm (VarLast dA) == liftTm (VarLast dA) :> liftTy (WeakTyR {k = last} {T = A} dA)
liftJdg dΓ (VarPrevCong {B = B} dA dk dk' dk=) = liftCtx dΓ ex.⊢ liftTm (WeakTmR {k = last} {T = B} dk) == liftTm (WeakTmR {k = last} {T = B} dk') :> liftTy (WeakTyR {k = last} {T = B} dA)
liftJdg {jdg = Γ ⊢ x == x₁ :> x₂} dΓ (TmSymm dA du dv du=) = liftCtx dΓ ex.⊢ liftTm dv == liftTm du :> liftTy dA
liftJdg {jdg = Γ ⊢ x == x₁ :> x₂} dΓ (TmTran dA du dv dw du= dv=) = liftCtx dΓ ex.⊢ liftTm du == liftTm dw :> liftTy dA
liftJdg {jdg = Γ ⊢ x == x₁ :> x₂} dΓ (ConvEq dA dB du du' du= dA=) = liftCtx dΓ ex.⊢ liftTm (Conv dA dB du dA=) == liftTm (Conv dA dB du' dA=) :> liftTy dB
liftJdg dΓ (LamCong dA dA' dB dB' du du' dA= dB= du=) = liftCtx dΓ ex.⊢ liftTm (Lam dA dB du) == ex.coerc (liftTy (Pi dA' dB')) (liftTy (Pi dA dB)) (liftTm (Lam dA' dB' du')) :> liftTy (Pi dA dB)
liftJdg {jdg = Γ ⊢ .(app _ _ _ _) == .(app _ _ _ _) :> .(_ [ idMor _ , _ ]Ty)} dΓ (AppCong {n} {Γ = Γ} {a = a} {a' = a'} dA dA' dB dB' df df' da da' dA= dB= df= da=) = liftCtx dΓ ex.⊢ liftTm (App dA dB df da) == ex.coerc (ex.substTy (liftTy dB') (liftTm da')) (ex.substTy (liftTy dB) (liftTm da)) (liftTm (App dA' dB' df' da')) :> ex.substTy (liftTy dB) (liftTm da)
liftJdg {jdg = Γ ⊢ .(app A B (lam A B u) a) == .(u [ idMor _ , a ]Tm) :> .(B [ idMor _ , a ]Ty)} dΓ (BetaPi {A = A} {B} {u} {a} dA dB du da) = liftCtx dΓ ex.⊢ liftTm (App dA dB (Lam dA dB du) da) == ex.substTm (liftTm du) (liftTm da) :> ex.substTy (liftTy dB) (liftTm da)

liftJdg {jdg = Γ ⊢ x == .(lam _ _ (app (weakenTy' last _) (weakenTy' (prev last) _) (weakenTm' last x) (var last))) :> .(pi _ _)} dΓ (EtaPi {n = n} {B = B} dA dB df) = liftCtx dΓ ex.⊢ liftTm df == ex.lam (liftTy dA) (liftTy dB) (ex.app (ex.weakenTy (liftTy dA)) (ex.weakenTy' (prev last) (liftTy dB)) (ex.weakenTm (liftTm df)) (ex.var last)) :> ex.pi (liftTy dA) (liftTy dB)

-- Alternative definition for eta lift
-- liftJdg {jdg = Γ ⊢ x == .(lam _ _ (app (weakenTy' last _) (weakenTy' (prev last) _) (weakenTm' last x) (var last))) :> .(pi _ _)} dΓ (EtaPi {n = n} {B = B} dA dB df)
--                = liftCtx dΓ ex.⊢ liftTm df ==  liftTm (Lam dA dB {! !}) :> liftTy (Pi dA dB)
--                where
--                App+Rewrite : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f : TmExpr n} → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ f :> pi A B) → Derivation ((Γ , A) ⊢ app (weakenTy A) (weakenTy' (prev last) B) (weakenTm f) (var last) :> B)
--                App+Rewrite {A = A} {B = B} {f = f} dA dB df 
--                  with weakenTy' (prev last) B [ (weakenMor (idMor n) , var last) , var last ]Ty | (substTy-weakenTyR' {k = prev (last {n = n})} {A = B} {δ = idMor (suc n)} {t = var last} R∙ ([idMor]TyR B))
--                App+Rewrite {A = A} {.B} {f} dA dB df | B | reflR = {! !R (substTy-weakenTyR' {k = prev (last {n = n})} {A = B} {δ = idMor (suc n)} {t = var last} R∙ ([idMor]TyR B))!}

-- (App (WeakTyR dA) (WeakTyR dB) (WeakTmR df) (VarLast dA))
-- weakenTy' (prev last) B [ (weakenMor (idMor n) , var last) , var last ]Ty
               -- with !R (substTy-weakenTyR' {k = prev (last {n = n})} {A = B} {δ = idMor (suc n)} {t = var last} R∙ ([idMor]TyR B))

               -- with substTy B (var last) | weakenTyInsertR B _ (var last)
-- ... | q | eq = {!eq!}
-- liftCtx dΓ ex.⊢ liftTm df == liftTm (Lam dA dB (App (ex.weakenTy (liftTy dA)) (ex.weakenTy' (prev last) (liftTy dB)) (ex.weakenTm (liftTm df)) (liftTm (VarLast dA)))) :> liftTy (Pi dA dB)

----------------------
---- Judgment-lifting experiments
----------------------
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

weakenTm'-liftTm (Conv dA dB du dA=) = ex.ap-coerc-Tm (weakenTy'-liftTy dA) (weakenTy'-liftTy dB) (weakenTm'-liftTm du)
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

Sound : {jdg : Judgment} → (dΓ : ⊢R snd (getCtx jdg)) → (dj : Derivation (jdg)) → ex.Derivable (liftJdg {n = fst (getCtx jdg)} {jdg = jdg} dΓ dj)
Sound (dΓ , dA) (VarLast dj) = ex.VarLast (Sound dΓ dj)
Sound ((dΓ , dA) , dB) (VarPrev dj (VarLast dj₁)) = {!!}
Sound ((dΓ , dA) , dB) (VarPrev dj (VarPrev dj₁ dj₂)) = {!!}
Sound ((dΓ , dA) , dB) (VarPrev dj (Conv dj₁ dj₂ dj₃ dj₄)) = {!!}
Sound dΓ (VarLastCong dj) = {!!}
Sound dΓ (VarPrevCong dj dj₁ dj₂ dj₃) = {!!}
Sound dΓ (TySymm dj dj₁ dj₂) = {!!}
Sound dΓ (TyTran dj dj₁ dj₂ dj₃ dj₄) = {!!}
Sound dΓ (TmSymm dj dj₁ dj₂ dj₃) = {!!}
Sound dΓ (TmTran dj dj₁ dj₂ dj₃ dj₄ dj₅) = {!!}
Sound dΓ (Conv dj dj₁ dj₂ dj₃) = {!!}
Sound dΓ (ConvEq dj dj₁ dj₂ dj₃ dj₄ dj₅) = {!!}
Sound dΓ UU = {!!}
Sound dΓ UUCong = {!!}
Sound dΓ (El dj) = ex.El {!Sound dΓ dj!}
Sound dΓ (ElCong dj dj₁ dj₂) = {!!}
Sound dΓ (Pi dj dj₁) = {!!}
Sound dΓ (PiCong dj dj₁ dj₂ dj₃ dj₄ dj₅) = {!!}
Sound dΓ (Lam dA dB du) = {!!}
Sound dΓ (LamCong dj dj₁ dj₂ dj₃ dj₄ dj₅ dj₆ dj₇ dj₈) = {!!}
Sound dΓ (App dj dj₁ dj₂ dj₃) = {!!}
Sound dΓ (AppCong dj dj₁ dj₂ dj₃ dj₄ dj₅ dj₆ dj₇ dj₈ dj₉ dj₁₀ dj₁₁) = {!!}
Sound dΓ (BetaPi dj dj₁ dj₂ dj₃) = {!!}
Sound dΓ (EtaPi dj dj₁ dj₂) = {!!}

----------------------
----- Different judgment lifting
----------------------
