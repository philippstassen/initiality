{-# OPTIONS --rewriting --prop --without-K --allow-unsolved-metas #-}

open import common renaming (Unit to metaUnit) renaming (UnitR to metaUnitR)
open import typetheory
open import syntx
open import reflection
open import rules
open import relevant-syntx

{- Rules for proof relevant reasoning -}
data Derivation : rules.Judgment → Set where

  -- Variable rules
  VarLast : {Γ : Ctx n} {A : TyExpr n}
    → Derivation (Γ ⊢ A)
    → Derivation ((Γ , A) ⊢ var last :> weakenTy A)
  VarPrev : {Γ : Ctx n} {B : TyExpr n} {k : Fin n} {A : TyExpr n}
    → Derivation (Γ ⊢ A)
    → Derivation (Γ ⊢ var k :> A)
    → Derivation ((Γ , B) ⊢ var (prev k) :> weakenTy A)
          
  -- Congruence for variables
  VarLastCong : {Γ : Ctx n} {A : TyExpr n}
    → Derivation (Γ ⊢ A)
    → Derivation ((Γ , A) ⊢ var last == var last :> weakenTy A)
  VarPrevCong : {Γ : Ctx n} {B : TyExpr n} {k k' : Fin n} {A : TyExpr n}
    → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ var k :> A) → Derivation (Γ ⊢ var k' :> A) 
    → Derivation (Γ ⊢ var k == var k' :> A) 
    → Derivation ((Γ , B) ⊢ var (prev k) == var (prev k') :> weakenTy A)
          
  -- Symmetry and transitivity for types
  TySymm : {Γ : Ctx n} {A B : TyExpr n}
    → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ B) 
    → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ B == A)
  TyTran : {Γ : Ctx n} {A B C : TyExpr n}
    → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ B) 
    → Derivation (Γ ⊢ C) → Derivation (Γ ⊢ A == B)→ Derivation (Γ ⊢ B == C) → Derivation (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmSymm : {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
    → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ v :> A) 
    → Derivation (Γ ⊢ u == v :> A) → Derivation (Γ ⊢ v == u :> A)
  TmTran : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
    → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ v :> A) 
    → Derivation (Γ ⊢ w :> A) → Derivation (Γ ⊢ u == v :> A)→ Derivation (Γ ⊢ v == w :> A) → Derivation (Γ ⊢ u == w :> A)

  -- Conversion rules
  Conv : {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n} → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ B) → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ u :> B)
  ConvEq : {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n} → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ B) → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ u' :> A) 
    → Derivation (Γ ⊢ u == u' :> A) → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ u == u' :> B)


  -- Rules for UU
  UU : {Γ : Ctx n}
    → Derivation (Γ ⊢ uu)
  UUCong : {Γ : Ctx n}
    → Derivation (Γ ⊢ uu == uu)

  -- Rules for El
  El : {Γ : Ctx n} {v : TmExpr n}
    → Derivation (Γ ⊢ v :> uu) → Derivation (Γ ⊢ el v)
  ElCong : {Γ : Ctx n} {v v' : TmExpr n} → Derivation (Γ ⊢ v :> uu) → Derivation (Γ ⊢ v' :> uu) 
    → Derivation (Γ ⊢ v == v' :> uu) → Derivation (Γ ⊢ el v == el v')


  -- Rules for Pi
  Pi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} 
    → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ pi A B)
  PiCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)}
    → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ A') → Derivation ((Γ , A) ⊢ B) → Derivation ((Γ , A') ⊢ B')
    → Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B == B') → Derivation (Γ ⊢ pi A B == pi A' B')


  -- Rules for lambda
  Lam : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
    → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation ((Γ , A) ⊢ u :> B)
    → Derivation (Γ ⊢ lam A B u :> pi A B)
  LamCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)}
    → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ A') → Derivation ((Γ , A) ⊢ B) → Derivation ((Γ , A') ⊢ B') → Derivation ((Γ , A) ⊢ u :> B) → Derivation ((Γ , A') ⊢ u' :> B') 
    → Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B == B') → Derivation ((Γ , A) ⊢ u == u' :> B)
    → Derivation (Γ ⊢ lam A B u == lam A' B' u' :> pi A B)

  -- Rules for app
  App : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f a : TmExpr n}
    → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ f :> pi A B) → Derivation (Γ ⊢ a :> A)
    → Derivation (Γ ⊢ app A B f a :> substTy B a)
  AppCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n}
    → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ A') → Derivation ((Γ , A) ⊢ B) → Derivation ((Γ , A') ⊢ B') → Derivation (Γ ⊢ f :> pi A B) → Derivation (Γ ⊢ f' :> pi A' B') → Derivation (Γ ⊢ a :> A) → Derivation (Γ ⊢ a' :> A') 
    →  Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B == B') → Derivation (Γ ⊢ f == f' :> pi A B) → Derivation (Γ ⊢ a == a' :> A)
    → Derivation (Γ ⊢ app A B f a == app A' B' f' a' :> substTy B a)
  -- Beta-reductions
  BetaPi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
    → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation ((Γ , A) ⊢ u :> B) → Derivation (Γ ⊢ a :> A)
    → Derivation (Γ ⊢ app A B (lam A B u) a == substTm u a :> substTy B a)
  -- Eta-equivalences
  EtaPi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f : TmExpr n}
    → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ f :> pi A B)
    → Derivation (Γ ⊢ f == lam A B (app (weakenTy A) (weakenTy' (prev last) B) (weakenTm f) (var last)) :> pi A B)
--   EtaSig' : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ u :> sig A B)
--     → Derivation (Γ ⊢ u == pair A B (pr1 A B u) (pr2 A B u) :> sig A B)

{- Derivability of contexts, context equality, context morphisms, and context morphism equality -}

data ⊢R_ : Ctx n → Set where
  tt : ⊢R ◇
  _,_ : {Γ : Ctx n} {A : _} → (⊢R Γ) → Derivation (Γ ⊢ A) → ⊢R (Γ , A)

data ⊢R_==_ : Ctx n → Ctx n → Set where
  tt : ⊢R ◇ == ◇
  _,_ : {Γ Γ' : Ctx n} {A A' : TyExpr n} → (⊢R Γ == Γ') → Derivation (Γ' ⊢ A == A') → ⊢R (Γ , A) == (Γ' , A')

data _⊢R_∷>_ (Γ : Ctx n) : Mor n m → Ctx m → Set where
  tt : Γ ⊢R ◇ ∷> ◇
  _,_ : {Δ : Ctx m} {δ : Mor n m} {u : TmExpr n} {A : TyExpr m} → (Γ ⊢R δ ∷> Δ) → Derivation (Γ ⊢ u :> A [ δ ]Ty) → (Γ ⊢R (δ , u) ∷> (Δ , A))

data _⊢R_==_∷>_ (Γ : Ctx n) : Mor n m → Mor n m → Ctx m → Set where
  tt : Γ ⊢R ◇ == ◇ ∷> ◇
  _,_ : {Δ : Ctx m} {δ δ' : Mor n m} {u u' : TmExpr n} {A : TyExpr m} → (Γ ⊢R δ == δ' ∷> Δ) → Derivation (Γ ⊢ u == u' :> A [ δ ]Ty) → (Γ ⊢R (δ , u) == (δ' , u') ∷> (Δ , A))

-- ⊢R_ : Ctx n → Set
-- ⊢R ◇ = metaUnitR
-- ⊢R (Γ , A) = (⊢R Γ) ×R Derivation (Γ ⊢ A)
-- 
-- ⊢R_==_ : Ctx n → Ctx n → Set
-- ⊢R ◇ == ◇ = metaUnitR
-- ⊢R (Γ , A) == (Γ' , A') = (⊢R Γ == Γ') ×R Derivation (Γ ⊢ A) ×R Derivation (Γ' ⊢ A') ×R Derivation (Γ ⊢ A == A') ×R Derivation (Γ' ⊢ A == A')
-- 
-- _⊢R_∷>_ : (Γ : Ctx n) → Mor n m → Ctx m → Set
-- Γ ⊢R ◇ ∷> ◇ = metaUnitR
-- Γ ⊢R (δ , u) ∷> (Δ , A) = (Γ ⊢R δ ∷> Δ) ×R Derivation (Γ ⊢ u :> A [ δ ]Ty) 
-- 
-- _⊢R_==_∷>_ : (Γ : Ctx n) → Mor n m → Mor n m → Ctx m → Set
-- Γ ⊢R ◇ == ◇ ∷> ◇ = metaUnitR
-- Γ ⊢R (δ , u) == (δ' , u') ∷> (Δ , A) = (Γ ⊢R δ == δ' ∷> Δ) ×R Derivation (Γ ⊢ u == u' :> A [ δ ]Ty)

 {- Congruences as needed -}

congTyEqR : {Γ : Ctx n} {A A' B B' : TyExpr n} → A ≡R A' → B ≡R B' → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ A' == B')
congTyEqR reflR reflR dA= = dA=

congTyEqR! : {Γ : Ctx n} {A A' B B' : TyExpr n} → A' ≡R A → B' ≡R B → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ A' == B')
congTyEqR! reflR reflR dA= = dA=

congTmR : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡R A' → u ≡R u' → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ u' :> A')
congTmR reflR reflR du = du

congTmR! : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A' ≡R A → u' ≡R u → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ u' :> A')
congTmR! reflR reflR du = du

congTmTyR : {Γ : Ctx n} {A A' : TyExpr n} {u : TmExpr n} → A ≡R A' → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ u :> A')
congTmTyR reflR du = du

congTmTyR! : {Γ : Ctx n} {A A' : TyExpr n} {u : TmExpr n} → A' ≡R A → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ u :> A')
congTmTyR! reflR du = du

congTmEqTyR : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡R A' → Derivation (Γ ⊢ u == u' :> A) → Derivation (Γ ⊢ u == u' :> A')
congTmEqTyR reflR du= = du=

congTmEqTyR! : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A' ≡R A → Derivation (Γ ⊢ u == u' :> A) → Derivation (Γ ⊢ u == u' :> A')
congTmEqTyR! reflR du= = du=

congTmEqR : {Γ : Ctx n} {A A' : TyExpr n} {u u' v v' : TmExpr n} → u ≡R v → u' ≡R v' → A ≡R A' → Derivation (Γ ⊢ u == u' :> A) → Derivation (Γ ⊢ v == v' :> A')
congTmEqR reflR reflR reflR du= = du=

congTmEqR! : {Γ : Ctx n} {A A' : TyExpr n} {u u' v v' : TmExpr n} → v ≡R u → v' ≡R u' → A' ≡R A → Derivation (Γ ⊢ u == u' :> A) → Derivation (Γ ⊢ v == v' :> A')
congTmEqR! reflR reflR reflR du= = du=

-- new congruences
CongTmR : {Γ Δ : Ctx n} {A B : TyExpr n} {u v : TmExpr n} → Γ ≡R Δ → A ≡R B → u ≡R v → Derivation (Γ ⊢ u :> A) ≡ Derivation (Δ ⊢ v :> B)
CongTmR reflR reflR reflR = refl

-- Reflexivity rules for the proof relevant derivations
TyReflR : {Γ : Ctx n} {A : TyExpr n} → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ A == A)
TmReflR : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ u == u :> A)

TyReflR (Pi dA dB) = PiCong dA dA dB dB (TyReflR dA) (TyReflR dB)
TyReflR UU = UUCong
TyReflR (El dv) = ElCong dv dv (TmReflR dv)

TmReflR (VarLast dA) = VarLastCong dA
TmReflR (VarPrev dA dk) = VarPrevCong dA {!!} {!!} (TmReflR dk) 
TmReflR (Conv dA dB du dA=) = ConvEq dA dB {!!} {!!} (TmReflR du) dA=
TmReflR (Lam dA dB du) = LamCong dA {!!} {!!} {!!} {!!} {!!} (TyReflR dA) (TyReflR dB) (TmReflR du)
TmReflR (App dA dB df da) = AppCong dA {!!} {!!} {!!} {!!} {!!} {!!} {!!} (TyReflR dA) (TyReflR dB) (TmReflR df) (TmReflR da)

CtxReflR : {Γ : Ctx n} → ⊢R Γ → ⊢R Γ == Γ
CtxReflR {Γ = ◇} tt = tt
CtxReflR {Γ = Γ , A} (dΓ , dA) = (CtxReflR dΓ , {!!})

MorReflR : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → (Γ ⊢R δ ∷> Δ) → (Γ ⊢R δ == δ ∷> Δ)
MorReflR {Δ = ◇} {δ = ◇} dδ = tt
MorReflR {Δ = Δ , B} {δ = δ , u} (dδ , du) = MorReflR dδ , TmReflR du


-- Weakening and Substitution for proof relevant
SubstTyR : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m}
       → Derivation (Δ ⊢ A) → Γ ⊢R δ ∷> Δ → Derivation (Γ ⊢ A [ δ ]Ty)
SubstTmR : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivation (Δ ⊢ u :> A) → Γ ⊢R δ ∷> Δ → Derivation (Γ ⊢ u [ δ ]Tm :> A [ δ ]Ty)
SubstTyEqR : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ : Mor n m}
       → Derivation (Δ ⊢ A == A') → Γ ⊢R δ ∷> Δ → Derivation (Γ ⊢ A [ δ ]Ty == A' [ δ ]Ty)
SubstTmEqR : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivation (Δ ⊢ u == u' :> A) → (Γ ⊢R δ ∷> Δ) → Derivation (Γ ⊢ u [ δ ]Tm == u' [ δ ]Tm :> A [ δ ]Ty)
SubstTyMorEqR : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivation (Δ ⊢ A) → (Γ ⊢R δ ∷> Δ)
       → (Γ ⊢R δ == δ' ∷> Δ) → Derivation (Γ ⊢ A [ δ ]Ty == A [ δ' ]Ty)
SubstTmMorEqR : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} →  Derivation (Δ ⊢ u :> A) → (Γ ⊢R δ ∷> Δ) 
       → (Γ ⊢R δ == δ' ∷> Δ) → Derivation (Γ ⊢ u [ δ ]Tm == u [ δ' ]Tm :> A [ δ ]Ty)

WeakTyR : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {A : TyExpr n}
     → Derivation (Γ ⊢ A) → Derivation (weakenCtx k Γ T ⊢ weakenTy' k A)
WeakTmR : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {u : TmExpr n} {A : TyExpr n}
     → Derivation (Γ ⊢ u :> A) → Derivation (weakenCtx k Γ T ⊢ weakenTm' k u :> weakenTy' k A)
WeakTyEqR : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {A A' : TyExpr n}
     → Derivation (Γ ⊢ A == A') → Derivation (weakenCtx k Γ T ⊢ weakenTy' k A == weakenTy' k A')
WeakTmEqR : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {u u' : TmExpr n} {A : TyExpr n}
     → Derivation (Γ ⊢ u == u' :> A) → Derivation (weakenCtx k Γ T ⊢ weakenTm' k u == weakenTm' k u' :> weakenTy' k A)

WeakCtxR : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} → ⊢R Γ → Derivation (cutCtx k Γ ⊢ T) → ⊢R (weakenCtx k Γ T)
WeakCtxR {k = last} {Γ} dΓ dT = dΓ , dT
WeakCtxR {k = (prev k)} {Γ = Γ , A} (dΓ , dA) dT = WeakCtxR {k = k} (dΓ) dT , WeakTyR (dA)

-------------
---- Rewriting theorems
-------------
WeakTm+Rewrite : {Γ : Ctx n} {B : TyExpr m} {T : TyExpr n} {δ : Mor n m} {u : TmExpr n} (du : Derivation (Γ ⊢ u :> B [ δ ]Ty)) → Derivation ((Γ , T) ⊢ weakenTm u :> B [ weakenMor δ ]Ty)
WeakTm+Rewrite {B = B} {δ = δ} du with (B [ weakenMor δ ]Ty) | (weaken[]TyR B δ last)
WeakTm+Rewrite du | _ | reflR = WeakTmR du

WeakMor+Rewrite : {Γ : Ctx n} {A : TyExpr m} {δ : Mor n m} → Derivation (Γ ⊢ A [ δ ]Ty) → Derivation ((Γ , (A [ δ ]Ty)) ⊢ var last :> (A [ weakenMor δ ]Ty))
WeakMor+Rewrite {Γ = Γ} {A} {δ} dAδ with A [ weakenMor δ ]Ty | weaken[]TyR A δ last 
...                 | .(weakenTy' last (A [ δ ]Ty)) | reflR = VarLast dAδ

----------------
----------------
WeakMorR : {Γ : Ctx n} {Δ : Ctx m} {T : TyExpr n} {δ : Mor n m} → Γ ⊢R δ ∷> Δ → (Γ , T) ⊢R weakenMor δ ∷> Δ
WeakMorR {Δ = ◇} {δ = ◇} tt = tt
WeakMorR {Γ = Γ} {Δ = Δ , B} {T = T} {δ = δ , u} (dδ , du) = (WeakMorR dδ , WeakTm+Rewrite du)
--               where
--               WeakTm+Rewrite : {Γ : Ctx n} {B : TyExpr m} {T : TyExpr n} {δ : Mor n m} {u : TmExpr n} (du : Derivation (Γ ⊢ u :> B [ δ ]Ty)) → Derivation ((Γ , T) ⊢ weakenTm u :> B [ weakenMor δ ]Ty)
--               WeakTm+Rewrite {B = B} {δ = δ} du with (B [ weakenMor δ ]Ty) | (weaken[]TyR B δ last)
--               WeakTm+Rewrite du | _ | reflR = WeakTmR du

-- = WeakMorR dδ , congTmTyR (weaken[]TyR _ _ _) (WeakTmR du)

{-  Try to get rid of congTmTyR by with abstraction. There might be some universe issues...
with (CongTm {Γ = Γ , T} {Δ = Γ , T} {A = weakenTy (B [ δ ]Ty)} {B = B [ weakenMor' last δ ]Ty} {u = weakenTm u} reflR (weaken[]TyR B δ last) reflR)
WeakMorR {Δ = Δ , B} {δ = δ , u} (dδ , du)   | eq = (WeakMorR dδ , {!WeakTmR du!} )
-}

WeakMorEqR : {Γ : Ctx n } {Δ : Ctx m} {T : TyExpr n} {δ δ' : Mor n m} → (Γ ⊢R δ == δ' ∷> Δ) → ((Γ , T) ⊢R weakenMor δ == weakenMor δ' ∷> Δ)
WeakMorEqR {Δ = ◇} {δ = ◇} {◇} dδ = tt
WeakMorEqR {Δ = Δ , B} {δ = δ , u} {δ' , u'} (dδ , du) = (WeakMorEqR dδ , congTmEqTyR (weaken[]TyR _ _ _) (WeakTmEqR du))

WeakMorR+~ : {Γ : Ctx n} {Δ : Ctx m} (A : TyExpr m) {δ : Mor n m} → Derivation (Γ ⊢ A [ δ ]Ty) → Γ ⊢R δ ∷> Δ → (Γ , A [ δ ]Ty) ⊢R weakenMor+ δ ∷> (Δ , A)
WeakMorR+~ {Γ = Γ} {Δ} A {δ} dAδ dδ = (WeakMorR dδ , WeakMor+Rewrite {Γ = Γ} {A} {δ} dAδ)
-- congTmTyR (weaken[]TyR _ _ _) (VarLast dAδ)
WeakMorR+ : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} → Derivation (Δ ⊢ A) → Γ ⊢R δ ∷> Δ → (Γ , A [ δ ]Ty) ⊢R weakenMor+ δ ∷> (Δ , A)
WeakMorR+ dA dδ = WeakMorR+~ _ (SubstTyR dA dδ) dδ

WeakMorR+Eq : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivation (Δ ⊢ A) → Γ ⊢R δ ∷> Δ → Γ ⊢R δ == δ' ∷> Δ → (Γ , A [ δ ]Ty) ⊢R weakenMor+ δ == weakenMor+ δ' ∷> (Δ , A)
WeakMorR+Eq dA dδ dδ= = (WeakMorEqR dδ= , TmReflR (congTmTyR (weaken[]TyR _ _ _) (VarLast (SubstTyR dA dδ))))


SubstTyR {A = pi A B} (Pi dA dB) dδ = Pi (SubstTyR dA dδ) (SubstTyR dB (WeakMorR+ dA dδ))
SubstTyR {A = uu} UU dδ = UU
SubstTyR {A = el v} (El dA) dδ = El (SubstTmR dA dδ)

SubstTmR (Conv dA dB du dA=) dδ = Conv (SubstTyR dA dδ) (SubstTyR dB dδ) (SubstTmR du dδ) (SubstTyEqR dA= dδ)
SubstTmR {Δ = (Δ , A)} {var last} {δ = δ , u} (VarLast dA) (dδ , du)
                                        with A [ δ ]Ty | weakenTyInsertR A δ u
...                  | .(weakenTy' last A [ δ , u ]Ty) | reflR = du
SubstTmR {Δ = (Δ , _)} {var k} {δ = δ , u} (VarPrev {A = A} dA dk) (dδ , du)
            with weakenTy' last A [ δ , u ]Ty | !R (weakenTyInsertR A δ u)
...                            | .(A [ δ ]Ty) | reflR = SubstTmR dk dδ
SubstTmR {u = lam A B u} (Lam dA dB du) dδ = Lam (SubstTyR dA dδ) (SubstTyR dB (WeakMorR+ dA dδ)) (SubstTmR du (WeakMorR+ dA dδ))
SubstTmR {u = app A B f a} {δ = δ} (App dA dB df da) dδ
            with (substTy B a) [ δ ]Ty | []Ty-substTyR {B = B} {a} {δ}
...  | .((B [ weakenMor' last δ , var last ]Ty) [ idMor _ , (a [ δ ]Tm) ]Ty) | reflR
     = App (SubstTyR dA dδ) (SubstTyR dB (WeakMorR+ dA dδ)) (SubstTmR df dδ) (SubstTmR da dδ)

SubstTyEqR (TySymm dA dB dA=) dδ = TySymm {!!} {!!} (SubstTyEqR dA= dδ)
SubstTyEqR (TyTran dA dB dC dA= dB=) dδ = TyTran {!!} (SubstTyR dB dδ) {!!} (SubstTyEqR dA= dδ) (SubstTyEqR dB= dδ)

SubstTyEqR (PiCong dA dA' dB dB' dA= dB=) dδ = PiCong (SubstTyR dA dδ) {!!} {!!} {!!} (SubstTyEqR dA= dδ) (SubstTyEqR dB= (WeakMorR+ dA dδ))
SubstTyEqR UUCong dδ = UUCong
SubstTyEqR (ElCong dv dw dv=) dδ = ElCong {!!} {!!} (SubstTmEqR dv= dδ)

SubstTmEqR {δ = _ , _} (VarLastCong _)     (_ , du) = congTmEqTyR! (weakenTyInsertR _ _ _) (TmReflR du)
SubstTmEqR {δ = _ , _} (VarPrevCong _ dk dk' dA=) (dδ , _) = congTmEqTyR! (weakenTyInsertR _ _ _) (SubstTmEqR dA= dδ)
SubstTmEqR (TmSymm dA du du' du=) dδ = TmSymm {!!} {!!} {!!} (SubstTmEqR du= dδ)
SubstTmEqR (TmTran dA du dv dw du= dv=) dδ = TmTran {!!} {!!} (SubstTmR dv dδ) {!!} (SubstTmEqR du= dδ) (SubstTmEqR dv= dδ)
SubstTmEqR (ConvEq dA dB du du' du= dA=) dδ = ConvEq (SubstTyR dA dδ) (SubstTyR dB dδ) {!!} {!!} (SubstTmEqR du= dδ) (SubstTyEqR dA= dδ) 
SubstTmEqR (LamCong dA dA' dB dB' du du' dA= dB= du=) dδ = LamCong (SubstTyR dA dδ) {!!} {!!} {!!} {!!} {!!} (SubstTyEqR dA= dδ) (SubstTyEqR dB= (WeakMorR+ dA dδ)) (SubstTmEqR du= (WeakMorR+ dA dδ))
SubstTmEqR (AppCong dA dA' dB dB' df df' da da' dA= dB= df= da=) dδ = congTmEqTyR! []Ty-substTyR (AppCong (SubstTyR dA dδ) {!!} {!!} {!!} {!!} {!!} {!!} {!!} (SubstTyEqR dA= dδ) (SubstTyEqR dB= (WeakMorR+ dA dδ)) (SubstTmEqR df= dδ) (SubstTmEqR da= dδ))
SubstTmEqR (BetaPi {u = u} dA dB du da) dδ = congTmEqR! reflR ([]Tm-substTmR u) []Ty-substTyR (BetaPi (SubstTyR dA dδ) (SubstTyR dB (WeakMorR+ dA dδ)) (SubstTmR du (WeakMorR+ dA dδ )) (SubstTmR da dδ))
SubstTmEqR (EtaPi {f = f} dA dB df) dδ =
  congTmEqR! reflR (apR-lam-Tm reflR reflR (apR-app-Tm []Ty-weakenTyR []Ty-weakenTy1R ([]Tm-weakenTmR f) reflR)) reflR
            (EtaPi (SubstTyR dA dδ)
                   (SubstTyR dB (WeakMorR+ dA dδ))
                   (SubstTmR df dδ))



WeakTyR (Pi dA dB) = Pi (WeakTyR dA) (WeakTyR dB)
WeakTyR UU = UU
WeakTyR (El dv) = El (WeakTmR dv)

WeakTmR (Conv dA dB du dA=) = Conv (WeakTyR dA) (WeakTyR dB) (WeakTmR du) (WeakTyEqR dA=) 
WeakTmR {k = last}   (VarLast dA)    = VarPrev (WeakTyR dA) (VarLast dA)
WeakTmR {k = last}   (VarPrev dA dk) = VarPrev (WeakTyR dA) (VarPrev dA dk)
WeakTmR {k = prev k} (VarLast {A = A} dA)
         with weakenTy' (prev k) (weakenTy A) | (weakenTy-weakenTy' {k = k} {A})
WeakTmR {k = prev k} (VarLast {A = A} dA) | _ | reflR = VarLast (WeakTyR dA)
-- congTmTyR! weakenTy-weakenTy' (VarLast (WeakTyR dA))
WeakTmR {k = prev k} (VarPrev {A = A} dA dk) with weakenTy' (prev k) (weakenTy A) | weakenTy-weakenTy' {k = k} {A}
WeakTmR {k = prev k} (VarPrev dA dk) | _ | reflR = VarPrev (WeakTyR dA) (WeakTmR dk)
-- congTmTyR! weakenTy-weakenTy' (VarPrev (WeakTyR dA) (WeakTmR dk))
WeakTmR (Lam dA dB du) = Lam (WeakTyR dA) (WeakTyR dB) (WeakTmR du)
WeakTmR {k = k} (App {B = B} {a = a} dA dB df da) 
                      with weakenTy' k (substTy B a) | weakenTy-substTy' {k = k} {B} {a}
WeakTmR {k = k} (App {B = B} {a = a} dA dB df da) | _ | reflR = App (WeakTyR dA) (WeakTyR dB) (WeakTmR df) (WeakTmR da)
-- congTmTyR! weakenTy-substTy' (App (WeakTyR dA) (WeakTyR dB) (WeakTmR df) (WeakTmR da))

WeakTyEqR (TySymm dA dB dA=) = TySymm {!!} {!!} (WeakTyEqR dA=)
WeakTyEqR (TyTran dA dB dC dA= dB=) = TyTran {!!} (WeakTyR dB) {!!} (WeakTyEqR dA=) (WeakTyEqR dB=)
WeakTyEqR (PiCong dA dA' dB dB' dA= dB=) = PiCong (WeakTyR dA) {!!} {!!} {!!} (WeakTyEqR dA=) (WeakTyEqR dB=)
WeakTyEqR UUCong = UUCong
WeakTyEqR (ElCong dv dw dv=) = ElCong {!!} {!!} (WeakTmEqR dv=)

WeakTmEqR {k = last}   (VarLastCong dA)     = VarPrevCong (WeakTyR dA) {!!} {!!} (VarLastCong dA)
WeakTmEqR {k = last}   (VarPrevCong dA dk dk' dk=) = VarPrevCong (WeakTyR dA) {!!} {!!} (WeakTmEqR dk=)
WeakTmEqR {k = prev k} (VarLastCong dA)     = congTmEqTyR! weakenTy-weakenTy' (VarLastCong (WeakTyR dA))
WeakTmEqR {k = prev k} (VarPrevCong dA dk dk' dk=) = congTmEqTyR! weakenTy-weakenTy' (VarPrevCong (WeakTyR dA) {!!} {!!} (WeakTmEqR dk=))
WeakTmEqR (TmSymm dA du dv du=) = TmSymm {!!} {!!} {!!} (WeakTmEqR du=)
WeakTmEqR (TmTran dA du dv dw du= dv=) = TmTran {!!} {!!} (WeakTmR dv) {!!} (WeakTmEqR du=) (WeakTmEqR dv=)
WeakTmEqR (ConvEq dA dB du du' du= dA=) = ConvEq (WeakTyR dA) (WeakTyR dB) {!!} {!!} (WeakTmEqR du=) (WeakTyEqR dA=)
-- WeakTmEqR UUUUCong = UUUUCong
-- WeakTmEqR (PiUUCong da da= db=) = PiUUCong (WeakTmR da) (WeakTmEqR da=) (WeakTmEqR db=)
WeakTmEqR (LamCong dA dA' dB dB' du du' dA= dB= du=) = LamCong (WeakTyR dA) {!!} {!!} {!!} {!!} {!!} (WeakTyEqR dA=) (WeakTyEqR dB=) (WeakTmEqR du=)
WeakTmEqR (AppCong dA dA' dB dB' df df' da da' dA= dB= df= da=) = congTmEqTyR! weakenTy-substTy' (AppCong (WeakTyR dA) {!!} {!!} {!!} {!!} {!!} {!!} {!!} (WeakTyEqR dA=) (WeakTyEqR dB=) (WeakTmEqR  df=) (WeakTmEqR da=))
WeakTmEqR {u = app A B (lam A B u) a} (BetaPi dA dB du da) = congTmEqR! reflR (weakenTm-substTmR u) weakenTy-substTy' (BetaPi (WeakTyR dA) (WeakTyR dB) (WeakTmR du) (WeakTmR da))
WeakTmEqR (EtaPi {f = f} dA dB df) =
  congTmEqR! reflR (apR-lam-Tm reflR reflR (apR-app-Tm weakenTy-weakenTy' weakenTy-weakenTy1R (!R (weakenTmCommutesR _ f)) reflR)) reflR
            (EtaPi (WeakTyR dA)
                   (WeakTyR dB)
                   (WeakTmR df))

SubstTyMorEqR (Pi dA dB) dδ dδ= = PiCong (SubstTyR dA dδ) {!!} {!!} {!!} (SubstTyMorEqR dA dδ dδ=) (SubstTyMorEqR dB (WeakMorR+ dA dδ) (WeakMorR+Eq dA dδ dδ=))
SubstTyMorEqR UU dδ dδ= = UUCong
SubstTyMorEqR (El dv) dδ dδ= = ElCong {!!} {!!} (SubstTmMorEqR dv dδ dδ=)

SubstTmMorEqR {δ = _ , _} {δ' = _ , _} (VarLast _) dδ (_ , du=) = congTmEqTyR! (weakenTyInsertR _ _ _) du=
SubstTmMorEqR {δ = _ , _} {δ' = _ , _} (VarPrev _ dk) (dδ , _) (dδ= , _) = congTmEqTyR! (weakenTyInsertR _ _ _) (SubstTmMorEqR dk dδ dδ=)
SubstTmMorEqR (Conv dA dB du dA=) dδ dδ= = ConvEq (SubstTyR dA dδ) (SubstTyR dB dδ) {!!} {!!} (SubstTmMorEqR du dδ dδ=) (SubstTyEqR dA= dδ)
SubstTmMorEqR (Lam dA dB du) dδ dδ= = LamCong (SubstTyR dA dδ) {!!} {!!} {!!} {!!} {!!} (SubstTyMorEqR dA dδ dδ=) (SubstTyMorEqR dB (WeakMorR+ dA dδ) (WeakMorR+Eq dA dδ dδ=)) (SubstTmMorEqR du (WeakMorR+ dA dδ) (WeakMorR+Eq dA dδ dδ=))
SubstTmMorEqR (App dA dB df da) dδ dδ= = congTmEqTyR! []Ty-substTyR (AppCong (SubstTyR dA dδ) {!!} {!!} {!!} {!!} {!!} {!!} {!!} (SubstTyMorEqR dA dδ dδ=) (SubstTyMorEqR dB (WeakMorR+ dA dδ) (WeakMorR+Eq dA dδ dδ=)) (SubstTmMorEqR df dδ dδ=) (SubstTmMorEqR da dδ dδ=))

SubstTyFullEqR : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m} → Derivation (Δ ⊢ A') → (Γ ⊢R δ ∷> Δ)
       → Derivation (Δ ⊢ A == A') → (Γ ⊢R δ == δ' ∷> Δ) → Derivation (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
SubstTyFullEqR dA' dδ dA= dδ= = TyTran {!!} (SubstTyR dA' dδ) {!!} (SubstTyEqR dA= dδ) (SubstTyMorEqR dA' dδ dδ=)

{- Derivability of the identity morphism -}

idMorDerivableR : {Γ : Ctx n} →  ⊢R Γ → (Γ ⊢R idMor n ∷> Γ)
idMorDerivableR {Γ = ◇} tt = tt
idMorDerivableR {Γ = Γ , A} (dΓ , dA) = (WeakMorR (idMorDerivableR dΓ) , congTmR (!R ([idMor]TyR _) R∙ substTy-weakenTyR') reflR (VarLast dA))

-- Conversion rules for proof relevant version are needed as well

-- ConvTy' : {Γ Δ : Ctx n} {A : TyExpr n} → Derivation (Γ ⊢ A) → (⊢R Γ == Δ) → Derivation (Δ ⊢ A)
-- ConvTm' : {Γ Δ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivation (Γ ⊢ u :> A) → (⊢R Γ == Δ) → Derivation (Δ ⊢ u :> A)
-- ConvTyEq' : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivation (Γ ⊢ A == B) → (⊢R Γ == Δ) → Derivation (Δ ⊢ A == B)
-- ConvTmEq' : {Γ Δ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → Derivation (Γ ⊢ u == v :> A) → (⊢R Γ == Δ) → Derivation (Δ ⊢ u == v :> A)
-- 
-- ConvTy' {Γ = Γ} {Δ = Δ} {A = A} (Pi dA dB) dΓ= = Pi (ConvTy' dA dΓ=) (ConvTy' dB (dΓ= , TyReflR (ConvTy' dA dΓ=)))
-- ConvTy' UU dΓ= = UU
-- ConvTy' (El dv) dΓ= = El (ConvTm' dv dΓ=)
-- 
-- ConvTyEq'(TySymm dA=) dΓ= = TySymm (ConvTyEq' dA= dΓ=)
-- ConvTyEq'(TyTran dB dA= dB=) dΓ= = TyTran (ConvTy' dB dΓ=) (ConvTyEq' dA= dΓ=) (ConvTyEq' dB= dΓ=)
-- ConvTyEq' (PiCong dA dA= dB=) dΓ= = PiCong (ConvTy' dA dΓ=) (ConvTyEq' dA= dΓ=) (ConvTyEq' dB= (dΓ= , TyReflR (ConvTy' dA dΓ=)))
-- ConvTyEq' UUCong dΓ= = UUCong
-- ConvTyEq' (ElCong dv=) dΓ= = ElCong (ConvTmEq' dv= dΓ=)
-- 
-- ConvTm' {Δ = Δ , B} {var last} (VarLast {A = A} dA) (dΓ= , dA=') = Conv (WeakTyR dB) {!!} (VarLast dB) (WeakTyEqR (TySymm dA='))
-- {- changed dA to dA' -}
-- ConvTm' {Γ = Γ , A} {Δ = Δ , B} (VarPrev dA dk) (dΓ= , dA' , dB , dA=) = VarPrev (ConvTy' dA dΓ=) (ConvTm' dk dΓ=)
-- ConvTm' (Conv dA dB du dA=) dΓ= = Conv (ConvTy' dA dΓ=) (ConvTy' dB dΓ=) (ConvTm' du dΓ=) (ConvTyEq' dA= dΓ=)
-- ConvTm' (Lam dA dB du) dΓ= = Lam (ConvTy' dA dΓ=) (ConvTy' dB (dΓ= , dA , ConvTy' dA dΓ= , TyReflR dA , TyReflR (ConvTy' dA dΓ=))) (ConvTm' du (dΓ= , dA , ConvTy' dA dΓ= , TyReflR dA , TyReflR (ConvTy' dA dΓ=)))
-- ConvTm' (App dA dB df da) dΓ= = App (ConvTy' dA dΓ=) (ConvTy' dB (dΓ= , dA , ConvTy' dA dΓ= , TyReflR dA , TyReflR (ConvTy' dA dΓ=))) (ConvTm' df dΓ=) (ConvTm' da dΓ=)
-- 
-- ConvTmEq'  {Δ = Δ , B} (VarLastCong {A = A} dA) (dΓ= , dA' , dB , dA= , dA=') = ConvEq (WeakTyR dB) {!!} (VarLastCong dB) (WeakTyEqR (TySymm dA='))
-- {- changed dA to dA' -}
-- ConvTmEq' {Γ = Γ , B} {Δ , B'} (VarPrevCong {A = A} dA dk=) (dΓ= , dA' , dB , dA=) = VarPrevCong (ConvTy' dA dΓ=) (ConvTmEq' dk= dΓ=)
-- ConvTmEq' (TmSymm du=) dΓ= = TmSymm (ConvTmEq' du= dΓ=)
-- ConvTmEq' (TmTran dv du= dv=) dΓ= = TmTran (ConvTm' dv dΓ=) (ConvTmEq' du= dΓ=) (ConvTmEq' dv= dΓ=)
-- ConvTmEq' (ConvEq dA dB du= dA=) dΓ= = ConvEq (ConvTy' dA dΓ=) (ConvTy' dB dΓ=) (ConvTmEq' du= dΓ=) (ConvTyEq' dA= dΓ=)
-- ConvTmEq' (LamCong dA dA= dB= du=) dΓ= = LamCong (ConvTy' dA dΓ=) (ConvTyEq' dA= dΓ=) (ConvTyEq' dB= (dΓ= , dA , ConvTy' dA dΓ= , TyReflR dA , TyReflR (ConvTy' dA dΓ=))) (ConvTmEq' du= (dΓ= , dA , ConvTy' dA dΓ= , TyReflR dA , TyReflR (ConvTy' dA dΓ=)))
-- ConvTmEq' (AppCong dA dA= dB= df= da=) dΓ= = AppCong (ConvTy' dA dΓ=) (ConvTyEq' dA= dΓ=) (ConvTyEq' dB= (dΓ= , dA , ConvTy' dA dΓ= , TyReflR dA , TyReflR (ConvTy' dA dΓ=))) (ConvTmEq' df= dΓ=) (ConvTmEq' da= dΓ=)
-- ConvTmEq' (BetaPi dA dB du da) dΓ= = BetaPi (ConvTy' dA dΓ=) (ConvTy' dB (dΓ= , dA , ConvTy' dA dΓ= , TyReflR dA , TyReflR (ConvTy' dA dΓ=))) (ConvTm' du (dΓ= , dA , ConvTy' dA dΓ= , TyReflR dA , TyReflR (ConvTy' dA dΓ=))) (ConvTm' da dΓ=)
-- ConvTmEq' (EtaPi dA dB df) dΓ= =
--   EtaPi (ConvTy' dA dΓ=)
--         (ConvTy' dB (dΓ= , dA , ConvTy' dA dΓ= , TyReflR dA , TyReflR (ConvTy' dA dΓ=)))
--         (ConvTm' df dΓ=)
-- 
-- TyEqTy1R : {Γ : Ctx n} {A B : TyExpr n} → (⊢R Γ) → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ A)
-- TyEqTy2R : {Γ : Ctx n} {A B : TyExpr n} → (⊢R Γ) → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ B)
-- TmEqTm1R : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢R Γ) → Derivation (Γ ⊢ u == u' :> A) → Derivation (Γ ⊢ u :> A)
-- TmEqTm2R : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢R Γ) → Derivation (Γ ⊢ u == u' :> A) → Derivation (Γ ⊢ u' :> A)
-- 
-- 
-- TyEqTy1R dΓ (TySymm dA=) = TyEqTy2R dΓ dA=
-- TyEqTy1R dΓ (TyTran _ dA= dB=) = TyEqTy1R dΓ dA=
-- TyEqTy1R dΓ UUCong = UU
-- TyEqTy1R dΓ (ElCong dv=) = El (TmEqTm1R dΓ dv=) 
-- TyEqTy1R dΓ (PiCong dA dA= dB=) = Pi dA (TyEqTy1R (dΓ , dA) dB=)
-- 
-- TyEqTy2R dΓ (TySymm dA=) = TyEqTy1R dΓ dA=
-- TyEqTy2R dΓ (TyTran dB dA= dB=) = TyEqTy2R dΓ dB=
-- TyEqTy2R dΓ UUCong = UU
-- TyEqTy2R dΓ (ElCong dv=) = El (TmEqTm2R dΓ dv=)
-- TyEqTy2R dΓ (PiCong dA dA= dB=) = Pi (TyEqTy2R dΓ dA=) (ConvTy' (TyEqTy2R (dΓ , (TyEqTy1R dΓ dA=)) dB=) ((CtxReflR dΓ) , dA , TyEqTy2R dΓ dA= , dA= , dA=))
-- 
-- TmEqTm1R dΓ (TmSymm du=) = TmEqTm2R dΓ du= 
-- TmEqTm1R dΓ (TmTran _ du= dv=) = TmEqTm1R dΓ du=
-- TmEqTm1R dΓ (ConvEq dA dB du= dA=) = Conv dA dB (TmEqTm1R dΓ du=) dA=
-- TmEqTm1R dΓ (VarLastCong dA) = VarLast dA
-- TmEqTm1R (dΓ , dA) (VarPrevCong dA' dk=) = VarPrev dA' (TmEqTm1R dΓ dk=)
-- TmEqTm1R dΓ (LamCong dA dA= dB= du=) = Lam (TyEqTy1R dΓ dA=) (TyEqTy1R (dΓ , dA) dB=) (TmEqTm1R (dΓ , dA) du=)
-- TmEqTm1R dΓ (AppCong dA dA= dB= df= da=) = App (TyEqTy1R dΓ dA=) (TyEqTy1R (dΓ , dA) dB=) (TmEqTm1R dΓ df=) (TmEqTm1R dΓ da=)
-- TmEqTm1R dΓ (BetaPi dA dB du da) = App dA dB (Lam dA dB du) da
-- TmEqTm1R dΓ (EtaPi dA dB df) = df
-- 
-- TmEqTm2R dΓ (TmSymm du=) = TmEqTm1R dΓ du=
-- TmEqTm2R dΓ (TmTran _ du= dv=) = TmEqTm2R dΓ dv=
-- TmEqTm2R dΓ (ConvEq dA dB du= dA=) = Conv dA dB (TmEqTm2R dΓ du=) dA=
-- TmEqTm2R dΓ (VarLastCong dA) = VarLast dA
-- TmEqTm2R (dΓ , dA) (VarPrevCong dA' dk=) = VarPrev dA' (TmEqTm2R dΓ dk=)
-- TmEqTm2R dΓ (LamCong dA dA= dB= du=) = 
--   Conv (Pi (TyEqTy2R dΓ dA=)
--            (ConvTy' (TyEqTy2R (dΓ , (TyEqTy1R dΓ dA=)) dB=) ((CtxReflR dΓ) , dA , TyEqTy2R dΓ dA= , dA= , dA=)))
--            {!!}
--        (Lam (TyEqTy2R dΓ dA=)
--             (ConvTy' (TyEqTy2R (dΓ , TyEqTy1R dΓ dA=) dB=) (CtxReflR dΓ , dA , TyEqTy2R dΓ dA= , dA= , dA=))
--             (ConvTm' (Conv (TyEqTy1R (dΓ , dA) dB=) {!!} (TmEqTm2R (dΓ , dA) du=) dB=) (CtxReflR dΓ , dA , TyEqTy2R dΓ dA= , dA= , dA=)))
--        (PiCong (TyEqTy2R dΓ dA=)
--                (TySymm dA=)
--                (ConvTyEq' (TySymm dB=) (CtxReflR dΓ , dA , ConvTy' (TyEqTy2R dΓ dA=) (CtxReflR dΓ) , dA= , dA=)))
-- TmEqTm2R dΓ (AppCong dA dA= dB= df= da=) =
--   Conv (SubstTyR (TyEqTy2R (dΓ , dA) dB=) (idMorDerivableR dΓ , Conv dA {!!} (TmEqTm2R dΓ da=) (congTyEqR! reflR ([idMor]TyR _) (TyReflR dA))))
--        {!!}
--        (App (TyEqTy2R dΓ dA=)
--             (ConvTy' (TyEqTy2R (dΓ , TyEqTy1R dΓ dA=) dB=) (CtxReflR dΓ , dA , TyEqTy2R dΓ dA= , dA= , dA=))
--             (Conv (Pi dA (TyEqTy1R (dΓ , dA) dB=)) {!!} (TmEqTm2R dΓ df=) (PiCong dA dA= dB=))
--             (Conv dA {!!} (TmEqTm2R dΓ da=) dA=))
--        (TySymm (SubstTyFullEqR (TyEqTy2R (dΓ , dA) dB=)
--                               (idMorDerivableR dΓ , congTmR! ([idMor]TyR _) reflR (TmEqTm1R dΓ da=))
--                               dB=
--                               (MorReflR (idMorDerivableR dΓ) , congTmEqTyR! ([idMor]TyR _) da=)))
-- TmEqTm2R dΓ (BetaPi dA dB du da) = SubstTmR du (idMorDerivableR dΓ , congTmR! ([idMor]TyR _) reflR da)
-- TmEqTm2R dΓ (EtaPi dA dB df) = Lam dA dB (congTmTyR (substTy-weakenTyR' R∙ [idMor]TyR _) (App (WeakTyR dA) (WeakTyR dB) (WeakTmR df) (VarLast dA)))


-- squashing for the proof relevant Derivations
-- squashJdg : {jdg : Judgment} → Derivation (jdg) → Derivable (jdg)
-- squashJdg (VarLast j) = VarLast (squashJdg j)
-- squashJdg (VarPrev j j₁) = VarPrev (squashJdg (j)) (squashJdg j₁)
-- squashJdg (VarLastCong j) = VarLastCong (squashJdg j)
-- squashJdg (VarPrevCong j j₁) = VarPrevCong (squashJdg j) (squashJdg j₁)
-- squashJdg (TySymm j) = TySymm (squashJdg j)
-- squashJdg (TyTran j j₁ j₂) = TyTran (squashJdg j) (squashJdg j₁) (squashJdg j₂)
-- squashJdg (TmSymm j) = TmSymm (squashJdg j)
-- squashJdg (TmTran j j₁ j₂) = TmTran (squashJdg j) (squashJdg j₁) (squashJdg j₂)
-- squashJdg (Conv j j₁ j₂) = Conv (squashJdg j) (squashJdg j₁) (squashJdg j₂)
-- squashJdg (ConvEq j j₁ j₂) = ConvEq (squashJdg j) (squashJdg j₁) (squashJdg j₂)
-- squashJdg UU = UU
-- squashJdg UUCong = UUCong
-- squashJdg (El j) = El (squashJdg j)
-- squashJdg (ElCong j) = ElCong (squashJdg j)
-- squashJdg (Pi j j₁) = Pi (squashJdg j) (squashJdg j₁)
-- squashJdg (PiCong j j₁ j₂) = PiCong (squashJdg j) (squashJdg j₁) (squashJdg j₂)
-- squashJdg (Lam j j₁ j₂) = Lam (squashJdg j) (squashJdg j₁) (squashJdg j₂)
-- squashJdg (LamCong j j₁ j₂ j₃) = LamCong (squashJdg j) (squashJdg j₁) (squashJdg j₂) (squashJdg j₃)
-- squashJdg (App j j₁ j₂ j₃) = App (squashJdg j) (squashJdg j₁) (squashJdg j₂) (squashJdg j₃)
-- squashJdg (AppCong j j₁ j₂ j₃ j₄) = AppCong (squashJdg j) (squashJdg j₁) (squashJdg j₂) (squashJdg j₃) (squashJdg j₄)
-- squashJdg (BetaPi j j₁ j₂ j₃) = BetaPi (squashJdg j) (squashJdg j₁) (squashJdg j₂) (squashJdg j₃)
-- squashJdg (EtaPi j j₁ j₂) = EtaPi (squashJdg j) (squashJdg j₁) (squashJdg j₂)
-- 
-- -- for some reason I cannot make case distinction over ⊢R
-- squashCtx : (Γ : Ctx n) → (⊢R_ Γ) → ⊢ Γ
-- squashCtx ◇ dΓ = tt
-- squashCtx (Γ , A) dΓ = (squashCtx Γ (fst dΓ)) , (squashJdg (snd dΓ))

-- Metatheorems
TmTyR : {Γ : Ctx n} {A : TyExpr n} {u : TmExpr n} → (⊢R Γ) → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ A)
TmTyR dΓ (VarLast du) = WeakTyR du
------- The Derivation Matters!
TmTyR (dΓ , dA) (VarPrev du du₁) = WeakTyR (TmTyR dΓ du₁)
TmTyR dΓ (Conv dA dB du dA=) = dB
TmTyR dΓ (Lam dA dB du) = Pi dA (TmTyR (dΓ , dA) du)
TmTyR dΓ (App {Γ = Γ} {A = A} dA dB df da) = SubstTyR {Δ = Γ , A} dB ((idMorDerivableR dΓ) , Mor+Rewrite da) 
      where
      Mor+Rewrite : {Γ : Ctx n} {A : TyExpr n} {a : TmExpr n} (da : Derivation (Γ ⊢ a :> A)) → Derivation (Γ ⊢ a :> A [ idMor n ]Ty)
      Mor+Rewrite {Γ = Γ} {A} {a} da with A [ idMor _ ]Ty | [idMor]TyR A
      ...                                             | q | reflR = da

TmTyUU : {Γ : Ctx n} {v : TmExpr n} (dΓ : ⊢R Γ) (dv : Derivation (Γ ⊢ v :> uu)) → TmTyR dΓ dv ≡ UU
TmTyUU {Γ = ◇} {lam A B v} tt (Conv dv dv₁ dv₂ dv₃) = ?
TmTyUU {Γ = ◇} {app A B v v₁} tt dv = {!!}
TmTyUU {Γ = Γ , A} dΓ dv = {!!}
TyEq1R : {Γ : Ctx n} {A B : TyExpr n} → (⊢R Γ) → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ A)
TyEq1R dΓ (TySymm dA dB dA=) = dB
TyEq1R dΓ (TyTran dA dB dC dA= dB=) = dA
TyEq1R dΓ UUCong = UU
TyEq1R dΓ (ElCong dv dv' dv=) = El dv
TyEq1R dΓ (PiCong dA dA' dB dB' dA= dB=) = Pi dA dB

TyEq2R : {Γ : Ctx n} {A B : TyExpr n} → (⊢R Γ) → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ B)
TyEq2R dΓ (TySymm dA dB dA=) = dA
TyEq2R dΓ (TyTran dA dB dC dA= dB=) = dC
TyEq2R dΓ UUCong = UU
TyEq2R dΓ (ElCong dv dv' dv=) = El dv'
TyEq2R dΓ (PiCong dA dA' dB dB' dA= dB=) = Pi dA' dB'

-- helper : {Γ : Ctx n} {A B : TyExpr n} {u : TmExpr n} → Derivation (Γ ⊢ u :> B) → ΣSS (TyExpr n) (λ A → ΣSS (TmExpr n) (λ u → Derivation (Γ ⊢ u :> A)))
-- helper {B = A} {u = u} (VarLast du) = A , u , {!VarLast du!}
-- helper (VarPrev du du₁) = {!!}
-- helper (Conv dA dB du dA=) = {!!}
-- helper (Lam du du₁ du₂) = {!!}
-- helper (App du du₁ du₂ du₃) = {!!}

