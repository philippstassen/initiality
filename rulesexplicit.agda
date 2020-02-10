{-# OPTIONS --rewriting --prop --allow-unsolved-metas #-}
open import common renaming (Unit to metaUnit)
open import typetheoryexplicit
open import syntxexplicit
open import reflectionexplicit
 
{- The four different forms of (pre)judgments. -}

data Judgment : Set where
  _⊢_ : (Γ : Ctx n) → TyExpr n → Judgment
  _⊢_:>_ : (Γ : Ctx n) → TmExpr n → TyExpr n → Judgment
  _⊢_==_ : (Γ : Ctx n) → TyExpr n → TyExpr n → Judgment
  _⊢_==_:>_ : (Γ : Ctx n) → TmExpr n → TmExpr n → TyExpr n → Judgment
{- Explicit Coercions: Isomorphism Type as in Curien Garner Hofmann, seems very useless atm though -}
--  _⊢_≃_ : (Γ : Ctx n) → TyExpr n → TyExpr n → Judgment


{- Derivability of judgments, the typing rules of the type theory -}

data Derivable : Judgment → Prop where
  
  -- Variable rules
  VarLast : {Γ : Ctx n} {A : TyExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable ((Γ , A) ⊢ var last :> weakenTy A)

  -- explicit Var Prev requires vark to be derived by Variable rule, while normal Var prev also allows the Conv rule. So we should possibly add a coercion?

  VarPrev : {Γ : Ctx n} {B : TyExpr n} {k : Fin n} {A : TyExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ var k :> A)
    → Derivable ((Γ , B) ⊢ var (prev k) :> weakenTy A)
          
--  -- Congruence for variables
--  VarLastCong : {Γ : Ctx n} {A : TyExpr n}
--    → Derivable (Γ ⊢ A)
--    → Derivable ((Γ , A) ⊢ var last == var last :> weakenTy A)
--  VarPrevCong : {Γ : Ctx n} {B : TyExpr n} {k k' : Fin n} {A : TyExpr n}
--    → Derivable (Γ ⊢ A)
--    → Derivable (Γ ⊢ var k == var k' :> A)
--    → Derivable ((Γ , B) ⊢ var (prev k) == var (prev k') :> weakenTy A)
          
  -- Reflexifity for terms and types
  TyRefl : {Γ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A)
  TmRefl : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u == u :> A)

  -- Symmetry and transitivity for types

  TySymm : {Γ : Ctx n} {A B : TyExpr n}
    → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == A)
  TyTran : {Γ : Ctx n} {A B C : TyExpr n}
    → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmSymm : {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == u :> A)
  TmTran : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ v :> A) → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)

  -- Here the explicit coercions need to be marked.
  -- Conversion rules
  Conv : {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ B) 
    → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ coerc A B u :> B)
  ConvEq : {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n} → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ coerc A B u == coerc A B u' :> B)
  CoercRefl : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A)
    → Derivable (Γ ⊢ coerc A A u == u :> A)
  CoercRefl! : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A)
    → Derivable (Γ ⊢ u == coerc A A u :> A)
  CoercTrans : {Γ : Ctx n} {u : TmExpr n} {A B C : TyExpr n} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ C) → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C) → Derivable (Γ ⊢ coerc B C (coerc A B u) == coerc A C u :> C)
  -- Rules for UU
  UU : {Γ : Ctx n}
    → Derivable (Γ ⊢ uu)
  UUCong : {Γ : Ctx n}
    → Derivable (Γ ⊢ uu == uu)

  -- Rules for El
  El : {Γ : Ctx n} {v : TmExpr n}
    → Derivable (Γ ⊢ v :> uu) → Derivable (Γ ⊢ el v)
  ElCong : {Γ : Ctx n} {v v' : TmExpr n}
     → Derivable (Γ ⊢ v == v' :> uu) → Derivable (Γ ⊢ el v == el v')


  -- Rules for Pi
  Pi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} 
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ pi A B)
  PiCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A') ⊢ B') → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == coercTy B' A' A) → Derivable (Γ ⊢ pi A B == pi A' B')

{- Version two PiCong, should be equivalent when Gamma is wellformed, but the first on might be nicer to work with -}
--  PiCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)}
--    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A') ⊢ B') → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == coercTy B' A' A) → Derivable (Γ ⊢ pi A B == pi A' (coercTy B' A' A))

  -- Rules for lambda
  Lam : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B)
    → Derivable (Γ ⊢ lam A B u :> pi A B)

  LamCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)}
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A') ⊢ B') → Derivable ((Γ , A) ⊢ u :> B) → Derivable ((Γ , A') ⊢ u' :> B') → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == (coercTy B' A' A)) → Derivable ((Γ , A) ⊢ u == coerc (coercTy B' A' A) B (coercTm u' A' A) :> B)
     → Derivable (Γ ⊢ lam A B u == coerc (pi A' B') (pi A B) (lam A' B' u') :> pi A B) 

    {- Version Two LamCong-}
--   LamCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)}
--     → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A') ⊢ B') → Derivable ((Γ , A) ⊢ u :> B) → Derivable ((Γ , A') ⊢ u' :> B') 
--     → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == (coercTy B' A' A)) → Derivable ((Γ , A) ⊢ u == coerc (coercTy B' A' A) B (coercTm u' A' A) :> B) → Derivable (Γ ⊢ lam A B u == coerc (pi A B) (pi A' B') lam A' B' u' :> pi A B) 


  -- Rules for app
  App : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B f a :> substTy B a)
  AppCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A') ⊢ B') → Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ f' :> pi A' B') → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ a' :> A') → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == coercTy B' A' A) → Derivable (Γ ⊢ f == coerc (pi A' B') (pi A B) f' :> pi A B) → Derivable (Γ ⊢ a == coerc A' A a' :> A)
    → Derivable (Γ ⊢ app A B f a == coerc (substTy B' a') (substTy B a) (app A' B' f' a') :> substTy B a)

    {- Version two -}
--   AppCong : {Γ : Ctx n} {A A' : TyExpr n} {B : TyExpr (suc n)} {f f' a a' : TmExpr n}
--     → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ f' :> pi A B) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ a' :> A') → Derivable (Γ ⊢ f == f' :> pi A B) → Derivable (Γ ⊢ a == coerc A' A a' :> A)
--     → Derivable (Γ ⊢ app A B f a == coerc (substTy B (coerc A' A a')) (substTy B a) (app A B f' (coerc A' A a')) :> substTy B a)

  -- Beta-reductions
  BetaPi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B (lam A B u) a == substTm u a :> substTy B a)

  -- Eta-equivalences: I still well-defined for Explicit syntax (see syntaxexplicit bottom)
  EtaPi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B)
    → Derivable (Γ ⊢ f == lam A B (app (weakenTy A) (weakenTy' (prev last) B) (weakenTm f) (var last)) :> pi A B)

{- Derivability of contexts, context equality, context morphisms, and context morphism equality -}

data ⊢_ : Ctx n → Prop where
  tt : ⊢ ◇
  _,_ : {Γ : Ctx n} {A : _} → (⊢ Γ) → Derivable (Γ ⊢ A) → ⊢ (Γ , A)

data ⊢_==_ : Ctx n → Ctx n → Prop where
  tt : ⊢ ◇ == ◇
  _,_ : {Γ Γ' : Ctx n} {A A' : TyExpr n} → (⊢ Γ == Γ') → Derivable (Γ' ⊢ A == A') → ⊢ (Γ , A) == (Γ' , A')

data _⊢_∷>_ (Γ : Ctx n) : Mor n m → Ctx m → Prop where
  tt : Γ ⊢ ◇ ∷> ◇
  _,_ : {Δ : Ctx m} {δ : Mor n m} {u : TmExpr n} {A : TyExpr m} → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u :> A [ δ ]Ty) → (Γ ⊢ (δ , u) ∷> (Δ , A))

data _⊢_==_∷>_ (Γ : Ctx n) : Mor n m → Mor n m → Ctx m → Prop where
  tt : Γ ⊢ ◇ == ◇ ∷> ◇
  _,_ : {Δ : Ctx m} {δ δ' : Mor n m} {u u' : TmExpr n} {A : TyExpr m} → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u == coerc (A [ δ' ]Ty) (A [ δ ]Ty) u' :> A [ δ ]Ty) → (Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A))

-- {- Derivability of contexts, context equality, context morphisms, and context morphism equality -}
-- 
-- ⊢_ : Ctx n → Prop
-- ⊢ ◇ = metaUnit
-- ⊢ (Γ , A) = (⊢ Γ) × Derivable (Γ ⊢ A)
-- 
-- ⊢_==_ : Ctx n → Ctx n → Prop
-- ⊢ ◇ == ◇ = metaUnit
-- ⊢ (Γ , A) == (Γ' , A') = (⊢ Γ == Γ') × Derivable (Γ ⊢ A) × Derivable (Γ' ⊢ A') × Derivable (Γ ⊢ A == A') × Derivable (Γ' ⊢ A == A')
-- 
-- _⊢_∷>_ : (Γ : Ctx n) → Mor n m → Ctx m → Prop
-- Γ ⊢ ◇ ∷> ◇ = metaUnit
-- Γ ⊢ (δ , u) ∷> (Δ , A) = (Γ ⊢ δ ∷> Δ) × Derivable (Γ ⊢ u :> A [ δ ]Ty) 
-- 
-- {- Explicit coercion -}
-- _⊢_==_∷>_ : (Γ : Ctx n) → Mor n m → Mor n m → Ctx m → Prop
-- Γ ⊢ ◇ == ◇ ∷> ◇ = metaUnit
-- Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A) = (Γ ⊢ δ == δ' ∷> Δ) × Derivable (Γ ⊢ u == coerc (A [ δ' ]Ty) (A [ δ ]Ty) u' :> A [ δ ]Ty)


{- Congruence with respect to the type in derivability of term expressions -}

congCtx : {Γ Γ' : Ctx n} → Γ ≡ Γ' → ⊢ Γ → ⊢ Γ'
congCtx refl dΓ = dΓ

congCtxEq : {Γ Γ' Δ Δ' : Ctx n} → Γ ≡ Γ' → Δ ≡ Δ' → ⊢ Γ == Δ → ⊢ Γ' == Δ'
congCtxEq refl refl dΓ= = dΓ=

congMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → Γ ⊢ δ ∷> Δ → Γ' ⊢ δ' ∷> Δ'
congMor refl refl refl dδ = dδ

congMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' θ θ' : Mor n m} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → θ ≡ θ' → Γ ⊢ δ == θ ∷> Δ → Γ' ⊢ δ' == θ' ∷> Δ'
congMorEq refl refl refl refl dδ= = dδ=

congMorEqCtxEq : {Γ Γ' : Ctx n} {Δ : Ctx m} {δ θ : Mor n m} → Γ ≡ Γ' → Γ ⊢ δ == θ ∷> Δ → Γ' ⊢ δ == θ ∷> Δ
congMorEqCtxEq refl dδ= = dδ=

congTy : {Γ : Ctx n} {A A' : TyExpr n} → A ≡ A' → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A')
congTy refl dA = dA

congTy! : {Γ : Ctx n} {A A' : TyExpr n} → A' ≡ A → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A')
congTy! refl dA = dA

congTyCtx :  {Γ Γ' : Ctx n} {A : TyExpr n} → Γ ≡ Γ' → Derivable (Γ ⊢ A) → Derivable (Γ' ⊢ A)
congTyCtx refl dA = dA

congTyCtxEq : {Γ Γ' : Ctx n} {A B : TyExpr n} → Γ ≡ Γ' → Derivable (Γ ⊢ A == B) → Derivable (Γ' ⊢ A == B)
congTyCtxEq refl dA= = dA=

congTyEq : {Γ : Ctx n} {A A' B B' : TyExpr n} → A ≡ A' → B ≡ B' → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A' == B')
congTyEq refl refl dA= = dA=

congTyEq! : {Γ : Ctx n} {A A' B B' : TyExpr n} → A' ≡ A → B' ≡ B → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A' == B')
congTyEq! refl refl dA= = dA=

congTm : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡ A' → u ≡ u' → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u' :> A')
congTm refl refl du = du

congTm! : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A' ≡ A → u' ≡ u → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u' :> A')
congTm! refl refl du = du

congTmTy : {Γ : Ctx n} {A A' : TyExpr n} {u : TmExpr n} → A ≡ A' → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u :> A')
congTmTy refl du = du

congTmTy! : {Γ : Ctx n} {A A' : TyExpr n} {u : TmExpr n} → A' ≡ A → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u :> A')
congTmTy! refl du = du

congTmEqTy : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡ A' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u == u' :> A')
congTmEqTy refl du= = du=

congTmEqTy! : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A' ≡ A → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u == u' :> A')
congTmEqTy! refl du= = du=

congTmEqTm : {Γ : Ctx n} {A : TyExpr n} {u u' v v' : TmExpr n} → u ≡ v → u' ≡ v' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ v == v' :> A)
congTmEqTm refl refl du= = du=

congTmEq : {Γ : Ctx n} {A A' : TyExpr n} {u u' v v' : TmExpr n} → u ≡ v → u' ≡ v' → A ≡ A' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ v == v' :> A')
congTmEq refl refl refl du= = du=

congTmEq! : {Γ : Ctx n} {A A' : TyExpr n} {u u' v v' : TmExpr n} → v ≡ u → v' ≡ u' → A' ≡ A → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ v == v' :> A')
congTmEq! refl refl refl du= = du=

{- Reflexivity rules -}

congTyRefl : {Γ : Ctx n} {A A' : TyExpr n} → Derivable (Γ ⊢ A) → A ≡ A' → Derivable (Γ ⊢ A == A')
congTyRefl dA refl = TyRefl dA

congTyRefl' : {Γ : Ctx n} {A A' : TyExpr n} → Derivable (Γ ⊢ A') → A ≡ A' → Derivable (Γ ⊢ A == A')
congTyRefl' dA refl = TyRefl dA

congTmRefl : {Γ : Ctx n} {A : TyExpr n} {u u' : TmExpr n} → Derivable (Γ ⊢ u :> A) → u ≡ u' → Derivable (Γ ⊢ u == u' :> A)
congTmRefl du refl = TmRefl du

CtxRefl : {Γ : Ctx n} → ⊢ Γ → ⊢ Γ == Γ
CtxRefl {Γ = ◇} tt = tt
CtxRefl {Γ = Γ , A} (dΓ , dA) = (CtxRefl dΓ , TyRefl dA)

MorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ ∷> Δ)
MorRefl {Δ = ◇} {δ = ◇} dδ = tt
MorRefl {Δ = Δ , B} {δ = δ , u} (dδ , du) = MorRefl dδ , CoercRefl! du

-- MorSymm : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Δ → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ' == δ ∷> Δ)
-- MorSymm dΔ tt = tt
-- MorSymm (dΔ , dA) (dδ= , x) = {!ConvEq (SubstTy dA dδ) x!}

congMorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → δ ≡ δ' → Γ ⊢ δ ∷> Δ → Γ ⊢ δ == δ' ∷> Δ
congMorRefl refl dδ = MorRefl dδ

{- Substitution and weakening are admissible -}

SubstTy : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ A [ δ ]Ty)
SubstTm : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u :> A) → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ u [ δ ]Tm :> A [ δ ]Ty)
SubstTyEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ A == A') → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ ]Ty)
SubstTmEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ ]Tm :> A [ δ ]Ty)


WeakTy : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {A : TyExpr n}
      → Derivable (Γ ⊢ A) → Derivable (weakenCtx k Γ T ⊢ weakenTy' k A)
WeakTm : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {u : TmExpr n} {A : TyExpr n}
      → Derivable (Γ ⊢ u :> A) → Derivable (weakenCtx k Γ T ⊢ weakenTm' k u :> weakenTy' k A)
WeakTyEq : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {A A' : TyExpr n}
      → Derivable (Γ ⊢ A == A') → Derivable (weakenCtx k Γ T ⊢ weakenTy' k A == weakenTy' k A')
WeakTmEq : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {u u' : TmExpr n} {A : TyExpr n}
     → Derivable (Γ ⊢ u == u' :> A) → Derivable (weakenCtx k Γ T ⊢ weakenTm' k u == weakenTm' k u' :> weakenTy' k A)

WeakMor : {Γ : Ctx n} {Δ : Ctx m} {T : TyExpr n} {δ : Mor n m} → Γ ⊢ δ ∷> Δ → (Γ , T) ⊢ weakenMor δ ∷> Δ
WeakMor {Δ = ◇} {δ = ◇} tt = tt
WeakMor {Δ = Δ , B} {δ = δ , u} (dδ , du) =  (WeakMor dδ , congTmTy (weaken[]Ty _ _ _) (WeakTm du))

WeakMorEq : {Γ : Ctx n } {Δ : Ctx m} {T : TyExpr n} {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → ((Γ , T) ⊢ weakenMor δ == weakenMor δ' ∷> Δ)
WeakMorEq {Δ = ◇} {δ = ◇} {◇} dδ = tt
WeakMorEq {Δ = Δ , B} {δ = δ , u} {δ' , u'} (dδ , du) rewrite ! (weaken[]Ty B δ last) | ! (weaken[]Ty B δ' last) = WeakMorEq dδ , congTmEqTy (weaken[]Ty B δ last) (congTmEq refl (ap-coerc-Tm (weaken[]Ty B δ' last) (weaken[]Ty B δ last) refl) refl (WeakTmEq du))

WeakMor+~ : {Γ : Ctx n} {Δ : Ctx m} (A : TyExpr m) {δ : Mor n m} → Derivable (Γ ⊢ A [ δ ]Ty) → Γ ⊢ δ ∷> Δ → (Γ , A [ δ ]Ty) ⊢ weakenMor+ δ ∷> (Δ , A)
WeakMor+~ A dAδ dδ = (WeakMor dδ , congTmTy (weaken[]Ty _ _ _) (VarLast dAδ))

WeakMor+ : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → (Γ , A [ δ ]Ty) ⊢ weakenMor+ δ ∷> (Δ , A)
WeakMor+ dA dδ = WeakMor+~ _ (SubstTy dA dδ) dδ

WeakMor+coerc : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {B : TyExpr n} {δ : Mor n m} → Derivable (Δ ⊢ A) → Derivable (Γ ⊢ B) → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ B == A [ δ ]Ty) → (Γ , B) ⊢ weakenMor+coerc δ B (A [ δ ]Ty) ∷> (Δ , A)
WeakMor+coerc dA dB dδ dB= = WeakMor dδ , congTmTy (weaken[]Ty _ _ _) (Conv (WeakTy dB) (WeakTy (SubstTy dA dδ)) (VarLast dB) (WeakTyEq dB=))

SubstTy {A = pi A B} (Pi dA dB) dδ = Pi (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ))
SubstTy {A = uu} UU dδ = UU
SubstTy {A = el v} (El dA) dδ = El (SubstTm dA dδ)

SubstTm (Conv dA dB du dA=) dδ = Conv (SubstTy dA dδ) (SubstTy dB dδ) (SubstTm du dδ) (SubstTyEq dA= dδ)
SubstTm {Δ = (_ , _)} {var last}     {δ = _ , _} (VarLast _) (_ , du) = congTmTy! (weakenTyInsert _ _ _) du
SubstTm {Δ = (_ , _)} {var (prev k)} {δ = _ , _} (VarPrev _ dk) (dδ , _) = congTmTy! (weakenTyInsert _ _ _) (SubstTm dk dδ)
SubstTm {u = lam A B u} (Lam dA dB du) dδ = Lam (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du (WeakMor+ dA dδ))
SubstTm {u = app A B f a} {δ = δ} (App dA dB df da) dδ = congTmTy! []Ty-substTy (App (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm df dδ) (SubstTm da dδ))

SubstTyEq (TyRefl dA) dδ = TyRefl (SubstTy dA dδ)
SubstTyEq (TySymm dA=) dδ = TySymm (SubstTyEq dA= dδ)
SubstTyEq (TyTran dB dA= dB=) dδ = TyTran (SubstTy dB dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= dδ)
SubstTyEq {δ = δ} (PiCong {A = A} {A' = A'} {B' = B'} dA dA' dB dB' dA= dB=) dδ = PiCong (SubstTy dA dδ) (SubstTy dA' dδ) (SubstTy dB (WeakMor {T = A [ δ ]Ty} dδ , congTmTy (weaken[]Ty A δ last) (VarLast (SubstTy dA dδ)))) (SubstTy dB' (WeakMor+ dA' dδ) ) (SubstTyEq dA= dδ) (congTyEq refl (coercTy[weakenMor+] B' A' A δ) (SubstTyEq dB= (WeakMor+ dA dδ)))
SubstTyEq UUCong dδ = UUCong
SubstTyEq (ElCong dv=) dδ = ElCong (SubstTmEq dv= dδ)

SubstTmEq (TmRefl da) dδ = TmRefl (SubstTm da dδ )
-- SubstTmEq {δ = _ , _} (VarLastCong _)     (_ , du) = congTmEqTy! (weakenTyInsert _ _ _) {!!}
-- -- (TmRefl du)
-- SubstTmEq {δ = _ , _} (VarPrevCong _ dA=) (dδ , _) = congTmEqTy! (weakenTyInsert _ _ _) (SubstTmEq dA= dδ)
SubstTmEq (TmSymm du=) dδ = TmSymm (SubstTmEq du= dδ)
SubstTmEq (TmTran dv du= dv=) dδ = TmTran (SubstTm dv dδ) (SubstTmEq du= dδ) (SubstTmEq dv= dδ)
SubstTmEq (ConvEq dA du= dA=) dδ = ConvEq (SubstTy dA dδ) (SubstTmEq du= dδ) (SubstTyEq dA= dδ) 
SubstTmEq {δ = δ} (CoercRefl du) dδ = CoercRefl (SubstTm du dδ)
SubstTmEq {δ = δ} (CoercRefl! du) dδ = CoercRefl! (SubstTm du dδ)
SubstTmEq {δ = δ} (CoercTrans dA dB dC du dA= dB= dA₁=) dδ = CoercTrans (SubstTy dA dδ) (SubstTy dB dδ) (SubstTy dC dδ) (SubstTm du dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= dδ) (SubstTyEq dA₁= dδ)
SubstTmEq {δ = δ} (LamCong {A = A} {A' = A'} {B = B} {B' = B'} {u' = u'} dA dA' dB dB' du du' dA= dB= du=) dδ =
             LamCong (SubstTy dA dδ) (SubstTy dA' dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTy dB' (WeakMor+ dA' dδ)) (SubstTm du (WeakMor+ dA dδ)) (SubstTm du' (WeakMor+ dA' dδ)) (SubstTyEq dA= dδ) (congTyEq refl (coercTy[weakenMor+] B' A' A δ) (SubstTyEq dB= ((WeakMor dδ) , (congTmTy (weaken[]Ty A δ last) (VarLast (SubstTy dA dδ)))))) (congTmEq refl (coercTm[weakenMor+]^2 A A' B B' u' δ) refl (SubstTmEq du= (WeakMor dδ , congTmTy (weaken[]Ty A δ last) (VarLast (SubstTy dA dδ))))) 

SubstTmEq {δ = δ} (AppCong {A = A} {A' = A'} {B = B} {B' = B'} dA dA' dB dB' df df' da da' dA= dB= df= da=) dδ = congTmEq! refl (ap-coerc-Tm []Ty-substTy []Ty-substTy refl) []Ty-substTy (AppCong (SubstTy dA dδ) (SubstTy dA' dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTy dB' (WeakMor+ dA' dδ)) (SubstTm df dδ) (SubstTm df' dδ) (SubstTm da dδ) (SubstTm da' dδ) (SubstTyEq dA= dδ) ( congTyEq refl (coercTy[weakenMor+] B' A' A δ) (SubstTyEq dB= ((WeakMor dδ) , (congTmTy (weaken[]Ty A δ last) (VarLast (SubstTy dA dδ)))))) (SubstTmEq df= dδ) (SubstTmEq da= dδ))

SubstTmEq (BetaPi {u = u} dA dB du da) dδ = congTmEq! refl ([]Tm-substTm u) []Ty-substTy (BetaPi (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du (WeakMor+ dA dδ )) (SubstTm da dδ))
SubstTmEq (EtaPi {f = f} dA dB df) dδ =  congTmEq! refl (ap-lam-Tm refl refl (ap-app-Tm []Ty-weakenTy []Ty-weakenTy1 ([]Tm-weakenTm f) refl)) refl
                 (EtaPi (SubstTy dA dδ)
                        (SubstTy dB (WeakMor+ dA dδ))
                        (SubstTm df dδ))


WeakTy (Pi dA dB) = Pi (WeakTy dA) (WeakTy dB)
WeakTy UU = UU
WeakTy (El dv) = El (WeakTm dv)

WeakTm (Conv dA dB du dA=) = Conv (WeakTy dA) (WeakTy dB) (WeakTm du) (WeakTyEq dA=)
WeakTm {k = last}   (VarLast dA)    = VarPrev (WeakTy dA) (VarLast dA)
WeakTm {k = last}   (VarPrev dA dk) = VarPrev (WeakTy dA) (VarPrev dA dk)
WeakTm {k = prev k} (VarLast dA)    = congTmTy! weakenTy-weakenTy (VarLast (WeakTy dA))
WeakTm {k = prev k} (VarPrev dA dk) = congTmTy! weakenTy-weakenTy (VarPrev (WeakTy dA) (WeakTm dk))
WeakTm (Lam dA dB du) = Lam (WeakTy dA) (WeakTy dB) (WeakTm du)
WeakTm (App dA dB df da) = congTmTy! weakenTy-substTy (App (WeakTy dA) (WeakTy dB) (WeakTm df) (WeakTm da))

WeakTyEq (TyRefl dA) = TyRefl (WeakTy dA)
WeakTyEq (TySymm dA=) = TySymm (WeakTyEq dA=)
WeakTyEq (TyTran dB dA= dB=) = TyTran (WeakTy dB) (WeakTyEq dA=) (WeakTyEq dB=)
WeakTyEq {k = k} (PiCong {A = A} {A' = A'} {B' = B'} dA dA' dB dB' dA= dB=) = PiCong (WeakTy dA) (WeakTy dA') (WeakTy dB) (WeakTy dB') (WeakTyEq dA=) (congTyEq refl (! (coercTy-weakenTy' B' A' A)) (WeakTyEq dB=))
WeakTyEq UUCong = UUCong
WeakTyEq (ElCong dv=) = ElCong (WeakTmEq dv=)

-- WeakTmEq {k = last}   (VarLastCong dA)     = VarPrevCong (WeakTy dA) (VarLastCong dA)
-- WeakTmEq {k = last}   (VarPrevCong dA dk=) = VarPrevCong (WeakTy dA) (WeakTmEq dk=)
-- WeakTmEq {k = prev k} (VarLastCong dA)     = congTmEqTy! weakenTy-weakenTy (VarLastCong (WeakTy dA))
-- WeakTmEq {k = prev k} (VarPrevCong dA dk=) = congTmEqTy! weakenTy-weakenTy (VarPrevCong (WeakTy dA) (WeakTmEq dk=))
WeakTmEq (TmRefl du) = TmRefl (WeakTm du)
WeakTmEq (TmSymm du=) = TmSymm (WeakTmEq du=)
WeakTmEq (TmTran dv du= dv=) = TmTran (WeakTm dv) (WeakTmEq du=) (WeakTmEq dv=)
WeakTmEq (ConvEq dA du= dA=) =  ConvEq (WeakTy dA) (WeakTmEq du=) (WeakTyEq dA=)
WeakTmEq {k = k} (CoercRefl x) = CoercRefl (WeakTm x)
WeakTmEq (CoercRefl! x) = CoercRefl! (WeakTm x)
WeakTmEq (CoercTrans dA dB dC du x x₁ x₂) = CoercTrans (WeakTy dA) (WeakTy dB) (WeakTy dC) (WeakTm du) (WeakTyEq x) (WeakTyEq x₁) (WeakTyEq x₂)
WeakTmEq (LamCong {A = A} {A' = A'} {B = B} {B' = B'} {u' = u'} dA dA' dB dB' du du' dA= dB= du=) =  LamCong (WeakTy dA) (WeakTy dA') (WeakTy dB) (WeakTy dB') (WeakTm du) (WeakTm du') (WeakTyEq dA=) (congTyEq refl (! (coercTy-weakenTy' B' A' A)) (WeakTyEq dB=)) (congTmEq refl ((coercTm-weakenTm'^2 A A' B B' u')) refl (WeakTmEq du=))
WeakTmEq (AppCong {A = A} {A' = A'} {B' = B'} dA dA' dB dB' df df' da da' dA= dB= df= da=) = congTmEq refl (ap-coerc-Tm (! (weakenTy-substTy)) (! (weakenTy-substTy)) refl) (! (weakenTy-substTy)) ( AppCong (WeakTy dA) (WeakTy dA') (WeakTy dB) (WeakTy dB') (WeakTm df) (WeakTm df') (WeakTm da) (WeakTm da') (WeakTyEq dA=) (congTyEq refl (! (coercTy-weakenTy' B' A' A)) (WeakTyEq dB=)) (WeakTmEq  df=) (WeakTmEq da=))
-- congTmEqTy! weakenTy-substTy (AppCong (WeakTy dA) (WeakTy dA') (WeakTy dB) (WeakTy dB') (WeakTm df) (WeakTm df') (WeakTm da) (WeakTm da') (WeakTyEq dA=) (WeakTyEq dB=) (WeakTmEq  df=) (WeakTmEq da=))
WeakTmEq {u = app A B (lam A B u) a} (BetaPi dA dB du da) = congTmEq! refl (weakenTm-substTm u) weakenTy-substTy (BetaPi (WeakTy dA) (WeakTy dB) (WeakTm du) (WeakTm da))
WeakTmEq (EtaPi {f = f} dA dB df) =
   congTmEq! refl (ap-lam-Tm refl refl (ap-app-Tm weakenTy-weakenTy weakenTy-weakenTy1 (! (weakenTmCommutes _ f)) refl)) refl
            (EtaPi (WeakTy dA)
                   (WeakTy dB)
                   (WeakTm df))


{- with adjustions for explicit syntax -}

WeakMor+Eq : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → Γ ⊢ δ' ∷> Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
  → (Γ , A [ δ' ]Ty) ⊢ weakenMor+ δ' == weakenMor+coerc δ (A [ δ' ]Ty) (A [ δ ]Ty) ∷> (Δ , A)

WeakMor+Eq! : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → Γ ⊢ δ' ∷> Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
  → (Γ , A [ δ' ]Ty) ⊢ weakenMor+coerc δ (A [ δ' ]Ty) (A [ δ ]Ty) == weakenMor+ δ' ∷> (Δ , A)

SubstTyMorEq : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ' ∷> Δ)
       → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ' == δ ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A [ δ' ]Ty)
SubstTmMorEq : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} →  Derivable (Δ ⊢ u :> A) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ' ∷> Δ)  
       → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ' == δ ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == coerc (A [ δ' ]Ty) (A [ δ ]Ty) (u [ δ' ]Tm) :> A [ δ ]Ty)


SubstTyMorEq {δ = δ} {δ' = δ'} (Pi {A = A} {B = B} dA dB) dδ dδ' dδ= dδ'=
                 = PiCong (SubstTy dA dδ) (SubstTy dA dδ') (SubstTy dB (WeakMor+ dA dδ)) ((SubstTy dB (WeakMor+ dA dδ'))) (SubstTyMorEq dA dδ dδ' dδ= dδ'=)
                 (congTyEq refl
                           MorRewrite
                           (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+coerc dA (SubstTy dA dδ) dδ' (SubstTyMorEq dA dδ dδ' dδ= dδ'=)) (WeakMor+Eq dA dδ' dδ dδ'= dδ=) (WeakMor+Eq! dA dδ' dδ dδ'= dδ=)))
             where
             MorRewrite = (((!(ap (λ x → B [ weakenMor x , coerc (weakenTy (A [ δ ]Ty)) (weakenTy (A [ δ' ]Ty)) (var last) ]Ty) ([idMor]Mor δ'))
                        ∙ ap (λ x → B [ x , coerc (weakenTy (A [ δ ]Ty)) (weakenTy (A [ δ' ]Ty)) (var last) ]Ty) (weaken[]Mor δ' (idMor _) last))
                        ∙ ! (ap (λ x → B [ x , coerc (weakenTy (A [ δ ]Ty)) (weakenTy (A [ δ' ]Ty)) (var last) ]Ty) (weakenMorInsert δ' (weakenMor (idMor _)) _)))
                        ∙ ! ([]Ty-assoc (weakenMor (idMor _) , coerc (weakenTy (A [ δ ]Ty)) (weakenTy (A [ δ' ]Ty)) (var last)) (weakenMor δ' , var last) B))
SubstTyMorEq UU dδ dδ' dδ= dδ'= = UUCong
SubstTyMorEq (El dv) dδ dδ' dδ= dδ'= = ElCong (TmTran
                                              (Conv UU UU (SubstTm dv dδ') UUCong)
                                              ((SubstTmMorEq dv dδ dδ' dδ= dδ'=))
                                              (TmSymm (SubstTmMorEq dv dδ' dδ' (MorRefl dδ') (MorRefl dδ'))))

SubstTmMorEq (VarLast _) dδ dδ' (_ , du=) dδ'= = congTmEq! refl
                                                      (ap-coerc-Tm (weakenTyInsert _ _ _) (weakenTyInsert _ _ _) refl)
                                                      (weakenTyInsert _ _ _)
                                                      du=

SubstTmMorEq (VarPrev dA dk) (dδ , _ ) (dδ' , _ ) (dδ= , _ ) (dδ'= , _) = congTmEq! refl (ap-coerc-Tm (weakenTyInsert _ _ _) (weakenTyInsert _ _ _) refl) (weakenTyInsert _ _ _) (SubstTmMorEq dk dδ dδ' dδ= dδ'=)

SubstTmMorEq {δ = δ} {δ' = δ'} (Conv {u = t} {A = A} {B = B} dA dB du dA=) dδ dδ' dδ= dδ'=
          = TmTran (Conv (SubstTy dA dδ) (SubstTy dB dδ) (Conv (SubstTy dA dδ') (SubstTy dA dδ) (SubstTm du dδ') (SubstTyMorEq dA dδ' dδ dδ'= dδ=)) (SubstTyEq dA= dδ))
                   (ConvEq (SubstTy dA dδ)
                           (SubstTmMorEq du dδ dδ' dδ= dδ'=)
                           (SubstTyEq dA= dδ))
                           (TmTran (Conv (SubstTy dA dδ') (SubstTy dB dδ) (SubstTm du dδ') (TyTran (SubstTy dB dδ') (SubstTyEq dA= dδ') (SubstTyMorEq dB dδ' dδ dδ'= dδ=))) 
                                   (CoercTrans (SubstTy dA dδ') (SubstTy dA dδ) (SubstTy dB dδ) (SubstTm du dδ') (SubstTyMorEq dA dδ' dδ dδ'= dδ=) (SubstTyEq dA= dδ)
                                    (TyTran
                                            (SubstTy dA dδ)
                                            (SubstTyMorEq dA dδ' dδ dδ'= dδ=)
                                            (SubstTyEq dA= dδ)))
                                            (TmSymm (CoercTrans (SubstTy dA dδ') (SubstTy dB dδ') (SubstTy dB dδ) (SubstTm du dδ') (SubstTyEq dA= dδ') (SubstTyMorEq dB dδ' dδ dδ'= dδ=)
                                                    (TyTran (SubstTy dB dδ') (SubstTyEq dA= dδ') (SubstTyMorEq dB dδ' dδ dδ'= dδ=)))))
SubstTmMorEq (Lam dA dB du) dδ dδ= = {!!}
-- LamCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) ({!!})) (SubstTmMorEq du (WeakMor+ dA dδ) ({!!}))
-- WeakMor+Eq dA dδ dδ=
SubstTmMorEq (App dA dB df da) dδ dδ' dδ= dδ'= = congTmEqTy! []Ty-substTy {!!}
-- (AppCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) ({!!})) (SubstTmMorEq df dδ dδ=) (SubstTmMorEq da dδ dδ=))

WeakMor+Eq {A = A} {δ = δ} {δ' = δ'} dA dδ dδ' dδ= dδ'=
              = WeakMorEq dδ'= , congTmEq
                                refl
                                ( ap-coerc-Tm ( weaken[]Ty A δ last) (weaken[]Ty A δ' last) refl) (weaken[]Ty A δ' last)
                                (TmSymm (TmTran (Conv (WeakTy (SubstTy dA dδ')) (WeakTy (SubstTy dA dδ')) (VarLast (SubstTy dA dδ')) (TyRefl (WeakTy (SubstTy dA dδ'))))
                                        (CoercTrans (WeakTy (SubstTy dA dδ')) (WeakTy (SubstTy dA dδ)) (WeakTy (SubstTy dA dδ')) (VarLast (SubstTy dA dδ')) (WeakTyEq (SubstTyMorEq dA dδ' dδ dδ'= dδ=)) (WeakTyEq (SubstTyMorEq dA dδ dδ' dδ= dδ'=)) (TyRefl (WeakTy (SubstTy dA dδ'))))
                                        (CoercRefl (VarLast (SubstTy dA dδ')))))
-- CoercRefl (VarLast (SubstTy dA dδ'))
WeakMor+Eq! {A = A} {δ = δ} {δ' = δ'} dA dδ dδ' dδ= dδ'=
              rewrite ! (weaken[]Ty A δ last) | ! (weaken[]Ty A δ' last)
              =  (WeakMorEq dδ= , congTmEq
                                refl
                                (ap-coerc-Tm ( weaken[]Ty A δ' last) (weaken[]Ty A δ last) refl)
                                (weaken[]Ty A δ last)
                                (TmRefl (Conv (WeakTy (SubstTy dA dδ')) (WeakTy (SubstTy dA dδ)) (VarLast (SubstTy dA dδ')) (WeakTyEq (SubstTyMorEq dA dδ' dδ (dδ'=) dδ=))) ) )

-- -- It does not seem easy to prove [SubstTyFullEq] directly instead of proving both [SubstTyEq] and
-- -- [SubstTyMorEq]. The reason is that in the [TySymm] case we would need [MorSymm] which is probably
-- -- bad for termination checking. On the other hand, neither [SubstTyEq] nor [SubstTyMorEq] require
-- -- [MorSymm]

-- -- Should those functions be replaced by [SubstTyMorEq2]?

SubstTyFullEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A') → (Γ ⊢ δ ∷> Δ)
       → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
SubstTyFullEq dA' dδ dA= dδ= = TyTran (SubstTy dA' dδ) (SubstTyEq dA= dδ) {!!}
-- (SubstTyMorEq dA' dδ dδ=)

SubstTmFullEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} →  Derivable (Δ ⊢ u' :> A) → (Γ ⊢ δ ∷> Δ) 
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == coerc ( A [ δ' ]Ty) (A [ δ ]Ty) (u' [ δ' ]Tm) :> A [ δ ]Ty)
SubstTmFullEq du' dδ du= dδ= = TmTran (SubstTm du' dδ) (SubstTmEq du= dδ) {!!}
-- (SubstTmMorEq du' dδ dδ=)


-- SubstMor : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ : Mor n m} → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor ∷> Θ)
-- SubstMor {Θ = ◇} {θ = ◇} tt dδ = tt
-- SubstMor {Θ = Θ , C} {θ = θ , w} (dθ , dw) dδ = (SubstMor dθ dδ , congTm ([]Ty-assoc _ _ _) refl (SubstTm dw dδ))

-- SubstMorEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ θ' : Mor m k} {δ : Mor n m} → (Δ ⊢ θ == θ' ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ' [ δ ]Mor ∷> Θ)
-- SubstMorEq {Θ = ◇} {θ = ◇} {θ' = ◇} dθ= dδ = tt
-- SubstMorEq {Θ = Θ , C} {θ = θ , w} {θ' = θ' , w'} (dθ= , dw) dδ = SubstMorEq dθ= dδ , congTmEqTy ([]Ty-assoc _ _ _) (SubstTmEq dw dδ)


-- SubstMorMorEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ δ' : Mor n m} → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ [ δ' ]Mor ∷> Θ)
-- SubstMorMorEq {Θ = ◇} {◇} tt dδ dδ= = tt
-- SubstMorMorEq {Θ = Θ , C} {θ , w} (dθ , dw) dδ dδ= = SubstMorMorEq dθ dδ dδ= , congTmEqTy ([]Ty-assoc _ _ _) (SubstTmMorEq dw dδ dδ=)




{- Derivability of the identity morphism -}

idMorDerivable : {Γ : Ctx n} →  ⊢ Γ → (Γ ⊢ idMor n ∷> Γ)
idMorDerivable {Γ = ◇} tt = tt
idMorDerivable {Γ = Γ , A} (dΓ , dA) = (WeakMor (idMorDerivable dΓ) , congTm (! ([idMor]Ty _) ∙ substTy-weakenTy') refl (VarLast dA))



-- {- Conversion rules for types and terms are admissible -}

-- ConvTy : {Γ Δ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A)
-- ConvTyEq : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivable (Γ ⊢ A == B) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A == B)
-- ConvTm : {Γ Δ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ u :> A)
-- ConvTmEq : {Γ Δ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → Derivable (Γ ⊢ u == v :> A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ u == v :> A)

-- ConvTm2' : {Γ Δ : Ctx n} {u : TmExpr n} {A A' : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A') → Derivable (Δ ⊢ u :> A')
-- ConvTm2' du dΓ= dA dA= = {!!}
-- {-Conv (ConvTy dA dΓ=) (ConvTm du dΓ=) (ConvTyEq dA= dΓ=) -}

-- ConvTy {Γ = Γ} {Δ = Δ} {A = A} (Pi dA dB) dΓ= = Pi (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
-- ConvTy UU dΓ= = UU
-- ConvTy (El dv) dΓ= = El (ConvTm dv dΓ=)
-- ConvTy (Sig dA dB) dΓ= = Sig (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
-- ConvTy Empty dΓ= = Empty
-- ConvTy Unit dΓ= = Unit
-- ConvTy Nat dΓ= = Nat
-- ConvTy (Id dA da db) dΓ= = Id (ConvTy dA dΓ=) (ConvTm da dΓ=) (ConvTm db dΓ=)

-- ConvTyEq (TySymm dA=) dΓ= = TySymm (ConvTyEq dA= dΓ=)
-- ConvTyEq (TyTran dB dA= dB=) dΓ= = TyTran (ConvTy dB dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= dΓ=)
-- ConvTyEq (PiCong dA dA= dB=) dΓ= = PiCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
-- ConvTyEq UUCong dΓ= = UUCong
-- ConvTyEq (ElCong dv=) dΓ= = ElCong (ConvTmEq dv= dΓ=)
-- ConvTyEq ElUU= dΓ= = ElUU=
-- ConvTyEq (ElPi= da db) dΓ= = ElPi= (ConvTm da dΓ=) (ConvTm db (dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=)))
-- ConvTyEq (SigCong dA dA= dB=) dΓ= = SigCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
-- ConvTyEq (ElSig= da db) dΓ= = ElSig= (ConvTm da dΓ=) (ConvTm db ((dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=))))
-- ConvTyEq EmptyCong dΓ= = EmptyCong
-- ConvTyEq ElEmpty= dΓ= = ElEmpty=
-- ConvTyEq UnitCong dΓ= = UnitCong
-- ConvTyEq ElUnit= dΓ= = ElUnit=
-- ConvTyEq NatCong dΓ= = NatCong
-- ConvTyEq ElNat= dΓ= = ElNat=
-- ConvTyEq (IdCong dA= da= db=) dΓ= = IdCong (ConvTyEq dA= dΓ=)  (ConvTmEq da= dΓ=) (ConvTmEq db= dΓ=)
-- ConvTyEq (ElId= da du dv) dΓ= = ElId= (ConvTm da dΓ=) (ConvTm du dΓ=) (ConvTm dv dΓ=)


-- ConvTm {Δ = Δ , B} {var last} (VarLast {A = A} dA) (dΓ= , dA' , dB , dA= , dA=') = {!!}
-- {- Conv (WeakTy dB) (VarLast dB) (WeakTyEq (TySymm dA=')) -}
-- ConvTm {Γ = Γ , A} {Δ = Δ , B} (VarPrev dA dk) (dΓ= , dA , dB , dA=) = VarPrev (ConvTy dA dΓ=) (ConvTm dk dΓ=)
-- ConvTm (Conv dA du dA=) dΓ= = Conv (ConvTy dA dΓ=) (ConvTm du dΓ=) (ConvTyEq dA= dΓ=)
-- ConvTm (Lam dA dB du) dΓ= = Lam (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm du (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
-- ConvTm (App dA dB df da) dΓ= = App (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm df dΓ=) (ConvTm da dΓ=)
-- ConvTm UUUU dΓ= = UUUU
-- ConvTm (PiUU da db) dΓ= = PiUU (ConvTm da dΓ=) (ConvTm db (dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=)))
-- ConvTm (SigUU da db) dΓ= = SigUU (ConvTm da dΓ=) (ConvTm db (dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=)))
-- ConvTm (Pair dA dB da db) dΓ= = Pair (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=) (ConvTm db dΓ=)
-- ConvTm (Pr1 dA dB du) dΓ= = Pr1 (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm du dΓ=)
-- ConvTm (Pr2 dA dB du) dΓ= = Pr2 (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm du dΓ=)
-- ConvTm EmptyUU dΓ= = EmptyUU
-- ConvTm (Emptyelim dA du) dΓ= = Emptyelim (ConvTy dA (dΓ= , Empty , Empty , EmptyCong , EmptyCong)) (ConvTm du dΓ=)
-- ConvTm UnitUU dΓ= = UnitUU
-- ConvTm TT dΓ= = TT
-- ConvTm (Unitelim dA ddtt du) dΓ= = Unitelim (ConvTy dA (dΓ= , Unit , Unit , UnitCong , UnitCong)) (ConvTm ddtt dΓ=) (ConvTm du dΓ=)
-- ConvTm NatUU dΓ= = NatUU
-- ConvTm Zero dΓ= = Zero
-- ConvTm (Suc du) dΓ= = Suc (ConvTm du dΓ=)
-- ConvTm (Natelim dP ddO ddS du) dΓ= = Natelim (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)) (ConvTm ddO dΓ=) (ConvTm ddS ((dΓ= , Nat , Nat , NatCong , NatCong) , dP , ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong) , TyRefl dP , TyRefl (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)))) (ConvTm du dΓ=)
-- ConvTm (IdUU da du dv) dΓ= = IdUU (ConvTm da dΓ=) (ConvTm du dΓ=) (ConvTm dv dΓ=)
-- ConvTm (Refl dA da) dΓ= = Refl (ConvTy dA dΓ=) (ConvTm da dΓ=)
-- ConvTm (JJ dA dP dd da db dp) dΓ= = JJ (ConvTy dA dΓ=) (ConvTy dP ((((dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)) , WeakTy dA , WeakTy (ConvTy dA dΓ=) , TyRefl (WeakTy dA) , TyRefl (WeakTy (ConvTy dA dΓ=))) , Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA)) , Id (WeakTy (WeakTy (ConvTy dA dΓ=))) (VarPrev (WeakTy (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy (ConvTy dA dΓ=))) , TyRefl (Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA))) , TyRefl (Id (WeakTy (WeakTy (ConvTy dA dΓ=))) (VarPrev (WeakTy (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy (ConvTy dA dΓ=))))))) (ConvTm dd (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=) (ConvTm db dΓ=) (ConvTm dp dΓ=)

-- ConvTmEq  {Δ = Δ , B} (VarLastCong {A = A} dA) (dΓ= , dA' , dB , dA= , dA=') = {!!}
-- -- ConvEq (WeakTy dB) (VarLastCong dB) (WeakTyEq (TySymm dA='))
-- ConvTmEq {Γ = Γ , B} {Δ , B'} (VarPrevCong {A = A} dA dk=) (dΓ= , dA , dB , dA=) = VarPrevCong (ConvTy dA dΓ=) (ConvTmEq dk= dΓ=)
-- ConvTmEq (TmSymm du=) dΓ= = TmSymm (ConvTmEq du= dΓ=)
-- ConvTmEq (TmTran dv du= dv=) dΓ= = TmTran (ConvTm dv dΓ=) (ConvTmEq du= dΓ=) (ConvTmEq dv= dΓ=)
-- ConvTmEq (ConvEq dA du= dA=) dΓ= = ConvEq (ConvTy dA dΓ=) (ConvTmEq du= dΓ=) (ConvTyEq dA= dΓ=)
-- ConvTmEq UUUUCong dΓ= = UUUUCong
-- ConvTmEq (PiUUCong da da= db=) dΓ= = PiUUCong (ConvTm da dΓ=) (ConvTmEq da= dΓ=) (ConvTmEq db= (dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=)))
-- ConvTmEq (LamCong dA dA= dB= du=) dΓ= = LamCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq du= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
-- ConvTmEq (AppCong dA dA= dB= df= da=) dΓ= = AppCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq df= dΓ=) (ConvTmEq da= dΓ=)
-- ConvTmEq (SigUUCong da da= db=) dΓ= = SigUUCong (ConvTm da dΓ=) (ConvTmEq da= dΓ=) (ConvTmEq db= (dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=)))
-- ConvTmEq (PairCong dA dA= dB= da= db=) dΓ= = PairCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq da= dΓ=) (ConvTmEq db= dΓ=)
-- ConvTmEq (Pr1Cong dA dA= dB= du=) dΓ= = Pr1Cong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq du= dΓ=)
-- ConvTmEq (Pr2Cong dA dA= dB= du=) dΓ= = Pr2Cong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq du= dΓ=)
-- ConvTmEq EmptyUUCong dΓ= = EmptyUUCong
-- ConvTmEq (EmptyelimCong dA= du=) dΓ= = EmptyelimCong (ConvTyEq dA= (dΓ= , Empty , Empty , EmptyCong , EmptyCong)) (ConvTmEq du= dΓ=)
-- ConvTmEq UnitUUCong dΓ= = UnitUUCong
-- ConvTmEq TTCong dΓ= = TTCong
-- ConvTmEq (UnitelimCong dA= ddtt= du=) dΓ= = UnitelimCong (ConvTyEq dA= (dΓ= , Unit , Unit , UnitCong , UnitCong)) (ConvTmEq ddtt= dΓ=) (ConvTmEq du= dΓ=)
-- ConvTmEq NatUUCong dΓ= = NatUUCong
-- ConvTmEq ZeroCong dΓ= = ZeroCong
-- ConvTmEq (SucCong du=) dΓ= = SucCong (ConvTmEq du= dΓ=)
-- ConvTmEq (NatelimCong dP dP= ddO= ddS= du=) dΓ= = NatelimCong (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)) (ConvTyEq dP= (dΓ= , Nat , Nat , NatCong , NatCong)) (ConvTmEq ddO= dΓ=) (ConvTmEq ddS= ((dΓ= , Nat , Nat , NatCong , NatCong) , dP , ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong) , TyRefl dP , TyRefl (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)))) (ConvTmEq du= dΓ=)
-- ConvTmEq (IdUUCong da= du= dv=) dΓ= = IdUUCong (ConvTmEq da= dΓ=) (ConvTmEq du= dΓ=) (ConvTmEq dv= dΓ=)
-- ConvTmEq (ReflCong dA= da=) dΓ= = ReflCong (ConvTyEq dA= dΓ=) (ConvTmEq da= dΓ=)
-- ConvTmEq (JJCong dA dA= dP= dd= da= db= dp=) dΓ= = JJCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dP= ((((dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)) , WeakTy dA , WeakTy (ConvTy dA dΓ=) , TyRefl (WeakTy dA) , TyRefl (WeakTy (ConvTy dA dΓ=))) , Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA)) , Id (WeakTy (WeakTy (ConvTy dA dΓ=))) (VarPrev (WeakTy (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy (ConvTy dA dΓ=))) , TyRefl (Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA))) , TyRefl (Id (WeakTy (WeakTy (ConvTy dA dΓ=))) (VarPrev (WeakTy (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy (ConvTy dA dΓ=))))))) (ConvTmEq dd= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq da= dΓ=) (ConvTmEq db= dΓ=) (ConvTmEq dp= dΓ=)
-- ConvTmEq (BetaPi dA dB du da) dΓ= = BetaPi (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm du (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=)
-- ConvTmEq (BetaSig1 dA dB da db) dΓ= = BetaSig1 (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=) (ConvTm db dΓ=)
-- ConvTmEq (BetaSig2 dA dB da db) dΓ= = BetaSig2 (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=) (ConvTm db dΓ=)
-- ConvTmEq (BetaUnit dA ddtt) dΓ= = BetaUnit (ConvTy dA (dΓ= , Unit , Unit , UnitCong , UnitCong)) (ConvTm ddtt dΓ=)
-- ConvTmEq (BetaNatZero dP ddO ddS) dΓ= = BetaNatZero (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)) (ConvTm ddO dΓ=) (ConvTm ddS ((dΓ= , Nat , Nat , NatCong , NatCong) , dP , ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong) , TyRefl dP , TyRefl (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong))))
-- ConvTmEq (BetaNatSuc dP ddO ddS du) dΓ= = BetaNatSuc (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)) (ConvTm ddO dΓ=) (ConvTm ddS ((dΓ= , Nat , Nat , NatCong , NatCong) , dP , ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong) , TyRefl dP , TyRefl (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)))) (ConvTm du dΓ=)
-- ConvTmEq (BetaIdRefl dA dP dd da) dΓ= =
--   BetaIdRefl
--     (ConvTy dA dΓ=)
--     (ConvTy dP (((dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))
--                , (WeakTy dA , WeakTy (ConvTy dA dΓ=) , TyRefl (WeakTy dA) , TyRefl (WeakTy (ConvTy dA dΓ=))))
--                , (Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA))
--                 , Id (WeakTy (WeakTy (ConvTy dA dΓ=))) (VarPrev (WeakTy (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy (ConvTy dA dΓ=)))
--                 , TyRefl (Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA)))
--                 , TyRefl (Id (WeakTy (WeakTy (ConvTy dA dΓ=))) (VarPrev (WeakTy (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy (ConvTy dA dΓ=)))))))
--     (ConvTm dd (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
--     (ConvTm da dΓ=)
-- ConvTmEq (EtaPi dA dB df) dΓ= =
--   EtaPi (ConvTy dA dΓ=)
--         (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
--         (ConvTm df dΓ=)
-- ConvTmEq (EtaSig dA dB du) dΓ= =
--   EtaSig (ConvTy dA dΓ=)
--          (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
--          (ConvTm du dΓ=)

-- {- Subst3 -}

-- Subst1Tm : {Γ : Ctx n} {B : TyExpr n} {A : TyExpr (suc n)} {t : TmExpr (suc n)} {u : TmExpr n}
--          → ⊢ Γ → Derivable ((Γ , B) ⊢ t :> A) → Derivable (Γ ⊢ u :> B)
--          → Derivable (Γ ⊢ substTm t u :> substTy A u)
-- Subst1Tm dΓ dt du = SubstTm dt (idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du)

-- Subst2Ty : {Γ : Ctx n} {B : TyExpr n} {C : TyExpr (suc n)} {D : TyExpr (suc (suc n))} {u v : TmExpr n}
--          → ⊢ Γ → Derivable ((((Γ , B) , C)) ⊢ D) → Derivable (Γ ⊢ u :> B) → Derivable (Γ ⊢ v :> substTy C u) → Derivable (Γ ⊢ subst2Ty D u v)
-- Subst2Ty dΓ dA du dv = SubstTy dA ((idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du) , dv)

-- Subst3Ty : {Γ : Ctx n} {B : TyExpr n} {C : TyExpr (suc n)} {D : TyExpr (suc (suc n))} {A : TyExpr (suc (suc (suc n)))} {u v w : TmExpr n}
--          → ⊢ Γ → Derivable ((((Γ , B) , C) , D) ⊢ A) → Derivable (Γ ⊢ u :> B) → Derivable (Γ ⊢ v :> substTy C u) → Derivable (Γ ⊢ w :> subst2Ty D u v)
--          → Derivable (Γ ⊢ subst3Ty A u v w)
-- Subst3Ty dΓ dA du dv dw = SubstTy dA (((idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du) , dv) , dw)

-- Subst3TyEq : {Γ : Ctx n} {B : TyExpr n} {C : TyExpr (suc n)} {D : TyExpr (suc (suc n))} {A A' : TyExpr (suc (suc (suc n)))} {u u' v v' w w' : TmExpr n}
--            → ⊢ Γ → Derivable ((((Γ , B) , C) , D) ⊢ A') → Derivable (Γ ⊢ u :> B) → Derivable (Γ ⊢ v :> substTy C u) → Derivable (Γ ⊢ w :> subst2Ty D u v)
--            → Derivable ((((Γ , B) , C) , D) ⊢ A == A') → Derivable (Γ ⊢ u == u' :> B) → Derivable (Γ ⊢ v == v' :> substTy C u) → Derivable (Γ ⊢ w == w' :> subst2Ty D u v)
--            → Derivable (Γ ⊢ subst3Ty A u v w == subst3Ty A' u' v' w')
-- Subst3TyEq dΓ dA' du dv dw dA= du= dv= dw= = SubstTyFullEq dA' (((idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du) , dv) , dw) dA= (((MorRefl (idMorDerivable dΓ) , congTmEqTy! ([idMor]Ty _) du=) , dv=) , dw=)

-- {- Various other admissible rules -}

-- CtxSymm : {Γ Δ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Γ
-- CtxSymm {Γ = ◇} {Δ = ◇} tt = tt
-- CtxSymm {Γ = Γ , A} {Δ , B} (dΓ= , dA , dB , dA= , dA=') = (CtxSymm dΓ= , dB , dA , TySymm dA=' , TySymm dA=)

-- CtxTran : {Γ Δ Θ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Θ → ⊢ Γ == Θ
-- CtxTran {Γ = ◇} {Δ = ◇} {Θ = ◇} tt tt = tt
-- CtxTran {Γ = Γ , A} {Δ , B} {Θ , C} (dΓ= , dA , dB , dA= , dA=') (dΔ= , dB' , dC , dB= , dB=') =
--   (CtxTran dΓ= dΔ= , dA , dC , TyTran (ConvTy dB (CtxSymm dΓ=)) dA= (ConvTyEq dB= (CtxSymm dΓ=)) , TyTran (ConvTy dB dΔ=) (ConvTyEq dA=' dΔ=) dB=')


-- CtxEqCtx1 : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → ⊢ Γ
-- CtxEqCtx1 {Γ = ◇} {Γ' = ◇} tt = tt
-- CtxEqCtx1 {Γ = Γ , A} {Γ' , A'} (dΓ= , dA , dA' , dA=) = (CtxEqCtx1 dΓ= , dA)

-- CtxEqCtx2 : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → ⊢ Γ'
-- CtxEqCtx2 {Γ = ◇} {Γ' = ◇} tt = tt
-- CtxEqCtx2 {Γ = Γ , A} {Γ' , A'} (dΓ= , dA , dA' , dA=) = (CtxEqCtx2 dΓ= , dA')



-- TyEqTy1 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A)
-- TyEqTy2 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B)
-- TmEqTm1 : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u :> A)
-- TmEqTm2 : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u' :> A)

-- TyEqTy1 dΓ (TySymm dA=) = TyEqTy2 dΓ dA=
-- TyEqTy1 dΓ (TyTran _ dA= dB=) = TyEqTy1 dΓ dA=
-- TyEqTy1 dΓ UUCong = UU
-- TyEqTy1 dΓ (ElCong dv=) = El (TmEqTm1 dΓ dv=) 
-- TyEqTy1 dΓ (PiCong dA dA= dB=) = Pi dA (TyEqTy1 (dΓ , dA) dB=)
-- TyEqTy1 dΓ (SigCong dA dA= dB=) = Sig dA (TyEqTy1 (dΓ , dA) dB=)
-- TyEqTy1 dΓ EmptyCong = Empty
-- TyEqTy1 dΓ ElEmpty= = El EmptyUU
-- TyEqTy1 dΓ UnitCong = Unit
-- TyEqTy1 dΓ ElUnit= = El UnitUU
-- TyEqTy1 dΓ NatCong = Nat
-- TyEqTy1 dΓ (IdCong dA= da= db=) = Id (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)
-- TyEqTy1 dΓ ElUU= = El UUUU
-- TyEqTy1 dΓ (ElPi= da db) = El (PiUU da db)
-- TyEqTy1 dΓ (ElSig= da db) = El (SigUU da db)
-- TyEqTy1 dΓ ElNat= = El NatUU
-- TyEqTy1 dΓ (ElId= da du dv) = El (IdUU da du dv)


-- TyEqTy2 dΓ (TySymm dA=) = TyEqTy1 dΓ dA=
-- TyEqTy2 dΓ (TyTran dB dA= dB=) = TyEqTy2 dΓ dB=
-- TyEqTy2 dΓ UUCong = UU
-- TyEqTy2 dΓ (ElCong dv=) = El (TmEqTm2 dΓ dv=)
-- TyEqTy2 dΓ (PiCong dA dA= dB=) = Pi (TyEqTy2 dΓ dA=) (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
-- TyEqTy2 dΓ (SigCong dA dA= dB=) = Sig (TyEqTy2 dΓ dA=) (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
-- TyEqTy2 dΓ EmptyCong = Empty
-- TyEqTy2 dΓ ElEmpty= = Empty
-- TyEqTy2 dΓ UnitCong = Unit
-- TyEqTy2 dΓ ElUnit= = Unit
-- TyEqTy2 dΓ NatCong = Nat
-- TyEqTy2 dΓ (IdCong dA= da= db=) = {!!}
-- -- Id (TyEqTy2 dΓ dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ db=) dA=)
-- TyEqTy2 dΓ ElUU= = UU
-- TyEqTy2 dΓ (ElPi= da db) = Pi (El da) (El db)
-- TyEqTy2 dΓ (ElSig= da db) = Sig (El da) (El db)
-- TyEqTy2 dΓ ElNat= = Nat
-- TyEqTy2 dΓ (ElId= da du dv) = Id (El da) du dv

-- TmEqTm1 dΓ (TmSymm du=) = TmEqTm2 dΓ du= 
-- TmEqTm1 dΓ (TmTran _ du= dv=) = TmEqTm1 dΓ du=
-- TmEqTm1 dΓ (ConvEq dA du= dA=) = Conv dA (TmEqTm1 dΓ du=) dA=
-- TmEqTm1 dΓ (VarLastCong dA) = VarLast dA
-- TmEqTm1 (dΓ , dA) (VarPrevCong dA' dk=) = VarPrev dA' (TmEqTm1 dΓ dk=)
-- TmEqTm1 dΓ UUUUCong = UUUU
-- TmEqTm1 dΓ (PiUUCong da da= db=) = PiUU da (TmEqTm1 (dΓ , El da) db=)
-- TmEqTm1 dΓ (LamCong dA dA= dB= du=) = Lam (TyEqTy1 dΓ dA=) (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 (dΓ , dA) du=)
-- TmEqTm1 dΓ (AppCong dA dA= dB= df= da=) = App (TyEqTy1 dΓ dA=) (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 dΓ df=) (TmEqTm1 dΓ da=)
-- TmEqTm1 dΓ (SigUUCong da da= db=) = SigUU da (TmEqTm1 (dΓ , El da) db=)
-- TmEqTm1 dΓ (PairCong dA dA= dB= da= db=) = Pair dA (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)
-- TmEqTm1 dΓ (Pr1Cong dA dA= dB= du=) = Pr1 dA (TyEqTy1  (dΓ , dA) dB=) (TmEqTm1 dΓ du=)
-- TmEqTm1 dΓ (Pr2Cong dA dA= dB= du=) = Pr2 dA (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 dΓ du=)
-- TmEqTm1 dΓ EmptyUUCong = EmptyUU
-- TmEqTm1 dΓ (EmptyelimCong dA= du=) = Emptyelim (TyEqTy1 (dΓ , Empty) dA=) (TmEqTm1 dΓ du=)
-- TmEqTm1 dΓ UnitUUCong = UnitUU
-- TmEqTm1 dΓ TTCong = TT
-- TmEqTm1 dΓ (UnitelimCong dA= ddtt= du=) = Unitelim (TyEqTy1 (dΓ , Unit) dA=) (TmEqTm1 dΓ ddtt=) (TmEqTm1 dΓ du=)
-- TmEqTm1 dΓ NatUUCong = NatUU
-- TmEqTm1 dΓ ZeroCong = Zero
-- TmEqTm1 dΓ (SucCong du=) = Suc (TmEqTm1 dΓ du=)
-- TmEqTm1 dΓ (NatelimCong dP dP= ddO= ddS= du=) = Natelim (TyEqTy1 (dΓ , Nat) dP=) (TmEqTm1 dΓ ddO=) (TmEqTm1 ((dΓ , Nat) , dP) ddS=) (TmEqTm1 dΓ du=)
-- TmEqTm1 dΓ (IdUUCong da= du= dv=) = IdUU (TmEqTm1 dΓ da=) (TmEqTm1 dΓ du=) (TmEqTm1 dΓ dv=)
-- TmEqTm1 dΓ (ReflCong dA= da=) = Refl (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=)
-- TmEqTm1 dΓ (JJCong dA dA= dP= dd= da= db= dp=) = JJ dA (TyEqTy1 (((dΓ , dA) , (WeakTy dA)) , (Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA)))) dP=) (TmEqTm1 (dΓ , dA) dd=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=) (TmEqTm1 dΓ dp=)
-- TmEqTm1 dΓ (BetaPi dA dB du da) = App dA dB (Lam dA dB du) da
-- TmEqTm1 dΓ (BetaSig1 dA dB da db) = Pr1 dA dB (Pair dA dB da db)
-- TmEqTm1 dΓ (BetaSig2 {B = B} dA dB da db) = {!!}
-- -- Conv (SubstTy dB (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (Pr1 dA dB (Pair dA dB da db)))) (Pr2 dA dB (Pair dA dB da db)) (SubstTyMorEq dB (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (Pr1 dA dB (Pair dA dB da db))) (MorRefl (idMorDerivable dΓ) , congTmEqTy! ([idMor]Ty _) (BetaSig1 dA dB da db)))
-- TmEqTm1 dΓ (BetaUnit dA ddtt) = Unitelim dA ddtt TT
-- TmEqTm1 dΓ (BetaNatZero dP ddO ddS) = Natelim dP ddO ddS Zero
-- TmEqTm1 dΓ (BetaNatSuc dP ddO ddS du) = Natelim dP ddO ddS (Suc du)
-- TmEqTm1 dΓ (BetaIdRefl dA dP dd da) = JJ dA dP dd da da (Refl dA da)
-- TmEqTm1 dΓ (EtaPi dA dB df) = df
-- TmEqTm1 dΓ (EtaSig dA dB du) = du

-- TmEqTm2 dΓ (TmSymm du=) = TmEqTm1 dΓ du=
-- TmEqTm2 dΓ (TmTran _ du= dv=) = TmEqTm2 dΓ dv=
-- TmEqTm2 dΓ (ConvEq dA du= dA=) = Conv dA (TmEqTm2 dΓ du=) dA=
-- TmEqTm2 dΓ (VarLastCong dA) = VarLast dA
-- TmEqTm2 (dΓ , dA) (VarPrevCong dA' dk=) = VarPrev dA' (TmEqTm2 dΓ dk=)
-- TmEqTm2 dΓ UUUUCong = UUUU
-- TmEqTm2 dΓ (PiUUCong da da= db=) = PiUU (TmEqTm2 dΓ da=) (ConvTm (TmEqTm2 (dΓ , El da) db=) (CtxRefl dΓ , El da , El (TmEqTm2 dΓ da=) , ElCong da= , ElCong da=))
-- TmEqTm2 dΓ (LamCong dA dA= dB= du=) = {!!}
-- --   Conv (Pi (TyEqTy2 dΓ dA=)
-- --            (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=)))
-- --        (Lam (TyEqTy2 dΓ dA=)
-- --             (ConvTy (TyEqTy2 (dΓ , TyEqTy1 dΓ dA=) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
-- --             (ConvTm (Conv (TyEqTy1 (dΓ , dA) dB=) (TmEqTm2 (dΓ , dA) du=) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=)))
-- --        (PiCong (TyEqTy2 dΓ dA=)
-- --                (TySymm dA=)
-- --                (ConvTyEq (TySymm dB=) (CtxRefl dΓ , dA , ConvTy (TyEqTy2 dΓ dA=) (CtxRefl dΓ) , dA= , dA=)))
-- TmEqTm2 dΓ (AppCong dA dA= dB= df= da=) = {!!}
-- --   Conv (SubstTy (TyEqTy2 (dΓ , dA) dB=) (idMorDerivable dΓ , Conv dA (TmEqTm2 dΓ da=) (congTyEq! refl ([idMor]Ty _) (TyRefl dA))))
-- --        (App (TyEqTy2 dΓ dA=)
-- --             (ConvTy (TyEqTy2 (dΓ , TyEqTy1 dΓ dA=) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
-- --             (Conv (Pi dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ df=) (PiCong dA dA= dB=))
-- --             (Conv dA (TmEqTm2 dΓ da=) dA=))
-- --        (TySymm (SubstTyFullEq (TyEqTy2 (dΓ , dA) dB=)
-- --                               (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (TmEqTm1 dΓ da=))
-- --                               dB=
-- --                               (MorRefl (idMorDerivable dΓ) , congTmEqTy! ([idMor]Ty _) da=)))
-- TmEqTm2 dΓ (SigUUCong da da= db=) = SigUU (TmEqTm2 dΓ da=) (ConvTm (TmEqTm2 (dΓ , El da) db=) (CtxRefl dΓ , El da , El (TmEqTm2 dΓ da=) , ElCong da= , ElCong da=))
-- TmEqTm2 dΓ (PairCong dA dA= dB= da= db=) = {!!}
-- --   Conv (Sig (TyEqTy2 dΓ dA=)
-- --             (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=)))
-- --        (Pair (TyEqTy2 dΓ dA=)
-- --              (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
-- --              (Conv dA (TmEqTm2 dΓ da=) dA=)
-- --              (Conv (SubstTy (TyEqTy1 (dΓ , dA) dB=) (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (TmEqTm1 dΓ da=)))
-- --                    (TmEqTm2 dΓ db=)
-- --                    (SubstTyFullEq (TyEqTy2 (dΓ , dA) dB=)
-- --                                   (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (TmEqTm1 dΓ da=))
-- --                                   dB=
-- --                                   (MorRefl (idMorDerivable dΓ) , congTmEqTy! ([idMor]Ty _) da=))))
-- --        (SigCong (TyEqTy2 dΓ dA=)
-- --                 (TySymm dA=)
-- --                 (ConvTyEq (TySymm dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=)))
-- TmEqTm2 dΓ (Pr1Cong dA dA= dB= du=) = {!!}
-- --   Conv (TyEqTy2 dΓ dA=)
-- --        (Pr1 (TyEqTy2 dΓ dA=)
-- --             (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
-- --             (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=)))
-- --        (TySymm dA=)
-- TmEqTm2 dΓ (Pr2Cong dA dA= dB= du=) = {!!}
-- --   Conv (SubstTy (TyEqTy2 (dΓ , dA) dB=)
-- --                 (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (Conv (TyEqTy2 dΓ dA=)
-- --                                                                       (Pr1 (TyEqTy2 dΓ dA=)
-- --                                                                            (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
-- --                                                                            (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=)))
-- --                                                                       (TySymm dA=))))
-- --        (Pr2 (TyEqTy2 dΓ dA=)
-- --             (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
-- --             (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=)))
-- --        (SubstTyFullEq (TyEqTy1 (dΓ , dA) dB=)
-- --                       (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (Conv (TyEqTy2 dΓ dA=)
-- --                                                                             (Pr1 (TyEqTy2 dΓ dA=)
-- --                                                                                  (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
-- --                                                                                  (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=)))
-- --                                                                             (TySymm dA=)))
-- --                       (TySymm dB=)
-- --                       (MorRefl (idMorDerivable dΓ) , TmSymm (congTmEqTy! ([idMor]Ty _) (Pr1Cong dA dA= dB= du=))))
-- TmEqTm2 dΓ EmptyUUCong = EmptyUU
-- TmEqTm2 dΓ (EmptyelimCong dA= du=) = {!!}
-- -- Conv (SubstTy (TyEqTy2 (dΓ , Empty) dA=) (idMorDerivable dΓ , TmEqTm2 dΓ du=)) (Emptyelim (TyEqTy2 (dΓ , Empty) dA=) (TmEqTm2 dΓ du=)) (SubstTyFullEq (TyEqTy1 (dΓ , Empty) dA=) (idMorDerivable dΓ , TmEqTm2 dΓ du=) (TySymm dA=) (MorRefl (idMorDerivable dΓ) , TmSymm du=))
-- TmEqTm2 dΓ UnitUUCong = UnitUU
-- TmEqTm2 dΓ TTCong = TT
-- TmEqTm2 dΓ (UnitelimCong dA= ddtt= du=) = {!!}
-- -- Conv (SubstTy (TyEqTy2 (dΓ , Unit) dA=)
-- --                                                (idMorDerivable dΓ , TmEqTm2 dΓ du=))
-- --                                                (Unitelim (TyEqTy2 (dΓ , Unit) dA=) (Conv (SubstTy (TyEqTy1 (dΓ , Unit) dA=) (idMorDerivable dΓ , TT)) (TmEqTm2 dΓ ddtt=) (SubstTyEq dA= (idMorDerivable dΓ , TT))) (TmEqTm2 dΓ du=)) (SubstTyFullEq (TyEqTy1 (dΓ , Unit) dA=) (idMorDerivable dΓ , TmEqTm2 dΓ du=) (TySymm dA=) (MorRefl (idMorDerivable dΓ) , TmSymm du=))
-- TmEqTm2 dΓ NatUUCong = NatUU
-- TmEqTm2 dΓ ZeroCong = Zero
-- TmEqTm2 dΓ (SucCong du=) = Suc (TmEqTm2 dΓ du=)
-- TmEqTm2 dΓ (NatelimCong dP dP= ddO= ddS= du=) =
--   let dP' = TyEqTy2 (dΓ , Nat) dP=
--       ddO' = Conv (SubstTy dP (idMorDerivable dΓ , Zero)) (TmEqTm2 dΓ ddO=) (SubstTyEq dP= (idMorDerivable dΓ , Zero))
--       ddS' = ConvTm2' (TmEqTm2 ((dΓ , Nat) , dP) ddS=)
--                       (CtxRefl (dΓ , Nat) , dP , dP' , dP= , dP=)
--                       (SubstTy (WeakTy (WeakTy dP)) (idMorDerivable ((dΓ , Nat) , dP) , Suc (VarPrev Nat (VarLast Nat)))) 
--                       (SubstTyEq (WeakTyEq (WeakTyEq dP=)) (idMorDerivable ((dΓ , Nat) , dP) , Suc (VarPrev Nat (VarLast Nat)))) 
--       du' = TmEqTm2 dΓ du= in {!!}
-- {-  Conv (SubstTy dP' (idMorDerivable dΓ , du'))
--        (Natelim dP' ddO' ddS' du')
--        (TySymm (SubstTyFullEq dP' (idMorDerivable dΓ , TmEqTm1 dΓ du=) dP= (MorRefl (idMorDerivable dΓ) , du=))) 
-- -}
-- TmEqTm2 dΓ (IdUUCong da= du= dv=) = {!!}
-- -- IdUU (TmEqTm2 dΓ da=) (Conv (El (TmEqTm1 dΓ da=)) (TmEqTm2 dΓ du=) (ElCong da=)) (Conv (El (TmEqTm1 dΓ da=)) (TmEqTm2 dΓ dv=) (ElCong da=))
-- TmEqTm2 dΓ (ReflCong dA= da=) = {!!}
-- {-  Conv (Id (TyEqTy2 dΓ dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=))
--        (Refl (TyEqTy2 dΓ dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=))
--        (IdCong (TySymm dA=) (ConvEq (TyEqTy1 dΓ dA=) (TmSymm da=) dA=) (ConvEq (TyEqTy1 dΓ dA=) (TmSymm da=) dA=))
-- -}
-- TmEqTm2 dΓ (JJCong dA dA= dP= dd= da= db= dp=) =
--   let dA' = TyEqTy2 dΓ dA=
--       dP' = ConvTy (TyEqTy2 (((dΓ , dA) , WeakTy dA) , Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA))) dP=)
--                    (((CtxRefl dΓ , dA , dA' , dA= , dA=) , WeakTy dA , WeakTy dA' , WeakTyEq dA= , WeakTyEq dA=) ,
--                      Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA)) , Id (WeakTy (WeakTy dA')) (VarPrev (WeakTy dA') (VarLast dA')) (VarLast (WeakTy dA')) ,
--                      IdCong (WeakTyEq (WeakTyEq dA=)) (VarPrevCong (WeakTy dA) (VarLastCong dA)) (VarLastCong (WeakTy dA)) ,
--                      IdCong (WeakTyEq (WeakTyEq dA=)) (VarPrevCong (WeakTy dA) (ConvTmEq (VarLastCong dA) (CtxRefl dΓ , dA , dA' , dA= , dA=)))
--                                                       (ConvTmEq (VarLastCong (WeakTy dA)) ((CtxRefl dΓ , dA , dA' , dA= , dA=) , WeakTy dA , WeakTy dA' , WeakTyEq dA= , WeakTyEq dA=)))
--       dd' = ConvTm2' (TmEqTm2 (dΓ , dA) dd=)
--                      (CtxRefl dΓ , dA , dA' , dA= , dA=)
--                      (Subst3Ty (dΓ , dA)
--                                (WeakTy (TyEqTy1 (((dΓ , dA) , WeakTy dA) , Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA))) dP=))
--                                (VarLast dA)
--                                (congTmTy! (ap-substTy weakenTy-weakenTy refl ∙ substTy-weakenTy) (VarLast dA))
--                                (congTmTy! (ap-id-Ty (substTy-weakenTy' ∙ substTy-weakenTy' ∙ [idMor]Ty _) refl refl) (Refl (WeakTy dA) (VarLast dA))))
--                      (Subst3TyEq (dΓ , dA)
--                                  (WeakTy (TyEqTy2 (((dΓ , dA) , WeakTy dA) , Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA))) dP=))
--                                  (VarLast dA)
--                                  (congTmTy! (ap-substTy weakenTy-weakenTy refl ∙ substTy-weakenTy) (VarLast dA))
--                                  (congTmTy! (ap-id-Ty (substTy-weakenTy' ∙ substTy-weakenTy' ∙ [idMor]Ty _) refl refl) (Refl (WeakTy dA) (VarLast dA)))
--                                  (WeakTyEq dP=)
--                                  (VarLastCong dA)
--                                  (congTmEqTy! (ap-substTy weakenTy-weakenTy refl ∙ substTy-weakenTy) (VarLastCong dA))
--                                  (congTmEqTy! (ap-id-Ty (substTy-weakenTy' ∙ substTy-weakenTy' ∙ [idMor]Ty _) refl refl) (ReflCong (WeakTyEq dA=) (VarLastCong dA))))
--       da' = Conv dA (TmEqTm2 dΓ da=) dA=
--       db' = Conv dA (TmEqTm2 dΓ db=) dA=
--       dp' = Conv (Id dA (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)) (TmEqTm2 dΓ dp=) (IdCong dA= da= db=) in {!!}
-- {-  Conv (Subst3Ty dΓ dP' da' (congTmTy! substTy-weakenTy db') (congTmTy! (ap-id-Ty subst2Ty-weakenTy refl refl) dp'))
--        (JJ dA' dP' dd' da' db' dp')
--        (Subst3TyEq dΓ
--                    (TyEqTy1 (((dΓ , dA) , (WeakTy dA)) , (Id (WeakTy (WeakTy dA)) (VarPrev (WeakTy dA) (VarLast dA)) (VarLast (WeakTy dA)))) dP=)
--                    (TmEqTm2 dΓ da=)
--                    (congTmTy! substTy-weakenTy (TmEqTm2 dΓ db=))
--                    (Conv (Id (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)) (TmEqTm2 dΓ dp=) (IdCong (congTyRefl dA (! subst2Ty-weakenTy)) da= db=))
--                    (TySymm dP=)
--                    (TmSymm da=)
--                    (congTmEqTy! substTy-weakenTy (TmSymm db=))
--                    (ConvEq (Id (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)) (TmSymm dp=) (IdCong (congTyRefl dA (! subst2Ty-weakenTy)) da= db=)))
-- -}
-- TmEqTm2 dΓ (BetaPi dA dB du da) = SubstTm du (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl da)
-- TmEqTm2 dΓ (BetaSig1 dA dB da db) = da
-- TmEqTm2 dΓ (BetaSig2 dA dB da db) = db
-- TmEqTm2 dΓ (BetaUnit dA ddtt) = ddtt
-- TmEqTm2 dΓ (BetaNatZero dP ddO ddS) = ddO
-- TmEqTm2 dΓ (BetaNatSuc dP ddO ddS du) = {!!}
-- {-  Conv (SubstTy (SubstTy (WeakTy (WeakTy dP)) (idMorDerivable ((dΓ , Nat) , dP) , Suc (VarPrev Nat (VarLast Nat)))) ((idMorDerivable dΓ , du) , Natelim dP ddO ddS du))
--        (SubstTm ddS ((idMorDerivable dΓ , du) , Natelim dP ddO ddS du))
--        (congTyRefl' (SubstTy dP (idMorDerivable dΓ , Suc du)) subst2Ty-substTy)  
-- -}
-- TmEqTm2 dΓ (BetaIdRefl dA dP dd da) = congTmTy (substTy-subst3Ty ∙ ap-subst3Ty refl refl refl (ap-refl-Tm substTy-weakenTy refl)) (Subst1Tm dΓ dd da)
-- TmEqTm2 dΓ (EtaPi dA dB df) = Lam dA dB (congTmTy (substTy-weakenTy' ∙ [idMor]Ty _) (App (WeakTy dA) (WeakTy dB) (WeakTm df) (VarLast dA)))
-- TmEqTm2 dΓ (EtaSig dA dB du) = Pair dA dB (Pr1 dA dB du) (Pr2 dA dB du)

-- MorEqMor1 : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ ∷> Δ)
-- MorEqMor2 : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ' ∷> Δ)

-- MorEqMor1 {Δ = ◇} {δ = ◇} {◇} _ _ dδ= = tt
-- MorEqMor1 {Δ = Δ , B} {δ = δ , u} {δ' , u'} dΓ (dΔ , _) (dδ= , du=) = (MorEqMor1 dΓ dΔ dδ= , TmEqTm1 dΓ du=)

-- MorEqMor2 {Δ = ◇} {δ = ◇} {◇} _ _ dδ= = tt
-- MorEqMor2 {Δ = Δ , B} {δ = δ , u} {δ' , u'} dΓ (dΔ , dB) (dδ= , du=) = {!!}
-- -- (MorEqMor2 dΓ dΔ dδ= , Conv (SubstTy dB (MorEqMor1 dΓ dΔ dδ=)) (TmEqTm2 dΓ du=) (SubstTyMorEq dB (MorEqMor1 dΓ dΔ dδ=) dδ=))


MorSymm : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
MorSymm {Δ = ◇} {◇} {◇} _ _ tt = tt
MorSymm {Δ = Δ , B} {δ , u} {δ' , u'} dΓ (dΔ , dB) (dδ , du) = {!!}
-- -- (MorSymm dΓ dΔ dδ , ConvEq (SubstTy dB (MorEqMor1 dΓ dΔ dδ)) (TmSymm du) (SubstTyMorEq dB (MorEqMor1 dΓ dΔ dδ) dδ))

MorTran : {Γ : Ctx n} {Δ : Ctx m} {δ δ' δ'' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ'' ∷> Δ → Γ ⊢ δ == δ'' ∷> Δ
MorTran {Δ = ◇} {◇} {◇} {◇} _ _ tt tt = tt
MorTran {Δ = Δ , B} {δ , u} {δ' , u'} {δ'' , u''} dΓ (dΔ , dB) (dδ , du) (dδ' , du') = {!!}
-- --  (MorTran dΓ dΔ dδ dδ' , TmTran (TmEqTm2 dΓ du) du (ConvEq (SubstTy dB (MorEqMor2 dΓ dΔ dδ)) du' (SubstTyMorEq dB (MorEqMor2 dΓ dΔ dδ) (MorSymm dΓ dΔ dδ))))


-- ConvTm2 : {Γ Δ : Ctx n} {u : TmExpr n} {A A' : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Γ ⊢ A == A') → Derivable (Δ ⊢ u :> A')
-- ConvTm2 du dΓ= dA= = {!!}
-- -- Conv (ConvTy (TyEqTy1 (CtxEqCtx1 dΓ=) dA=) dΓ=) (ConvTm du dΓ=) (ConvTyEq dA= dΓ=)

-- ConvTmEq2 : {Γ Δ : Ctx n} {u u' : TmExpr n} {A A' : TyExpr n} → Derivable (Γ ⊢ u == u' :> A) → (⊢ Γ == Δ) → Derivable (Γ ⊢ A == A') → Derivable (Δ ⊢ u == u' :> A')
-- ConvTmEq2 du= dΓ= dA= = {!!}
-- -- ConvTmEq (ConvEq (TyEqTy1 (CtxEqCtx1 dΓ=) dA=) du= dA=) dΓ=

-- ConvMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ ∷> Δ')
-- ConvMor {Δ = ◇} {Δ' = ◇} {δ = ◇} dδ dΓ= dΔ= = tt
-- ConvMor {Δ = Δ , B} {Δ' = Δ' , B'} {δ = δ , u} (dδ , du) dΓ= (dΔ= , dB , dB' ,  dB= , dB=') = {!!}
-- --  (ConvMor dδ dΓ= dΔ= , Conv (ConvTy (SubstTy dB dδ) dΓ=) (ConvTm du dΓ=) (SubstTyEq dB= (ConvMor dδ dΓ= (CtxRefl (CtxEqCtx1 dΔ=)))))

-- ConvMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ == δ' ∷> Δ')
-- ConvMorEq {Δ = ◇} {Δ' = ◇} {δ = ◇} {◇} dδ= dΓ= dΔ= = tt
-- ConvMorEq {Δ = Δ , B} {Δ' = Δ' , B'} {δ = δ , u} {δ' , u₁} (dδ= , du=) dΓ= (dΔ= , dB , dB' , dB= , dB=') = {!!}
-- --  (ConvMorEq dδ= dΓ= dΔ= , ConvTmEq (ConvEq (SubstTy dB (MorEqMor1 (CtxEqCtx1 dΓ=) (CtxEqCtx1 dΔ=) dδ=)) du= (SubstTyEq dB= (MorEqMor1 (CtxEqCtx1 dΓ=) (CtxEqCtx1 dΔ=) dδ=))) dΓ=)

-- SubstMorFullEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ θ' : Mor m k} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (⊢ Θ) → (Δ ⊢ θ == θ' ∷> Θ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ' [ δ' ]Mor ∷> Θ)
-- SubstMorFullEq {Θ = ◇} {◇} {◇} dΓ dΔ tt tt dδ= = tt
-- SubstMorFullEq {Θ = Θ , C} {θ , w} {θ' , w'} dΓ dΔ (dΘ , dC) (dθ= , dw=) dδ= = {!!}
-- --  (SubstMorFullEq dΓ dΔ dΘ dθ= dδ= , congTmEqTy ([]Ty-assoc _ _ _) (SubstTmFullEq (Conv (SubstTy dC (MorEqMor2 dΔ dΘ dθ=)) (TmEqTm2 dΔ (ConvEq (SubstTy dC (MorEqMor1 dΔ dΘ dθ=)) dw= (SubstTyMorEq dC (MorEqMor1 dΔ dΘ dθ=) dθ=))) (SubstTyMorEq dC (MorEqMor2 dΔ dΘ dθ=) (MorSymm dΔ dΘ dθ=))) (MorEqMor1 dΓ dΔ dδ=) dw= dδ=))


-- SubstTyMorEq2 : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m}
--               → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
-- SubstTyMorEq2 dΓ dΔ dA= dδ= =
--   let dδ = MorEqMor1 dΓ dΔ dδ=
--       dA' = TyEqTy2 dΔ dA=
--   in
--   SubstTyFullEq dA' dδ dA= dδ=


-- _,,_ : {Γ Γ' : Ctx n} {A A' : TyExpr n} → ⊢ Γ == Γ' → Derivable (Γ ⊢ A == A') → ⊢ (Γ , A) == (Γ' , A')
-- dΓ= ,, dA= =
--   let dΓ = CtxEqCtx1 dΓ=
--   in
--   (dΓ= , TyEqTy1 dΓ dA= , ConvTy (TyEqTy2 dΓ dA=) dΓ= , dA= , ConvTyEq dA= dΓ=)

-- TmTran' : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n} → ⊢ Γ
--         → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)
-- TmTran' dΓ du= dv= = TmTran (TmEqTm1 dΓ dv=) du= dv=

{- extract type from Derivability -}
TyofDerivation : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → TyExpr n
TyofDerivation {A = A} dj = A
{- If the Term is derivable, then also its Type is -}

Derivable-getTy : {n : ℕ} {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → ⊢ Γ → Derivable (Γ ⊢ getTy Γ u)
Derivable-getTy {Γ = Γ , A₁} {var last} {.(weakenTy' last A₁)} (VarLast dj) dΓ = WeakTy dj
Derivable-getTy {Γ = Γ , A₁} {var (prev x)} {.(weakenTy' last _)} (VarPrev dj dj₁) (dΓ , dA) = WeakTy (Derivable-getTy dj₁ dΓ)
Derivable-getTy {Γ = ◇} {lam A₁ B u} {.(pi A₁ B)} (Lam dj dj₁ dj₂) dΓ = Pi dj dj₁
Derivable-getTy {Γ = Γ , A} {lam A₁ B u} {.(pi A₁ B)} (Lam dj dj₁ dj₂) dΓ = Pi dj dj₁
Derivable-getTy {Γ = ◇} {app A₁ B u u₁} {.(B [ ◇ , u₁ ]Ty)} (App dj dj₁ dj₂ dj₃) dΓ = SubstTy dj₁ (tt , congTmTy! ([idMor]Ty A₁) dj₃)
Derivable-getTy {Γ = Γ , A} {app A₁ B u u₁} {.(B [ (weakenMor' last (idMor _) , var last) , u₁ ]Ty)} (App dj dj₁ dj₂ dj₃) dΓ = SubstTy dj₁ ((idMorDerivable dΓ) , congTmTy! ([idMor]Ty A₁) dj₃)
Derivable-getTy {Γ = ◇} {coerc A₁ B u} {.B} (Conv dj dj₁ dj₂ dj₃) dΓ = dj₁
Derivable-getTy {Γ = Γ , A} {coerc A₁ B u} {.B} (Conv dj dj₁ dj₂ dj₃) dΓ = dj₁

{- get Context from a judgment -}
getCtx : Judgment → ΣSS ℕ Ctx 
getCtx ( _⊢_ {n = n} Γ x) = (n , Γ)
getCtx (_⊢_:>_ {n = n} Γ x x₁) = n , Γ
getCtx (_⊢_==_ {n = n} Γ x x₁) = n , Γ
getCtx (_⊢_==_:>_ {n = n} Γ x x₁ x₂) = n , Γ
-- getCtx (_⊢_≃_ {n = n} Γ x x₁) = n , Γ

getTyExpr : Judgment → ΣSS ℕ TyExpr
getTyExpr (_⊢_ {n = n} Γ x) = n , x
getTyExpr (_⊢_:>_ {n = n} Γ x x₁) = n , x₁
getTyExpr (Γ ⊢ x == x₁) = _ , x
getTyExpr (Γ ⊢ x == x₁ :> x₂) = _ , x₂

{- if welltyped getTy u is equal to the typing of u -}
getTy=Ty : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → (dj : Derivable (Γ ⊢ u :> A)) → getTy Γ u ≡ TyofDerivation dj
getTy=Ty (VarLast dj) = refl
getTy=Ty (VarPrev {Γ = Γ} dj dj₁) rewrite getTy=Ty dj₁ = refl
getTy=Ty (Conv dj dj₁ dj₂ dj₃) = refl
getTy=Ty (Lam dj dj₁ dj₂) = refl
getTy=Ty (App dj dj₁ dj₂ dj₃) = refl


{-getTy commutes with welltyped substitutions -}
getTy-[]Ty : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} (u : TmExpr m) → Γ ⊢ δ ∷> Δ → (getTy Δ u) [ δ ]Ty ≡ getTy Γ (u [ δ ]Tm)
getTy-[]Ty (var last) (dδ , x₁) rewrite getTy=Ty x₁ = weakenTyInsert _ _ _
getTy-[]Ty (var (prev x)) (dδ , x₁) = weakenTyInsert _ _ _ ∙ getTy-[]Ty (var x) dδ
getTy-[]Ty (lam A B u) dδ = refl
getTy-[]Ty {δ = δ} (app A B u u₁) dδ = []Ty-assoc δ ( idMor _ , u₁ ) B ∙
                                     ap (λ z → B [ z , u₁ [ δ ]Tm ]Ty) (idMor[]Mor δ) ∙
                                     (! (ap (λ z → B [ z , (u₁ [ δ ]Tm)]Ty) (weakenMorInsert δ (idMor _) (u₁ [ δ ]Tm) ∙ [idMor]Mor δ ))) ∙ ! ([]Ty-assoc (idMor _ , (u₁ [ δ ]Tm)) (weakenMor δ , var last) B)
getTy-[]Ty (coerc S T u) dδ = refl

{- getTy preserves judgmental equality -}
getTyEq : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u == u' :> A) → ⊢ Γ → Derivable (Γ ⊢ getTy Γ u == getTy Γ u')
getTyEq (TmRefl du=) dΓ = TyRefl (Derivable-getTy du= dΓ)
getTyEq (TmSymm du=) dΓ = TySymm (getTyEq du= dΓ)
getTyEq (TmTran du= du=₁ du=₂) dΓ = TyTran (Derivable-getTy du= dΓ) (getTyEq du=₁ dΓ) (getTyEq du=₂ dΓ)
getTyEq (ConvEq du= du=₁ du=₂) dΓ = TyTran du= (TySymm du=₂) du=₂
getTyEq (CoercRefl du=) dΓ rewrite ! (getTy=Ty du=) = TyRefl (Derivable-getTy du= dΓ)
getTyEq (CoercRefl! du=) dΓ rewrite ! (getTy=Ty du=) =  TyRefl (Derivable-getTy du= dΓ)
getTyEq (CoercTrans du= du=₁ du=₂ du=₃ du=₄ du=₅ du=₆) dΓ = TyTran du=₁ (TySymm du=₅) du=₅
getTyEq (LamCong dA dA' dB dB' du du' dA= dB= du=) dΓ = TyRefl (Pi dA dB)
-- PiCong dA dA' dB dB' dA= dB=
getTyEq (AppCong {A = A} du= du=₁ du=₂ du=₃ du=₄ du=₅ du=₆ du=₇ du=₈ du=₉ du=₁₀ du=₁₁) dΓ = SubstTyEq (TyRefl du=₂) (idMorDerivable dΓ , congTmTy (! ([idMor]Ty A)) du=₆)
getTyEq (BetaPi {A = A} {u = u} du= du=₁ du=₂ du=₃) dΓ
                   rewrite ! (getTy=Ty du=₂)
                     = congTyEq refl
                                (getTy-[]Ty u (idMorDerivable dΓ , (congTmTy (! ([idMor]Ty A)) du=₃)))
                                (TyRefl (SubstTy (Derivable-getTy du=₂ (dΓ , du=)) (idMorDerivable dΓ , congTmTy (! ([idMor]Ty A)) du=₃)))
getTyEq (EtaPi du= du=₁ du=₂) dΓ
                   rewrite getTy=Ty du=₂
                     = TyRefl (Pi du= du=₁)

coercInvTm : {Γ : Ctx n} {A B : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ coerc A B u :> B) → Derivable (Γ ⊢ u :> A)
coercInvTm (Conv du du₁ du₂ du₃) = du₂

coercInvTy1 : {Γ : Ctx n} {A B : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ coerc A B u :> B) → Derivable (Γ ⊢ A)
coercInvTy1 (Conv du du₁ du₂ du₃) = du

coercInvTy2 : {Γ : Ctx n} {A B : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ coerc A B u :> B) → Derivable (Γ ⊢ B)
coercInvTy2 (Conv du du₁ du₂ du₃) = du₁

coercInvEq : {Γ : Ctx n} {A B : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ coerc A B u :> B) → Derivable (Γ ⊢ A == B)
coercInvEq (Conv du du₁ du₂ du₃) = du₃

{- coercTm and coercTy are derivable -}

CoercTy : {Γ : Ctx n} {A A' : TyExpr n} {B : TyExpr (suc n)} → ⊢ Γ → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A') ⊢ coercTy B A A')
CoercTm : {Γ : Ctx n} {A A' : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} → ⊢ Γ → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A') ⊢ coercTm u A A' :> coercTy B A A')

CoercTy {A = A} dΓ dA dA' dB dA= = SubstTy dB (WeakMor (idMorDerivable dΓ) , congTmTy (ap weakenTy (! ([idMor]Ty A)) ∙ (weaken[]Ty A (idMor _) last)) ((Conv (WeakTy dA') (WeakTy dA) (VarLast dA') (TySymm (WeakTyEq dA=)))))
CoercTm {A = A} dΓ dA dA' du dA= = SubstTm du (WeakMor (idMorDerivable dΓ) ,  congTmTy (ap weakenTy (! ([idMor]Ty A)) ∙ (weaken[]Ty A (idMor _) last)) (Conv (WeakTy dA') (WeakTy dA) (VarLast dA') (TySymm (WeakTyEq dA=))))

---------------------------
---------------- Meta Theorems
--------------------------
TmTy : {Γ : Ctx n} {A : TyExpr n} {u : TmExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A)
TmTy dΓ du = ?
