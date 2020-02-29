{-# OPTIONS --without-K --rewriting --prop --allow-unsolved-metas #-}
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

----------
--- ap lemma
----------
ap-jdg-Ty : {Γ Γ' : Ctx n} {A A' : TyExpr n} → Γ ≡ Γ' → A ≡ A' → Γ ⊢ A ≡ Γ ⊢ A'
ap-jdg-Ty refl refl = refl

ap-jdg-Tm : {Γ Γ' : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → Γ ≡ Γ' → A ≡ A' → u ≡ u' → Γ ⊢ u :> A ≡ Γ ⊢ u' :> A'
ap-jdg-Tm refl refl refl = refl

ap-jdg-TyEq : {Γ Γ' : Ctx n} {A A' B B' : TyExpr n} → Γ ≡ Γ' → A ≡ A' → B ≡ B' → Γ ⊢ A == B ≡ Γ ⊢ A' == B'
ap-jdg-TyEq refl refl refl = refl

ap-jdg-TmEq : {Γ Γ' : Ctx n} {A A' : TyExpr n} {u u' v v' : TmExpr n} → Γ ≡ Γ' → A ≡ A' → u ≡ u' → v ≡ v' → Γ ⊢ u == v :> A ≡ Γ ⊢ u == v' :> A'
ap-jdg-TmEq refl refl refl refl = refl
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
  CoercTrans : {Γ : Ctx n} {u : TmExpr n} {A B C : TyExpr n} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ C) → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ coerc B C (coerc A B u) == coerc A C u :> C)
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
  _,_ : {Γ Γ' : Ctx n} {A A' : TyExpr n} → (⊢ Γ == Γ') → Derivable (Γ ⊢ A == coercCtxTy Γ' Γ A') → ⊢ (Γ , A) == (Γ' , A')

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

congTyCtxEq : {Γ Γ' : Ctx n} {A A' B B' : TyExpr n} → Γ ≡ Γ' → A ≡ A' → B ≡ B' → Derivable (Γ ⊢ A == B) → Derivable (Γ' ⊢ A' == B')
congTyCtxEq refl refl refl dA= = dA=

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

congTmCtxEq : {Γ Γ' : Ctx n} {A A' : TyExpr n} {u u' v v' : TmExpr n} → Γ ≡ Γ' → u ≡ v → u' ≡ v' → A ≡ A' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ' ⊢ v == v' :> A')
congTmCtxEq refl refl refl refl du= = du=

congTmEq! : {Γ : Ctx n} {A A' : TyExpr n} {u u' v v' : TmExpr n} → v ≡ u → v' ≡ u' → A' ≡ A → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ v == v' :> A')
congTmEq! refl refl refl du= = du=

{- Reflexivity rules -}

congTyRefl : {Γ : Ctx n} {A A' : TyExpr n} → Derivable (Γ ⊢ A) → A ≡ A' → Derivable (Γ ⊢ A == A')
congTyRefl dA refl = TyRefl dA

congTyRefl' : {Γ : Ctx n} {A A' : TyExpr n} → Derivable (Γ ⊢ A') → A ≡ A' → Derivable (Γ ⊢ A == A')
congTyRefl' dA refl = TyRefl dA

congTmRefl : {Γ : Ctx n} {A : TyExpr n} {u u' : TmExpr n} → Derivable (Γ ⊢ u :> A) → u ≡ u' → Derivable (Γ ⊢ u == u' :> A)
congTmRefl du refl = TmRefl du


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
SubstTmEq {δ = δ} (CoercTrans dA dB dC du dA= dB=) dδ = CoercTrans (SubstTy dA dδ) (SubstTy dB dδ) (SubstTy dC dδ) (SubstTm du dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= dδ) 
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
WeakTmEq (CoercTrans dA dB dC du x x₁) = CoercTrans (WeakTy dA) (WeakTy dB) (WeakTy dC) (WeakTm du) (WeakTyEq x) (WeakTyEq x₁) 
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
                                    )
                                            (TmSymm (CoercTrans (SubstTy dA dδ') (SubstTy dB dδ') (SubstTy dB dδ) (SubstTm du dδ') (SubstTyEq dA= dδ') (SubstTyMorEq dB dδ' dδ dδ'= dδ=)
                                                    ) ))
SubstTmMorEq {δ = δ} {δ'} (Lam {A = A} {B = B} {u = u} dA dB du) dδ dδ' dδ= dδ'= = LamCong
                                              (SubstTy dA dδ)
                                              (SubstTy dA dδ')
                                              (SubstTy dB (WeakMor+ dA dδ))
                                              (SubstTy dB (WeakMor+ dA dδ'))
                                              (SubstTm du (WeakMor+ dA dδ))
                                              (SubstTm du (WeakMor+ dA dδ'))
                                              (SubstTyMorEq dA dδ dδ' dδ= dδ'= )
                                              ((congTyEq refl
                                                         MorRewrite
                                                         (SubstTyMorEq dB
                                                                       (WeakMor+ dA dδ)
                                                                       (WeakMor+coerc dA (SubstTy dA dδ) dδ' (SubstTyMorEq dA dδ dδ' dδ= dδ'=))
                                                                       (WeakMor+Eq dA dδ' dδ dδ'= dδ=)
                                                                       (WeakMor+Eq! dA dδ' dδ dδ'= dδ=))))
                                              (congTmEq refl
                                                        (ap-coerc-Tm MorRewrite
                                                                     refl
                                                                     (ap[]Tm {u = u}
                                                                             refl
                                                                             (Mor+= ((ap (weakenMor) (! ([idMor]Mor _)) ∙ weaken[]Mor _ _ _) ∙ ! (weakenMorInsert _ _ _))
                                                                                    refl) 
                                                                        ∙ ! ([]Tm-assoc _ _ u)))
                                                        refl
                                                        (SubstTmMorEq du (WeakMor+ dA dδ)
                                                                         (WeakMor+coerc dA (SubstTy dA dδ) dδ' (SubstTyMorEq dA dδ dδ' dδ= dδ'=))
                                                                         (WeakMor+Eq dA dδ' dδ dδ'= dδ=)
                                                                         (WeakMor+Eq! dA dδ' dδ dδ'= dδ=)) )
             where
             MorRewrite = (((!(ap (λ x → B [ weakenMor x , coerc (weakenTy (A [ δ ]Ty)) (weakenTy (A [ δ' ]Ty)) (var last) ]Ty) ([idMor]Mor δ'))
                        ∙ ap (λ x → B [ x , coerc (weakenTy (A [ δ ]Ty)) (weakenTy (A [ δ' ]Ty)) (var last) ]Ty) (weaken[]Mor δ' (idMor _) last))
                        ∙ ! (ap (λ x → B [ x , coerc (weakenTy (A [ δ ]Ty)) (weakenTy (A [ δ' ]Ty)) (var last) ]Ty) (weakenMorInsert δ' (weakenMor (idMor _)) _)))
                        ∙ ! ([]Ty-assoc (weakenMor (idMor _) , coerc (weakenTy (A [ δ ]Ty)) (weakenTy (A [ δ' ]Ty)) (var last)) (weakenMor δ' , var last) B))

-- LamCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) ({!!})) (SubstTmMorEq du (WeakMor+ dA dδ) ({!!}))
-- WeakMor+Eq dA dδ dδ=
SubstTmMorEq {δ = δ} {δ' = δ'} (App {A = A} {B = B} dA dB df da) dδ dδ' dδ= dδ'= = congTmEqTy! []Ty-substTy
          (congTmEq refl (ap-coerc-Tm (! []Ty-substTy) (! []Ty-substTy ) refl) refl
             (AppCong
                 (SubstTy dA dδ)
                 (SubstTy dA dδ')
                 (SubstTy dB (WeakMor+ dA dδ))
                 (SubstTy dB (WeakMor+ dA dδ'))
                 (SubstTm df dδ) (SubstTm df dδ')
                 (SubstTm da dδ) (SubstTm da dδ')
                 (SubstTyMorEq dA dδ dδ' dδ= dδ'=)
                 (congTyEq refl
                           (ap (λ x → B [ x , coerc (weakenTy (A [ δ ]Ty)) (weakenTy (A [ δ' ]Ty)) (var last) ]Ty) ( (ap (λ x → weakenMor x) (! ([idMor]Mor δ')) ∙ weaken[]Mor _ _ _) ∙ (! (weakenMorInsert _ _ _))) ∙ (! ([]Ty-assoc _ _ _)))
                           ((SubstTyMorEq dB
                                          (WeakMor+ dA dδ)
                                          (WeakMor+coerc dA (SubstTy dA dδ) dδ' (SubstTyMorEq dA dδ dδ' dδ= dδ'=))
                                          (WeakMorEq dδ= , congTmEq refl
                                                (ap-coerc-Tm (weaken[]Ty _ _ _) (weaken[]Ty _ _ _) refl) (weaken[]Ty _ _ _)
                                                (TmTran (Conv (WeakTy (SubstTy dA dδ)) (WeakTy (SubstTy dA dδ)) (VarLast (SubstTy dA dδ)) (TyRefl (WeakTy (SubstTy dA dδ)))) (CoercRefl! (VarLast (SubstTy dA dδ))) (TmSymm (CoercTrans (WeakTy (SubstTy dA dδ)) (WeakTy (SubstTy dA dδ')) (WeakTy (SubstTy dA dδ)) (VarLast (SubstTy dA dδ)) (WeakTyEq (SubstTyMorEq dA dδ dδ' dδ= dδ'=)) (WeakTyEq (SubstTyMorEq dA dδ' dδ dδ'= dδ=))))))
                                           (WeakMorEq dδ'= , congTmEq refl
                                                (ap-coerc-Tm (weaken[]Ty _ _ _) (weaken[]Ty _ _ _) refl) (weaken[]Ty _ _ _) (ConvEq (WeakTy (SubstTy dA dδ)) (TmRefl (VarLast (SubstTy dA dδ))) (WeakTyEq (SubstTyMorEq dA dδ dδ' dδ= dδ'=))))
                    )))
                 (SubstTmMorEq df dδ dδ' dδ= dδ'=)
                 (SubstTmMorEq da dδ dδ' dδ= dδ'=)))

----------------------------------------
------------- WeakMor+ equality results
----------------------------------------
WeakMor+Eq {A = A} {δ = δ} {δ' = δ'} dA dδ dδ' dδ= dδ'=
              = WeakMorEq dδ'= , congTmEq
                                refl
                                ( ap-coerc-Tm ( weaken[]Ty A δ last) (weaken[]Ty A δ' last) refl) (weaken[]Ty A δ' last)
                                (TmSymm (TmTran (Conv (WeakTy (SubstTy dA dδ')) (WeakTy (SubstTy dA dδ')) (VarLast (SubstTy dA dδ')) (TyRefl (WeakTy (SubstTy dA dδ'))))
                                        (CoercTrans (WeakTy (SubstTy dA dδ')) (WeakTy (SubstTy dA dδ)) (WeakTy (SubstTy dA dδ')) (VarLast (SubstTy dA dδ')) (WeakTyEq (SubstTyMorEq dA dδ' dδ dδ'= dδ=)) (WeakTyEq (SubstTyMorEq dA dδ dδ' dδ= dδ'=)) )
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

-- SubstTyFullEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A') → (Γ ⊢ δ ∷> Δ)
--        → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
-- SubstTyFullEq dA' dδ dA= dδ= = TyTran (SubstTy dA' dδ) (SubstTyEq dA= dδ) {!!}
-- -- (SubstTyMorEq dA' dδ dδ=)
-- 
-- SubstTmFullEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} →  Derivable (Δ ⊢ u' :> A) → (Γ ⊢ δ ∷> Δ) 
--        → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == coerc ( A [ δ' ]Ty) (A [ δ ]Ty) (u' [ δ' ]Tm) :> A [ δ ]Ty)
-- SubstTmFullEq du' dδ du= dδ= = TmTran (SubstTm du' dδ) (SubstTmEq du= dδ) {!!}
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
getTyEq (CoercTrans du= du=₁ du=₂ du=₃ du=₄ du=₅ ) dΓ = TyTran du=₁ (TySymm du=₅) du=₅
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

--------------------------------
--------------- Weakening is injective and ap-Ty & ap-Tm  inverse
-------------------------------
elEq-charac : {u v : TmExpr n} → el v ≡ el u → v ≡ u
elEq-charac {u = u} refl = refl

piEq-pr1 : {A A' : TyExpr n} {B B' : TyExpr (suc n)} → (_≡_ {A = TyExpr n} (pi A B) (pi A' B')) → A ≡ A'
piEq-pr1 refl = refl

piEq-pr2 : {A A' : TyExpr n} {B B' : TyExpr (suc n)} → (_≡_ {A = TyExpr n} (pi A B) (pi A' B')) → B ≡ B'
piEq-pr2 refl = refl

varEq-charac : {x y : Fin n} → _≡_ {A = TmExpr n} (var x) (var y) → x ≡ y
varEq-charac refl = refl

lamEq-pr1 : {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)} → _≡_ {A = TmExpr n} (lam A B u) (lam A' B' u') → A ≡ A'
lamEq-pr1 refl = refl
lamEq-pr2 : {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)} → _≡_ {A = TmExpr n} (lam A B u) (lam A' B' u') → B ≡ B'
lamEq-pr2 refl = refl
lamEq-pr3 : {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)} → _≡_ {A = TmExpr n} (lam A B u) (lam A' B' u') → u ≡ u'
lamEq-pr3 refl = refl

appEq-pr1 : {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u v u' v' : TmExpr n} → app A B u v ≡ app A' B' u' v' → A ≡ A'
appEq-pr1 refl = refl
appEq-pr2 : {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u v u' v' : TmExpr n} → app A B u v ≡ app A' B' u' v' → B ≡ B'
appEq-pr2 refl = refl
appEq-pr3 : {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u v u' v' : TmExpr n} → app A B u v ≡ app A' B' u' v' → u ≡ u'
appEq-pr3 refl = refl
appEq-pr4 : {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u v u' v' : TmExpr n} → app A B u v ≡ app A' B' u' v' → v ≡ v'
appEq-pr4 refl = refl

prevInj : {x y : Fin n} → prev x ≡ prev y → x ≡ y
prevInj refl = refl

weakVarInj : {x y : Fin n} {k : Fin (suc n)} → weakenVar' k x ≡ weakenVar' k y → x ≡ y
weakVarInj {x = x} {.x} {last} refl = refl
weakVarInj {x = last} {last} {prev k} eq = refl
weakVarInj {x = prev x} {prev y} {prev k} eq = ap prev (weakVarInj (prevInj eq))

weakTyInj : {n : ℕ} {A B : TyExpr n} {k : Fin (suc n)} → weakenTy' k A ≡ weakenTy' k B → A ≡ B
weakTmInj : {n : ℕ} {u v : TmExpr n} {k : Fin (suc n)} → weakenTm' k u ≡ weakenTm' k v → u ≡ v

weakTyInj {A = uu} {uu} refl = refl
weakTyInj {A = el v} {el v₁} A= = ap-el-Ty (weakTmInj (elEq-charac A=))
weakTyInj {A = pi A A₁} {pi B B₁} {k} A= = ap-pi-Ty (weakTyInj (piEq-pr1 A=)) (weakTyInj (piEq-pr2 A=))

weakTmInj {u = var x} {var y} {k} eq = ap-var-Tm (weakVarInj (varEq-charac eq))
weakTmInj {u = lam A B u} {lam A₁ B₁ v} wu= = ap-lam-Tm (weakTyInj (lamEq-pr1 wu=)) (weakTyInj (lamEq-pr2 wu=)) (weakTmInj (lamEq-pr3 wu=))
weakTmInj {u = app A B u u₁} {app A₁ B₁ v v₁} wu= = ap-app-Tm (weakTyInj (appEq-pr1 wu=)) ( weakTyInj (appEq-pr2 wu=)) ( weakTmInj (appEq-pr3 wu=)) ( weakTmInj (appEq-pr4 wu=))
weakTmInj {u = coerc S T u} {coerc S₁ T₁ v} wu= = {!!} 

-----------------------------
-------------------- Inversion Lemmas
-----------------------------

VarPrevInvTm : {Γ : Ctx n} {B : TyExpr n} {k : Fin n} {A : TyExpr n}
               → Derivable ((Γ , B) ⊢ var (prev k) :> weakenTy A) 
               → Derivable (Γ ⊢ var k :> A)
VarPrevInvTm {A = A} dpk = helper refl dpk
             where
             helper : {Γ : Ctx n} {B : TyExpr n} {k : Fin n} {A : TyExpr n} {C : TyExpr (suc n)}
               → weakenTy A ≡ C
               → Derivable ((Γ , B) ⊢ var (prev k) :> C) 
               → Derivable (Γ ⊢ var k :> A)
             helper {A = A} C= (VarPrev dpk dpk₁) rewrite weakTyInj C= = dpk₁

coercInvTm : {Γ : Ctx n} {A B B' : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ coerc A B u :> B') → Derivable (Γ ⊢ u :> A)
coercInvTm (Conv du du₁ du₂ du₃) = du₂

coercInvTy1 : {Γ : Ctx n} {A B B' : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ coerc A B u :> B') → Derivable (Γ ⊢ A)
coercInvTy1 (Conv du du₁ du₂ du₃) = du

coercInvTy2 : {Γ : Ctx n} {A B B' : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ coerc A B u :> B') → Derivable (Γ ⊢ B)
coercInvTy2 (Conv du du₁ du₂ du₃) = du₁

coercInvEq : {Γ : Ctx n} {A B B' : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ coerc A B u :> B') → Derivable (Γ ⊢ A == B)
coercInvEq (Conv du du₁ du₂ du₃) = du₃

---------------------------
---------------- Meta Theorems
--------------------------
TmTy : {Γ : Ctx n} {A : TyExpr n} {u : TmExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A)
TmTy dΓ (VarLast du) = WeakTy du
TmTy dΓ (VarPrev du du₁) = WeakTy du
TmTy dΓ (Conv du du₁ du₂ du₃) = du₁
TmTy dΓ (Lam du du₁ du₂) = Pi du du₁
TmTy dΓ (App du du₁ du₂ du₃) = SubstTy du₁ (idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du₃)

TyEqTy1 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A)

TyEqTy2 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B)

TmEqTm1 : {Γ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ u :> A)

TmEqTm2 : {Γ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v :> A)

TyEqTy1 dΓ (TyRefl dA=) = dA=
TyEqTy1 dΓ (TySymm dA=) = TyEqTy2 dΓ dA=
TyEqTy1 dΓ (TyTran dA= dA=₁ dA=₂) = {!!}
TyEqTy1 dΓ UUCong = {!!}
TyEqTy1 dΓ (ElCong dA=) = {!!}
TyEqTy1 dΓ (PiCong dA= dA=₁ dA=₂ dA=₃ dA=₄ dA=₅) = Pi dA= dA=₂

TyEqTy2 dΓ (TyRefl dA=) = dA=
TyEqTy2 dΓ (TySymm dA=) = TyEqTy1 dΓ dA=
TyEqTy2 dΓ (TyTran dA= dA=₁ dA=₂) = {!!}
TyEqTy2 dΓ UUCong = {!!}
TyEqTy2 dΓ (ElCong dA=) = {!!}
TyEqTy2 dΓ (PiCong dA= dA=₁ dA=₂ dA=₃ dA=₄ dA=₅) = {!!}

TmEqTm1 dΓ (TmRefl du=) = du=
TmEqTm1 dΓ (TmSymm du=) = TmEqTm2 dΓ du=
TmEqTm1 dΓ (TmTran du= du=₁ du=₂) = {!!}
TmEqTm1 dΓ (ConvEq du= du=₁ du=₂) = Conv du= (TyEqTy2 dΓ du=₂) (TmEqTm1 dΓ du=₁) du=₂
TmEqTm1 dΓ (CoercRefl du=) = Conv (TmTy dΓ du=) (TmTy dΓ du=) du= (TyRefl (TmTy dΓ du=))
TmEqTm1 dΓ (CoercRefl! du=) = du=
TmEqTm1 dΓ (CoercTrans du= du=₁ du=₂ du=₃ du=₄ du=₅) = Conv (TyEqTy1 dΓ du=₅) (TyEqTy2 dΓ du=₅) (Conv (TyEqTy1 dΓ du=₄) (TyEqTy2 dΓ du=₄) du=₃ du=₄) du=₅
TmEqTm1 dΓ (LamCong du= du=₁ du=₂ du=₃ du=₄ du=₅ du=₆ du=₇ du=₈) = Lam du= (TyEqTy1 (dΓ , TyEqTy1 dΓ du=₆) du=₇) (TmEqTm1 (dΓ , TyEqTy1 dΓ du=₆) du=₈)
TmEqTm1 dΓ (AppCong du= du=₁ du=₂ du=₃ du=₄ du=₅ du=₆ du=₇ du=₈ du=₉ du=₁₀ du=₁₁) = {!!}
TmEqTm1 dΓ (BetaPi du= du=₁ du=₂ du=₃) = App du= du=₁ (Lam du= du=₁ du=₂) du=₃
TmEqTm1 dΓ (EtaPi du= du=₁ du=₂) = du=₂

TmEqTm2 dΓ (TmRefl du=) = du=
TmEqTm2 dΓ (TmSymm du=) = TmEqTm1 dΓ du=
TmEqTm2 dΓ (TmTran du= du=₁ du=₂) = TmEqTm2 dΓ du=₂
TmEqTm2 dΓ (ConvEq du= du=₁ du=₂) = Conv du= (TyEqTy2 dΓ du=₂) (TmEqTm2 dΓ du=₁) du=₂ 
TmEqTm2 dΓ (CoercRefl du=) = {!!}
TmEqTm2 dΓ (CoercRefl! du=) = {!!}
TmEqTm2 dΓ (CoercTrans du= du=₁ du=₂ du=₃ du=₄ du=₅) = {!!}
TmEqTm2 dΓ (LamCong dA dA' dB dB' du du' dA= dB= du=) = Conv (Pi dA' dB')
                                                             (Pi dA dB)
                                                             (Lam dA' dB' du')
                                                             (PiCong dA' dA dB' dB (TySymm dA=) {!!})
TmEqTm2 dΓ (AppCong dA dA' dB dB' df df' da da' dA= dB= df= da=) = Conv {!!}
                                                                        {!!}
                                                                        {!!}
                                                                        {!!}
TmEqTm2 dΓ (BetaPi du= du=₁ du=₂ du=₃) = {!!}
TmEqTm2 dΓ (EtaPi du= du=₁ du=₂) = {!!}

{- coercTm and coercTy are derivable -}

CoercTy : {Γ : Ctx n} {A A' : TyExpr n} {B : TyExpr (suc n)} → ⊢ Γ → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A') ⊢ coercTy B A A')
CoercTm : {Γ : Ctx n} {A A' : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} → ⊢ Γ → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A') → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A') ⊢ coercTm u A A' :> coercTy B A A')

CoercTyEq : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} → ⊢ Γ → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable ((Γ , A') ⊢ coercTy B A A' == coercTy B' A A')
CoercTyEq dΓ dA= dB= = SubstTyEq dB= (WeakMor (idMorDerivable dΓ) , congTmTy (ap weakenTy (! ([idMor]Ty _)) ∙ (weaken[]Ty _ _ _)) (Conv (WeakTy (TyEqTy2 dΓ dA=)) (WeakTy (TyEqTy1 dΓ dA=)) (VarLast (TyEqTy2 dΓ dA=)) (WeakTyEq (TySymm dA=))))

CoercTy {A = A} dΓ dA dA' dB dA= = SubstTy dB (WeakMor (idMorDerivable dΓ) , congTmTy (ap weakenTy (! ([idMor]Ty A)) ∙ (weaken[]Ty A (idMor _) last)) ((Conv (WeakTy dA') (WeakTy dA) (VarLast dA') (TySymm (WeakTyEq dA=)))))
CoercTm {A = A} dΓ dA dA' du dA= = SubstTm du (WeakMor (idMorDerivable dΓ) ,  congTmTy (ap weakenTy (! ([idMor]Ty A)) ∙ (weaken[]Ty A (idMor _) last)) (Conv (WeakTy dA') (WeakTy dA) (VarLast dA') (TySymm (WeakTyEq dA=))))

-----------------------
-------------- coercion Equality lemmas
-----------------------
coercSymm : {Γ : Ctx n} {A B : TyExpr n} {u v : TmExpr n}
          → ⊢ Γ
          → Derivable (Γ ⊢ coerc A B u == v :> B)
          → Derivable (Γ ⊢ u == coerc B A v :> A)
coercSymm dΓ du= = TmTran (Conv dB dA (Conv dA dB du dA=) (TySymm dA=))
                          (TmTran (Conv dA dA du (TyRefl dA))
                                  (CoercRefl! du)
                                  (TmSymm (CoercTrans dA dB dA du dA= (TySymm dA=))))
                          (ConvEq dB du= (TySymm dA=))
              where
              dA = coercInvTy1 (TmEqTm1 dΓ du=)
              dB = coercInvTy2 (TmEqTm1 dΓ du=)
              du = coercInvTm (TmEqTm1 dΓ du=)
              dA= = coercInvEq (TmEqTm1 dΓ du=)
              dv = TmEqTm2 dΓ du=

coercTySymm : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)}
           → ⊢ Γ
           → Derivable (Γ ⊢ A == A')
           → Derivable ((Γ , A') ⊢ B')
           → Derivable ((Γ , A) ⊢ B == coercTy B' A' A)
           → Derivable ((Γ , A') ⊢ coercTy B A A' == B')
coercTySymm dΓ dA= dB' dB= = TyTran {!!} (CoercTyEq dΓ dA= dB=)
                                (congTyEq (ap[]Ty refl (Mor+= ((ap weakenMor (! ([idMor]Mor _)) ∙ weaken[]Mor _ _ _) ∙ ! (weakenMorInsert _ _ _))
                                                              (ap-coerc-Tm (ap weakenTy (! ([idMor]Ty _)) ∙ weaken[]Ty _ _ _ ∙ ! (weakenTyInsert _ _ _))
                                                                           (ap weakenTy (! ([idMor]Ty _)) ∙ weaken[]Ty _ _ _ ∙ ! (weakenTyInsert _ _ _))
                                                                           refl))
                                                ∙ ! ([]Ty-assoc _ _ _))
                                           ([idMor]Ty _)
                                           (SubstTyMorEq dB' {!!} {!!} {!!} {!!})) 
---------------
---------- Meta Properties for Morphisms
---------------
MorEqMor1 : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ ∷> Δ
MorEqMor2 : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' ∷> Δ

MorEqMor1 dΓ dΔ tt = tt
MorEqMor1 dΓ (dΔ , dA) (dδ= , x) = MorEqMor1 dΓ dΔ dδ= , TmEqTm1 dΓ x
MorEqMor2 dΓ dΔ tt = tt
MorEqMor2 dΓ (dΔ , dA) (dδ= , du) = MorEqMor2 dΓ dΔ dδ= , coercInvTm (TmEqTm2 dΓ du)

MorSymm : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
MorSymm {Δ = ◇} {◇} {◇} _ _ tt = tt
MorSymm {Δ = Δ , B} {δ , u} {δ' , u'} dΓ (dΔ , dB) (dδ , du) =
                 MorSymm dΓ dΔ dδ , TmTran (Conv (coercInvTy2 rightEq) (coercInvTy1 rightEq) rightEq (TySymm (coercInvEq rightEq)))
                                           (TmSymm (TmTran (Conv (coercInvTy1 (TmEqTm2 dΓ du)) (coercInvTy1 (TmEqTm2 dΓ du)) (coercInvTm (TmEqTm2 dΓ du)) (TyRefl (coercInvTy1 (TmEqTm2 dΓ du)))) (CoercTrans (coercInvTy1 (TmEqTm2 dΓ du)) (coercInvTy2 (TmEqTm2 dΓ du)) (coercInvTy1 (TmEqTm2 dΓ du)) (coercInvTm (TmEqTm2 dΓ du)) (coercInvEq (TmEqTm2 dΓ du)) (TySymm (coercInvEq (TmEqTm2 dΓ du)))) (CoercRefl (coercInvTm (TmEqTm2 dΓ du)))))
                                           (ConvEq (coercInvTy2 (TmEqTm2 dΓ du)) (TmSymm du) (TySymm (coercInvEq (TmEqTm2 dΓ du))))
                                           where
                                           rightEq = TmEqTm2 dΓ du
-- -- (MorSymm dΓ dΔ dδ , ConvEq (SubstTy dB (MorEqMor1 dΓ dΔ dδ)) (TmSymm du) (SubstTyMorEq dB (MorEqMor1 dΓ dΔ dδ) dδ))

MorTran : {Γ : Ctx n} {Δ : Ctx m} {δ δ' δ'' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ ∷> Δ → Γ ⊢ δ' ∷> Δ → Γ ⊢ δ'' ∷> Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ'' ∷> Δ → Γ ⊢ δ == δ'' ∷> Δ
MorTran {Δ = ◇} {◇} {◇} {◇} _ _ tt tt tt tt tt = tt
MorTran {Δ = Δ , B} {δ , u} {δ' , u'} {δ'' , u''} dΓ (dΔ , dB) (dδ , du) (dδ' , du') (dδ'' , du'') (dδ= , du=) (dδ'= , du'=)
                       = MorTran dΓ dΔ dδ dδ' dδ'' dδ= dδ'= , TmTran (Conv (SubstTy dB dδ')
                                                                           (SubstTy dB dδ)
                                                                           du'
                                                                           (SubstTyMorEq dB dδ' dδ (MorSymm dΓ dΔ dδ=) dδ=))
                                                            du=
                                                            (TmTran (Conv (SubstTy dB dδ')
                                                                          (SubstTy dB dδ)
                                                                          (Conv (SubstTy dB dδ'')
                                                                                (SubstTy dB dδ')
                                                                                du''
                                                                                (SubstTyMorEq dB dδ'' dδ' (MorSymm dΓ dΔ dδ'=) dδ'=))
                                                                          (SubstTyMorEq dB dδ' dδ (MorSymm dΓ dΔ dδ=) dδ=))
                                                                    (ConvEq (SubstTy dB dδ')
                                                                            du'=
                                                                            (SubstTyMorEq dB dδ' dδ (MorSymm dΓ dΔ dδ=) dδ=))
                                                                    (CoercTrans (SubstTy dB dδ'')
                                                                                (SubstTy dB dδ')
                                                                                (SubstTy dB dδ)
                                                                                du''
                                                                                (SubstTyMorEq dB
                                                                                              dδ''
                                                                                              dδ'
                                                                                              (MorSymm dΓ dΔ dδ'=)
                                                                                              dδ'=)
                                                                                (SubstTyMorEq dB dδ' dδ (MorSymm dΓ dΔ dδ=) dδ=)))
-- --  (MorTran dΓ dΔ dδ dδ' , TmTran (TmEqTm2 dΓ du) du (ConvEq (SubstTy dB (MorEqMor2 dΓ dΔ dδ)) du' (SubstTyMorEq dB (MorEqMor2 dΓ dΔ dδ) (MorSymm dΓ dΔ dδ))))

---------------
---- SubstTyMorEq1 resp for terms
-----------------
SubstTyMorEq1 : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} 
       → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ A) → (Γ ⊢ δ == δ' ∷> Δ)
       → Derivable (Γ ⊢ A [ δ ]Ty == A [ δ' ]Ty)
SubstTmMorEq1 : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ u :> A) → (Γ ⊢ δ == δ' ∷> Δ)
       → Derivable (Γ ⊢ u [ δ ]Tm == coerc (A [ δ' ]Ty) (A [ δ ]Ty) (u [ δ' ]Tm) :> A [ δ ]Ty)

SubstTyMorEq1 dΓ dΔ dA dδ= = SubstTyMorEq dA (MorEqMor1 dΓ dΔ dδ=) (MorEqMor2 dΓ dΔ dδ=) dδ= (MorSymm dΓ dΔ dδ=)
SubstTmMorEq1 dΓ dΔ du dδ= = SubstTmMorEq du (MorEqMor1 dΓ dΔ dδ=) (MorEqMor2 dΓ dΔ dδ=) dδ= (MorSymm dΓ dΔ dδ=)

SubstTyFullEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m}
       → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ)
       → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
SubstTyFullEq dΓ dΔ dA= dδ= = TyTran (SubstTy (TyEqTy1 dΔ dA=) (MorEqMor2 dΓ dΔ dδ=))
                                     (SubstTyMorEq1 dΓ dΔ (TyEqTy1 dΔ dA=) dδ=)
                                     (SubstTyEq dA= (MorEqMor2 dΓ dΔ dδ=))

SubstTmFullEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m}
                → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ == δ' ∷> Δ)
       → Derivable (Γ ⊢ u [ δ ]Tm == coerc (A [ δ' ]Ty) (A [ δ ]Ty) (u' [ δ' ]Tm) :> A [ δ ]Ty)
SubstTmFullEq dΓ dΔ du= dδ= = TmTran (SubstTm (TmEqTm2 dΔ du=) (MorEqMor1 dΓ dΔ dδ=)) (SubstTmEq du= (MorEqMor1 dΓ dΔ dδ=))
                                     (SubstTmMorEq1 dΓ dΔ (TmEqTm2 dΔ du=) dδ=)

SubstTyFullEqExt : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {B B' : TyExpr (suc m)} {a a' : TmExpr n} {δ δ' : Mor n m}
       → ⊢ Γ → ⊢ Δ
       → Derivable (Δ ⊢ A == A')
       → Derivable ((Δ , A') ⊢ B')
       → Derivable ((Δ , A) ⊢ B == coercTy B' A' A)
       → (Γ ⊢ δ == δ' ∷> Δ)
       → Derivable (Γ ⊢ a == coerc (A' [ δ' ]Ty) (A [ δ ]Ty) a' :> A [ δ ]Ty)
       → Derivable (Γ ⊢ B [ δ , a ]Ty == B' [ δ' , a' ]Ty)
SubstTyFullEqExt dΓ dΔ dA= dB' dB= dδ= da= = TyTran (SubstTy (CoercTy dΔ dA' dA dB' (TySymm dA=))
                                                    (dδ , da))
                                                    (SubstTyEq dB= (dδ , da))
                                                    (congTyEq (ap[]Ty refl (Mor+= (! (weakenMorInsert _ _ _))
                                                                              (ap-coerc-Tm (! (weakenTyInsert _ _ _)) (! (weakenTyInsert _ _ _)) refl))
                                                          ∙ ! ([]Ty-assoc _ _ _))
                                                          refl
                                                          (SubstTyMorEq1 dΓ (dΔ , TyEqTy2 dΔ dA=) dB' (congMorEq refl refl (! (idMor[]Mor _)) refl dδ=
                                                                                                      , congTmEq refl (ap-coerc-Tm refl (ap[]Ty refl (! (idMor[]Mor _))) refl)
                                                                                                                      (ap[]Ty refl (! (idMor[]Mor _)))
                                                                                                      (TmTran (Conv (SubstTy dA dδ) (SubstTy dA' dδ)
                                                                                                                    (Conv (SubstTy dA' dδ') (SubstTy dA dδ) (coercInvTm da')
                                                                                                                          (TySymm (SubstTyFullEq dΓ dΔ dA= dδ=)))
                                                                                                                    (SubstTyEq dA= dδ))
                                                                                                              (ConvEq (SubstTy dA dδ) da= (SubstTyEq dA= (MorEqMor1 dΓ dΔ dδ=)))
                                                                                                              (CoercTrans (SubstTy dA' dδ') (SubstTy dA dδ)
                                                                                                                          (SubstTy dA' dδ)
                                                                                                                          (coercInvTm da')
                                                                                                                          (TySymm (SubstTyFullEq dΓ dΔ dA= dδ=))
                                                                                                                          (SubstTyEq dA= dδ))))))
                                          where
                                          dδ = MorEqMor1 dΓ dΔ dδ=
                                          dδ' = MorEqMor2 dΓ dΔ dδ=
                                          dA = TyEqTy1 dΔ dA=
                                          dA' = TyEqTy2 dΔ dA=
                                          da = TmEqTm1 dΓ da=
                                          da' = TmEqTm2 dΓ da=
{- Derivability of Context Conversion identity Morphism -}
{- Some definitions are repetitive (e.g. Conv-idMor-Derivable could also be defined with ConvMor-Derivable and CtxRefl). -}
ConvMor-Derivable : {Γ Γ' : Ctx n} → ⊢ Γ → ⊢ Γ' → ⊢ Γ == Γ' → Γ ⊢ ConvMor Γ Γ' ∷> Γ'

ConvMor-Derivable {Γ = ◇} {◇} dΓ dΓ' dΓ= = tt
ConvMor-Derivable {Γ = Γ , A} {Γ' , A₁} (dΓ , dA) (dΓ' , dA') (dΓ= , dA=) = WeakMor (ConvMor-Derivable dΓ dΓ' dΓ=) , Conv (WeakTy dA)
                                                                                                                          (SubstTy dA' (WeakMor (ConvMor-Derivable dΓ dΓ' dΓ=)))
                                                                                                                          (VarLast dA)
                                                                                                                          (congTyEq refl (weaken[]Ty _ _ _) (WeakTyEq dA=))

ConvMor-id : {Γ : Ctx n} → ⊢ Γ → Γ ⊢ ConvMor Γ Γ == idMor n ∷> Γ

Conv-idMor-Derivable : {Γ : Ctx n} → ⊢ Γ → Γ ⊢ ConvMor Γ Γ ∷> Γ

Conv-idMor-Derivable tt = tt
Conv-idMor-Derivable (dΓ , x) = WeakMor (Conv-idMor-Derivable dΓ) , Conv (WeakTy x)
                                                                 (SubstTy x (WeakMor (Conv-idMor-Derivable dΓ)))
                                                                 (VarLast x)
                                                                 (congTyEq (ap (weakenTy) ([idMor]Ty _))
                                                                           (weaken[]Ty _ _ _)
                                                                           (WeakTyEq (SubstTyMorEq1 dΓ dΓ x (MorSymm dΓ dΓ (ConvMor-id dΓ)))))

ConvMor-id tt = tt
ConvMor-id (dΓ , x) = WeakMorEq (ConvMor-id dΓ) , congTmEq refl
                                                         (ap-coerc-Tm (ap (weakenTy) (! ([idMor]Ty _))  ∙ weaken[]Ty _ _ _)
                                                                      refl
                                                                      refl)
                                                         refl
                                                         (TmRefl ((Conv (WeakTy x)
                                                                        (SubstTy x (WeakMor (Conv-idMor-Derivable dΓ)))
                                                                        (VarLast x)
                                                                        (congTyEq (ap weakenTy ([idMor]Ty _))
                                                                                  (weaken[]Ty _ _ _)
                                                                                  (WeakTyEq (SubstTyMorEq1 dΓ
                                                                                                           dΓ
                                                                                                           x
                                                                                                           (MorSymm dΓ dΓ (ConvMor-id dΓ))))))))




ConvMor-id! : {Γ : Ctx n} → ⊢ Γ → Γ ⊢ idMor n == ConvMor Γ Γ ∷> Γ
ConvMor-id! dΓ = MorSymm dΓ dΓ (ConvMor-id dΓ)

ConvMorReflTy : {Γ : Ctx n} {A : TyExpr n} → ⊢ Γ → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == coercCtxTy Γ Γ A)
ConvMorReflTy dΓ dA = congTyEq ([idMor]Ty _) refl (SubstTyMorEq1 dΓ dΓ dA (ConvMor-id! dΓ))

-- {- admissable rules related to contexts. Simultaneous induction with ConvMor-Trans and ConvMorTranTy to avoid too many assumptions -}

ConvMor-Trans : {Γ1 Γ2 Γ3 : Ctx n} → ⊢ Γ1 → ⊢ Γ2 → ⊢ Γ3
                                   → ⊢ Γ1 == Γ2
                                   → ⊢ Γ2 == Γ3
                                   → Γ1 ⊢ ConvMor Γ2 Γ3 [ ConvMor Γ1 Γ2 ]Mor == ConvMor Γ1 Γ3 ∷> Γ3

ConvMorTranTy : {Γ1 Γ2 Γ3 : Ctx n} {A : TyExpr n} → ⊢ Γ1 → ⊢ Γ2 → ⊢ Γ3 → ⊢ Γ1 == Γ2 → ⊢ Γ2 == Γ3 → Derivable (Γ1 ⊢ A)
                    → Derivable (Γ3 ⊢ coercCtxTy Γ1 Γ3 A == coercCtxTy Γ2 Γ3 (coercCtxTy Γ1 Γ2 A))

CtxRefl : {Γ : Ctx n} → ⊢ Γ → ⊢ Γ == Γ
CtxRefl {Γ = ◇} tt = tt
CtxRefl {Γ = Γ , A} (dΓ , dA) = (CtxRefl dΓ , ConvMorReflTy dΓ dA)

CtxSymm : {Γ Δ : Ctx n} → ⊢ Γ → ⊢ Δ → ⊢ Γ == Δ → ⊢ Δ == Γ
CtxSymm {Γ = ◇} {Δ = ◇} tt tt tt = tt
CtxSymm {Γ = Γ , A} {Δ , A'} (dΓ , dA) (dΔ , dA') (dΓ= , dA=) = CtxSymm dΓ dΔ dΓ= , TyTran (SubstTy (SubstTy dA' (ConvMor-Derivable dΓ dΔ dΓ=))
                                                                                                    (ConvMor-Derivable dΔ dΓ (CtxSymm dΓ dΔ dΓ=)))
                                                                                           (TyTran (SubstTy dA' (Conv-idMor-Derivable dΔ))
                                                                                                   (ConvMorReflTy dΔ dA')
                                                                                                   (ConvMorTranTy dΔ dΓ dΔ (CtxSymm dΓ dΔ dΓ=) dΓ= dA'))
                                                                                           (SubstTyEq (TySymm dA=) (ConvMor-Derivable dΔ dΓ (CtxSymm dΓ dΔ dΓ=)))

CtxTran : {Γ1 Γ2 Γ3 : Ctx n} → ⊢ Γ1 → ⊢ Γ2 → ⊢ Γ3 → ⊢ Γ1 == Γ2 → ⊢ Γ2 == Γ3 → ⊢ Γ1 == Γ3
CtxTran tt tt tt tt tt = tt
CtxTran {Γ1 = (Γ1 , A1)} {(Γ2 , A2)} {(Γ3 , A3)} (dΓ1 , dA1) (dΓ2 , dA2) (dΓ3 , dA3) (dΓ1= , A1=) (dΓ2= , A2=)
                    = CtxTran dΓ1 dΓ2 dΓ3 dΓ1= dΓ2= , TyTran (SubstTy (SubstTy dA3 (ConvMor-Derivable dΓ2 dΓ3 dΓ2=)) (ConvMor-Derivable dΓ1 dΓ2 dΓ1=))
                                                             (TyTran (SubstTy dA2 (ConvMor-Derivable dΓ1 dΓ2 dΓ1=)) A1= (SubstTyEq A2= (ConvMor-Derivable dΓ1 dΓ2 dΓ1=) ))
                                                             (TySymm (ConvMorTranTy dΓ3 dΓ2 dΓ1 (CtxSymm dΓ2 dΓ3 dΓ2=) (CtxSymm dΓ1 dΓ2 dΓ1=) dA3))

ConvMor-Trans {Γ1 = ◇} {Γ2} {◇} dG1 dG2 dG3 g1= g2= = tt
ConvMor-Trans {Γ1 = Γ1 , A} {Γ2 , B} {Γ3 , C} (dG1 , dA) (dG2 , dB) (dG3 , dC) (g1= , a1=) (g2= , a2=) 
                         = congMorEq refl
                                     refl
                                     (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert (ConvMor Γ2 Γ3) _ _))
                                     refl
                                     (WeakMorEq (ConvMor-Trans dG1 dG2 dG3 g1= g2=))
                           , congTmEq (ap-coerc-Tm (! (weakenTyInsert B _ _))
                                                   (((weaken[]Ty _ _ _ ∙ ap[]Ty refl (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert (ConvMor Γ2 Γ3) _ _)))) ∙ ! ([]Ty-assoc _ _ C))
                                                   refl)
                                      (ap-coerc-Tm refl
                                                   (weaken[]Ty _ _ _ ∙ ap[]Ty refl (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert (ConvMor Γ2 Γ3) _ _)))
                                                   refl)
                                      (weaken[]Ty _ _ _ ∙ ap[]Ty refl (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert (ConvMor Γ2 Γ3) _ _)))
                                      (TmTran (Conv (WeakTy dA)
                                                    (WeakTy (congTy ([]Ty-assoc _ _ C) (SubstTy (SubstTy dC (ConvMor-Derivable dG2 dG3 g2=)) (ConvMor-Derivable dG1 dG2 g1=))))
                                                    (VarLast dA)
                                                    (WeakTyEq (TyTran (SubstTy dC (ConvMor-Derivable dG1 dG3 (CtxTran dG1 dG2 dG3 g1= g2=)))
                                                                       (TyTran (SubstTy (SubstTy dC (ConvMor-Derivable dG2 dG3 g2=) ) (ConvMor-Derivable dG1 dG2 g1=))
                                                                               (TyTran (SubstTy dB (ConvMor-Derivable dG1 dG2 g1=)) a1= (SubstTyEq a2= (ConvMor-Derivable dG1 dG2 g1=)))
                                                                               (TySymm (ConvMorTranTy dG3 dG2 dG1 (CtxSymm dG2 dG3 g2=) (CtxSymm dG1 dG2 g1=) dC)))
                                                                       (SubstTyMorEq1 dG1 dG3 dC (MorSymm dG1 dG3 (ConvMor-Trans dG1 dG2 dG3 g1= g2=))))))
                                              (CoercTrans (WeakTy dA)
                                                          (SubstTy dB (WeakMor (ConvMor-Derivable dG1 dG2 g1=)))
                                                          (WeakTy (congTy ([]Ty-assoc _ _ C) (SubstTy (SubstTy dC (ConvMor-Derivable dG2 dG3 g2=))
                                                                                                      (ConvMor-Derivable dG1 dG2 g1=))))
                                                          (VarLast dA)
                                                          (congTyEq refl (weaken[]Ty _ _ _)
                                                                    (WeakTyEq a1=))
                                                          (congTyEq (weaken[]Ty _ _ _) (ap (weakenTy) ([]Ty-assoc _ _ C)) (WeakTyEq (SubstTyEq a2= (ConvMor-Derivable dG1 dG2 g1=)))))
                                              (TmSymm (CoercTrans (WeakTy dA)
                                                                  (SubstTy dC (WeakMor (ConvMor-Derivable dG1 dG3 (CtxTran dG1 dG2 dG3 g1= g2=))))
                                                                  (WeakTy (congTy ([]Ty-assoc _ _ C) (SubstTy (SubstTy dC (ConvMor-Derivable dG2 dG3 g2=)) (ConvMor-Derivable dG1 dG2 g1=))))
                                                                  (VarLast dA)
                                                                  (congTyEq refl
                                                                            (weaken[]Ty C _ _)
                                                                            (WeakTyEq (TyTran (SubstTy (SubstTy dC (ConvMor-Derivable dG2 dG3 g2=) )
                                                                                                       (ConvMor-Derivable dG1 dG2 g1=))
                                                                                              (TyTran (SubstTy dB (ConvMor-Derivable dG1 dG2 g1=))
                                                                                                      a1=
                                                                                                      (SubstTyEq a2= (ConvMor-Derivable dG1 dG2 g1=)))
                                                                                                      (TySymm (ConvMorTranTy dG3
                                                                                                                             dG2
                                                                                                                             dG1
                                                                                                                             (CtxSymm dG2 dG3 g2=)
                                                                                                                             (CtxSymm dG1 dG2 g1=)
                                                                                                                             dC)))))
                                                                  (congTyEq (weaken[]Ty C _ _) refl
                                                                            (WeakTyEq (SubstTyMorEq1 dG1
                                                                                                     dG3
                                                                                                     dC
                                                                                                     (MorSymm dG1 dG3 (ConvMor-Trans dG1 dG2 dG3 g1= g2=))))))))                                   

ConvMorTranTy {A = A} dΓ1 dΓ2 dΓ3 dΓ1= dΓ2= dA = congTyEq refl (! ([]Ty-assoc _ _ A)) (SubstTyMorEq1 dΓ3
                                                                                                     dΓ1
                                                                                                     dA
                                                                                                     (MorSymm dΓ3
                                                                                                              dΓ1
                                                                                                              (ConvMor-Trans dΓ3
                                                                                                                             dΓ2
                                                                                                                             dΓ1
                                                                                                                             (CtxSymm dΓ2 dΓ3 dΓ2=)
                                                                                                                             (CtxSymm dΓ1 dΓ2 dΓ1=))))

