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
    → Derivation (Γ ⊢ A)
    → Derivation (Γ ⊢ var k == var k' :> A)
    → Derivation ((Γ , B) ⊢ var (prev k) == var (prev k') :> weakenTy A)
          
  -- Symmetry and transitivity for types
  TySymm : {Γ : Ctx n} {A B : TyExpr n}
    → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ B == A)
  TyTran : {Γ : Ctx n} {A B C : TyExpr n}
    → Derivation (Γ ⊢ B) → Derivation (Γ ⊢ A == B)→ Derivation (Γ ⊢ B == C) → Derivation (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmSymm : {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
    → Derivation (Γ ⊢ u == v :> A) → Derivation (Γ ⊢ v == u :> A)
  TmTran : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
    → Derivation (Γ ⊢ v :> A) → Derivation (Γ ⊢ u == v :> A)→ Derivation (Γ ⊢ v == w :> A) → Derivation (Γ ⊢ u == w :> A)

  -- Conversion rules
  Conv : {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n} → Derivation (Γ ⊢ A)
    → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ u :> B)
  ConvEq : {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n} → Derivation (Γ ⊢ A)
    → Derivation (Γ ⊢ u == u' :> A) → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ u == u' :> B)


  -- Rules for UU
  UU : {Γ : Ctx n}
    → Derivation (Γ ⊢ uu)
  UUCong : {Γ : Ctx n}
    → Derivation (Γ ⊢ uu == uu)

  -- Rules for El
  El : {Γ : Ctx n} {v : TmExpr n}
    → Derivation (Γ ⊢ v :> uu) → Derivation (Γ ⊢ el v)
  ElCong : {Γ : Ctx n} {v v' : TmExpr n}
    → Derivation (Γ ⊢ v == v' :> uu) → Derivation (Γ ⊢ el v == el v')


  -- Rules for Pi
  Pi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} 
    → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ pi A B)
  PiCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)}
    → Derivation (Γ ⊢ A)
    → Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B == B') → Derivation (Γ ⊢ pi A B == pi A' B')

--   -- Rules for pi
--   PiUU : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {b : TmExpr (suc n)}
--     → Derivation (Γ ⊢ a :> uu) → Derivation ((Γ , el a) ⊢ b :> uu) → Derivation (Γ ⊢ pi i a b :> uu)
--   PiUUCong : {i : ℕ} {Γ : Ctx n} {a a' : TmExpr n} {b b' : TmExpr (suc n)}
--     → Derivation (Γ ⊢ a :> uu) → Derivation (Γ ⊢ a == a' :> uu) → Derivation ((Γ , el a) ⊢ b == b' :> uu) → Derivation (Γ ⊢ pi i a b == pi i a' b' :> uu)
--   ElPi=' : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {b : TmExpr (suc n)}
--     → Derivation (Γ ⊢ a :> uu) → Derivation ((Γ , el a) ⊢ b :> uu) → Derivation (Γ ⊢ el (pi i a b) == pi (el a) (el b))

  -- Rules for lambda
  Lam : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
    → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation ((Γ , A) ⊢ u :> B)
    → Derivation (Γ ⊢ lam A B u :> pi A B)
  LamCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)}
    → Derivation (Γ ⊢ A)
    → Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B == B') → Derivation ((Γ , A) ⊢ u == u' :> B)
    → Derivation (Γ ⊢ lam A B u == lam A' B' u' :> pi A B)

  -- Rules for app
  App : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f a : TmExpr n}
    → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ f :> pi A B) → Derivation (Γ ⊢ a :> A)
    → Derivation (Γ ⊢ app A B f a :> substTy B a)
  AppCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n}
    → Derivation (Γ ⊢ A)
    → Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B == B') → Derivation (Γ ⊢ f == f' :> pi A B) → Derivation (Γ ⊢ a == a' :> A)
    → Derivation (Γ ⊢ app A B f a == app A' B' f' a' :> substTy B a)


--   -- Rules for Sigma
--   Sig' : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)}
--     → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ sig A B)
--   SigCong' : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} → Derivation (Γ ⊢ A)
--     → Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B == B') → Derivation (Γ ⊢ sig A B == sig A' B')

--   -- Rules for sig
--   SigUU : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {b : TmExpr (suc n)}
--     → Derivation (Γ ⊢ a :> uu) → Derivation ((Γ , el a) ⊢ b :> uu) → Derivation (Γ ⊢ sig i a b :> uu)
--   SigUUCong : {i : ℕ} {Γ : Ctx n} {a a' : TmExpr n} {b b' : TmExpr (suc n)}
--     → Derivation (Γ ⊢ a :> uu) → Derivation (Γ ⊢ a == a' :> uu) → Derivation ((Γ , el a) ⊢ b == b' :> uu) → Derivation (Γ ⊢ sig i a b == sig i a' b' :> uu)
--   ElSig=' : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {b : TmExpr (suc n)}
--     → Derivation (Γ ⊢ a :> uu) → Derivation ((Γ , el a) ⊢ b :> uu) → Derivation (Γ ⊢ el (sig i a b) == sig (el a) (el b))

--   -- Rules for pair
--   Pair' : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {a : TmExpr n} {b : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ a :> A) → Derivation (Γ ⊢ b :> substTy B a) → Derivation (Γ ⊢ pair A B a b :> sig A B)
--   PairCong' : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {a a' : TmExpr n} {b b' : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B == B') → Derivation (Γ ⊢ a == a' :> A) → Derivation (Γ ⊢ b == b' :> substTy B a) → Derivation (Γ ⊢ pair A B a b == pair A' B' a' b' :> sig A B)

--   -- Rules for pr1
--   Pr1' : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ u :> sig A B) → Derivation (Γ ⊢ pr1 A B u :> A)
--   Pr1Cong' : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B == B') → Derivation (Γ ⊢ u == u' :> sig A B) → Derivation (Γ ⊢ pr1 A B u == pr1 A' B' u' :> A)

--   -- Rules for pr2
--   Pr2' : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ u :> sig A B) → Derivation (Γ ⊢ pr2 A B u :> substTy B (pr1 A B u))
--   Pr2Cong' : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ A == A') → Derivation ((Γ , A) ⊢ B == B') → Derivation (Γ ⊢ u == u' :> sig A B) → Derivation (Γ ⊢ pr2 A B u == pr2 A' B' u' :> substTy B (pr1 A B u))


--   -- Rules for Empty
--   Empty' : {Γ : Ctx n}
--       → Derivation (Γ ⊢ empty)
--   EmptyCong' : {Γ : Ctx n}
--       → Derivation (Γ ⊢ empty == empty)

--   -- Rules for empty
--   EmptyUU : {i : ℕ} {Γ : Ctx n}
--      → Derivation (Γ ⊢ empty i :> uu)
--   EmptyUUCong : {i : ℕ} {Γ : Ctx n}
--      → Derivation (Γ ⊢ empty i == empty i :> uu)
--   ElEmpty=' : {i : ℕ} {Γ : Ctx n}
--      → Derivation (Γ ⊢ el (empty i) == empty)

--   -- Rules for emptyelim
--   Emptyelim' : {Γ : Ctx n} {A : TyExpr (suc n)} {u : TmExpr n}
--      → Derivation ((Γ , empty) ⊢ A) → Derivation (Γ ⊢ u :> empty) → Derivation (Γ ⊢ emptyelim A u :> substTy A u)
--   EmptyelimCong' : {Γ : Ctx n} {A A' : TyExpr (suc n)} {u u' : TmExpr n}
--      → Derivation ((Γ , empty) ⊢ A == A') → Derivation (Γ ⊢ u == u' :> empty) → Derivation (Γ ⊢ emptyelim A u == emptyelim A' u' :> substTy A u)

--   -- Rules for Unit
--   Unit' : {Γ : Ctx n}
--      → Derivation (Γ ⊢ unit)
--   UnitCong' : {Γ : Ctx n}
--      → Derivation (Γ ⊢ unit == unit)

--   -- Rules for unit
--   UnitUU : {i : ℕ} {Γ : Ctx n}
--      → Derivation (Γ ⊢ unit i :> uu)
--   UnitUUCong : {i : ℕ} {Γ : Ctx n}
--      → Derivation (Γ ⊢ unit i == unit i :> uu)
--   ElUnit=' : {i : ℕ} {Γ : Ctx n}
--      → Derivation (Γ ⊢ el (unit i) == unit)

--   -- Rules for tt
--   TT' : {Γ : Ctx n}
--      → Derivation (Γ ⊢ tt :> unit)
--   TTCong' : {Γ : Ctx n}
--      → Derivation (Γ ⊢ tt == tt :> unit)

--   -- Rules for unitelim
--   Unitelim' : {Γ : Ctx n} {A : TyExpr (suc n)} {dtt : TmExpr n} {u : TmExpr n}
--      → Derivation ((Γ , unit) ⊢ A) → Derivation (Γ ⊢ dtt :> substTy A tt) → Derivation (Γ ⊢ u :> unit) → Derivation (Γ ⊢ unitelim A dtt u :> substTy A u)
--   UnitelimCong' : {Γ : Ctx n} {A A' : TyExpr (suc n)} {dtt dtt' : TmExpr n} {u u' : TmExpr n}
--      → Derivation ((Γ , unit) ⊢ A == A') → Derivation (Γ ⊢ dtt == dtt' :> substTy A tt) → Derivation (Γ ⊢ u == u' :> unit) → Derivation (Γ ⊢ unitelim A dtt u == unitelim A' dtt' u' :> substTy A u)
    

--   -- Rules for Nat
--   Nat' : {Γ : Ctx n}
--     → Derivation (Γ ⊢ nat)
--   NatCong' : {Γ : Ctx n}
--     → Derivation (Γ ⊢ nat == nat)

--   -- Rules for nat
--   NatUU : {i : ℕ} {Γ : Ctx n}
--     → Derivation (Γ ⊢ nat i :> uu)
--   NatUUCong : {i : ℕ} {Γ : Ctx n}
--     → Derivation (Γ ⊢ nat i == nat i :> uu)
--   ElNat=' : {i : ℕ} {Γ : Ctx n}
--     → Derivation (Γ ⊢ el (nat i) == nat)

--   -- Rules for zero
--   Zero' : {Γ : Ctx n}
--     → Derivation (Γ ⊢ zero :> nat)
--   ZeroCong' : {Γ : Ctx n}
--     → Derivation (Γ ⊢ zero == zero :> nat)

--   -- Rules for suc
--   Suc' : {Γ : Ctx n} {u : TmExpr n}
--     → Derivation (Γ ⊢ u :> nat) → Derivation (Γ ⊢ suc u :> nat)
--   SucCong' : {Γ : Ctx n} {u u' : TmExpr n}
--     → Derivation (Γ ⊢ u == u' :> nat) → Derivation (Γ ⊢ suc u == suc u' :> nat)

--   -- Rules for natelim
--   Natelim' : {Γ : Ctx n} {P : TyExpr (suc n)} {dO : TmExpr n} {dS : TmExpr (suc (suc n))} {u : TmExpr n}
--     → Derivation ((Γ , nat) ⊢ P) → Derivation (Γ ⊢ dO :> substTy P zero) → Derivation (((Γ , nat) , P) ⊢ dS :> substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last)))) → Derivation (Γ ⊢ u :> nat) → Derivation (Γ ⊢ natelim P dO dS u :> substTy P u)
--   NatelimCong' : {Γ : Ctx n} {P P' : TyExpr (suc n)} {dO dO' : TmExpr n} {dS dS' : TmExpr (suc (suc n))} {u u' : TmExpr n}
--     → Derivation ((Γ , nat) ⊢ P) → Derivation ((Γ , nat) ⊢ P == P') → Derivation (Γ ⊢ dO == dO' :> substTy P zero) → Derivation (((Γ , nat) , P) ⊢ dS == dS' :> substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last)))) → Derivation (Γ ⊢ u == u' :> nat) → Derivation (Γ ⊢ natelim P dO dS u == natelim P' dO' dS' u' :> substTy P u)


--   -- Rules for Id
--   Id' : {Γ : Ctx n} {A : TyExpr n} {a b : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ a :> A) → Derivation (Γ ⊢ b :> A) → Derivation (Γ ⊢ id A a b)
--   IdCong' : {Γ : Ctx n} {A A' : TyExpr n} {a a' b b' : TmExpr n}
--     → Derivation (Γ ⊢ A == A') → Derivation (Γ ⊢ a == a' :> A) → Derivation (Γ ⊢ b == b' :> A) → Derivation (Γ ⊢ id A a b == id A' a' b')

--   -- Rules for id
--   IdUU : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {u v : TmExpr n}
--     → Derivation (Γ ⊢ a :> uu) → Derivation (Γ ⊢ u :> el a) → Derivation (Γ ⊢ v :> el a) → Derivation (Γ ⊢ id i a u v :> uu)
--   IdUUCong : {i : ℕ} {Γ : Ctx n} {a a' : TmExpr n} {u u' v v' : TmExpr n}
--     → Derivation (Γ ⊢ a == a' :> uu) → Derivation (Γ ⊢ u == u' :> el a) → Derivation (Γ ⊢ v == v' :> el a) → Derivation (Γ ⊢ id i a u v == id i a' u' v' :> uu)
--   ElId=' : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {u v : TmExpr n}
--     → Derivation (Γ ⊢ a :> uu) → Derivation (Γ ⊢ u :> el a) → Derivation (Γ ⊢ v :> el a) → Derivation (Γ ⊢ el (id i a u v) == id (el a) u v)
  
--   -- Rules for refl
--   Refl' : {Γ : Ctx n} {A : TyExpr n} {a : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ a :> A) → Derivation (Γ ⊢ refl A a :> id A a a)
--   ReflCong' : {Γ : Ctx n} {A A' : TyExpr n} {a a' : TmExpr n}
--     → Derivation (Γ ⊢ A == A') → Derivation (Γ ⊢ a == a' :> A) → Derivation (Γ ⊢ refl A a == refl A' a' :> id A a a)

--   -- Rules for jj
--   JJ' : {Γ : Ctx n} {A : TyExpr n} {P : TyExpr (suc (suc (suc n)))} {d : TmExpr (suc n)} {a b p : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation ((((Γ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⊢ P) → Derivation ((Γ , A) ⊢ d :> subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last))) → Derivation (Γ ⊢ a :> A) → Derivation (Γ ⊢ b :> A) → Derivation (Γ ⊢ p :> id A a b) → Derivation (Γ ⊢ jj A P d a b p :> subst3Ty P a b p)
--   JJCong' :  {Γ : Ctx n} {A A' : TyExpr n} {P P' : TyExpr (suc (suc (suc n)))} {d d' : TmExpr (suc n)} {a a' b b' p p' : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ A == A') →  Derivation ((((Γ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⊢ P == P') → Derivation ((Γ , A) ⊢ d == d' :> subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last))) → Derivation (Γ ⊢ a == a' :> A) → Derivation (Γ ⊢ b == b' :> A) → Derivation (Γ ⊢ p == p' :> id A a b) → Derivation (Γ ⊢ jj A P d a b p == jj A' P' d' a' b' p' :> subst3Ty P a b p)


  -- Beta-reductions
  BetaPi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
    → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation ((Γ , A) ⊢ u :> B) → Derivation (Γ ⊢ a :> A)
    → Derivation (Γ ⊢ app A B (lam A B u) a == substTm u a :> substTy B a)
--   BetaSig1' : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {a : TmExpr n} {b : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ a :> A) → Derivation (Γ ⊢ b :> substTy B a) → Derivation (Γ ⊢ pr1 A B (pair A B a b) == a :> A)
--   BetaSig2' : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {a : TmExpr n} {b : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ a :> A) → Derivation (Γ ⊢ b :> substTy B a) → Derivation (Γ ⊢ pr2 A B (pair A B a b) == b :> substTy B a)
--   BetaUnit' : {Γ : Ctx n} {A : TyExpr (suc n)} {dtt : TmExpr n}
--     → Derivation ((Γ , unit) ⊢ A) → Derivation (Γ ⊢ dtt :> substTy A tt) → Derivation (Γ ⊢ unitelim A dtt tt == dtt :> substTy A tt)
--   BetaNatZero' : {Γ : Ctx n} {P : TyExpr (suc n)} {dO : TmExpr n} {dS : TmExpr (suc (suc n))}
--     → Derivation ((Γ , nat) ⊢ P) → Derivation (Γ ⊢ dO :> substTy P zero) → Derivation (((Γ , nat) , P) ⊢ dS :> substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last))))
--     → Derivation (Γ ⊢ natelim P dO dS zero == dO :> substTy P zero)
--   BetaNatSuc' : {Γ : Ctx n} {P : TyExpr (suc n)} {dO : TmExpr n} {dS : TmExpr (suc (suc n))} {u : TmExpr n}
--     → Derivation ((Γ , nat) ⊢ P) → Derivation (Γ ⊢ dO :> substTy P zero) → Derivation (((Γ , nat) , P) ⊢ dS :> substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last)))) → Derivation (Γ ⊢ u :> nat)
--     → Derivation (Γ ⊢ natelim P dO dS (suc u) == subst2Tm dS u (natelim P dO dS u) :> substTy P (suc u))
--   BetaIdRefl' : {Γ : Ctx n} {A : TyExpr n} {P : TyExpr (suc (suc (suc n)))} {d : TmExpr (suc n)} {a : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation ((((Γ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⊢ P) → Derivation ((Γ , A) ⊢ d :> subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last))) → Derivation (Γ ⊢ a :> A)
--     → Derivation (Γ ⊢ jj A P d a a (refl A a) == substTm d a :> subst3Ty P a a (refl A a))

  -- Eta-equivalences
  EtaPi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f : TmExpr n}
    → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ f :> pi A B)
    → Derivation (Γ ⊢ f == lam A B (app (weakenTy A) (weakenTy' (prev last) B) (weakenTm f) (var last)) :> pi A B)
--   EtaSig' : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr n}
--     → Derivation (Γ ⊢ A) → Derivation ((Γ , A) ⊢ B) → Derivation (Γ ⊢ u :> sig A B)
--     → Derivation (Γ ⊢ u == pair A B (pr1 A B u) (pr2 A B u) :> sig A B)

{- Proof Relevant version of derivability of contexts, context equality, context morphisms, and context morphism equality -}

⊢R_ : Ctx n → Set
⊢R ◇ = metaUnitR
⊢R (Γ , A) = (⊢R Γ) ×R Derivation (Γ ⊢ A)

⊢R_==_ : Ctx n → Ctx n → Set
⊢R ◇ == ◇ = metaUnitR
⊢R (Γ , A) == (Γ' , A') = (⊢R Γ == Γ') ×R Derivation (Γ ⊢ A) ×R Derivation (Γ' ⊢ A') ×R Derivation (Γ ⊢ A == A') ×R Derivation (Γ' ⊢ A == A')

_⊢R_∷>_ : (Γ : Ctx n) → Mor n m → Ctx m → Set
Γ ⊢R ◇ ∷> ◇ = metaUnitR
Γ ⊢R (δ , u) ∷> (Δ , A) = (Γ ⊢R δ ∷> Δ) ×R Derivation (Γ ⊢ u :> A [ δ ]Ty) 

_⊢R_==_∷>_ : (Γ : Ctx n) → Mor n m → Mor n m → Ctx m → Set
Γ ⊢R ◇ == ◇ ∷> ◇ = metaUnitR
Γ ⊢R (δ , u) == (δ' , u') ∷> (Δ , A) = (Γ ⊢R δ == δ' ∷> Δ) ×R Derivation (Γ ⊢ u == u' :> A [ δ ]Ty)

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
TyRefl' : {Γ : Ctx n} {A : TyExpr n} → Derivation (Γ ⊢ A) → Derivation (Γ ⊢ A == A)
TmRefl' : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivation (Γ ⊢ u :> A) → Derivation (Γ ⊢ u == u :> A)

TyRefl' (Pi dA dB) = PiCong dA (TyRefl' dA) (TyRefl' dB)
TyRefl' UU = UUCong
TyRefl' (El dv) = ElCong (TmRefl' dv)

TmRefl' (VarLast dA) = VarLastCong dA
TmRefl' (VarPrev dA dk) = VarPrevCong dA (TmRefl' dk) 
TmRefl' (Conv dA du dA=) = ConvEq dA (TmRefl' du) dA=
TmRefl' (Lam dA dB du) = LamCong dA (TyRefl' dA) (TyRefl' dB) (TmRefl' du)
TmRefl' (App dA dB df da) = AppCong dA (TyRefl' dA) (TyRefl' dB) (TmRefl' df) (TmRefl' da)

CtxReflR : {Γ : Ctx n} → ⊢R Γ → ⊢R Γ == Γ
CtxReflR {Γ = ◇} starU = starU
CtxReflR {Γ = Γ , A} (dΓ , dA) = (CtxReflR dΓ , dA , dA , TyRefl' dA , TyRefl' dA)

MorReflR : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → (Γ ⊢R δ ∷> Δ) → (Γ ⊢R δ == δ ∷> Δ)
MorReflR {Δ = ◇} {δ = ◇} dδ = starU
MorReflR {Δ = Δ , B} {δ = δ , u} (dδ , du) = MorReflR dδ , TmRefl' du


-- Weakening and Substitution for proof relevant
SubstTyR : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m}
       → Derivation (Δ ⊢ A) → Γ ⊢R δ ∷> Δ → Derivation (Γ ⊢ A [ δ ]Ty)
SubstTmR : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivation (Δ ⊢ u :> A) → Γ ⊢R δ ∷> Δ → Derivation (Γ ⊢ u [ δ ]Tm :> A [ δ ]Ty)
SubstTyREq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ : Mor n m}
       → Derivation (Δ ⊢ A == A') → Γ ⊢R δ ∷> Δ → Derivation (Γ ⊢ A [ δ ]Ty == A' [ δ ]Ty)
SubstTmREq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivation (Δ ⊢ u == u' :> A) → (Γ ⊢R δ ∷> Δ) → Derivation (Γ ⊢ u [ δ ]Tm == u' [ δ ]Tm :> A [ δ ]Ty)
SubstTyMorEqR : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivation (Δ ⊢ A) → (Γ ⊢R δ ∷> Δ)
       → (Γ ⊢R δ == δ' ∷> Δ) → Derivation (Γ ⊢ A [ δ ]Ty == A [ δ' ]Ty)
SubstTmMorEqR : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} →  Derivation (Δ ⊢ u :> A) → (Γ ⊢R δ ∷> Δ) 
       → (Γ ⊢R δ == δ' ∷> Δ) → Derivation (Γ ⊢ u [ δ ]Tm == u [ δ' ]Tm :> A [ δ ]Ty)

WeakTy' : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {A : TyExpr n}
     → Derivation (Γ ⊢ A) → Derivation (weakenCtx k Γ T ⊢ weakenTy' k A)
WeakTm' : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {u : TmExpr n} {A : TyExpr n}
     → Derivation (Γ ⊢ u :> A) → Derivation (weakenCtx k Γ T ⊢ weakenTm' k u :> weakenTy' k A)
WeakTyEq' : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {A A' : TyExpr n}
     → Derivation (Γ ⊢ A == A') → Derivation (weakenCtx k Γ T ⊢ weakenTy' k A == weakenTy' k A')
WeakTmEq' : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} {u u' : TmExpr n} {A : TyExpr n}
     → Derivation (Γ ⊢ u == u' :> A) → Derivation (weakenCtx k Γ T ⊢ weakenTm' k u == weakenTm' k u' :> weakenTy' k A)

WeakCtxR : {k : Fin (suc n)} {Γ : Ctx n} {T : TyExpr (n -F' k)} → ⊢R Γ → Derivation (cutCtx k Γ ⊢ T) → ⊢R (weakenCtx k Γ T)
WeakCtxR {k = last} {Γ} dΓ dT = dΓ , dT
WeakCtxR {k = (prev k)} {Γ = Γ , A} dΓ dT = WeakCtxR {k = k} (fst dΓ) dT , WeakTy' (snd dΓ)

WeakMorR : {Γ : Ctx n} {Δ : Ctx m} {T : TyExpr n} {δ : Mor n m} → Γ ⊢R δ ∷> Δ → (Γ , T) ⊢R weakenMor δ ∷> Δ
WeakMorR {Δ = ◇} {δ = ◇} starU = starU
WeakMorR {Γ = Γ} {Δ = Δ , B} {T = T} {δ = δ , u} (dδ , du) with (B [ weakenMor' last δ ]Ty) | !R (weaken[]TyR B δ last)
WeakMorR {Δ = Δ , B} {δ = δ , u} (dδ , du) | .(weakenTy' last (B [ δ ]Ty)) | reflR = (WeakMorR dδ , WeakTm' du )

-- = WeakMorR dδ , congTmTyR (weaken[]TyR _ _ _) (WeakTm' du)

{-  Try to get rid of congTmTyR by with abstraction. There might be some universe issues...
with (CongTm {Γ = Γ , T} {Δ = Γ , T} {A = weakenTy (B [ δ ]Ty)} {B = B [ weakenMor' last δ ]Ty} {u = weakenTm u} reflR (weaken[]TyR B δ last) reflR)
WeakMorR {Δ = Δ , B} {δ = δ , u} (dδ , du)   | eq = (WeakMorR dδ , {!WeakTm' du!} )
-}

WeakMorEqR : {Γ : Ctx n } {Δ : Ctx m} {T : TyExpr n} {δ δ' : Mor n m} → (Γ ⊢R δ == δ' ∷> Δ) → ((Γ , T) ⊢R weakenMor δ == weakenMor δ' ∷> Δ)
WeakMorEqR {Δ = ◇} {δ = ◇} {◇} dδ = starU
WeakMorEqR {Δ = Δ , B} {δ = δ , u} {δ' , u'} (dδ , du) = (WeakMorEqR dδ , congTmEqTyR (weaken[]TyR _ _ _) (WeakTmEq' du))

WeakMorR+~ : {Γ : Ctx n} {Δ : Ctx m} (A : TyExpr m) {δ : Mor n m} → Derivation (Γ ⊢ A [ δ ]Ty) → Γ ⊢R δ ∷> Δ → (Γ , A [ δ ]Ty) ⊢R weakenMor+ δ ∷> (Δ , A)
WeakMorR+~ A dAδ dδ = (WeakMorR dδ , congTmTyR (weaken[]TyR _ _ _) (VarLast dAδ))

WeakMorR+ : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} → Derivation (Δ ⊢ A) → Γ ⊢R δ ∷> Δ → (Γ , A [ δ ]Ty) ⊢R weakenMor+ δ ∷> (Δ , A)
WeakMorR+ dA dδ = WeakMorR+~ _ (SubstTyR dA dδ) dδ

WeakMorR+Eq : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivation (Δ ⊢ A) → Γ ⊢R δ ∷> Δ → Γ ⊢R δ == δ' ∷> Δ → (Γ , A [ δ ]Ty) ⊢R weakenMor+ δ == weakenMor+ δ' ∷> (Δ , A)
WeakMorR+Eq dA dδ dδ= = (WeakMorEqR dδ= , TmRefl' (congTmTyR (weaken[]TyR _ _ _) (VarLast (SubstTyR dA dδ))))


SubstTyR {A = pi A B} (Pi dA dB) dδ = Pi (SubstTyR dA dδ) (SubstTyR dB (WeakMorR+ dA dδ))
SubstTyR {A = uu} UU dδ = UU
SubstTyR {A = el v} (El dA) dδ = El (SubstTmR dA dδ)

SubstTmR (Conv dA du dA=) dδ = Conv (SubstTyR dA dδ) (SubstTmR du dδ) (SubstTyREq dA= dδ)
SubstTmR {Δ = (_ , _)} {var last}     {δ = _ , _} (VarLast _) (_ , du) = congTmTyR! (weakenTyInsertR _ _ _) du
SubstTmR {Δ = (_ , _)} {var (prev k)} {δ = _ , _} (VarPrev _ dk) (dδ , _) = congTmTyR! (weakenTyInsertR _ _ _) (SubstTmR dk dδ)
SubstTmR {u = lam A B u} (Lam dA dB du) dδ = Lam (SubstTyR dA dδ) (SubstTyR dB (WeakMorR+ dA dδ)) (SubstTmR du (WeakMorR+ dA dδ))
SubstTmR {u = app A B f a} {δ = δ} (App dA dB df da) dδ = congTmTyR! []Ty-substTyR (App (SubstTyR dA dδ) (SubstTyR dB (WeakMorR+ dA dδ)) (SubstTmR df dδ) (SubstTmR da dδ))

SubstTyREq (TySymm dA=) dδ = TySymm (SubstTyREq dA= dδ)
SubstTyREq (TyTran dB dA= dB=) dδ = TyTran (SubstTyR dB dδ) (SubstTyREq dA= dδ) (SubstTyREq dB= dδ)

SubstTyREq (PiCong dA dA= dB=) dδ = PiCong (SubstTyR dA dδ) (SubstTyREq dA= dδ) (SubstTyREq dB= (WeakMorR+ dA dδ))
SubstTyREq UUCong dδ = UUCong
SubstTyREq (ElCong dv=) dδ = ElCong (SubstTmREq dv= dδ)

SubstTmREq {δ = _ , _} (VarLastCong _)     (_ , du) = congTmEqTyR! (weakenTyInsertR _ _ _) (TmRefl' du)
SubstTmREq {δ = _ , _} (VarPrevCong _ dA=) (dδ , _) = congTmEqTyR! (weakenTyInsertR _ _ _) (SubstTmREq dA= dδ)
SubstTmREq (TmSymm du=) dδ = TmSymm (SubstTmREq du= dδ)
SubstTmREq (TmTran dv du= dv=) dδ = TmTran (SubstTmR dv dδ) (SubstTmREq du= dδ) (SubstTmREq dv= dδ)
SubstTmREq (ConvEq dA du= dA=) dδ = ConvEq (SubstTyR dA dδ) (SubstTmREq du= dδ) (SubstTyREq dA= dδ) 
SubstTmREq (LamCong dA dA= dB= du=) dδ = LamCong (SubstTyR dA dδ) (SubstTyREq dA= dδ) (SubstTyREq dB= (WeakMorR+ dA dδ)) (SubstTmREq du= (WeakMorR+ dA dδ))
SubstTmREq (AppCong dA dA= dB= df= da=) dδ = congTmEqTyR! []Ty-substTyR (AppCong (SubstTyR dA dδ) (SubstTyREq dA= dδ) (SubstTyREq dB= (WeakMorR+ dA dδ)) (SubstTmREq df= dδ) (SubstTmREq da= dδ))
SubstTmREq (BetaPi {u = u} dA dB du da) dδ = congTmEqR! reflR ([]Tm-substTmR u) []Ty-substTyR (BetaPi (SubstTyR dA dδ) (SubstTyR dB (WeakMorR+ dA dδ)) (SubstTmR du (WeakMorR+ dA dδ )) (SubstTmR da dδ))
SubstTmREq (EtaPi {f = f} dA dB df) dδ =
  congTmEqR! reflR (apR-lam-Tm reflR reflR (apR-app-Tm []Ty-weakenTyR []Ty-weakenTy1R ([]Tm-weakenTmR f) reflR)) reflR
            (EtaPi (SubstTyR dA dδ)
                   (SubstTyR dB (WeakMorR+ dA dδ))
                   (SubstTmR df dδ))



WeakTy' (Pi dA dB) = Pi (WeakTy' dA) (WeakTy' dB)
WeakTy' UU = UU
WeakTy' (El dv) = El (WeakTm' dv)

WeakTm' (Conv dA du dA=) = Conv (WeakTy' dA) (WeakTm' du) (WeakTyEq' dA=) 
WeakTm' {k = last}   (VarLast dA)    = VarPrev (WeakTy' dA) (VarLast dA)
WeakTm' {k = last}   (VarPrev dA dk) = VarPrev (WeakTy' dA) (VarPrev dA dk)
WeakTm' {k = prev k} (VarLast dA)    = congTmTyR! weakenTy-weakenTy' (VarLast (WeakTy' dA))
WeakTm' {k = prev k} (VarPrev dA dk) = congTmTyR! weakenTy-weakenTy' (VarPrev (WeakTy' dA) (WeakTm' dk))
WeakTm' (Lam dA dB du) = Lam (WeakTy' dA) (WeakTy' dB) (WeakTm' du)
WeakTm' (App dA dB df da) = congTmTyR! weakenTy-substTy' (App (WeakTy' dA) (WeakTy' dB) (WeakTm' df) (WeakTm' da))

WeakTyEq' (TySymm dA=) = TySymm (WeakTyEq' dA=)
WeakTyEq' (TyTran dB dA= dB=) = TyTran (WeakTy' dB) (WeakTyEq' dA=) (WeakTyEq' dB=)
WeakTyEq' (PiCong dA dA= dB=) = PiCong (WeakTy' dA) (WeakTyEq' dA=) (WeakTyEq' dB=)
WeakTyEq' UUCong = UUCong
WeakTyEq' (ElCong dv=) = ElCong (WeakTmEq' dv=)

WeakTmEq' {k = last}   (VarLastCong dA)     = VarPrevCong (WeakTy' dA) (VarLastCong dA)
WeakTmEq' {k = last}   (VarPrevCong dA dk=) = VarPrevCong (WeakTy' dA) (WeakTmEq' dk=)
WeakTmEq' {k = prev k} (VarLastCong dA)     = congTmEqTyR! weakenTy-weakenTy' (VarLastCong (WeakTy' dA))
WeakTmEq' {k = prev k} (VarPrevCong dA dk=) = congTmEqTyR! weakenTy-weakenTy' (VarPrevCong (WeakTy' dA) (WeakTmEq' dk=))
WeakTmEq' (TmSymm du=) = TmSymm (WeakTmEq' du=)
WeakTmEq' (TmTran dv du= dv=) = TmTran (WeakTm' dv) (WeakTmEq' du=) (WeakTmEq' dv=)
WeakTmEq' (ConvEq dA du= dA=) = ConvEq (WeakTy' dA) (WeakTmEq' du=) (WeakTyEq' dA=)
-- WeakTmEq' UUUUCong = UUUUCong
-- WeakTmEq' (PiUUCong da da= db=) = PiUUCong (WeakTm' da) (WeakTmEq' da=) (WeakTmEq' db=)
WeakTmEq' (LamCong dA dA= dB= du=) = LamCong (WeakTy' dA) (WeakTyEq' dA=) (WeakTyEq' dB=) (WeakTmEq' du=)
WeakTmEq' (AppCong dA dA= dB= df= da=) = congTmEqTyR! weakenTy-substTy' (AppCong (WeakTy' dA) (WeakTyEq' dA=) (WeakTyEq' dB=) (WeakTmEq'  df=) (WeakTmEq' da=))
WeakTmEq' {u = app A B (lam A B u) a} (BetaPi dA dB du da) = congTmEqR! reflR (weakenTm-substTmR u) weakenTy-substTy' (BetaPi (WeakTy' dA) (WeakTy' dB) (WeakTm' du) (WeakTm' da))
WeakTmEq' (EtaPi {f = f} dA dB df) =
  congTmEqR! reflR (apR-lam-Tm reflR reflR (apR-app-Tm weakenTy-weakenTy' weakenTy-weakenTy1R (!R (weakenTmCommutesR _ f)) reflR)) reflR
            (EtaPi (WeakTy' dA)
                   (WeakTy' dB)
                   (WeakTm' df))

SubstTyMorEqR (Pi dA dB) dδ dδ= = PiCong (SubstTyR dA dδ) (SubstTyMorEqR dA dδ dδ=) (SubstTyMorEqR dB (WeakMorR+ dA dδ) (WeakMorR+Eq dA dδ dδ=))
SubstTyMorEqR UU dδ dδ= = UUCong
SubstTyMorEqR (El dv) dδ dδ= = ElCong (SubstTmMorEqR dv dδ dδ=)

SubstTmMorEqR {δ = _ , _} {δ' = _ , _} (VarLast _) dδ (_ , du=) = congTmEqTyR! (weakenTyInsertR _ _ _) du=
SubstTmMorEqR {δ = _ , _} {δ' = _ , _} (VarPrev _ dk) (dδ , _) (dδ= , _) = congTmEqTyR! (weakenTyInsertR _ _ _) (SubstTmMorEqR dk dδ dδ=)
SubstTmMorEqR (Conv dA du dA=) dδ dδ= = ConvEq (SubstTyR dA dδ) (SubstTmMorEqR du dδ dδ=) (SubstTyREq dA= dδ)
SubstTmMorEqR (Lam dA dB du) dδ dδ= = LamCong (SubstTyR dA dδ) (SubstTyMorEqR dA dδ dδ=) (SubstTyMorEqR dB (WeakMorR+ dA dδ) (WeakMorR+Eq dA dδ dδ=)) (SubstTmMorEqR du (WeakMorR+ dA dδ) (WeakMorR+Eq dA dδ dδ=))
SubstTmMorEqR (App dA dB df da) dδ dδ= = congTmEqTyR! []Ty-substTyR (AppCong (SubstTyR dA dδ) (SubstTyMorEqR dA dδ dδ=) (SubstTyMorEqR dB (WeakMorR+ dA dδ) (WeakMorR+Eq dA dδ dδ=)) (SubstTmMorEqR df dδ dδ=) (SubstTmMorEqR da dδ dδ=))

substTy-weakenTyR' : {k : Fin (suc m)} {A : TyExpr m} {δ : Mor n m} {t : TmExpr n} → weakenTy' k A [ insertMor k t δ ]Ty ≡R A [ δ ]Ty
substTy-weakenTyR' = weakenTyInsert'R _ _ _ _

SubstTyFullEqR : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m} → Derivation (Δ ⊢ A') → (Γ ⊢R δ ∷> Δ)
       → Derivation (Δ ⊢ A == A') → (Γ ⊢R δ == δ' ∷> Δ) → Derivation (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
SubstTyFullEqR dA' dδ dA= dδ= = TyTran (SubstTyR dA' dδ) (SubstTyREq dA= dδ) (SubstTyMorEqR dA' dδ dδ=)

{- Derivability of the identity morphism -}

idMorDerivableR : {Γ : Ctx n} →  ⊢R Γ → (Γ ⊢R idMor n ∷> Γ)
idMorDerivableR {Γ = ◇} starU = starU
idMorDerivableR {Γ = Γ , A} (dΓ , dA) = (WeakMorR (idMorDerivableR dΓ) , congTmR (!R ([idMor]TyR _) R∙ substTy-weakenTyR') reflR (VarLast dA))

-- Conversion rules for proof relevant version are needed as well

ConvTy' : {Γ Δ : Ctx n} {A : TyExpr n} → Derivation (Γ ⊢ A) → (⊢R Γ == Δ) → Derivation (Δ ⊢ A)
ConvTm' : {Γ Δ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivation (Γ ⊢ u :> A) → (⊢R Γ == Δ) → Derivation (Δ ⊢ u :> A)
ConvTyEq' : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivation (Γ ⊢ A == B) → (⊢R Γ == Δ) → Derivation (Δ ⊢ A == B)
ConvTmEq' : {Γ Δ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → Derivation (Γ ⊢ u == v :> A) → (⊢R Γ == Δ) → Derivation (Δ ⊢ u == v :> A)

ConvTy' {Γ = Γ} {Δ = Δ} {A = A} (Pi dA dB) dΓ= = Pi (ConvTy' dA dΓ=) (ConvTy' dB (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=)))
ConvTy' UU dΓ= = UU
ConvTy' (El dv) dΓ= = El (ConvTm' dv dΓ=)

ConvTyEq'(TySymm dA=) dΓ= = TySymm (ConvTyEq' dA= dΓ=)
ConvTyEq'(TyTran dB dA= dB=) dΓ= = TyTran (ConvTy' dB dΓ=) (ConvTyEq' dA= dΓ=) (ConvTyEq' dB= dΓ=)
ConvTyEq' (PiCong dA dA= dB=) dΓ= = PiCong (ConvTy' dA dΓ=) (ConvTyEq' dA= dΓ=) (ConvTyEq' dB= (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=)))
ConvTyEq' UUCong dΓ= = UUCong
ConvTyEq' (ElCong dv=) dΓ= = ElCong (ConvTmEq' dv= dΓ=)

ConvTm' {Δ = Δ , B} {var last} (VarLast {A = A} dA) (dΓ= , dA' , dB , dA= , dA=') = Conv (WeakTy' dB) (VarLast dB) (WeakTyEq' (TySymm dA='))
{- changed dA to dA' -}
ConvTm' {Γ = Γ , A} {Δ = Δ , B} (VarPrev dA dk) (dΓ= , dA' , dB , dA=) = VarPrev (ConvTy' dA dΓ=) (ConvTm' dk dΓ=)
ConvTm' (Conv dA du dA=) dΓ= = Conv (ConvTy' dA dΓ=) (ConvTm' du dΓ=) (ConvTyEq' dA= dΓ=)
ConvTm' (Lam dA dB du) dΓ= = Lam (ConvTy' dA dΓ=) (ConvTy' dB (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=))) (ConvTm' du (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=)))
ConvTm' (App dA dB df da) dΓ= = App (ConvTy' dA dΓ=) (ConvTy' dB (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=))) (ConvTm' df dΓ=) (ConvTm' da dΓ=)

ConvTmEq'  {Δ = Δ , B} (VarLastCong {A = A} dA) (dΓ= , dA' , dB , dA= , dA=') = ConvEq (WeakTy' dB) (VarLastCong dB) (WeakTyEq' (TySymm dA='))
{- changed dA to dA' -}
ConvTmEq' {Γ = Γ , B} {Δ , B'} (VarPrevCong {A = A} dA dk=) (dΓ= , dA' , dB , dA=) = VarPrevCong (ConvTy' dA dΓ=) (ConvTmEq' dk= dΓ=)
ConvTmEq' (TmSymm du=) dΓ= = TmSymm (ConvTmEq' du= dΓ=)
ConvTmEq' (TmTran dv du= dv=) dΓ= = TmTran (ConvTm' dv dΓ=) (ConvTmEq' du= dΓ=) (ConvTmEq' dv= dΓ=)
ConvTmEq' (ConvEq dA du= dA=) dΓ= = ConvEq (ConvTy' dA dΓ=) (ConvTmEq' du= dΓ=) (ConvTyEq' dA= dΓ=)
ConvTmEq' (LamCong dA dA= dB= du=) dΓ= = LamCong (ConvTy' dA dΓ=) (ConvTyEq' dA= dΓ=) (ConvTyEq' dB= (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=))) (ConvTmEq' du= (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=)))
ConvTmEq' (AppCong dA dA= dB= df= da=) dΓ= = AppCong (ConvTy' dA dΓ=) (ConvTyEq' dA= dΓ=) (ConvTyEq' dB= (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=))) (ConvTmEq' df= dΓ=) (ConvTmEq' da= dΓ=)
ConvTmEq' (BetaPi dA dB du da) dΓ= = BetaPi (ConvTy' dA dΓ=) (ConvTy' dB (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=))) (ConvTm' du (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=))) (ConvTm' da dΓ=)
ConvTmEq' (EtaPi dA dB df) dΓ= =
  EtaPi (ConvTy' dA dΓ=)
        (ConvTy' dB (dΓ= , dA , ConvTy' dA dΓ= , TyRefl' dA , TyRefl' (ConvTy' dA dΓ=)))
        (ConvTm' df dΓ=)

TyEqTy1R : {Γ : Ctx n} {A B : TyExpr n} → (⊢R Γ) → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ A)
TyEqTy2R : {Γ : Ctx n} {A B : TyExpr n} → (⊢R Γ) → Derivation (Γ ⊢ A == B) → Derivation (Γ ⊢ B)
TmEqTm1R : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢R Γ) → Derivation (Γ ⊢ u == u' :> A) → Derivation (Γ ⊢ u :> A)
TmEqTm2R : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢R Γ) → Derivation (Γ ⊢ u == u' :> A) → Derivation (Γ ⊢ u' :> A)


TyEqTy1R dΓ (TySymm dA=) = TyEqTy2R dΓ dA=
TyEqTy1R dΓ (TyTran _ dA= dB=) = TyEqTy1R dΓ dA=
TyEqTy1R dΓ UUCong = UU
TyEqTy1R dΓ (ElCong dv=) = El (TmEqTm1R dΓ dv=) 
TyEqTy1R dΓ (PiCong dA dA= dB=) = Pi dA (TyEqTy1R (dΓ , dA) dB=)

TyEqTy2R dΓ (TySymm dA=) = TyEqTy1R dΓ dA=
TyEqTy2R dΓ (TyTran dB dA= dB=) = TyEqTy2R dΓ dB=
TyEqTy2R dΓ UUCong = UU
TyEqTy2R dΓ (ElCong dv=) = El (TmEqTm2R dΓ dv=)
TyEqTy2R dΓ (PiCong dA dA= dB=) = Pi (TyEqTy2R dΓ dA=) (ConvTy' (TyEqTy2R (dΓ , (TyEqTy1R dΓ dA=)) dB=) ((CtxReflR dΓ) , dA , TyEqTy2R dΓ dA= , dA= , dA=))

TmEqTm1R dΓ (TmSymm du=) = TmEqTm2R dΓ du= 
TmEqTm1R dΓ (TmTran _ du= dv=) = TmEqTm1R dΓ du=
TmEqTm1R dΓ (ConvEq dA du= dA=) = Conv dA (TmEqTm1R dΓ du=) dA=
TmEqTm1R dΓ (VarLastCong dA) = VarLast dA
TmEqTm1R (dΓ , dA) (VarPrevCong dA' dk=) = VarPrev dA' (TmEqTm1R dΓ dk=)
TmEqTm1R dΓ (LamCong dA dA= dB= du=) = Lam (TyEqTy1R dΓ dA=) (TyEqTy1R (dΓ , dA) dB=) (TmEqTm1R (dΓ , dA) du=)
TmEqTm1R dΓ (AppCong dA dA= dB= df= da=) = App (TyEqTy1R dΓ dA=) (TyEqTy1R (dΓ , dA) dB=) (TmEqTm1R dΓ df=) (TmEqTm1R dΓ da=)
TmEqTm1R dΓ (BetaPi dA dB du da) = App dA dB (Lam dA dB du) da
TmEqTm1R dΓ (EtaPi dA dB df) = df

TmEqTm2R dΓ (TmSymm du=) = TmEqTm1R dΓ du=
TmEqTm2R dΓ (TmTran _ du= dv=) = TmEqTm2R dΓ dv=
TmEqTm2R dΓ (ConvEq dA du= dA=) = Conv dA (TmEqTm2R dΓ du=) dA=
TmEqTm2R dΓ (VarLastCong dA) = VarLast dA
TmEqTm2R (dΓ , dA) (VarPrevCong dA' dk=) = VarPrev dA' (TmEqTm2R dΓ dk=)
TmEqTm2R dΓ (LamCong dA dA= dB= du=) = 
  Conv (Pi (TyEqTy2R dΓ dA=)
           (ConvTy' (TyEqTy2R (dΓ , (TyEqTy1R dΓ dA=)) dB=) ((CtxReflR dΓ) , dA , TyEqTy2R dΓ dA= , dA= , dA=)))
       (Lam (TyEqTy2R dΓ dA=)
            (ConvTy' (TyEqTy2R (dΓ , TyEqTy1R dΓ dA=) dB=) (CtxReflR dΓ , dA , TyEqTy2R dΓ dA= , dA= , dA=))
            (ConvTm' (Conv (TyEqTy1R (dΓ , dA) dB=) (TmEqTm2R (dΓ , dA) du=) dB=) (CtxReflR dΓ , dA , TyEqTy2R dΓ dA= , dA= , dA=)))
       (PiCong (TyEqTy2R dΓ dA=)
               (TySymm dA=)
               (ConvTyEq' (TySymm dB=) (CtxReflR dΓ , dA , ConvTy' (TyEqTy2R dΓ dA=) (CtxReflR dΓ) , dA= , dA=)))
TmEqTm2R dΓ (AppCong dA dA= dB= df= da=) =
  Conv (SubstTyR (TyEqTy2R (dΓ , dA) dB=) (idMorDerivableR dΓ , Conv dA (TmEqTm2R dΓ da=) (congTyEqR! reflR ([idMor]TyR _) (TyRefl' dA))))
       (App (TyEqTy2R dΓ dA=)
            (ConvTy' (TyEqTy2R (dΓ , TyEqTy1R dΓ dA=) dB=) (CtxReflR dΓ , dA , TyEqTy2R dΓ dA= , dA= , dA=))
            (Conv (Pi dA (TyEqTy1R (dΓ , dA) dB=)) (TmEqTm2R dΓ df=) (PiCong dA dA= dB=))
            (Conv dA (TmEqTm2R dΓ da=) dA=))
       (TySymm (SubstTyFullEqR (TyEqTy2R (dΓ , dA) dB=)
                              (idMorDerivableR dΓ , congTmR! ([idMor]TyR _) reflR (TmEqTm1R dΓ da=))
                              dB=
                              (MorReflR (idMorDerivableR dΓ) , congTmEqTyR! ([idMor]TyR _) da=)))
TmEqTm2R dΓ (BetaPi dA dB du da) = SubstTmR du (idMorDerivableR dΓ , congTmR! ([idMor]TyR _) reflR da)
TmEqTm2R dΓ (EtaPi dA dB df) = Lam dA dB (congTmTyR (substTy-weakenTyR' R∙ [idMor]TyR _) (App (WeakTy' dA) (WeakTy' dB) (WeakTm' df) (VarLast dA)))


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
TmTyR dΓ (VarLast du) = WeakTy' du
TmTyR dΓ (VarPrev du du₁) = WeakTy' du
TmTyR dΓ (Conv du du₁ du₂) = TyEqTy2R dΓ du₂
-- TmTy dΓ UUUU = UU
-- TmTy dΓ (PiUU du du₁) = UU
TmTyR dΓ (Lam du du₁ du₂) = Pi du du₁
TmTyR dΓ (App {Γ = Γ} {A = A} du du₁ du₂ du₃) = SubstTyR {Δ = Γ , A} du₁ ((idMorDerivableR dΓ) , congTmTyR! ([idMor]TyR _) du₃) 

helper : {Γ : Ctx n} {A B : TyExpr n} {u : TmExpr n} → Derivation (Γ ⊢ u :> B) → ΣSS (TyExpr n) (λ A → ΣSS (TmExpr n) (λ u → Derivation (Γ ⊢ u :> A)))
helper {B = A} {u = u} (VarLast du) = A , u , {!VarLast du!}
helper (VarPrev du du₁) = {!!}
helper (Conv du du₁ du₂) = {!!}
helper (Lam du du₁ du₂) = {!!}
helper (App du du₁ du₂ du₃) = {!!}
