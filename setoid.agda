{-# OPTIONS --rewriting --prop --allow-unsolved-metas #-}
open import common renaming (Unit to metaUnit)
open import typetheoryexplicit
open import syntxexplicit
open import reflectionexplicit
open import rulesexplicit


private
  variable
    A B C : Set

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

-- Heterogeneous binary relations

REL : Set → Set → Set _
REL A B = A → B → Set

-- Homogeneous binary relations

Rel : Set → Set _
Rel A = REL A A

------------------------------------------------------------------------
-- Relationships between relations
------------------------------------------------------------------------

infixr 4 _⇒_

-- Implication/containment - could also be written _⊆_.

_⇒_ : REL A B → REL A B → Set
P ⇒ Q = ∀ {x y} → P x y → Q x y

Reflexive : Rel A → Set
Reflexive _∼_ = ∀ {x} → x ∼ x

-- Symmetry.

Symmetric : Rel A → Set
Symmetric _∼_ = ∀ {x} {y} → x ∼ y → y ∼ x

-- -- Transitivity.

Transitive : Rel A → Set
Transitive _∼_ = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

record IsEquivalence (_≈_ : Rel A) : Set where
  field
    reflexivity : Reflexive _≈_
    symmetry : Symmetric _≈_
    transitivity : Transitive _≈_

record Setoid : Set (lsuc lzero) where
  infix 4 _≈_
  field
    Carrier       : Set
    _≈_           : Rel Carrier
    isEquivalence : IsEquivalence _≈_

record TmFibgen (A : Set) (B : Set) : Set where
  constructor _<:_
  field
    Cont : A
    Tm : B

record TyFibgen (A : Set) (B : Set) : Set where
  constructor _<:_
  field
    Cont : A
    Ty : B

infix 6 _<:_
TmFib : (n : ℕ) → Set
TmFib n = TmFibgen (Ctx n) (TmExpr n)

TyFib : (n : ℕ) → Set
TyFib n = TyFibgen (Ctx n) (TyExpr n)
-- TmFib : {n : ℕ} → Set
-- TmFib = ΣSS (TyExpr n) TmFam where
--       TmFam : {n : ℕ} → TyExpr n → Set
--       TmFam A = TmExpr n

open Setoid public

infix 4 _∼Ctx_
infix 4 _∼Ty_
infix 4 _∼Tm_

data _∼Ctx_ : {n : ℕ} → Ctx n → Ctx n → Set

data _∼Tm_ : {n : ℕ} → TmFib n → TmFib n → Set

data _∼Ty_ : TyFib n → TyFib n → Set where
  ttuu : {Γ Γ' : Ctx n} → Γ ∼Ctx Γ' → (Γ <: uu) ∼Ty (Γ' <: uu)
  ttel : {Γ Γ' : Ctx n} {v : TmExpr n} → {u : TmExpr n} → Γ ∼Ctx Γ' → (Γ <: v) ∼Tm (Γ <: u) → (Γ <: el v) ∼Ty (Γ <: el u)
  ttpi : {Γ Γ' : Ctx n} {A A₁ : TyExpr n} {B B₁ : TyExpr (suc n)} → Γ ∼Ctx Γ' → (Γ <: A) ∼Ty (Γ' <: A₁) → ((Γ , A) <: B) ∼Ty ((Γ' , A₁) <: B₁) → (Γ <: (pi A B)) ∼Ty (Γ' <: (pi A₁ B₁))

data _∼Tm_ where 
  ttvar : {k : Fin n} {Γ Γ' : Ctx n} → Γ ∼Ctx Γ' → (Γ <: var k) ∼Tm (Γ' <: (var k))
  ttlam : {Γ Γ' : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u v : TmExpr (suc n)} → Γ ∼Ctx Γ' → (Γ <: A) ∼Ty (Γ' <: A') → ((Γ , A) <: B) ∼Ty (Γ' , A') <: B' → (Γ , A) <: u ∼Tm (Γ' , A') <: v → Γ <: (lam A B u) ∼Tm Γ' <: (lam A' B' v)
  ttapp : {Γ Γ' : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n} → Γ ∼Ctx Γ' → Γ <: A ∼Ty Γ' <: A' → (Γ , A) <: B ∼Ty (Γ' , A') <: B' → Γ <: f ∼Tm Γ' <: f' → Γ <: a ∼Tm Γ' <: a' → Γ <: app A B f a ∼Tm Γ' <: app A' B' f' a'
  ttcoerc : {Γ Γ' : Ctx n} {A B : TyExpr n} {u v : TmExpr n} → Γ ∼Ctx Γ' → Γ <: u ∼Tm Γ' <: v → Γ <: (coerc A B u) ∼Tm Γ' <: (coerc A B v)
  ttrefl : {Γ Γ' : Ctx n} {u v : TmExpr n} → Γ ∼Ctx Γ' → Γ <: u ∼Tm Γ' <: v → Γ <: u ∼Tm Γ' <: coerc (getTy Γ' v) (getTy Γ' v) v
  ttrefl! : {Γ Γ' : Ctx n} {u v : TmExpr n} → Γ ∼Ctx Γ' → Γ <: u ∼Tm Γ' <: v → Γ <: coerc (getTy Γ u) (getTy Γ u) u ∼Tm Γ' <: v


data _∼Ctx_ where
  tt◇ : ◇ ∼Ctx ◇
  ttCtx : {n : ℕ} {Γ Γ' : Ctx n} {A A' : TyExpr n} → Γ ∼Ctx Γ' → Γ <: A ∼Ty Γ' <: A' → (Γ , A) ∼Ctx (Γ' , A')

{- with this extrem strict relation (almost as strict as normal equality) the typings are not effected -}
data _∼Jdg_ : Judgment → Judgment → Set where
  ttTy : {n : ℕ} {Γ Γ' : Ctx n} {A A' : TyExpr n} → Γ <: A ∼Ty Γ' <: A' → (Γ ⊢ A) ∼Jdg (Γ' ⊢ A')
  ttTm : {n : ℕ} {Γ Γ' : Ctx n} {u v : TmExpr n} {A A' : TyExpr n} → Γ <: u ∼Tm Γ' <: v
    → Γ <: A ∼Ty Γ' <: A' → (Γ ⊢ u :> A) ∼Jdg (Γ' ⊢ coerc (getTy Γ' v) A' v :> A')
  ttTmTriv : {n : ℕ} {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n} → Γ <: u ∼Tm Γ <: v → (_⊢_:>_ Γ u A) ∼Jdg (Γ ⊢ v :> A)
  ttTyEq : {n : ℕ} {Γ Γ' : Ctx n} {A A' B B' : TyExpr n} → Γ <: A ∼Ty Γ' <: A' → Γ <: B ∼Ty Γ' <: B' → (Γ ⊢ A == B) ∼Jdg (Γ ⊢ A == B)
  ttTmEq : {n : ℕ} {Γ Γ' : Ctx n} {A A' : TyExpr n} {u u' v v' : TmExpr n} → Γ <: u ∼Tm Γ' <: u' → Γ <: v ∼Tm Γ <: v' → Γ <: A ∼Ty Γ' <: A' → (Γ ⊢ u == v :> A) ∼Jdg (Γ ⊢ coerc (getTy Γ' v') A' u' == coerc (getTy Γ' v') A' v' :> A')

Der∼ : {j j' : Judgment} → j ∼Jdg j' → Derivable j → Derivable j'
Der∼ (ttTy (ttuu x)) UU = UU
Der∼ (ttTy (ttel x x₁)) (El dj) = El (Der∼ (ttTmTriv x₁) dj)
Der∼ (ttTy (ttpi x x₁ x₂)) (Pi dj dj₁) = Pi (Der∼ (ttTy x₁) dj) (Der∼ (ttTy x₂) dj₁)
Der∼ {j} {j'} (ttTm {Γ} {Γ'} {u} {v} {A} {A'} a b) (VarLast dj) = {!!}
Der∼ (ttTm x y) (VarPrev dj dj₁) = {!!}
Der∼ (ttTm x y) (Conv dj dj₁ dj₂ dj₃) = {!!}
Der∼ (ttTm x y) (Lam dj dj₁ dj₂) = {!!}
Der∼ (ttTm x y) (App dj dj₁ dj₂ dj₃) = {!!}
Der∼ (ttTmTriv x) dj = {!!}
Der∼ (ttTyEq x x₁) dj = {!!}
Der∼ (ttTmEq x x₁ x₂) dj = {!!}

isequivTm : {n : ℕ} → IsEquivalence (_∼Tm_ {n})
isequivTy : {n : ℕ} → IsEquivalence (_∼Ty_ {n})
isequivCtx : {n : ℕ} → IsEquivalence (_∼Ctx_ {n})
isequivJdg : {n : ℕ} → IsEquivalence (_∼Jdg_ )

isequivTy = {!!}
isequivCtx = {!!}
isequivTm = {!!}
isequivJdg = {!!}

TypeSetoid : {n : ℕ} → Setoid
TypeSetoid {n} = record { Carrier = TyExpr n ; _≈_ = relation; isEquivalence = equiv}
  where
  relation = {!!}
  equiv = {!!}
-- Rel : {ℓ : Level} (A : Set ℓ) → Set (lsuc lzero ⊔ ℓ)
-- Rel A = A → A → Prop
-- 
-- Reflexive : {A : Set} → Rel A → Set
-- Reflexive _∼_ = ∀ {x} → x ∼ x
-- 
-- Symmetric : {A : Set} → Rel A → Set
-- Symmetric _∼_ = 

{- Term definition with type adaptions, I think this might not work since a relation that changes the type of a term cannot be respected by judgmental equality -}

-- data _∼Ty_ : TyFib n → TyFib n → Set where
--   ttuu : {Γ Γ' : Ctx n} → Γ ∼Ctx Γ' → (Γ <: uu) ∼Ty (Γ' <: uu)
--   ttel : {Γ Γ' : Ctx n} {v : TmExpr n} → {u : TmExpr n} → Γ ∼Ctx Γ' → (Γ <: v) ∼Tm (Γ <: u) → (Γ <: el v) ∼Ty (Γ <: el u)
--   ttpi : {Γ Γ' : Ctx n} {A A₁ : TyExpr n} {B B₁ : TyExpr (suc n)} → Γ ∼Ctx Γ' → (Γ <: A) ∼Ty (Γ' <: A₁) → ((Γ , A) <: B) ∼Ty ((Γ' , A₁) <: B₁) → (Γ <: (pi A B)) ∼Ty (Γ' <: (pi A₁ B₁))

-- data _∼Tm_ where 
--   ttvar : {k : Fin n} {Γ Γ' : Ctx n} → Γ ∼Ctx Γ' → (Γ <: var k) ∼Tm (Γ' <: (var k))
--   ttlam : {Γ Γ' : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u v : TmExpr (suc n)} → Γ ∼Ctx Γ' → (Γ <: A) ∼Ty (Γ' <: A') → ((Γ , A) <: B) ∼Ty (Γ' , A') <: B' → (Γ , A) <: u ∼Tm (Γ' , A') <: v → Γ <: (lam A B u) ∼Tm Γ' <: (lam A' B' v)
--   ttapp : {Γ Γ' : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n} → Γ ∼Ctx Γ' → Γ <: A ∼Ty Γ' <: A' → (Γ , A) <: B ∼Ty (Γ' , A') <: B' → Γ <: f ∼Tm Γ' <: f' → Γ <: a ∼Tm Γ' <: a' → Γ <: app A B f a ∼Tm Γ' <: app A' B' f' a'
--   ttcoerc : {Γ Γ' : Ctx n} {A B : TyExpr n} {u v : TmExpr n} → Γ ∼Ctx Γ' → Γ <: u ∼Tm Γ' <: v → Γ <: (coerc A B u) ∼Tm Γ' <: (coerc A B v)
--   ttrefl : {Γ Γ' : Ctx n} {u v : TmExpr n} → Γ ∼Ctx Γ' → Γ <: u ∼Tm Γ' <: v → Γ <: u ∼Tm Γ' <: coerc (getTy Γ' v) (getTy Γ' v) v
--   ttrefl! : {Γ Γ' : Ctx n} {u v : TmExpr n} → Γ ∼Ctx Γ' → Γ <: u ∼Tm Γ' <: v → Γ <: coerc (getTy Γ u) (getTy Γ u) u ∼Tm Γ' <: v
-- 
-- data _∼Ctx_ where
--   tt◇ : ◇ ∼Ctx ◇
--   ttCtx : {n : ℕ} {Γ Γ' : Ctx n} {A A' : TyExpr n} → Γ ∼Ctx Γ' → Γ <: A ∼Ty Γ' <: A' → (Γ , A) ∼Ctx (Γ' , A')
-- 
-- data _∼Jdg_ : Judgment → Judgment → Set where
--   ttTy : {n : ℕ} {Γ Γ' : Ctx n} {A A' : TyExpr n} → Γ ∼Ctx Γ' → (Γ <: A ∼Ty Γ' <: A') → (Γ ⊢ A) ∼Jdg (Γ' ⊢ A')
--   ttTm : {n : ℕ} {Γ Γ' : Ctx n} {u v : TmExpr n} → Γ ∼Ctx Γ' → Γ <: u ∼Tm Γ' <: v → (Γ ⊢ u :> getTy Γ u) ∼Jdg (Γ' ⊢ v :> getTy Γ' v)
--   ttTyEq : {n : ℕ} (Γ Γ' : Ctx n} {A A' B B' : TyExpr n} → Γ ∼Ctx Γ' → Γ <: A ∼Ty Γ' <: A' → Γ <: B ∼Ty Γ' <: B' → (Γ ⊢ A == B) ∼Jdg (Γ ⊢ A' == B')
--   ttTmEq : {n : ℕ} {Γ Γ' : Ctx n} {u u' v v' : TmExpr n} → Γ ∼Ctx Γ' → Γ <: u ∼Tm Γ' <: u' → Γ <: u' ∼Tm Γ <: v' → (Γ ⊢ u == v :> getTy Γ u) ∼Jdg (Γ ⊢ u' == v' :> getTy Γ' u')

---------------------------------------
--              STRICT VERSIION
---------------------------------------
-- data _∼Tm_ where 
--   ttvar : {k : Fin n} {Γ Γ' : Ctx n} → Γ ∼Ctx Γ' → (Γ <: var k) ∼Tm (Γ' <: (var k))
--   ttlam : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u v : TmExpr (suc n)} → (Γ , A) <: u ∼Tm (Γ , A) <: v → Γ <: (lam A B u) ∼Tm Γ <: (lam A B v)
--   ttapp : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f f' a a' : TmExpr n} → Γ <: f ∼Tm Γ <: f' → Γ <: a ∼Tm Γ <: a' → Γ <: app A B f a ∼Tm Γ <: app A B f' a'
--   ttcoerc : {Γ : Ctx n} {A B : TyExpr n} {u v : TmExpr n} → Γ <: u ∼Tm Γ <: v → Γ <: (coerc A B u) ∼Tm Γ <: (coerc A B v)
--   ttrefl : {Γ : Ctx n} {u v : TmExpr n} → Γ <: u ∼Tm Γ <: v → Γ <: u ∼Tm Γ <: coerc (getTy Γ v) (getTy Γ v) v
--   ttrefl! : {Γ : Ctx n} {u v : TmExpr n}  → Γ <: u ∼Tm Γ <: v → Γ <: coerc (getTy Γ u) (getTy Γ u) u ∼Tm Γ <: v

{- with this extrem strict relation (almost as strict as normal equality) the typings are not effected -}
-- data _∼Jdg_ : Judgment → Judgment → Set where
--   ttTy : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} → (Γ ⊢ A) ∼Jdg (Γ ⊢ A)
--   ttTm : {n : ℕ} {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n} → Γ <: u ∼Tm Γ <: v → (_⊢_:>_ Γ u A) ∼Jdg (_⊢_:>_ Γ v A)
--   ttTyEq : {n : ℕ} {Γ : Ctx n} {A B : TyExpr n} → (Γ ⊢ A == B) ∼Jdg (Γ ⊢ A == B)
--   ttTmEq : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {u u' v v' : TmExpr n} → Γ <: u ∼Tm Γ <: u' → Γ <: v ∼Tm Γ <: v' → (_⊢_==_:>_ Γ u v A) ∼Jdg (_⊢_==_:>_ Γ u' v' A)
