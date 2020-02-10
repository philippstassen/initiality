{-# OPTIONS --rewriting --prop --without-K -v tc.unquote:10 #-}

open import common renaming (Unit to metaUnit) renaming (UnitR to metaUnitR)
open import typetheory
open import syntx
open import reflection
open import rules

 {- some syntx.agda functions also for proof relevant ≡R are needed -}

Mor+=R : {δ δ' : Mor n m} {u u' : TmExpr n} → δ ≡R δ' → u ≡R u' → Mor._,_ δ u ≡R (δ' , u')
Mor+=R reflR reflR = reflR

weakenTyCommutes' : {n : ℕ} (k : Fin (suc n)) (A : TyExpr (0 + n)) → weakenTy' (prev^ 0 last) (weakenTy' (prev^ 0 k) A) ≡R weakenTy' (prev^ (suc 0) k) (weakenTy' (prev^ 0 last) A)

weakenTyCommutes' k A = (Sig-Fin-leftTy k A R∙ sndΣSSℕR (weakenTyCommutessig (Fin-Bounded k) _ A reflR) R∙ Sig-Fin-rightTy k A)

weakenTmCommutesR : {n : ℕ} (k : Fin (suc n)) (A : TmExpr (0 + n)) → weakenTm' (prev^ 0 last) (weakenTm' (prev^ 0 k) A) ≡R weakenTm' (prev^ (suc 0) k) (weakenTm' (prev^ 0 last) A)
weakenTmCommutesR k A = (Sig-Fin-leftTm k A R∙ sndΣSSℕR (weakenTmCommutessig (Fin-Bounded k) _ A reflR) R∙ Sig-Fin-rightTm k A)

weakenTyCommutesprev1R : {n : ℕ} (k : Fin (suc n)) (A : TyExpr (1 + n)) → weakenTy' (prev^ 1 last) (weakenTy' (prev^ 1 k) A) ≡R weakenTy' (prev^ (suc 1) k) (weakenTy' (prev^ 1 last) A)
weakenTyCommutesprev1R k A = (Sig-Fin-leftTyprev1 k A R∙ sndΣSSℕR (weakenTyCommutessigprev1 (Fin-Bounded k) _ A reflR) R∙ Sig-Fin-rightTyprev1 k A)

weakenMorCommutesR : (k : Fin (suc n)) (δ : Mor n m) → weakenMor' last (weakenMor' k δ) ≡R weakenMor' (prev k) (weakenMor' last δ)
weakenMorCommutesR {m = zero} k ◇ = reflR
weakenMorCommutesR {m = suc m} k (δ , u) = Mor+=R (weakenMorCommutesR k δ) (weakenTmCommutesR k u)
-- rewrite weakenMorCommutesR k δ | weakenTmCommutesR k u = reflR

weakenCommutesInsertR : (k : Fin (suc m)) (l : Fin (suc n)) (u : TmExpr n) (δ : Mor n m) → insertMor k (weakenTm' l u) (weakenMor' l δ) ≡R weakenMor' l (insertMor k u δ)
weakenCommutesInsertR last l u ◇ = reflR
weakenCommutesInsertR (prev ()) l u ◇ 
weakenCommutesInsertR last l u (δ , u') = reflR
weakenCommutesInsertR (prev k) l u (δ , u') = apR (λ z → z , _) (weakenCommutesInsertR k l u δ)

insertIdMorR : (k  : Fin (suc n)) → insertMor k (var k) (weakenMor' k (idMor n)) ≡R idMor (suc n)
insertIdMorR last = reflR
insertIdMorR {n = zero} (prev ()) 
insertIdMorR {n = suc n} (prev k) = Mor+=R ((apR (λ z → insertMor k (var (prev k)) z) (!R (weakenMorCommutesR k (idMor n))) R∙ weakenCommutesInsertR k last (var k) (weakenMor' k (idMor n))) R∙ apR weakenMor (insertIdMorR k))  reflR


{- Weakening commutes with total substitution -}

weakenMorCommutesLemmaTyR : (A : TyExpr (suc m)) (δ : Mor n m) (k : Fin (suc n))
                           → A [ weakenMor' (prev k) (weakenMor+ δ) ]Ty ≡R A [ weakenMor+ (weakenMor' k δ) ]Ty
weakenMorCommutesLemmaTyR A δ k = apR (λ z → A [ z , var last ]Ty) (!R (weakenMorCommutesR k δ))

weakenMorCommutesLemmaTyR2 : (A : TyExpr (suc (suc m))) (δ : Mor n m) (k : Fin (suc n))
                            → A [ weakenMor' (prev (prev k)) (weakenMor+^ 2 δ) ]Ty ≡R A [ weakenMor+^ 2 (weakenMor' k δ) ]Ty
weakenMorCommutesLemmaTyR2 A δ k = weakenMorCommutesLemmaTyR A (weakenMor+ δ) (prev k) R∙ apR (λ z → A [ weakenMor+ (z , var last) ]Ty) (!R (weakenMorCommutesR k δ))

weakenMorCommutesLemmaTyR3 : (A : TyExpr (suc (suc (suc m)))) (δ : Mor n m) (k : Fin (suc n))
                            → A [ weakenMor' (prev (prev (prev k))) (weakenMor+^ 3 δ) ]Ty ≡R A [ weakenMor+^ 3 (weakenMor' k δ) ]Ty
weakenMorCommutesLemmaTyR3 A δ k = weakenMorCommutesLemmaTyR2 A (weakenMor+ δ) (prev k) R∙ apR (λ z → A [ weakenMor+^ 2 (z , var last) ]Ty) (!R (weakenMorCommutesR k δ))

weakenMorCommutesLemmaTmR : (u : TmExpr (suc m)) (δ : Mor n m) (k : Fin (suc n)) → u [ weakenMor' (prev k) (weakenMor+ δ) ]Tm ≡R
                                                                                  u [ weakenMor+ (weakenMor' k δ) ]Tm
weakenMorCommutesLemmaTmR u δ k = apR (λ z → u [ z , var last ]Tm) (!R (weakenMorCommutesR k δ))

weakenMorCommutesLemmaTmR2 : (u : TmExpr (suc (suc m))) (δ : Mor n m) (k : Fin (suc n))
                            → u [ weakenMor' (prev (prev k)) (weakenMor+^ 2 δ) ]Tm ≡R u [ weakenMor+^ 2 (weakenMor' k δ) ]Tm
weakenMorCommutesLemmaTmR2 u δ k = weakenMorCommutesLemmaTmR u (weakenMor+ δ) (prev k) R∙ apR (λ z → u [ weakenMor+ (z , var last) ]Tm) (!R (weakenMorCommutesR k δ))

weakenMorCommutesLemmaTmR3 : (u : TmExpr (suc (suc (suc m)))) (δ : Mor n m) (k : Fin (suc n))
                            → u [ weakenMor' (prev (prev (prev k))) (weakenMor+^ 3 δ) ]Tm ≡R u [ weakenMor+^ 3 (weakenMor' k δ) ]Tm
weakenMorCommutesLemmaTmR3 u δ k = weakenMorCommutesLemmaTmR2 u (weakenMor+ δ) (prev k) R∙ apR (λ z → u [ weakenMor+^ 2 (z , var last) ]Tm) (!R (weakenMorCommutesR k δ))

generate-weaken[]R : Name → Name → Name → TC ⊤
generate-weaken[]R weaken[]TyR weaken[]TmR weaken[]VarR =
  generateClausewise weaken[]TyR weaken[]TmR
    [] (earg (var "δ") ∷ earg (var "k") ∷ [])
    (λ l → def weaken[]VarR (earg (var 2 []) ∷ earg (var 1 []) ∷ earg (var 0 []) ∷ []))
    (apRify thing)

   where

    thing : Name → ℕ → ℕ → Arg Term
    thing T n 0 =
      earg (def (Ty?Tm T weaken[]TyR weaken[]TmR) (earg (var (n + 2) []) ∷ earg (var 1 []) ∷ earg (var 0 []) ∷ []))
    thing T n 1 =
      earg (def (quote _R∙_) (earg (def (Ty?Tm T weaken[]TyR weaken[]TmR)
                                         (earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+^) (earg (lit (nat 1)) ∷ earg (var 1 []) ∷ []))
                                        ∷ earg (iterate 1 (con (quote prev)) (var 0 [])) ∷ []))
                           ∷ earg (def (Ty?Tm T (quote weakenMorCommutesLemmaTyR) (quote weakenMorCommutesLemmaTmR))
                                         (earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ []))
    thing T n 2 =
      earg (def (quote _∙_) (earg (def (Ty?Tm T weaken[]TyR weaken[]TmR)
                                         (earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+^) (earg (lit (nat 2)) ∷ earg (var 1 []) ∷ []))
                                        ∷ earg (iterate 2 (con (quote prev)) (var 0 [])) ∷ []))
                           ∷ earg (def (Ty?Tm T (quote weakenMorCommutesLemmaTyR2) (quote weakenMorCommutesLemmaTmR2))
                                         (earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ []))
    thing T n 3 =
      earg (def (quote _∙_) (earg (def (Ty?Tm T weaken[]TyR weaken[]TmR)
                                         (earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+^) (earg (lit (nat 3)) ∷ earg (var 1 []) ∷ []))
                                        ∷ earg (iterate 3 (con (quote prev)) (var 0 [])) ∷ []))
                           ∷ earg (def (Ty?Tm T (quote weakenMorCommutesLemmaTyR3) (quote weakenMorCommutesLemmaTmR3))
                                         (earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ []))
    thing T n _ = earg unknown

weaken[]TyR : (A : TyExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTy' k (A [ δ ]Ty) ≡R A [ weakenMor' k δ ]Ty
weaken[]TmR : (u : TmExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTm' k (u [ δ ]Tm) ≡R u [ weakenMor' k δ ]Tm

weaken[]VarR : (x : Fin n) (δ : Mor m n) (k : Fin (suc m)) → weakenTm' k (x [ δ ]Var) ≡R x [ weakenMor' k δ ]Var
weaken[]VarR last (δ , u) k = reflR
weaken[]VarR (prev x) (δ , u) k = weaken[]VarR x δ k

unquoteDef weaken[]TyR weaken[]TmR = generate-weaken[]R weaken[]TyR weaken[]TmR (quote weaken[]VarR)

weaken[]MorR : (θ : Mor n k) (δ : Mor m n) (k : Fin (suc m)) → weakenMor' k (θ [ δ ]Mor) ≡R (θ [ weakenMor' k δ ]Mor)

weaken[]MorR ◇ _ k = reflR
weaken[]MorR (θ , u) δ k = Mor+=R (weaken[]MorR θ δ k) (weaken[]TmR u δ k)
-- rewrite weaken[]MorR θ δ k | weaken[]Tm u δ k = reflR


{- proof relevant version Substituting a morphism where a term is inserted into a type/term/morphism that is weakened at that point does nothing -}

weakenTyInsertLemmaR : (k : Fin (suc n)) (A : TyExpr (suc n)) (δ : Mor m n) (t : TmExpr m)
  → weakenTy' (prev k) A [ weakenMor+ (insertMor k t δ) ]Ty ≡R
    weakenTy' (prev k) A [ insertMor k (weakenTm t) (weakenMor δ) , var last ]Ty
weakenTyInsertLemmaR k A δ t = apR (λ z → weakenTy' (prev k) A [ z , var last ]Ty) (!R (weakenCommutesInsertR k last t δ))

weakenTyInsertLemmaR2 : (k : Fin (suc n)) (A : TyExpr (suc (suc n))) (δ : Mor m n) (t : TmExpr m)
  → weakenTy' (prev (prev k)) A [ weakenMor+^ 2 (insertMor k t δ) ]Ty ≡R
    weakenTy' (prev (prev k)) A [ insertMor (prev (prev k)) (weakenTm (weakenTm t)) (weakenMor+^ 2 δ) ]Ty
weakenTyInsertLemmaR2 k A δ t = apR (λ z → weakenTy' (prev (prev k)) A [ z , var last ]Ty) (apR (λ z → weakenMor z , var (prev last)) (!R (weakenCommutesInsertR k last t δ)) R∙ !R (weakenCommutesInsertR (prev k) last (weakenTm t) (weakenMor+ δ)))

weakenTyInsertLemmaR3 : (k : Fin (suc n)) (A : TyExpr (suc (suc (suc n)))) (δ : Mor m n) (t : TmExpr m)
  → weakenTy' (prev (prev (prev k))) A [ weakenMor+^ 3 (insertMor k t δ) ]Ty ≡R
    weakenTy' (prev (prev (prev k))) A [ insertMor (prev (prev (prev k))) (weakenTm (weakenTm (weakenTm t))) (weakenMor+^ 3 δ) ]Ty
weakenTyInsertLemmaR3 k A δ t = apR (λ z → weakenTy' (prev (prev (prev k))) A [ weakenMor+ (weakenMor+ (z , var last))]Ty) (!R (weakenCommutesInsertR k last t δ))
                               R∙ weakenTyInsertLemmaR2 (prev k) A (weakenMor+ δ) (weakenTm t)

weakenTmInsertLemmaR : (k : Fin (suc n)) (u : TmExpr (suc n)) (δ : Mor m n) (t : TmExpr m)
  → weakenTm' (prev k) u [ weakenMor+ (insertMor k t δ) ]Tm ≡R
    weakenTm' (prev k) u [ insertMor k (weakenTm t) (weakenMor δ) , var last ]Tm
weakenTmInsertLemmaR k u δ t = apR (λ z → weakenTm' (prev k) u [ z , var last ]Tm) (!R (weakenCommutesInsertR k last t δ))

weakenTmInsertLemmaR2 : (k : Fin (suc n)) (u : TmExpr (suc (suc n))) (δ : Mor m n) (t : TmExpr m)
  → weakenTm' (prev (prev k)) u [ weakenMor+^ 2 (insertMor k t δ) ]Tm ≡R
    weakenTm' (prev (prev k)) u [ insertMor (prev (prev k)) (weakenTm (weakenTm t)) (weakenMor+^ 2 δ) ]Tm
weakenTmInsertLemmaR2 k u δ t = apR (λ z → weakenTm' (prev (prev k)) u [ z , var last ]Tm) (apR (λ z → weakenMor z , var (prev last)) (!R (weakenCommutesInsertR k last t δ)) R∙ !R (weakenCommutesInsertR (prev k) last (weakenTm t) (weakenMor+ δ)))

weakenTmInsertLemmaR3 : (k : Fin (suc n)) (u : TmExpr (suc (suc (suc n)))) (δ : Mor m n) (t : TmExpr m)
  → weakenTm' (prev (prev (prev k))) u [ weakenMor+^ 3 (insertMor k t δ) ]Tm ≡R
    weakenTm' (prev (prev (prev k))) u [ insertMor (prev (prev (prev k))) (weakenTm (weakenTm (weakenTm t))) (weakenMor+^ 3 δ) ]Tm
weakenTmInsertLemmaR3 k u δ t = apR (λ z → weakenTm' (prev (prev (prev k))) u [ weakenMor+ (weakenMor+ (z , var last))]Tm) (!R (weakenCommutesInsertR k last t δ))
                               R∙ weakenTmInsertLemmaR2 (prev k) u (weakenMor+ δ) (weakenTm t)


generate-weakenInsertR : Name → Name → Name → TC ⊤
generate-weakenInsertR weakenInsertTy weakenInsertTm weakenInsertVar =
  generateClausewise weakenInsertTy weakenInsertTm
    (earg (var "k") ∷ []) (earg (var "δ") ∷ earg (var "t") ∷ [])
    (λ l → def weakenInsertVar (earg (var 3 []) ∷ earg (var 2 []) ∷ earg (var 1 []) ∷ earg (var 0 []) ∷ []))
    (λ l → apRify (thing l) l)

   where

    thing : ℕ → Name → ℕ → ℕ → Arg Term
    thing l T n 0 =
      earg (def (Ty?Tm T weakenInsertTy weakenInsertTm) (earg (var (l + 2) []) ∷ earg (var (n + 2) []) ∷ earg (var 1 []) ∷ earg (var 0 []) ∷ []))
    thing l T n 1 =
      earg (def (quote _R∙_) (earg (def (Ty?Tm T (quote weakenTyInsertLemmaR) (quote weakenTmInsertLemmaR))
                                         (earg (var (l + 2) [])
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ earg (def (Ty?Tm T weakenInsertTy weakenInsertTm)
                                         (earg (con (quote prev) (earg (var (l + 2) []) ∷ []))
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+) (earg (var 1 []) ∷ []))
                                        ∷ earg (def (quote weakenTm) (earg (var 0 []) ∷ [])) ∷ []))
                           ∷ []))
    thing l T n 2 =
      earg (def (quote _R∙_) (earg (def (Ty?Tm T (quote weakenTyInsertLemmaR2) (quote weakenTmInsertLemmaR2))
                                         (earg (var (l + 2) [])
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ earg (def (Ty?Tm T weakenInsertTy weakenInsertTm)
                                         (earg (iterate 2 (con (quote prev)) (var (l + 2) []))
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+^) (earg (lit (nat 2)) ∷ earg (var 1 []) ∷ []))
                                        ∷ earg (iterate 2 (def (quote weakenTm)) (var 0 [])) ∷ []))
                           ∷ []))
    thing l T n 3 =
      earg (def (quote _R∙_) (earg (def (Ty?Tm T (quote weakenTyInsertLemmaR3) (quote weakenTmInsertLemmaR3))
                                         (earg (var (l + 2) [])
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ earg (def (Ty?Tm T weakenInsertTy weakenInsertTm)
                                         (earg (iterate 3 (con (quote prev)) (var (l + 2) []))
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+^) (earg (lit (nat 3)) ∷ earg (var 1 []) ∷ []))
                                        ∷ earg (iterate 3 (def (quote weakenTm)) (var 0 [])) ∷ []))
                           ∷ []))
    thing l T n _ = earg unknown

weakenTyInsert'R : (k : Fin (suc m)) (A : TyExpr m) (δ : Mor n m) (t : TmExpr n) → weakenTy' k A [ insertMor k t δ ]Ty ≡R A [ δ ]Ty
weakenTmInsert'R : (k : Fin (suc m)) (u : TmExpr m) (δ : Mor n m) (t : TmExpr n) → weakenTm' k u [ insertMor k t δ ]Tm ≡R u [ δ ]Tm

weakenVarInsert'R : (k : Fin (suc m)) (x : Fin m) (δ : Mor n m) (t : TmExpr n) → (weakenVar' k x [ insertMor k t δ ]Var) ≡R (x [ δ ]Var)
weakenVarInsert'R last x δ t = reflR
weakenVarInsert'R (prev k) last (δ , u) t = reflR
weakenVarInsert'R (prev k) (prev x) (δ , u) t = weakenVarInsert'R k x δ t

unquoteDef weakenTyInsert'R weakenTmInsert'R = generate-weakenInsertR weakenTyInsert'R weakenTmInsert'R (quote weakenVarInsert'R)

weakenTyInsertR : (A : TyExpr m) (δ : Mor n m) (t : TmExpr n) → weakenTy A [ δ , t ]Ty ≡R A [ δ ]Ty
weakenTyInsertR A δ t = weakenTyInsert'R last A δ t

weakenTmInsertR : (u : TmExpr m) (δ : Mor n m) (t : TmExpr n) → weakenTm u [ δ , t ]Tm ≡R u [ δ ]Tm
weakenTmInsertR u δ t = weakenTmInsert'R last u δ t

weakenMorInsertR : (θ : Mor n m) (δ : Mor k n) (t : TmExpr k) →  weakenMor θ [ δ ,  t ]Mor ≡R θ [ δ ]Mor
weakenMorInsertR ◇ _ _ = reflR
weakenMorInsertR (θ , u) δ t = Mor+=R (weakenMorInsertR θ δ t) (weakenTmInsertR u δ t)
-- rewrite weakenMorInsertR θ δ t | weakenTmInsert u δ t = reflR


weakenTy-weakenTy' : {k : Fin (suc n)} {A : TyExpr n} → weakenTy' (prev k) (weakenTy A) ≡R weakenTy (weakenTy' k A)
weakenTy-weakenTy' = !R (weakenTyCommutes' _ _)

weakenTy-weakenTy1R : {k : Fin (suc n)} {A : TyExpr (1 + n)} → weakenTy' (prev (prev k)) (weakenTy' (prev last) A) ≡R weakenTy' (prev last) (weakenTy' (prev k) A)
weakenTy-weakenTy1R = !R (weakenTyCommutesprev1R _ _)

weakenTy-substTy' : {k : Fin (suc m)} {A : TyExpr (suc m)} {u : TmExpr m} → weakenTy' k (substTy A u) ≡R substTy (weakenTy' (prev k) A) (weakenTm' k u)
weakenTy-substTy' {k = k} {A} {u} =
  weaken[]TyR A _ _
  R∙ !R (weakenTyInsert'R (prev k) A _ (var k))
  R∙ apR (λ z → weakenTy' (prev k) A [ z , weakenTm' k u ]Ty)
       (insertIdMorR k)

weakenTm-substTmR : {k : Fin (suc m)} (t : TmExpr (suc m)) {u : TmExpr m} → weakenTm' k (substTm t u) ≡R substTm (weakenTm' (prev k) t) (weakenTm' k u)
weakenTm-substTmR {k = k} t {u} =
  weaken[]TmR t _ _
  R∙ !R (weakenTmInsert'R (prev k) t _ (var k))
  R∙ apR (λ z → weakenTm' (prev k) t [ z , weakenTm' k u ]Tm)
       (insertIdMorR k)

[weakenMor]MorR : (δ : Mor n m) (θ : Mor m l) → (weakenMor θ [ weakenMor+ δ ]Mor) ≡R weakenMor (θ [ δ ]Mor)
[weakenMor]TyR  : (δ : Mor n m) (C : TyExpr m) → (weakenTy C [ weakenMor+ δ ]Ty) ≡R weakenTy (C [ δ ]Ty)
[weakenMor]TmR  : (δ : Mor n m) (w : TmExpr m) → (weakenTm w [ weakenMor+ δ ]Tm) ≡R weakenTm (w [ δ ]Tm)

[weakenMor]MorR δ θ = weakenMorInsertR θ (weakenMor δ) (var last) R∙ !R (weaken[]MorR θ δ last)
[weakenMor]TyR δ C = weakenTyInsertR C (weakenMor δ) (var last) R∙ !R (weaken[]TyR C δ last)
[weakenMor]TmR δ w = weakenTmInsertR w (weakenMor δ) (var last) R∙ !R (weaken[]TmR w δ last)

[weakenMor+]Mor-auxR : (k : ℕ) {δ : Mor n m} {θ : Mor m l} → weakenMor+^ k θ [ weakenMor+^ k δ ]Mor ≡R weakenMor+^ k (θ [ δ ]Mor)
[weakenMor+]Mor-auxR zero = reflR
[weakenMor+]Mor-auxR (suc k) = apR (λ z → z , var last) ([weakenMor]MorR _ _ R∙ apR weakenMor ([weakenMor+]Mor-auxR k))

[weakenMor+]MorTyR : (k : ℕ) (B : TyExpr (k + l)) {δ : Mor n m} {θ : Mor m l} → B [ weakenMor+^ k θ [ weakenMor+^ k δ ]Mor ]Ty ≡R B [ weakenMor+^ k (θ [ δ ]Mor) ]Ty
[weakenMor+]MorTyR k B = apR (λ z → B [ z ]Ty) ([weakenMor+]Mor-auxR k)

[weakenMor+]MorTmR : (k : ℕ) (u : TmExpr (k + l)) {δ : Mor n m} {θ : Mor m l} → u [ weakenMor+^ k θ [ weakenMor+^ k δ ]Mor ]Tm ≡R u [ weakenMor+^ k (θ [ δ ]Mor) ]Tm
[weakenMor+]MorTmR k u = apR (λ z → u [ z ]Tm) ([weakenMor+]Mor-auxR k)


{- Substitution by the identity morphism does nothing -}

[idMor]TyR : (A : TyExpr n) → A [ idMor n ]Ty ≡R A
[idMor]TmR : (u : TmExpr n) → u [ idMor n ]Tm ≡R u
[idMor]VarR : (x : Fin n) → (var x) [ idMor n ]Tm ≡R var x

[idMor]VarR {n = zero} ()
[idMor]VarR {n = suc n} last = reflR
[idMor]VarR {n = suc n} (prev x) = !R (weaken[]TmR (var x) (idMor n) last) R∙ apR weakenTm ([idMor]VarR x)

unquoteDef [idMor]TyR [idMor]TmR =
  generateClausewise [idMor]TyR [idMor]TmR [] []
    (λ _ → def (quote [idMor]VarR) (earg (var 0 []) ∷ []))
    (apRify (λ T n _ → earg (def (Ty?Tm T [idMor]TyR [idMor]TmR) (earg (var n []) ∷ []))))

{- Substitution is associative -}

generate-assocR : Name → Name → Name → TC ⊤
generate-assocR []Ty-assocR []Tm-assocR []Var-assocR =
  generateClausewise []Ty-assocR []Tm-assocR
    (earg (var "θ") ∷ earg (var "δ") ∷ []) []
    (λ l → def []Var-assocR (earg (var (l + 1) []) ∷ earg (var l []) ∷ earg (var 0 []) ∷ []))
    (λ l → apRify (thing (earg (var (l + 1) [])) (earg (var l []))) l)

   where

    thing : Arg Term → Arg Term → Name → ℕ → ℕ → Arg Term
    thing δ θ T n 0 =
      earg (def (Ty?Tm T []Ty-assocR []Tm-assocR) (δ ∷ θ ∷ earg (var n []) ∷ []))
    thing (arg _ δ) (arg _ θ) T n k =
      earg (def (quote _R∙_) (earg (def (Ty?Tm T []Ty-assocR []Tm-assocR)
                                         (earg (iterate k (def (quote weakenMor+)) δ)
                                        ∷ earg (iterate k (def (quote weakenMor+)) θ)
                                        ∷ earg (var n []) ∷ []))
                           ∷ earg (def (Ty?Tm T (quote [weakenMor+]MorTyR) (quote [weakenMor+]MorTmR))
                                         (earg (lit (nat k)) ∷ earg (var n []) ∷ [])) ∷ []))

[]Ty-assocR : (δ : Mor n m) (θ : Mor m k) (A : TyExpr k) → (A [ θ ]Ty [ δ ]Ty) ≡R (A [ θ [ δ ]Mor ]Ty)
[]Tm-assocR : (δ : Mor n m) (θ : Mor m k) (u : TmExpr k) → u [ θ ]Tm [ δ ]Tm ≡R u [ θ [ δ ]Mor ]Tm

[]Var-assocR : (δ : Mor n m) (θ : Mor m k) (x : Fin k) → var x [ θ ]Tm [ δ ]Tm ≡R var x [ θ [ δ ]Mor ]Tm
[]Var-assocR δ (θ , v) last = reflR
[]Var-assocR δ (θ , v) (prev x) = []Var-assocR δ θ x

unquoteDef []Ty-assocR []Tm-assocR = generate-assocR []Ty-assocR []Tm-assocR (quote []Var-assocR)

[idMor]MorR : {n m : ℕ} (δ : Mor n m) → δ [ idMor n ]Mor ≡R δ
[idMor]MorR ◇ = reflR
[idMor]MorR (δ , u) = Mor+=R ([idMor]MorR δ) ([idMor]TmR u)
-- rewrite [idMor]MorR δ | [idMor]TmR u = refl

idMor[]MorR : (δ : Mor n m) → idMor m [ δ ]Mor ≡R δ

idMor[]MorR {m = zero} ◇ = reflR
idMor[]MorR {m = suc m} (δ , u) = Mor+=R (weakenMorInsertR (idMor m) δ u R∙ idMor[]MorR δ) reflR
-- rewrite weakenMorInsertR (idMor m) δ u | idMor[]MorR δ  = refl

{- Total substitution commutes with partial substitution -}

[]Ty-substTyR : {B : TyExpr (suc m)} {a : TmExpr m} {δ : Mor n m} → (substTy B a) [ δ ]Ty ≡R substTy (B [ weakenMor+ δ ]Ty) (a [ δ ]Tm)
[]Ty-substTyR {B = B} {a} {δ} = []Ty-assocR _ _ _ R∙ apR (λ z → B [ z , a [ δ ]Tm ]Ty) (idMor[]MorR δ R∙ !R ([idMor]MorR δ) R∙ !R (weakenMorInsertR _ _ _)) R∙ !R ([]Ty-assocR _ _ _)

[]Tm-substTmR : (u : TmExpr (suc m)) {a : TmExpr m} {δ : Mor n m} → (substTm u a) [ δ ]Tm ≡R substTm (u [ weakenMor+ δ ]Tm) (a [ δ ]Tm)
[]Tm-substTmR u {a} {δ} = []Tm-assocR _ _ u R∙ apR (λ z → u [ z , a [ δ ]Tm ]Tm) (idMor[]MorR δ R∙ !R ([idMor]MorR δ) R∙ !R (weakenMorInsertR _ _ _)) R∙ !R ([]Tm-assocR _ _ u)

{- more commuting -}

[]Ty-weakenTyR : {δ : Mor n m} {A : TyExpr m} → (weakenTy A [ weakenMor+ δ ]Ty) ≡R weakenTy (A [ δ ]Ty)
[]Ty-weakenTyR {A = A} = [weakenMor]TyR _ A

[]Ty-weakenTy1R : {δ : Mor n m} {A : TyExpr (suc m)} {u : TmExpr (suc (suc n))} {v : TmExpr (suc n)}
  → (weakenTy' (prev last) A [ (weakenMor (weakenMor δ) , u) , weakenTm' (prev last) v ]Ty) ≡R weakenTy' (prev last) (A [ weakenMor δ , v ]Ty)
[]Ty-weakenTy1R {δ = δ} {A} {u} {v} = weakenTyInsert'R (prev last) A (weakenMor (weakenMor δ) , _) u R∙ apR (λ z → A [ z , _ ]Ty) (weakenMorCommutesR last δ) R∙ !R (weaken[]TyR A (weakenMor δ , _) (prev last))

[]Tm-weakenTmR : {δ : Mor n m} (u : TmExpr m) → (weakenTm u [ weakenMor+ δ ]Tm) ≡R weakenTm (u [ δ ]Tm)
[]Tm-weakenTmR u = [weakenMor]TmR _ u

substTy-weakenTyR' : {k : Fin (suc m)} {A : TyExpr m} {δ : Mor n m} {t : TmExpr n} → weakenTy' k A [ insertMor k t δ ]Ty ≡R A [ δ ]Ty
substTy-weakenTyR' = weakenTyInsert'R _ _ _ _

substTy-weakenTyR : {A : TyExpr n} {u : TmExpr n} → substTy (weakenTy A) u ≡R A
substTy-weakenTyR {A = A} {u = u} =  (weakenTyInsertR A (idMor _) u ) R∙ [idMor]TyR _
