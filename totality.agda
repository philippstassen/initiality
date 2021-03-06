{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat

module _ (sC : StructuredCCat) where

open StructuredCCat sC
open CCat+ ccat renaming (Mor to MorC; id to idC)

open import partialinterpretation sC

{- We start by stating the types of the main properties that we are going to prove by mutual induction

Unfortunately we cannot define ⟦weaken⟧ᵈ in terms of ⟦tsubst⟧ᵈ because ⟦tsubst⟧Ty+ᵈ calls
⟦weakenMor+⟧ᵈ on δ, whereas the induction defining ⟦tsubst⟧Tyᵈ is on A.  There is no similar issue
defining ⟦weaken⟧ first (as there is no δ that would mess up the termination) and then ⟦tsubst⟧
(which uses ⟦weaken⟧ which is already defined).  -}

{- Totality of the partial interpretation functions -}

⟦⟧Tyᵈ  : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ))
⟦⟧Tmᵈ  : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → isDefined (⟦ u ⟧Tm (⟦ Γ ⟧Ctx $ Γᵈ))
⟦⟧Morᵈ : {Γ : Ctx n} {Δ : Ctx m} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (Δᵈ : isDefined (⟦ Δ ⟧Ctx)) {δ : Mor n m} (dδ : Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor (⟦ Γ ⟧Ctx $ Γᵈ) (⟦ Δ ⟧Ctx $ Δᵈ))

{- Interpretation of definitional equalities -}

⟦⟧TyEq : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X)}
       → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X $ A'ᵈ
⟦⟧TmEq : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A)) {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X)}
       → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X $ u'ᵈ

{- Codomain of the interpretation of a derivable term -}

⟦⟧Tm₁ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {u : TmExpr n} {uᵈ : isDefined (⟦ u ⟧Tm X)} {A : TyExpr n} {Aᵈ : isDefined (⟦ A ⟧Ty X)} (du : Derivable (Γ ⊢ u :> A)) → ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ⟦ A ⟧Ty X $ Aᵈ

{- Interpretation of weakening -}

⟦weakenTy⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (A : TyExpr n)
             → isDefined (⟦ A ⟧Ty X)
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → isDefined (⟦ weakenTy' k A ⟧Ty Z)

⟦weakenTm⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (u : TmExpr n)
             → isDefined (⟦ u ⟧Tm X)
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → isDefined (⟦ weakenTm' k u ⟧Tm Z)

⟦weakenTy⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (A : TyExpr n)
             → (Aᵈ : isDefined (⟦ A ⟧Ty X))
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → star (qq^ k X+= X=) (⟦ A ⟧Ty X $ Aᵈ) (⟦⟧Ty-ft A) qq^₁ ≡ ⟦ weakenTy' k A ⟧Ty Z $ ⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z=

⟦weakenTm⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (u : TmExpr n)
             → (uᵈ : isDefined (⟦ u ⟧Tm X))
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → starTm (qq^ k X+= X=) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' k u ⟧Tm Z $ ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z=

{- Interpretation of total substitutions -}

⟦tsubst⟧Tyᵈ : {X : Ob n} {Y : Ob m} (A : TyExpr m)
            → isDefined (⟦ A ⟧Ty Y)
            → (δ : Mor n m)
            → isDefined (⟦ δ ⟧Mor X Y)
            → isDefined (⟦ A [ δ ]Ty ⟧Ty X)

⟦tsubst⟧Tmᵈ : {X : Ob n} {Y : Ob m} (u : TmExpr m)
            → isDefined (⟦ u ⟧Tm Y)
            → (δ : Mor n m)
            → isDefined (⟦ δ ⟧Mor X Y)
            → isDefined (⟦ u [ δ ]Tm ⟧Tm X)

⟦tsubst⟧Ty= : {X : Ob n} {Y : Ob m} (A : TyExpr m)
              (Aᵈ : isDefined (⟦ A ⟧Ty Y))
              (δ : Mor n m)
              (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → star (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y $ Aᵈ) (⟦⟧Ty-ft A) (⟦⟧Mor₁ δ)
              ≡ ⟦ A [ δ ]Ty ⟧Ty X $ ⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ

⟦tsubst⟧Tm= : {X : Ob n} {Y : Ob m} (u : TmExpr m)
              (uᵈ : isDefined (⟦ u ⟧Tm Y))
              (δ : Mor n m)
              (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → starTm (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ u ⟧Tm Y $ uᵈ) (⟦⟧Tm₀ u) (⟦⟧Mor₁ δ)
              ≡ ⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ



{- We now prove a ton of lemmas, mainly special cases of the properties above… -}

{- Type of a weakening -}

⟦weakenTm⟧₁' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (u : TmExpr n)
             → (uᵈ : isDefined (⟦ u ⟧Tm X))
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Y : Ob (suc n)} (Y= : star^ k X+ X X+= X= ≡ Y)
             → {Z : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Z)
             → ∂₁ (⟦ weakenTm' k u ⟧Tm Y $ ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Y=) ≡ star (qq^ k X+= X=) Z (⟦⟧Tm₁-ft u u₁) qq^₁
⟦weakenTm⟧₁' k u uᵈ X+= X= Y= u₁ = ap ∂₁ (! (⟦weakenTm⟧=' k u uᵈ X+= X= Y=)) ∙ starTm₁ _ (⟦⟧Tm₁-ft u u₁) _ (⟦⟧Tmₛ u) u₁ qq^₁

{- Weakening at [last] -}

⟦weakenTm⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → isDefined (⟦ weakenTm u ⟧Tm X+)
⟦weakenTm⟧ᵈ u uᵈ X= = ⟦weakenTm⟧ᵈ' last u uᵈ X= refl refl

⟦weakenTm⟧= : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → starTm (pp X+) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) (pp₁ ∙ X=) ≡ ⟦ weakenTm u ⟧Tm X+ $ ⟦weakenTm⟧ᵈ u uᵈ X=
⟦weakenTm⟧= u uᵈ X= = ap-irr-starTm (! qq^last) refl ∙ ⟦weakenTm⟧=' last u uᵈ X= refl refl

⟦weakenTy⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (A : TyExpr n)
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (X= : ft X+ ≡ X)
            → isDefined (⟦ weakenTy A ⟧Ty X+)
⟦weakenTy⟧ᵈ A Aᵈ X= = ⟦weakenTy⟧ᵈ' last A Aᵈ X= refl refl

⟦weakenTy⟧= : {X+ : Ob (suc n)} {X : Ob n} (A : TyExpr n)
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (X= : ft X+ ≡ X)
            → star (pp X+) (⟦ A ⟧Ty X $ Aᵈ) (⟦⟧Ty-ft A) (pp₁ ∙ X=) ≡ ⟦ weakenTy A ⟧Ty X+ $ ⟦weakenTy⟧ᵈ A Aᵈ X=
⟦weakenTy⟧= A Aᵈ X= = ap-irr-star (! qq^last) refl ∙ ⟦weakenTy⟧=' last A Aᵈ X= refl refl

⟦weakenTm⟧₁ : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → {Z : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Z)
            → ∂₁ (⟦ weakenTm u ⟧Tm X+ $ ⟦weakenTm⟧ᵈ u uᵈ X=) ≡ star (pp X+) Z (⟦⟧Tm₁-ft u u₁) (pp₁ ∙ X=)
⟦weakenTm⟧₁ u uᵈ X= refl = ⟦weakenTm⟧₁' last u uᵈ X= refl refl refl ∙ ap3-irr2 star qq^last refl refl

{- Weakening at [prev k] -}

⟦weakenTy+⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -F' k)} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (X'= : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' X'= qq^₁ ≡ Z)
              → isDefined (⟦ weakenTy' (prev k) A ⟧Ty Z)
⟦weakenTy+⟧ᵈ' k A Aᵈ X+= X= refl Y= = ⟦weakenTy⟧ᵈ' (prev k) A Aᵈ X+= X= Y=

⟦weakenTm+⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -F' k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → isDefined (⟦ weakenTm' (prev k) u ⟧Tm Z)
⟦weakenTm+⟧ᵈ' k u uᵈ X+= X= refl Y= = ⟦weakenTm⟧ᵈ' (prev k) u uᵈ X+= X= Y=

⟦weakenTy+⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -F' k)} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → star+ (qq^ k X+= X=) (⟦ A ⟧Ty X' $ Aᵈ) (⟦⟧Ty-ft A) p qq^₁ ≡ ⟦ weakenTy' (prev k) A ⟧Ty Z $ ⟦weakenTy+⟧ᵈ' k A Aᵈ X+= X= p Y=
⟦weakenTy+⟧=' k A Aᵈ X+= X= refl Y= = ap-irr-star (! qq^prev) refl ∙ ⟦weakenTy⟧=' (prev k) A Aᵈ X+= X= Y=

⟦weakenTm+⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -F' k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → starTm+ (qq^ k X+= X=) p (⟦ u ⟧Tm X' $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' (prev k) u ⟧Tm Z $ ⟦weakenTm+⟧ᵈ' k u uᵈ X+= X= p Y=
⟦weakenTm+⟧=' k u uᵈ X+= X= refl Y= = ap ss (ap-irr-comp refl (! qq^prev)) ∙ ⟦weakenTm⟧=' (prev k) u uᵈ X+= X= Y=

⟦weakenTm+⟧₁' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} {Y : Ob (n -F' k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc n))}
              → (X= : ft X ≡ X')
              → (X'= : ft X' ≡ X'')
              → (Z= : star (qq^ k X+= X''=) X' X'= qq^₁ ≡ Z)
              → (u₁ : ∂₁ (⟦ u ⟧Tm X' $ uᵈ) ≡ X)
              → ∂₁ (⟦ weakenTm' (prev k) u ⟧Tm Z $ ⟦weakenTm+⟧ᵈ' k u uᵈ X+= X''= X'= Z=) ≡ star (qq (qq^ k X+= X''=) X' X'= qq^₁) X X= qq₁
⟦weakenTm+⟧₁' k u uᵈ X+= X''= refl refl Z= u₁ = ⟦weakenTm⟧₁' (prev k) u uᵈ X+= X''= Z= u₁ ∙ ap-irr-star qq^prev refl

{- Weakening at [prev (prev k)] -}

⟦weakenTm++⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X))
               → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc (suc n)))} (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : star+ (qq^ k X+= X''=) X X= X'= qq^₁ ≡ Z)
               → isDefined (⟦ weakenTm' (prev (prev k)) u ⟧Tm Z)
⟦weakenTm++⟧ᵈ' k u uᵈ X+= X''= refl refl Y= = ⟦weakenTm+⟧ᵈ' (prev k) u uᵈ X+= X''= refl (ap-irr-star qq^prev refl ∙ Y=)

⟦weakenTm++⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X))
               → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc (suc n)))} (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : star+ (qq^ k X+= X''=) X X= X'= qq^₁ ≡ Z)
               → starTm++ (qq^ k X+= X''=) X= X'= (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' (prev (prev k)) u ⟧Tm Z $ ⟦weakenTm++⟧ᵈ' k u uᵈ X+= X''= X= X'= Y=
⟦weakenTm++⟧=' k u uᵈ X+= X''= refl refl Y= = ap ss (ap-irr-comp refl (ap-irr-qq (! qq^prev) refl)) ∙ ⟦weakenTm+⟧=' (prev k) u uᵈ X+= X''= refl (ap-irr-star qq^prev refl ∙ Y=)

⟦weakenTm++⟧₁' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {X : Ob (suc (suc (suc n))) } {X' : Ob (suc (suc n))} {X'' : Ob (suc n)} {X''' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X'))
               → (X+= : ft X+ ≡ Y) (X'''= : ft^ k X''' ≡ Y) {Z : Ob (suc (suc (suc n)))}
               → (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (X''= : ft X'' ≡ X''')
               → (Z= : star+ (qq^ k X+= X'''=) X' X'= X''= qq^₁ ≡ Z)
               → (u₁ : ∂₁ (⟦ u ⟧Tm X' $ uᵈ) ≡ X)
               → ∂₁ (⟦ weakenTm' (prev (prev k)) u ⟧Tm Z $ ⟦weakenTm++⟧ᵈ' k u uᵈ X+= X'''= X'= X''= Z=) ≡ star++ (qq^ k X+= X'''=) X X= X'= X''= qq^₁
⟦weakenTm++⟧₁' k u uᵈ X+= X'''= refl refl refl Y= u₁ = ⟦weakenTm+⟧₁' (prev k) u uᵈ X+= X'''= refl refl (ap-irr-star qq^prev refl ∙ Y=) u₁ ∙ ap-irr-star (ap-irr-qq qq^prev refl) refl

{- Weakening at [prev (prev (prev k))] -}

⟦weakenTy+++⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
                → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
                → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc (suc (suc n))))} (X'''= : ft X''' ≡ X'') (X''= : ft X'' ≡ X') (X'= : ft X' ≡ X) (Z= : star++ (qq^ k X+= X=)  X''' X'''= X''= X'= qq^₁ ≡ Z)
               → isDefined (⟦ weakenTy' (prev (prev (prev k))) A ⟧Ty Z)
⟦weakenTy+++⟧ᵈ' k A Aᵈ X+= X= refl refl refl Z= = ⟦weakenTy⟧ᵈ' (prev (prev (prev k))) A Aᵈ X+= X= (ap-irr-star (qq^prev ∙ ap-irr-qq qq^prev refl) refl ∙ Z=)

⟦weakenTy+++⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
                → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
                → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc (suc (suc n))))} (X'''= : ft X''' ≡ X'') (X''= : ft X'' ≡ X') (X'= : ft X' ≡ X) (Z= : star++ (qq^ k X+= X=)  X''' X'''= X''= X'= qq^₁ ≡ Z)
               → star+++ (qq^ k X+= X=) (⟦ A ⟧Ty X''' $ Aᵈ) (⟦⟧Ty-ft A) X'''= X''= X'= qq^₁ ≡ ⟦ weakenTy' (prev (prev (prev k))) A ⟧Ty Z $ ⟦weakenTy+++⟧ᵈ' k A Aᵈ X+= X= X'''= X''= X'= Z=
⟦weakenTy+++⟧=' k A Aᵈ X+= X= refl refl refl Z= = ap-irr-star (! (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^prev refl) refl)) refl ∙ ⟦weakenTy⟧=' (prev (prev (prev k))) A Aᵈ X+= X= (ap-irr-star (qq^prev ∙ ap-irr-qq qq^prev refl) refl ∙ Z=)

{- Weakening at [prev last] -}

⟦weakenTy+⟧ᵈ : {X+ : Ob (suc n)} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
             → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
             → (X= : ft X+ ≡ X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (pp X+) X' p (pp₁ ∙ X=) ≡ Y)
             → isDefined (⟦ weakenTy' (prev last) A ⟧Ty Y)
⟦weakenTy+⟧ᵈ A Aᵈ X= p Y= = ⟦weakenTy+⟧ᵈ' last A Aᵈ X= refl p (ap-irr-star qq^last refl ∙ Y=)

⟦weakenTy+⟧= : {X+ : Ob (suc n)} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
             → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
             → (X= : ft X+ ≡ X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (pp X+) X' p (pp₁ ∙ X=) ≡ Y)
             → star (qq (pp X+) X' p (pp₁ ∙ X=)) (⟦ A ⟧Ty X' $ Aᵈ) (⟦⟧Ty-ft A) qq₁ ≡ ⟦ weakenTy' (prev last) A ⟧Ty Y $ ⟦weakenTy+⟧ᵈ A Aᵈ X= p Y=
⟦weakenTy+⟧= A Aᵈ X= refl Y= = ap-irr-star (ap-irr-qq (! qq^last) refl) refl ∙ ⟦weakenTy+⟧=' last A Aᵈ X= refl refl (ap-irr-star qq^last refl ∙ Y=)

{- Weakening at [prev (prev last)] -}

⟦weakenTy++⟧ᵈ : {X+ : Ob (suc n)} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc n)))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X''))
              → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc n)))} (p : ft X'' ≡ X') (p' : ft X' ≡ X) (Y= : star (qq (pp X+) X' p' (pp₁ ∙ X=)) X'' p qq₁ ≡ Y)
              → isDefined (⟦ weakenTy' (prev (prev last)) A ⟧Ty Y)
⟦weakenTy++⟧ᵈ A Aᵈ X= refl refl Y= = ⟦weakenTy⟧ᵈ' (prev (prev last)) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq qq^last refl) refl ∙ Y=)

⟦weakenTy++⟧= : {X+ : Ob (suc n)} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc n)))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X''))
              → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc n)))} (p : ft X'' ≡ X') (p' : ft X' ≡ X) (Y= : star (qq (pp X+) X' p' (pp₁ ∙ X=)) X'' p qq₁ ≡ Y)
              → star (qq (qq (pp X+) X' p' (pp₁ ∙ X=)) X'' p qq₁) (⟦ A ⟧Ty X'' $ Aᵈ) (⟦⟧Ty-ft A) qq₁ ≡ ⟦ weakenTy' (prev (prev last)) A ⟧Ty Y $ ⟦weakenTy++⟧ᵈ A Aᵈ X= p p' Y=
⟦weakenTy++⟧= A Aᵈ X= refl refl Y= = ap-irr-star (ap-irr-qq (ap-irr-qq (! qq^last) refl ∙ ! qq^prev) refl ∙ ! qq^prev) refl ∙ ⟦weakenTy⟧=' (prev (prev last)) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq qq^last refl) refl ∙ Y=)

{- Weakening at [prev (prev (prev last))] -}

⟦weakenTy+++⟧ᵈ : {X+ : Ob (suc n)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
               → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
               → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc (suc n))))} (p : ft X''' ≡ X'') (p' : ft X'' ≡ X') (p'' : ft X' ≡ X) (Y= : star (qq (qq (pp X+) X' p'' (pp₁ ∙ X=)) X'' p' qq₁) X''' p qq₁ ≡ Y)
               → isDefined (⟦ weakenTy' (prev (prev (prev last))) A ⟧Ty Y)
⟦weakenTy+++⟧ᵈ A Aᵈ X= refl refl refl Y= = ⟦weakenTy⟧ᵈ' (prev (prev (prev last))) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^last refl) refl) refl ∙ Y=)

⟦weakenTy+++⟧= : {X+ : Ob (suc n)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
               → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
               → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc (suc n))))} (p : ft X''' ≡ X'') (p' : ft X'' ≡ X') (p'' : ft X' ≡ X) (Y= : star (qq (qq (pp X+) X' p'' (pp₁ ∙ X=)) X'' p' qq₁) X''' p qq₁ ≡ Y)
               → star (qq (qq (qq (pp X+) X' p'' (pp₁ ∙ X=)) X'' p' qq₁) X''' p qq₁) (⟦ A ⟧Ty X''' $ Aᵈ) (⟦⟧Ty-ft A) qq₁ ≡ ⟦ weakenTy' (prev (prev (prev last))) A ⟧Ty Y $ ⟦weakenTy+++⟧ᵈ A Aᵈ X= p p' p'' Y=
⟦weakenTy+++⟧= A Aᵈ X= refl refl refl Y= = ap-irr-star (ap-irr-qq (ap-irr-qq (ap-irr-qq (! qq^last) refl ∙ ! qq^prev) refl ∙ ! qq^prev) refl ∙ ! qq^prev) refl ∙ ⟦weakenTy⟧=' (prev (prev (prev last))) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^last refl) refl) refl ∙ Y=)

{- Weakening of morphisms -}

⟦weakenMor⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → isDefined (⟦ δ ⟧Mor X Y)
           → isDefined (⟦ weakenMor δ ⟧Mor X+ Y)
⟦weakenMor⟧= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → ⟦ weakenMor δ ⟧Mor X+ Y $ ⟦weakenMor⟧ᵈ X= δ δᵈ ≡ comp (⟦ δ ⟧Mor X Y $ δᵈ) (pp X+) (⟦⟧Mor₀ δ ∙ ! X=) pp₁

⟦weakenMor⟧ᵈ refl ◇ tt = tt
⟦weakenMor⟧ᵈ {X+ = X+} refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = (⟦weakenMor⟧ᵈ refl δ δᵈ , ⟦weakenTm⟧ᵈ u uᵈ refl , ⟦⟧Mor₁ (weakenMor δ) , (⟦weakenTm⟧₁ u uᵈ refl u₁ ∙ ! star-comp ∙ ! (ap3-irr2 star (⟦weakenMor⟧= refl δ δᵈ) refl refl)) , tt)

⟦weakenMor⟧= refl ◇ tt = ! (ptmor-unique _ _ (comp₀ ∙ pp₀) (comp₁ ∙ pt-unique _))
⟦weakenMor⟧= refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) =
  ap-irr-comp
    (ap-irr-qq
      (⟦weakenMor⟧= refl δ δᵈ)
      refl
     ∙ qq-comp
     ∙ ap-irr-comp refl
       ((ap-irr-qq (! (! assoc ∙ ap-irr-comp (is-section= (ft-star ∙ ⟦⟧Mor₀ δ) (⟦⟧Tmₛ u) u₁) refl ∙ id-right pp₁)) refl)))
    (! ((⟦weakenTm⟧= u uᵈ refl)))
  ∙ assoc {g₁ = qq₁} {h₀ = qq₀}
  ∙ ! (ap-irr-comp refl (ss-qq {f₁ = comp₁ ∙ u₁}))
  ∙ ! assoc

⟦weakenMor+⟧ᵈ : {Z : Ob (suc n)} {X : Ob n} {Y' : Ob (suc m)} {Y : Ob m}
                (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y) 
              → (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → isDefined (⟦ weakenMor+ δ ⟧Mor Z Y')
⟦weakenMor+⟧ᵈ δ δᵈ refl Z= = (⟦weakenMor⟧ᵈ (ap ft (! Z=) ∙ ft-star ∙ ⟦⟧Mor₀ δ) δ δᵈ , (tt , (⟦⟧Mor₁ (weakenMor δ) , (varCL₁ {X= = refl} ∙ ap-irr-star refl (! Z=) ∙ ! star-comp ∙ ap-irr-star (! (⟦weakenMor⟧= (ap ft (! Z=) ∙ ft-star ∙ ⟦⟧Mor₀ δ) δ δᵈ)) refl) , tt)))

⟦weakenMor+⟧= : {Z : Ob (suc n)} {X : Ob n} {Y' : Ob (suc m)} {Y : Ob m}
                (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y) 
              → (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → ⟦ weakenMor+ δ ⟧Mor Z Y' $ ⟦weakenMor+⟧ᵈ δ δᵈ Y'= Z= ≡ qq (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ)
⟦weakenMor+⟧= δ δᵈ refl Z= = ap-irr-comp (ap-irr-qq (⟦weakenMor⟧= (ap ft (! Z=) ∙ ft-star ∙ ⟦⟧Mor₀ δ) δ δᵈ ∙ refl) refl ∙ qq-comp) refl {f₁' = varCL₁ {X= = refl}} ∙ assoc {g₀ = qq₀ ∙ ap-irr-star refl Z=} ∙ ap-irr-comp refl (ap-irr-comp (ap-irr-qq (! (id-left pp₀)) Z=) refl ∙ (! ss-qq)) ∙ id-left (qq₀ ∙ Z=)


{- Type of a substitution -}

⟦tsubst⟧Tm₁ : {Z : Ob (suc m)} {X : Ob n} {Y : Ob m} (u : TmExpr m)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y)) (u₁ : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ Z)
            → (δ : Mor n m)
            → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))            
            → ∂₁ (⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ)
              ≡ star (⟦ δ ⟧Mor X Y $ δᵈ) Z (⟦⟧Tm₁-ft u u₁) (⟦⟧Mor₁ δ)
⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ = ap ∂₁ (! (⟦tsubst⟧Tm= u uᵈ δ δᵈ)) ∙ starTm₁ _ (⟦⟧Tm₁-ft u u₁) _ (⟦⟧Tmₛ u) u₁ (⟦⟧Mor₁ δ)

{- Substitution by a weakenMor+ -}

⟦tsubst⟧Ty+ᵈ : {Z : Ob (suc n)} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} (A : TyExpr (suc m)) (Aᵈ : isDefined (⟦ A ⟧Ty Y'))
               (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
                → isDefined (⟦ A [ weakenMor+ δ ]Ty ⟧Ty Z)
⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ Y'= Z= = ⟦tsubst⟧Tyᵈ A Aᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ δ δᵈ Y'= Z=)

⟦tsubst⟧Ty++ᵈ : {Z : Ob (suc (suc n))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} (A : TyExpr (suc (suc m))) (Aᵈ : isDefined (⟦ A ⟧Ty Y''))
                (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
                → isDefined (⟦ A [ weakenMor+ (weakenMor+ δ) ]Ty ⟧Ty Z)
⟦tsubst⟧Ty++ᵈ A Aᵈ δ δᵈ Y''= Y'= Z= = ⟦tsubst⟧Ty+ᵈ A Aᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) Y''= ((ap-irr-star (⟦weakenMor+⟧= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) refl) ∙ Z=)

⟦tsubst⟧Ty+++ᵈ : {Z : Ob (suc (suc (suc n)))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} {Y''' : Ob (suc (suc (suc m)))} (A : TyExpr (suc (suc (suc m)))) (Aᵈ : isDefined (⟦ A ⟧Ty Y'''))
                 (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'''= : ft Y''' ≡ Y'') (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                 (Z= : star++ (⟦ δ ⟧Mor X Y $ δᵈ) Y''' Y'''= Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
                → isDefined (⟦ A [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty ⟧Ty Z)
⟦tsubst⟧Ty+++ᵈ A Aᵈ δ δᵈ Y'''= Y''= Y'= Z= = ⟦tsubst⟧Ty++ᵈ A Aᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) Y'''= Y''= (ap-irr-star (ap-irr-qq (⟦weakenMor+⟧= δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) refl) refl ∙ Z=)


⟦tsubst⟧Ty+= : {Z : Ob (suc n)} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} (A : TyExpr (suc m)) (Aᵈ : isDefined (⟦ A ⟧Ty Y'))
               (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
               → star+ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y' $ Aᵈ) (⟦⟧Ty-ft A) Y'= (⟦⟧Mor₁ δ)
                 ≡ ⟦ A [ weakenMor+ δ ]Ty ⟧Ty Z $ ⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ Y'= Z=
⟦tsubst⟧Ty+= A Aᵈ δ δᵈ Y'= Z= = ap-irr-star (! (⟦weakenMor+⟧= δ δᵈ Y'= Z=)) refl ∙ ⟦tsubst⟧Ty= A Aᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ δ δᵈ Y'= Z=)

⟦tsubst⟧Ty++= : {Z : Ob (suc (suc n))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} (A : TyExpr (suc (suc m))) (Aᵈ : isDefined (⟦ A ⟧Ty Y''))
               (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
               (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
               → star++ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y'' $ Aᵈ) (⟦⟧Ty-ft A) Y''= Y'= (⟦⟧Mor₁ δ)
                 ≡ ⟦ A [ weakenMor+ (weakenMor+ δ) ]Ty ⟧Ty Z $ ⟦tsubst⟧Ty++ᵈ A Aᵈ δ δᵈ Y''= Y'= Z=
⟦tsubst⟧Ty++= A Aᵈ δ δᵈ Y''= Y'= Z= = ap-irr-star (ap-irr-qq (! (⟦weakenMor+⟧= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=))) refl) refl ∙ ⟦tsubst⟧Ty+= A Aᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) Y''= (ap-irr-star (⟦weakenMor+⟧= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) refl ∙ Z=) 

⟦tsubst⟧Ty+++= : {Z : Ob (suc (suc (suc n)))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} {Y''' : Ob (suc (suc (suc m)))} (A : TyExpr (suc (suc (suc m)))) (Aᵈ : isDefined (⟦ A ⟧Ty Y'''))
                 (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'''= : ft Y''' ≡ Y'') (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                 (Z= : star++ (⟦ δ ⟧Mor X Y $ δᵈ) Y''' Y'''= Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
                 → star+++ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y''' $ Aᵈ) (⟦⟧Ty-ft A) Y'''= Y''= Y'= (⟦⟧Mor₁ δ)
                   ≡ ⟦ A [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty ⟧Ty Z $ ⟦tsubst⟧Ty+++ᵈ A Aᵈ δ δᵈ Y'''= Y''= Y'= Z=
⟦tsubst⟧Ty+++= A Aᵈ δ δᵈ Y'''= Y''= Y'= Z= = ap-irr-star (ap-irr-qq (ap-irr-qq (! (⟦weakenMor+⟧= δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=)))) refl) refl) refl ∙ ⟦tsubst⟧Ty++= A Aᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) Y'''= Y''= (ap-irr-star (ap-irr-qq (⟦weakenMor+⟧= δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) refl) refl ∙ Z=)


⟦tsubst⟧Tm+ᵈ : {Z : Ob (suc n)} {X : Ob n} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc m))
               (uᵈ : isDefined (⟦ u ⟧Tm Y'))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → isDefined (⟦ u [ weakenMor+ δ ]Tm ⟧Tm Z)
⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ Y'= Z= = ⟦tsubst⟧Tmᵈ u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ δ δᵈ Y'= Z=)

⟦tsubst⟧Tm+= : {Z : Ob (suc n)} {X : Ob n} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc m))
               (uᵈ : isDefined (⟦ u ⟧Tm Y'))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
             → starTm+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'= (⟦ u ⟧Tm Y' $ uᵈ) (⟦⟧Tm₀ u) (⟦⟧Mor₁ δ)
               ≡ ⟦ u [ weakenMor+ δ ]Tm ⟧Tm Z $ ⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ Y'= Z=
⟦tsubst⟧Tm+= u uᵈ δ δᵈ Y'= Z= =
  ap ss (ap-irr-comp refl (! (⟦weakenMor+⟧= δ δᵈ Y'= Z=)))
  ∙ ⟦tsubst⟧Tm= u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ δ δᵈ Y'= Z=)

⟦tsubst⟧Tm+₁ : {Z : Ob (suc n)} {X : Ob n} {Y'' : Ob (suc (suc m))} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc m))
               (uᵈ : isDefined (⟦ u ⟧Tm Y')) (u₁ : ∂₁ (⟦ u ⟧Tm Y' $ uᵈ) ≡ Y'')               
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)            
               → ∂₁ (⟦ u [ weakenMor+ δ ]Tm ⟧Tm Z $ ⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ Y'= Z=) ≡ star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ)
⟦tsubst⟧Tm+₁ u uᵈ u₁ δ δᵈ Y''= Y'= Z= = ! (ap ∂₁ (⟦tsubst⟧Tm+= u uᵈ δ δᵈ Y'= Z=)) ∙ starTm+₁ (⟦ δ ⟧Mor _ _ $ δᵈ) Y''= Y'= (⟦ u ⟧Tm _ $ uᵈ) (⟦⟧Tmₛ u) u₁ (⟦⟧Mor₁ δ)

{- Substitution by a weakenMor+ ^2 -}

⟦tsubst⟧Tm++ᵈ : {Z : Ob (suc (suc n))} {X : Ob n} {Y'' : Ob (suc (suc m))} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc (suc m)))
               (uᵈ : isDefined (⟦ u ⟧Tm Y''))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
               (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → isDefined (⟦ u [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm Z)             
⟦tsubst⟧Tm++ᵈ u uᵈ δ δᵈ Y''= Y'= Z= = ⟦tsubst⟧Tm+ᵈ u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) Y''= (ap-irr-star (⟦weakenMor+⟧= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) refl ∙ Z=)  

-- TODO : make something prettier
⟦tsubst⟧Tm++= : {Z : Ob (suc (suc n))} {X : Ob n} {Y'' : Ob (suc (suc m))} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc (suc m)))
                (uᵈ : isDefined (⟦ u ⟧Tm Y''))
                (δ : Mor n m)
                (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
                (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
                → starTm++ (⟦ δ ⟧Mor X Y $ δᵈ) Y''= Y'= (⟦ u ⟧Tm Y'' $ uᵈ) (⟦⟧Tm₀ u) (⟦⟧Mor₁ δ)
                  ≡ ⟦ u [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm Z $ ⟦tsubst⟧Tm++ᵈ u uᵈ δ δᵈ Y''= Y'= Z=
⟦tsubst⟧Tm++= u uᵈ δ δᵈ Y''= Y'= Z= = ap-irr-starTm (ap-irr-qq (! (⟦weakenMor+⟧= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=))) refl) refl ∙ ⟦tsubst⟧Tm+= u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) Y''= (ap-irr-star (⟦weakenMor+⟧= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) refl ∙ Z=) 
 

⟦tsubst⟧Tm++₁ : {Z : Ob (suc (suc n))} {X : Ob n} {Y''' : Ob (suc (suc (suc m)))} {Y'' : Ob (suc (suc m))} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc (suc m)))
                (uᵈ : isDefined (⟦ u ⟧Tm Y'')) (u₁ : ∂₁ (⟦ u ⟧Tm Y'' $ uᵈ) ≡ Y''')
                (δ : Mor n m)
                (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
                (Y'''= : ft Y''' ≡ Y'') (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → ∂₁ (⟦ u [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm Z $ ⟦tsubst⟧Tm++ᵈ u uᵈ δ δᵈ Y''= Y'= Z=) ≡ star++ (⟦ δ ⟧Mor X Y $ δᵈ) Y''' Y'''= Y''= Y'= (⟦⟧Mor₁ δ)
⟦tsubst⟧Tm++₁ u uᵈ u₁ δ δᵈ Y'''= Y''= Y'= Z= = ap ∂₁ (! (⟦tsubst⟧Tm++= u uᵈ δ δᵈ Y''= Y'= Z=)) ∙ starTm++₁ (⟦ δ ⟧Mor _ _ $ δᵈ) Y'''= Y''= Y'= (⟦ u ⟧Tm _ $ uᵈ) (⟦⟧Tmₛ u) u₁ (⟦⟧Mor₁ δ) 

{- Interpretation of the identity morphism -}

⟦idMor⟧ᵈ : {X Y : Ob n} → Y ≡ X → isDefined (⟦ idMor n ⟧Mor X Y)
⟦idMor⟧= : {X Y : Ob n} (p : Y ≡ X) → ⟦ idMor n ⟧Mor X Y $ ⟦idMor⟧ᵈ p ≡ idC X

⟦idMor⟧ᵈ {zero} Y= = tt
⟦idMor⟧ᵈ {suc n} {Y = Y} Y= = ⟦weakenMor+⟧ᵈ (idMor n) (⟦idMor⟧ᵈ {n = n} (ap ft Y=)) refl (ap-irr-star (⟦idMor⟧= (ap ft Y=)) Y= ∙ star-id {p = refl})

⟦idMor⟧= {zero} Y= = ! (ptmor-unique _ (idC _) id₀ (id₁ ∙ pt-unique _))
⟦idMor⟧= {suc n} {Y = Y} Y= = ⟦weakenMor+⟧= (idMor n) (⟦idMor⟧ᵈ {n = n} (ap ft Y=)) refl (ap-irr-star (⟦idMor⟧= (ap ft Y=)) Y= ∙ star-id {p = refl}) ∙ ap-irr-qq (⟦idMor⟧= (ap ft Y=)) Y= ∙ qq-id {p = refl}

{- Simple substitutions -}

⟦idMor+⟧ᵈ : {X : Ob n} {Y : Ob (suc n)} (p : ft Y ≡ X) (u : TmExpr n)
            (uᵈ : isDefined (⟦ u ⟧Tm X)) (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Y)
            → isDefined (⟦ idMor n , u ⟧Mor X Y)
⟦idMor+⟧ᵈ p u uᵈ u₁ =
  (⟦idMor⟧ᵈ p ,
   uᵈ ,
   ⟦⟧Mor₁ (idMor _) ,
   (u₁ ∙ ! (ap-irr-star (⟦idMor⟧= p) refl ∙ star-id {p = p})) , tt)

⟦idMor+⟧= : {X : Ob n} {Y : Ob (suc n)} (p : ft Y ≡ X) (u : TmExpr n)
            (uᵈ : isDefined (⟦ u ⟧Tm X)) (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Y)
            → ⟦ idMor n , u ⟧Mor X Y $ ⟦idMor+⟧ᵈ p u uᵈ u₁ ≡ ⟦ u ⟧Tm X $ uᵈ
⟦idMor+⟧= refl u uᵈ u₁ =
  ap-irr-comp (ap-irr-qq (⟦idMor⟧= refl) refl ∙ qq-id {p = refl}) refl ∙ id-right u₁

⟦subst⟧Tyᵈ : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (B : TyExpr (suc n))
           → isDefined (⟦ B ⟧Ty X)
           → (u : TmExpr n)
           → (uᵈ : isDefined (⟦ u ⟧Tm Y))
           → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
           → isDefined (⟦ substTy B u ⟧Ty Y)
⟦subst⟧Tyᵈ p B Bᵈ u uᵈ q = ⟦tsubst⟧Tyᵈ B Bᵈ _ (⟦idMor+⟧ᵈ p u uᵈ q)

⟦subst⟧Tmᵈ : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (v : TmExpr (suc n))
            → isDefined (⟦ v ⟧Tm X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y))
            → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → isDefined (⟦ substTm v u ⟧Tm Y)
⟦subst⟧Tmᵈ p v vᵈ u uᵈ q = ⟦tsubst⟧Tmᵈ v vᵈ _ (⟦idMor+⟧ᵈ p u uᵈ q)

⟦subst⟧Ty= : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (B : TyExpr (suc n))
             (Bᵈ : isDefined (⟦ B ⟧Ty X))
             (u : TmExpr n)
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTy B u ⟧Ty Y $ ⟦subst⟧Tyᵈ p B Bᵈ u uᵈ q ≡ star (⟦ u ⟧Tm Y $ uᵈ) (⟦ B ⟧Ty X $ Bᵈ) (⟦⟧Ty-ft B) q
⟦subst⟧Ty= p B Bᵈ u uᵈ q = ! (⟦tsubst⟧Ty= B Bᵈ _ (⟦idMor+⟧ᵈ p u uᵈ q)) ∙ ap-irr-star (⟦idMor+⟧= p u uᵈ q) refl

⟦subst⟧Tm= : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (v : TmExpr (suc n))
             (vᵈ : isDefined (⟦ v ⟧Tm X))
             (u : TmExpr n)
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTm v u ⟧Tm Y $ ⟦subst⟧Tmᵈ p v vᵈ u uᵈ q ≡ starTm (⟦ u ⟧Tm Y $ uᵈ) (⟦ v ⟧Tm X $ vᵈ) (⟦⟧Tm₀ v) q
⟦subst⟧Tm= p v vᵈ u uᵈ q = ! (⟦tsubst⟧Tm= v vᵈ _ (⟦idMor+⟧ᵈ p u uᵈ q)) ∙ ap-irr-starTm (⟦idMor+⟧= p u uᵈ q) refl

{- Double substitutions -}

⟦idMor++⟧ᵈ : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'')
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
            → isDefined (⟦ (idMor n , u) , v ⟧Mor X'' X)
⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁ =
  (⟦idMor+⟧ᵈ (ap ft X= ∙ X'=) u uᵈ (u₁ ∙ ! X=) ,
   vᵈ ,
   (comp₁ ∙ qq₁) ,
   (v₁ ∙ ap-irr-star (! (⟦idMor+⟧= (ap ft X= ∙ X'=) u uᵈ (u₁ ∙ ! X=))) refl) , tt)

⟦idMor++⟧= : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'')
           → (u : TmExpr n)
           → (uᵈ : isDefined (⟦ u ⟧Tm X''))
           → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
           → (v : TmExpr n)
           → (vᵈ : isDefined (⟦ v ⟧Tm X''))
           → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
           → ⟦ (idMor n , u) , v ⟧Mor X'' X $ ⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁ ≡ comp (qq (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁) (⟦ v ⟧Tm X'' $ vᵈ) qq₀ v₁
⟦idMor++⟧= X= X'= u uᵈ u₁ v vᵈ v₁ = ap-irr-comp (ap-irr-qq (⟦idMor+⟧= (ap ft X= ∙ X'=) u uᵈ (u₁ ∙ ! X=)) refl) refl

⟦subst2⟧Tyᵈ : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'') (B : TyExpr (suc (suc n)))
            → isDefined (⟦ B ⟧Ty X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
            → isDefined (⟦ subst2Ty B u v ⟧Ty X'')
⟦subst2⟧Tyᵈ X= X'= B Bᵈ u uᵈ u₁ v vᵈ v₁ = ⟦tsubst⟧Tyᵈ B Bᵈ _ (⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁)

⟦subst2⟧Ty= : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'') (B : TyExpr (suc (suc n)))
            → (Bᵈ : isDefined (⟦ B ⟧Ty X))
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
            → ⟦ subst2Ty B u v ⟧Ty X'' $ ⟦subst2⟧Tyᵈ X= X'= B Bᵈ u uᵈ u₁ v vᵈ v₁ ≡ star (⟦ v ⟧Tm X'' $ vᵈ) (star (qq (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁) (⟦ B ⟧Ty X $ Bᵈ) (⟦⟧Ty-ft B) qq₁) (ft-star ∙ qq₀) v₁
⟦subst2⟧Ty= X= X'= B Bᵈ u uᵈ u₁ v vᵈ v₁ = ! (⟦tsubst⟧Ty= B Bᵈ _ (⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁)) ∙ ap-irr-star (⟦idMor++⟧= X= X'= u uᵈ u₁ v vᵈ v₁) refl ∙ star-comp

⟦subst2⟧Tmᵈ : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'') (t : TmExpr (suc (suc n)))
            → isDefined (⟦ t ⟧Tm X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
            → isDefined (⟦ subst2Tm t u v ⟧Tm X'')
⟦subst2⟧Tmᵈ X= X'= t tᵈ u uᵈ u₁ v vᵈ v₁ = ⟦tsubst⟧Tmᵈ t tᵈ _ (⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁)

⟦subst2⟧Tm= : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'') (t : TmExpr (suc (suc n)))
            → (tᵈ : isDefined (⟦ t ⟧Tm X))
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
            → ⟦ subst2Tm t u v ⟧Tm X'' $ ⟦subst2⟧Tmᵈ X= X'= t tᵈ u uᵈ u₁ v vᵈ v₁ ≡ starTm (⟦ v ⟧Tm X'' $ vᵈ) (starTm (qq (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁) (⟦ t ⟧Tm X $ tᵈ) (⟦⟧Tm₀ t) qq₁) (ss₀ ∙ comp₀ ∙ qq₀) v₁
⟦subst2⟧Tm= X= X'= t tᵈ u uᵈ u₁ v vᵈ v₁ = ! (⟦tsubst⟧Tm= t tᵈ _ (⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁)) ∙ ap-irr-starTm (⟦idMor++⟧= X= X'= u uᵈ u₁ v vᵈ v₁) refl ∙ starTm-comp qq₀

{- Triple substitutions -}

⟦idMor+++⟧ᵈ : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''')
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ) (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁) X X= qq₁) (ft-star ∙ qq₀) v₁)
            → isDefined (⟦ ((idMor n , u) , v) , w ⟧Mor X''' X)
⟦idMor+++⟧ᵈ refl X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ =
  (⟦idMor++⟧ᵈ X'= X''= u uᵈ u₁ v vᵈ v₁ ,
   wᵈ ,
   (comp₁ ∙ qq₁) ,
   (w₁ ∙ ! star-comp ∙ ap-irr-star (! (⟦idMor++⟧= X'= X''= u uᵈ u₁ v vᵈ v₁)) refl) , tt)

⟦idMor+++⟧= : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''')
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ) (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁) X X= qq₁) (ft-star ∙ qq₀) v₁)
            → ⟦ ((idMor n , u) , v) , w ⟧Mor X''' X $ ⟦idMor+++⟧ᵈ X= X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ ≡
              comp (comp (qq (qq (⟦ u ⟧Tm X''' $ uᵈ)
                                 (ft X)
                                 (ap ft X= ∙ X'=)
                                 u₁)
                             X
                             refl
                             qq₁)
                         (qq (⟦ v ⟧Tm X''' $ vᵈ)
                             (star (qq (⟦ u ⟧Tm X''' $ uᵈ)
                                       X'
                                       X'=
                                       u₁)
                                   X
                                   X=
                                   qq₁)
                             (ft-star ∙ qq₀)
                             v₁)
                         (qq₀ ∙ ap-irr-star (ap-irr-qq refl X=) refl)
                         qq₁)
                   (⟦ w ⟧Tm X''' $ wᵈ)
                   (comp₀ ∙ qq₀)
                   w₁
⟦idMor+++⟧= refl X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ = ap-irr-comp (ap-irr-qq (⟦idMor++⟧= X'= X''= u uᵈ u₁ v vᵈ v₁) refl ∙ qq-comp) refl

⟦subst3⟧Tyᵈ : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''') (A : TyExpr (suc (suc (suc n))))
            → isDefined (⟦ A ⟧Ty X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ)
                                               (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
                                                  X
                                                  X=
                                                  qq₁)
                                               (ft-star ∙ qq₀)
                                               v₁)
            → isDefined (⟦ subst3Ty A u v w ⟧Ty X''')
⟦subst3⟧Tyᵈ X= X'= X''= A Aᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ = ⟦tsubst⟧Tyᵈ A Aᵈ _ (⟦idMor+++⟧ᵈ X= X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁)

⟦subst3⟧Ty= : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''') (A : TyExpr (suc (suc (suc n))))
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ)
                                               (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
                                                  X
                                                  X=
                                                  qq₁)
                                               (ft-star ∙ qq₀)
                                               v₁)
            → ⟦ subst3Ty A u v w ⟧Ty X''' $ ⟦subst3⟧Tyᵈ X= X'= X''= A Aᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁
              ≡ star
                  (⟦ w ⟧Tm X''' $ wᵈ)
                  (star
                     (qq (⟦ v ⟧Tm X''' $ vᵈ) (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁) X X= qq₁) (ft-star ∙ qq₀) v₁)
                     (star
                       (qq (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁) X X= qq₁)
                       (⟦ A ⟧Ty X $ Aᵈ)
                       (⟦⟧Ty-ft A)
                       qq₁)
                     (ft-star ∙ qq₀)
                     qq₁)
                   (ft-star ∙ qq₀)
                   w₁
⟦subst3⟧Ty= refl X'= X''= A Aᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ = ! (⟦tsubst⟧Ty= A Aᵈ (((idMor _ , u) , v) , w) (⟦idMor+++⟧ᵈ refl X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁)) ∙ ap-irr-star (⟦idMor+++⟧= refl X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁) refl ∙ star-comp ∙ ap-irr-star refl star-comp

{-
Unused
⟦subst3⟧Tmᵈ : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''') (t : TmExpr (suc (suc (suc n))))
            → isDefined (⟦ t ⟧Tm X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' (u₁ ∙ ! X'=))
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ)
                                               (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' (u₁ ∙ ! X'=))
                                                  X
                                                  (qq₁ ∙ ! X=))
                                               (v₁ ∙ ! qq₀ ∙ ! ft-star))
            → isDefined (⟦ t [ ((idMor _ , u) , v) , w ]Tm ⟧Tm X''')
⟦subst3⟧Tmᵈ X= X'= X''= t tᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ = ⟦tsubst⟧Tmᵈ t tᵈ _ (⟦idMor+++⟧ᵈ X= X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁)

⟦subst3⟧Tm= : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''') (t : TmExpr (suc (suc (suc n))))
            → (tᵈ : isDefined (⟦ t ⟧Tm X))
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' (u₁ ∙ ! X'=))
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ)
                                               (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' (u₁ ∙ ! X'=))
                                                  X
                                                  (qq₁ ∙ ! X=))
                                               (v₁ ∙ ! qq₀ ∙ ! ft-star))
            → ⟦ t [ ((idMor _ , u) , v) , w ]Tm ⟧Tm X''' $ ⟦subst3⟧Tmᵈ X= X'= X''= t tᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁
              ≡ starTm
                  (⟦ w ⟧Tm X''' $ wᵈ)
                  (starTm
                     (qq (⟦ v ⟧Tm X''' $ vᵈ) (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' (u₁ ∙ ! X'=)) X (qq₁ ∙ ! X=)) (v₁ ∙ ! qq₀ ∙ ! ft-star))
                     (starTm
                       (qq (qq (⟦ u ⟧Tm X''' $ uᵈ) (ft X) (u₁ ∙ ! (ap ft X= ∙ X'=))) X qq₁)
                       (⟦ t ⟧Tm X $ tᵈ)
                       (⟦⟧Tm₀ t ∙ ! qq₁))
                     (ss₀ ∙ comp₀ ∙ qq₀ ∙ ap2-irr star (ap2-irr qq refl X=) refl ∙ ! qq₁))
                   (ss₀ ∙ comp₀ ∙ qq₀ ∙ ! w₁)
⟦subst3⟧Tm= X= X'= X''= t tᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ = ! (⟦tsubst⟧Tm= t tᵈ (((idMor _ , u) , v) , w) (⟦idMor+++⟧ᵈ X= X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁)) ∙ ap2-irr starTm (⟦idMor+++⟧= X= X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁) refl ∙ starTm-comp {p = comp₁ ∙ qq₁ ∙ {!!} ∙ ! qq₀} {!!} ∙ starTm-comp {p = {!!}} {!!}
-}

{- More stuff -}

cong⟦⟧Ty : {X Y : Ob n} {A : TyExpr n} → X ≡ Y → isDefined (⟦ A ⟧Ty X) → isDefined (⟦ A ⟧Ty Y)
cong⟦⟧Ty refl Aᵈ = Aᵈ

cong⟦⟧Mor : {X : Ob n} {Y Y' : Ob m} {δ : Mor n m} → Y ≡ Y' → isDefined (⟦ δ ⟧Mor X Y) → isDefined (⟦ δ ⟧Mor X Y')
cong⟦⟧Mor refl δᵈ = δᵈ

⟦⟧TyEq+ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {X' : Ob n} {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A'))
          {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X')} → X ≡ X' → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X' $ A'ᵈ
⟦⟧TyEq+ Γᵈ dA= refl = ⟦⟧TyEq Γᵈ dA=

⟦⟧TmEq+ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {X' : Ob n} {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A))
          {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X')} → X ≡ X' → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X' $ u'ᵈ
⟦⟧TmEq+ Γᵈ du= refl = ⟦⟧TmEq Γᵈ du=


{- We can now finally define our main properties -}

⟦⟧Tyᵈ Γᵈ UU = tt
⟦⟧Tyᵈ Γᵈ {A = el i v} (El dv) =
  (⟦⟧Tmᵈ Γᵈ dv ,
   ⟦⟧Tmₛ v ,
   ⟦⟧Tm₁ Γᵈ dv , tt)
⟦⟧Tyᵈ Γᵈ {A = pi A B} (Pi dA dB) =
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Ty-ft B , tt)
  where Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
⟦⟧Tyᵈ Γᵈ {A = sig A B} (Sig dA dB) =
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Ty-ft B , tt)
  where
    Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
⟦⟧Tyᵈ Γᵈ Empty = tt
⟦⟧Tyᵈ Γᵈ Unit = tt
⟦⟧Tyᵈ Γᵈ Nat = tt
⟦⟧Tyᵈ Γᵈ {A = id A a b} (Id dA da db) =
  (⟦⟧Tyᵈ Γᵈ dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ db ,
   ⟦⟧Tmₛ b ,
   ⟦⟧Tm₁ Γᵈ db , tt)

⟦⟧Tmᵈ Γᵈ (VarLast _) = tt
⟦⟧Tmᵈ Γᵈ (VarPrev _ _) = tt
⟦⟧Tmᵈ Γᵈ (Conv dA du dA=) = ⟦⟧Tmᵈ Γᵈ du

⟦⟧Tmᵈ Γᵈ {u = uu i} UUUU = tt

⟦⟧Tmᵈ Γᵈ {u = pi i a b} (PiUU da db) =
  (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
    where
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da
      bᵈ = ⟦⟧Tmᵈ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
⟦⟧Tmᵈ Γᵈ {u = lam A B u} (Lam dA dB du) =
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt ) dB ,
   ⟦⟧Ty-ft B ,
   ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ (Γᵈ , Aᵈ , tt) du , tt)
  where
    Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
⟦⟧Tmᵈ Γᵈ {u = app A B f a} (App dA dB df da) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ df ,
   ⟦⟧Tmₛ f ,
   ⟦⟧Tm₁ Γᵈ {A = pi A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} df ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B
 
  

⟦⟧Tmᵈ Γᵈ {u = sig i a b} (SigUU da db) =
  (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
    where
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da
      bᵈ = ⟦⟧Tmᵈ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
⟦⟧Tmᵈ Γᵈ {u = pair A B a b} (Pair dA dB da db) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   ⟦⟧Ty-ft B ,
   aᵈ ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ db ,
   ⟦⟧Tmₛ b ,
   (⟦⟧Tm₁ Γᵈ db ∙ ⟦subst⟧Ty= (⟦⟧Ty-ft A) B Bᵈ a aᵈ (⟦⟧Tm₁ Γᵈ da)) , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
⟦⟧Tmᵈ Γᵈ {u = pr1 A B u} (Pr1 dA dB du) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} du , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B 
⟦⟧Tmᵈ Γᵈ {u = pr2 A B u} (Pr2 dA dB du) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} du , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B  

⟦⟧Tmᵈ Γᵈ EmptyUU = tt
⟦⟧Tmᵈ Γᵈ {u = emptyelim A u} (Emptyelim dA du) =
  (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ Γᵈ UnitUU = tt
⟦⟧Tmᵈ Γ TT = tt
⟦⟧Tmᵈ Γᵈ {u = unitelim A dtt u} (Unitelim dA ddtt du) =
  (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ ddtt ,
   ⟦⟧Tmₛ dtt ,
   (⟦⟧Tm₁ Γᵈ ddtt ∙ ⟦subst⟧Ty= UnitStr= A (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA) tt tt ttStr₁) ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ Γᵈ {u = nat i} NatUU = tt
⟦⟧Tmᵈ Γᵈ {u = zero} Zero = tt
⟦⟧Tmᵈ Γᵈ {u = suc u} (Suc du) =
  (⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ Γᵈ {u = natelim P dO dS u} (Natelim dP ddO ddS du) =
  (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt)
    where
      Pᵈ  = ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP
      P=  = ⟦⟧Ty-ft P
      dOᵈ = ⟦⟧Tmᵈ Γᵈ ddO
      dOₛ = ⟦⟧Tmₛ dO
      dO₁ = ⟦⟧Tm₁ Γᵈ ddO
            ∙ ⟦subst⟧Ty= NatStr= P Pᵈ zero tt zeroStr₁
      dSᵈ = ⟦⟧Tmᵈ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS
      dSₛ = ⟦⟧Tmₛ dS
      natthing = NatStrNat pp₀
      auxauxᵈ = ⟦weakenTy+⟧ᵈ P Pᵈ NatStr= NatStr= natthing
      auxᵈ = ⟦subst⟧Tyᵈ NatStr= (weakenTy' (prev last) P) auxauxᵈ (suc (var last)) (tt , (ssₛ , (varCL₁ ∙ natthing) , tt)) sucStr₁
      dS₁ = ⟦⟧Tm₁ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS ∙ ⟦subst⟧Ty= NatStr= (weakenTy' (prev last) (weakenTy' (prev last) P))
                                                                (⟦weakenTy+⟧ᵈ (weakenTy' (prev last) P) auxauxᵈ P= NatStr= (NatStrNat pp₀))
                                                                (suc (var (prev last))) (tt , ssₛ , (varC+₁ last P= varCL₁ ∙ ! (star-comp {g₀ = pp₀}) ∙ NatStrNat (comp₀ ∙ pp₀)) , tt) sucStr₁ ∙
                                                     ap-irr-star refl (! (ap-irr-star (ap-irr-qq refl natthing)
                                                                                      (⟦weakenTy+⟧= P Pᵈ NatStr= NatStr= natthing) ∙
                                                                          ⟦weakenTy+⟧= (weakenTy' (prev last) P) (⟦weakenTy+⟧ᵈ P Pᵈ NatStr= NatStr= natthing) P= NatStr= (NatStrNat pp₀)))
      uᵈ  = ⟦⟧Tmᵈ Γᵈ du
      uₛ  = ⟦⟧Tmₛ u
      u₁  = ⟦⟧Tm₁ Γᵈ du


⟦⟧Tmᵈ Γᵈ {u = id i a u v} (IdUU da du dv) =
  (⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = el i a} {Aᵈ = ⟦⟧Tmᵈ Γᵈ da , ⟦⟧Tmₛ a , ⟦⟧Tm₁ Γᵈ da , tt} du ,
   ⟦⟧Tmᵈ Γᵈ dv ,
   ⟦⟧Tmₛ v ,
   ⟦⟧Tm₁ Γᵈ {A = el i a} {Aᵈ = ⟦⟧Tmᵈ Γᵈ da , ⟦⟧Tmₛ a , ⟦⟧Tm₁ Γᵈ da , tt} dv , tt)
⟦⟧Tmᵈ Γᵈ {u = refl A a} (Refl dA da) =
  (⟦⟧Tyᵈ Γᵈ dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da , tt)
⟦⟧Tmᵈ {Γ = Γ} Γᵈ {u = jj A P d a b p} (JJ dA dP dd da db dp) = 
   (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt)
   where
      X = ⟦ Γ ⟧Ctx $ Γᵈ
      Aᵈ : isDefined (⟦ A ⟧Ty X)
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      [A] = ⟦ A ⟧Ty X $ Aᵈ
      A= : ft [A] ≡ X
      A= = ⟦⟧Ty-ft A
      wAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
      wAᵈ = ⟦weakenTy⟧ᵈ A Aᵈ A=
      wA= = ⟦weakenTy⟧= A Aᵈ A=
      [wA] = ⟦ weakenTy A ⟧Ty [A] $ wAᵈ
      [wA]-ft : ft [wA] ≡ [A]
      [wA]-ft = ⟦⟧Ty-ft (weakenTy A)
      wwAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty [wA])
      wwAᵈ = ⟦weakenTy⟧ᵈ (weakenTy A) wAᵈ [wA]-ft
      wwA= = ⟦weakenTy⟧= (weakenTy A) wAᵈ [wA]-ft
      [wwA] = ⟦ weakenTy (weakenTy A) ⟧Ty [wA] $ wwAᵈ
      [wwA]-ft : ft [wwA] ≡ [wA]
      [wwA]-ft = ⟦⟧Ty-ft (weakenTy (weakenTy A))
      idᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA])
      idᵈ = (wwAᵈ , [wwA]-ft , tt , varCₛ (prev last) [wA] , (varC+₁ last [wA]-ft (varCL₁ ∙ wA=) ∙ wwA=) , tt , varCₛ last [wA] , (varCL₁ ∙ wwA=) , tt)
      id= : ⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA] $ idᵈ ≡ T-ftP X [A] A=
      id= = ap-irr-IdStr (! wA=) (! wwA= ∙ ap-irr-star (ap pp (! wA=)) (! wA=)) (ap ss (ap pp (! wA=))) (ap ss (ap idC (! wA=)))
      [id] = ⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA] $ idᵈ
      [id]-ft : ft [id] ≡ [wA]
      [id]-ft = ⟦⟧Ty-ft (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) {Aᵈ = idᵈ}
      Pᵈ' : isDefined (⟦ P ⟧Ty [id])
      Pᵈ' = ⟦⟧Tyᵈ (((Γᵈ , (Aᵈ , tt)) , wAᵈ , tt) , (idᵈ , tt)) dP
      Pᵈ : isDefined (⟦ P ⟧Ty (T-ftP X [A] A=))
      Pᵈ = cong⟦⟧Ty {A = P} id= Pᵈ'
      P= = ⟦⟧Ty-ft P
      wwA'ᵈ : isDefined (⟦ weakenTy' (prev last) (weakenTy A) ⟧Ty [wA])
      wwA'ᵈ = ⟦weakenTy+⟧ᵈ (weakenTy A) wAᵈ A= A= wA=
      [wwA'] = ⟦ weakenTy' (prev last) (weakenTy A) ⟧Ty [wA] $ wwA'ᵈ
      wwA'=' : star (qq (pp [A]) [A] A= (pp₁ ∙ A=)) [wA] (⟦⟧Ty-ft (weakenTy A)) qq₁ ≡ [wwA']
      wwA'=' = ⟦weakenTy+⟧= (weakenTy A) wAᵈ A= A= wA=
      [wwA']-ft : ft [wwA'] ≡ [wA]
      [wwA']-ft = ⟦⟧Ty-ft (weakenTy' (prev last) (weakenTy A))
      wwwAᵈ : isDefined (⟦ weakenTy (weakenTy' (prev last) (weakenTy A)) ⟧Ty [wwA'])
      wwwAᵈ = ⟦weakenTy⟧ᵈ (weakenTy' (prev last) (weakenTy A)) wwA'ᵈ [wwA']-ft
      wwwA= = ⟦weakenTy⟧= (weakenTy' (prev last) (weakenTy A)) wwA'ᵈ [wwA']-ft
      [wwwA] = ⟦ weakenTy (weakenTy' (prev last) (weakenTy A)) ⟧Ty [wwA'] $ wwwAᵈ
      widᵈ : isDefined (⟦ weakenTy' (prev (prev last)) (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⟧Ty [wwA'])
      widᵈ = ⟦weakenTy++⟧ᵈ (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) idᵈ A= (⟦⟧Ty-ft (weakenTy A)) A= wwA'='
      [wid] = ⟦ weakenTy' (prev (prev last)) (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⟧Ty [wwA'] $ widᵈ
      wid= = ⟦weakenTy++⟧= (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) idᵈ A= (⟦⟧Ty-ft (weakenTy A)) A= wwA'='
      [wid]-ft : ft [wid] ≡ [wwA']
      [wid]-ft = ⟦⟧Ty-ft (weakenTy' (prev (prev last)) (id (weakenTy (weakenTy A)) (var (prev last)) (var last))) {Aᵈ = widᵈ}
      reflᵈ : isDefined (⟦ refl (weakenTy A) (var last) ⟧Tm [A])
      reflᵈ = (wAᵈ , ⟦⟧Ty-ft (weakenTy A) , tt , varCₛ last [A] , (varCL₁ ∙ wA=) , tt)
      wPᵈ : isDefined (⟦ weakenTy' (prev (prev (prev last))) P ⟧Ty [wid])
      wPᵈ = ⟦weakenTy+++⟧ᵈ P Pᵈ' A= IdStr= [wA]-ft A= wid=
      wP= = ⟦weakenTy+++⟧= P Pᵈ A= IdStr= (ap ft wA= ∙ [wA]-ft) A= (ap-irr-star (ap-irr-qq refl wA=) (! id=) ∙ wid=)
      dᵈ : isDefined (⟦ d ⟧Tm (⟦ A ⟧Ty X $ Aᵈ))
      dᵈ = ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) dd
      dₛ = ⟦⟧Tmₛ d
      d₁ : ∂₁ (⟦ d ⟧Tm (⟦ A ⟧Ty X $ Aᵈ) $ dᵈ) ≡ T-d₁ (⟦ Γ ⟧Ctx $ Γᵈ)
                                                     (⟦ A ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ) $ ⟦⟧Tyᵈ Γᵈ dA) A=
                                                     (⟦ P ⟧Ty (T-ftP (⟦ Γ ⟧Ctx $ Γᵈ) (⟦ A ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ) $ Aᵈ) A=) $ Pᵈ) P=
      d₁ = ⟦⟧Tm₁ {Γ = Γ , A} (Γᵈ , Aᵈ , tt) {u = d} {uᵈ = dᵈ} {A = subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last))} dd
                 ∙ ⟦subst3⟧Ty= [wid]-ft [wwA']-ft [wA]-ft
                               (weakenTy' (prev (prev (prev last))) P) wPᵈ
                               (var last) tt (varCL₁ ∙ wA=)
                               (var last) tt (varCL₁ ∙ eq4)
                               (refl (weakenTy A) (var last)) reflᵈ (reflStr₁ ∙ ! eq1)
                 ∙ eq3
                   where eq4 = ap-irr-star (! (id-left pp₀) ∙ ap-irr-comp refl (ss-qq ∙ ap-irr-comp (ap-irr-qq (id-left pp₀) refl) refl {g₀' = qq₀} {f₁' = ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl}) {g₀' = pp₀} {f₁' = comp₁ ∙ qq₁}) refl {q = A=}
                               ∙ star-comp ∙ ap-irr-star refl wA= ∙ star-comp ∙ ap-irr-star refl wwA'='
                         eq1 = ap-irr-star refl eq2 ∙ IdStrNat (varC₀ {k = last}) {g₁ = varCL₁} ∙
                               ap-irr-IdStr refl (! star-comp ∙ ap-irr-star (is-section= (ft-star ∙ pp₀) (varCₛ last _) varCL₁ ) refl {q' = ft-star ∙ pp₀}∙ star-id ∙ wA=)
                                                 (star-varCL'' ∙ ap ss (is-section= (ft-star ∙ pp₀) (varCₛ last _) varCL₁))
                                                 (star-varCL' ∙ ss-of-section _ (varCₛ last _))
                             where eq2 = ap-irr-star (ap-irr-qq refl
                                                                (! wwA'=' ∙ ap-irr-star refl (! wA=) {f₁' = qq₁}) {f₁' = ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl})
                                                     (! wid= ∙ ap-irr-star (ap-irr-qq refl (! wA=) {q' = ft-star ∙ pp₀} {f₁' = qq₁})
                                                                           id= {q' = IdStr=} {f₁' = qq₁})
                                         ∙ ! star-comp ∙ ap-irr-star (! (qq-comp {g₀ = qq₀}) ∙ ap-irr-qq (ap-irr-comp (ap-irr-qq (! (id-left pp₀)) refl) refl ∙ ! ss-qq) refl {q' = ft-star ∙ pp₀} ∙ qq-id)
                                                                   refl {q' = T-ftP=} ∙ star-id
                         eq3 =  ap-irr-star (ap-irr-reflStr refl (! wA=) refl)
                               (ap-irr-star (ap-irr-qq refl (ap-irr-star (ap-irr-qq refl (! wwA'=' ∙ ap-irr-star refl (! wA=))) (! wid= ∙ ap-irr-star (ap-irr-qq refl (! wA=)) id=)))
                                            (ap-irr-star (ap-irr-qq (ap-irr-qq refl (! wwA'=' ∙ ap-irr-star refl (! wA=))) (! wid= ∙ ap-irr-star (ap-irr-qq refl (! wA=)) id=))
                                                         (! wP=)))

      aᵈ : isDefined (⟦ a ⟧Tm X)
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da

      bᵈ : isDefined (⟦ b ⟧Tm X)
      bᵈ = ⟦⟧Tmᵈ Γᵈ db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ Γᵈ db

      pᵈ : isDefined (⟦ p ⟧Tm X)
      pᵈ = ⟦⟧Tmᵈ Γᵈ dp
      pₛ = ⟦⟧Tmₛ p
      p₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = (Aᵈ , A= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)} dp
 

⟦⟧Morᵈ {Δ = ◇} _ _ {◇} tt = tt
⟦⟧Morᵈ {Δ = Δ , B} Γᵈ (Δᵈ , Bᵈ , tt) {δ , u} (dδ , du) =
  (δᵈ , uᵈ , δ₁ , u₁ , tt)
    where
      δᵈ' = ⟦⟧Morᵈ Γᵈ Δᵈ dδ
      δᵈ = cong⟦⟧Mor {δ = δ} (! (⟦⟧Ty-ft B)) δᵈ'
      uᵈ = ⟦⟧Tmᵈ Γᵈ du
      δ₁ = ⟦⟧Mor₁ δ
      u₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ'} du ∙ ! (⟦tsubst⟧Ty= B Bᵈ δ δᵈ') ∙ ap-irr-star (ap-irr (λ x z → ⟦ δ ⟧Mor _ x $ z) (! (⟦⟧Ty-ft B))) refl
  
⟦⟧Tm₁ Γᵈ (VarLast {A = A} dA) = varCL₁ ∙ ⟦weakenTy⟧= A (fst (snd Γᵈ)) (⟦⟧Ty-ft A)
⟦⟧Tm₁ Γᵈ {u = var (prev k)} (VarPrev {B = B} {A = A} dA dk) = varC+₁ k (⟦⟧Ty-ft B) (⟦⟧Tm₁ (fst Γᵈ) dk) ∙ ⟦weakenTy⟧= A (⟦⟧Tyᵈ (fst Γᵈ) dA) (⟦⟧Ty-ft B)
⟦⟧Tm₁ Γᵈ (Conv dA du dA=) = ⟦⟧Tm₁ Γᵈ du ∙ ⟦⟧TyEq Γᵈ dA= {Aᵈ = ⟦⟧Tyᵈ Γᵈ dA}

⟦⟧Tm₁ Γᵈ {u = uu i} UUUU = uuStr₁

⟦⟧Tm₁ Γᵈ {u = pi i a b} (PiUU da db) = piStr₁
⟦⟧Tm₁ Γᵈ {u = lam A B u} (Lam dA dB du) = lamStr₁
⟦⟧Tm₁ Γᵈ {u = app A B f a} (App dA dB df da) = appStr₁ ∙ ! (⟦subst⟧Ty= (⟦⟧Ty-ft A) B (⟦⟧Tyᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))

⟦⟧Tm₁ Γᵈ {u = sig i a b} (SigUU da db) = sigStr₁
⟦⟧Tm₁ Γᵈ {u = pair A B a b} (Pair dA dB da db) = pairStr₁
⟦⟧Tm₁ Γᵈ {u = pr1 A B u} (Pr1 dA dB du) = pr1Str₁
⟦⟧Tm₁ Γᵈ {u = pr2 A B u} (Pr2 dA dB du) =
  pr2Str₁ ∙ ! (⟦subst⟧Ty= A= B Bᵈ (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , ⟦⟧Tmᵈ Γᵈ du , ⟦⟧Tmₛ u , ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = Aᵈ , A= , Bᵈ , B= , tt} du , tt) pr1Str₁)
    where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B
      
⟦⟧Tm₁ Γᵈ EmptyUU = emptyStr₁
⟦⟧Tm₁ Γᵈ {u = emptyelim A u} (Emptyelim dA du) = emptyelimStr₁ ∙ ! (⟦subst⟧Ty= EmptyStr= A (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))
⟦⟧Tm₁ Γᵈ UnitUU = unitStr₁
⟦⟧Tm₁ Γᵈ TT = ttStr₁
⟦⟧Tm₁ Γᵈ {u = unitelim A dtt u} (Unitelim dA ddtt du) = unitelimStr₁ ∙ ! (⟦subst⟧Ty= UnitStr= A (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))

⟦⟧Tm₁ Γᵈ {u = nat i} NatUU = natStr₁
⟦⟧Tm₁ Γᵈ {u = zero} Zero = zeroStr₁
⟦⟧Tm₁ Γᵈ {u = suc u} (Suc du) = sucStr₁
⟦⟧Tm₁ Γᵈ {u = natelim P dO dS u} (Natelim dP ddO ddS du) = natelimStr₁ ∙ ! (⟦subst⟧Ty= NatStr= P (⟦⟧Tyᵈ (Γᵈ , tt , tt) dP) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))

⟦⟧Tm₁ Γᵈ {u = id i a u v} (IdUU da du dv) = idStr₁
⟦⟧Tm₁ Γᵈ {u = refl A a} (Refl dA da) = reflStr₁
⟦⟧Tm₁ {Γ = Γ} Γᵈ {u = jj A P d a b p} (JJ dA dP dd da db dp) =
         jjStr₁ ∙ ! (⟦subst3⟧Ty= IdStr= (⟦⟧Ty-ft (weakenTy A)) (⟦⟧Ty-ft A) P (⟦⟧Tyᵈ (((Γᵈ , (Aᵈ , tt)) , wAᵈ , tt) , (idᵈ , tt)) dP)
                                 a aᵈ a₁
                                 b bᵈ (b₁ ∙ ! [wA][a] ∙ ap-irr-star refl wA=)
                                 p pᵈ (p₁ ∙ eq1)
                ∙ ap-irr-star refl (ap-irr-star (ap-irr-qq refl (ap-irr-star (ap-irr-qq refl (! wA=)) id=))
                                                (ap-irr-star (ap-irr-qq  (ap-irr-qq refl (! wA=)) id=)
                                                             (ap-irr (λ z p → ⟦ P ⟧Ty z $ p) id=))))
      where
        X = ⟦ Γ ⟧Ctx $ Γᵈ
        Aᵈ : isDefined (⟦ A ⟧Ty X)
        Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
        [A] = ⟦ A ⟧Ty X $ Aᵈ
        A= : ft [A] ≡ X
        A= = ⟦⟧Ty-ft A
        wAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
        wAᵈ = ⟦weakenTy⟧ᵈ A Aᵈ A=
        wA= = ⟦weakenTy⟧= A Aᵈ A=
        [wA] = ⟦ weakenTy A ⟧Ty [A] $ wAᵈ
        [wA]-ft : ft [wA] ≡ [A]
        [wA]-ft = ⟦⟧Ty-ft (weakenTy A)
        wwAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty [wA])
        wwAᵈ = ⟦weakenTy⟧ᵈ (weakenTy A) wAᵈ [wA]-ft
        wwA= = ⟦weakenTy⟧= (weakenTy A) wAᵈ [wA]-ft
        [wwA] = ⟦ weakenTy (weakenTy A) ⟧Ty [wA] $ wwAᵈ
        [wwA]-ft : ft [wwA] ≡ [wA]
        [wwA]-ft = ⟦⟧Ty-ft (weakenTy (weakenTy A))
        idᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA])
        idᵈ = (wwAᵈ , [wwA]-ft , tt , varCₛ (prev last) [wA] , (varC+₁ last [wA]-ft (varCL₁ ∙ wA=) ∙ wwA=) , tt , varCₛ last [wA] , (varCL₁ ∙ wwA=) , tt)     
        id= = ap-irr-IdStr (!  wA=) (! wwA= ∙ ap-irr-star (ap pp (! wA=)) (! wA=)) (ap ss (ap pp (! wA=))) (ap ss (ap idC (! wA=))) {v'ₛ = ssₛ} {v'₁ = ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl}

        aᵈ : isDefined (⟦ a ⟧Tm X)
        aᵈ = ⟦⟧Tmᵈ Γᵈ da
        aₛ = ⟦⟧Tmₛ a
        a₁ = ⟦⟧Tm₁ Γᵈ da

        bᵈ : isDefined (⟦ b ⟧Tm X)
        bᵈ = ⟦⟧Tmᵈ Γᵈ db
        bₛ = ⟦⟧Tmₛ b
        b₁ = ⟦⟧Tm₁ Γᵈ db

        pᵈ : isDefined (⟦ p ⟧Tm X)
        pᵈ = ⟦⟧Tmᵈ Γᵈ dp
        p₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = (Aᵈ , A= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)} dp
 
        [wA][a] = star-pp' A= A= aₛ a₁
        [wA][b] = star-pp' A= A= bₛ b₁
        eq1 = ! (ap-irr-star refl ((ap-irr-star (ap-irr-qq refl (! wA=)) id=) ∙ IdStrNat (qq₀ ∙ [wA][a]) ∙ ap-irr-IdStr refl (star-pp (⟦⟧Tm₀ a) ∙ ap-irr-star (ap pp [wA][a]) [wA][a])
                                                                              (star-varC+' (⟦⟧Tmₛ a) ∙ ap-irr-starTm (ap pp [wA][a]) refl) {u'ₛ = ssₛ} {u'₁ = starTm₁ (pp [A]) A= _ aₛ a₁ (pp₁ ∙ A=)}
                                                                              (star-varCL ∙ ap (varC last) [wA][a]) {v'ₛ = ssₛ} {v'₁ = varCL₁}) {q = ft-star ∙ qq₀} {q' = IdStr=} {f₁' = b₁}
                                  ∙ IdStrNat (⟦⟧Tm₀ b) ∙ ap-irr-IdStr refl [wA][b]
                                                                           (! (starTm-comp pp₀) ∙ ap-irr-starTm (is-section= A= bₛ b₁) refl ∙ starTm-id (⟦⟧Tm₀ a) aₛ)
                                                                           (star-varCL' ∙ ss-of-section _ bₛ))
                                                                                            


⟦weakenTy⟧ᵈ' k (uu i) Aᵈ _ _ _ = tt
⟦weakenTy⟧ᵈ' k (el i v) (vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  (⟦weakenTm⟧ᵈ' k v vᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X+= X= Z= v₁ ∙ UUStrNat (qq^₀ ∙ Z=)) , tt)
⟦weakenTy⟧ᵈ' k (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) , tt)
⟦weakenTy⟧ᵈ' k (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) , tt)
⟦weakenTy⟧ᵈ' k empty Aᵈ _ _ _  = tt
⟦weakenTy⟧ᵈ' k unit Aᵈ _ _ _ = tt
⟦weakenTy⟧ᵈ' k nat Aᵈ _ _ _ = tt
⟦weakenTy⟧ᵈ' k (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) ,
   ⟦weakenTm⟧ᵈ' k v vᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X+= X= Z= v₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) , tt)

⟦weakenTm⟧ᵈ' k (var x) tt X+= X= Z= = tt

⟦weakenTm⟧ᵈ' k (uu i) tt X+= X= Z= = tt

⟦weakenTm⟧ᵈ' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X+= X= Z= a₁ ∙ UUStrNat (qq^₀ ∙ Z=)) ,
   ⟦weakenTm+⟧ᵈ' k b bᵈ X+= X= ElStr= (ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weakenTm+⟧₁' k b bᵈ X+= X= UUStr= ElStr= (ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)) b₁ ∙ UUStrNat (qq₀ ∙ ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Z=))) , tt)
⟦weakenTm⟧ᵈ' k (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weakenTm+⟧ᵈ' k u uᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) u) ,
   (⟦weakenTm+⟧₁' k u uᵈ X+= X= (⟦⟧Ty-ft B) (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) u₁ ∙ ⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)) , tt)
⟦weakenTm⟧ᵈ' k (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X+= X= Z= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weakenTm⟧ᵈ' k f fᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k f) ,
   (⟦weakenTm⟧₁' k f fᵈ X+= X= Z= f₁ ∙ PiStrNat qq^₀ ∙ ap-irr-PiStr Z= (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))) ,
   ⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) , tt)

⟦weakenTm⟧ᵈ' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X+= X= Z= a₁ ∙ UUStrNat (qq^₀ ∙ Z=) ) ,
   (⟦weakenTm+⟧ᵈ' k b bᵈ X+= X= ElStr= (ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Z=))) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weakenTm+⟧₁' k b bᵈ X+= X= UUStr= ElStr= (ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)) b₁ ∙ UUStrNat (qq₀ ∙ ElStrNat qq^₀ ∙ ap-irr-ElStr Z= (⟦weakenTm⟧=' k a aᵈ X+= X= Z=))) , tt)
⟦weakenTm⟧ᵈ' k (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) ,
   ⟦weakenTm⟧ᵈ' k b bᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k b) ,
   (⟦weakenTm⟧₁' k b bᵈ X+= X= Z= b₁ ∙ starstar (⟦⟧Ty-ft A) aₛ ∙ ap-irr-star (⟦weakenTm⟧=' k a aᵈ X+= X= Z=) (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))) , tt)
⟦weakenTm⟧ᵈ' k (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Z= u₁ ∙ SigStrNat qq^₀ ∙ ap-irr-SigStr Z= (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))) , tt)
⟦weakenTm⟧ᵈ' k (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Z= u₁ ∙ SigStrNat qq^₀ ∙ ap-irr-SigStr Z= (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))) , tt)

⟦weakenTm⟧ᵈ' k (empty i) tt X+= X= Z= = tt
⟦weakenTm⟧ᵈ' k (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weakenTy+⟧ᵈ' k A Aᵈ X+= X= EmptyStr= (EmptyStrNat (qq^₀ ∙ Z=)) ,
    ⟦⟧Ty-ft (weakenTy' (prev k) A) ,
    ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z= ,
    ⟦⟧Tmₛ (weakenTm' k u) ,
    (⟦weakenTm⟧₁' k u uᵈ X+= X= Z= u₁ ∙ EmptyStrNat (qq^₀ ∙ Z=)) , tt)

⟦weakenTm⟧ᵈ' k (unit i) tt X+= X= Z= = tt
⟦weakenTm⟧ᵈ' k tt tt X+= X= Z= = tt
⟦weakenTm⟧ᵈ' k (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weakenTy+⟧ᵈ' k A Aᵈ X+= X= UnitStr= (UnitStrNat (qq^₀ ∙ Z=)) ,
    ⟦⟧Ty-ft (weakenTy' (prev k) A) ,
    ⟦weakenTm⟧ᵈ' k dtt dttᵈ X+= X= Z= ,
    ⟦⟧Tmₛ (weakenTm' k dtt) ,
    (⟦weakenTm⟧₁' k dtt dttᵈ X+= X= Z= dtt₁ ∙ starstar UnitStr= ttStrₛ ∙ ap-irr-star (ttStrNat (qq^₀ ∙ Z=)) (⟦weakenTy+⟧=' k A Aᵈ X+= X= UnitStr= (UnitStrNat (qq^₀ ∙ Z=)))) ,
    ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z= ,
    ⟦⟧Tmₛ (weakenTm' k u) ,
    (⟦weakenTm⟧₁' k u uᵈ X+= X= Z= u₁ ∙ UnitStrNat (qq^₀ ∙ Z=)) , tt)

⟦weakenTm⟧ᵈ' k (nat i) tt X+= X= Z= = tt
⟦weakenTm⟧ᵈ' k zero tt X+= X= Z= = tt
⟦weakenTm⟧ᵈ' k (suc u) (uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Z= u₁ ∙ NatStrNat qq^₀ ∙ ap NatStr Z=) , tt)
⟦weakenTm⟧ᵈ' k (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) X+= X= {Z = Y} Z= =
  (Pᵈw , P=w , dOᵈw , dOₛw , dO₁w , dSᵈw , dSₛw , dS₁w , uᵈw , uₛw , u₁w , tt)
    where
      naturalityNat = NatStrNat (qq^₀ ∙ Z=)
      wP= = ⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= naturalityNat
      Pᵈw = ⟦weakenTy+⟧ᵈ' k P Pᵈ X+= X= NatStr= naturalityNat
      P=w = ⟦⟧Ty-ft (weakenTy' (prev k) P)
      dOᵈw = ⟦weakenTm⟧ᵈ' k dO dOᵈ X+= X= Z=
      dOₛw = ⟦⟧Tmₛ (weakenTm' k dO)
      dO₁w = ⟦weakenTm⟧₁' k dO dOᵈ X+= X= Z= dO₁ ∙ starstar NatStr= zeroStrₛ ∙ ap-irr-star (zeroStrNat (qq^₀ ∙ Z=)) wP=
      dSᵈw = ⟦weakenTm++⟧ᵈ' k dS dSᵈ X+= X= (⟦⟧Ty-ft P) NatStr= (⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= naturalityNat)
      dSₛw = ⟦⟧Tmₛ (weakenTm' (prev (prev k)) dS)
      dS₁w = ⟦weakenTm++⟧₁' k dS dSᵈ X+= X= (ft-star ∙ sucStr₀) P= NatStr= wP= dS₁ ∙
             T-dS₁Nat (qq^₀ ∙ Z=) ∙ ap-irr-T-dS₁ refl wP=
      uᵈw = ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z=
      uₛw = ⟦⟧Tmₛ (weakenTm' k u)
      u₁w = ⟦weakenTm⟧₁' k u uᵈ X+= X= Z= u₁ ∙ naturalityNat
      
⟦weakenTm⟧ᵈ' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X+= X= Z= a₁ ∙ UUStrNat (qq^₀ ∙ Z=)) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Z= u₁ ∙ ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)) ,
   ⟦weakenTm⟧ᵈ' k v vᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X+= X= Z= v₁ ∙ ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)) , tt)
⟦weakenTm⟧ᵈ' k (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) , tt)
⟦weakenTm⟧ᵈ' k (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) X+= X= Z= =
  (Aᵈw , A=w , Pᵈw , P=w , dᵈw , dₛw , d₁w , aᵈw , aₛw , a₁w , bᵈw , bₛw , b₁w , pᵈw , pₛw , p₁w , tt)
  where
   Aᵈw = ⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z=
   Aw= = ⟦weakenTy⟧=' k A Aᵈ X+= X= Z=
   A=w = ⟦⟧Ty-ft (weakenTy' k A)
   Pᵈw = ⟦weakenTy+++⟧ᵈ' k P Pᵈ X+= X= T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (qq^₀ ∙ Z=) ∙ ap-irr (T-ftP _) Aw=)
   Pw= = ⟦weakenTy+++⟧=' k P Pᵈ X+= X= T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (qq^₀ ∙ Z=) ∙ ap-irr (T-ftP _) Aw=)
   P=w = ⟦⟧Ty-ft (weakenTy' (prev (prev (prev k))) P)
   dᵈw = ⟦weakenTm+⟧ᵈ' k d dᵈ X+= X= A= Aw=
   dₛw = ⟦⟧Tmₛ (weakenTm' (prev k) d)
   d₁w = ⟦weakenTm+⟧₁' k d dᵈ X+= X= T-d₁= A= Aw= d₁ ∙ T-d₁Nat  (qq^₀ ∙ Z=) ∙ ap-irr-T-d₁ refl Aw= Pw=
   aᵈw = ⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Z=
   aₛw = ⟦⟧Tmₛ (weakenTm' k a)
   a₁w = ⟦weakenTm⟧₁' k a aᵈ X+= X= Z= a₁ ∙ Aw=
   bᵈw = ⟦weakenTm⟧ᵈ' k b bᵈ X+= X= Z=
   bₛw = ⟦⟧Tmₛ (weakenTm' k b)
   b₁w = ⟦weakenTm⟧₁' k b bᵈ X+= X= Z= b₁ ∙ Aw=
   pᵈw = ⟦weakenTm⟧ᵈ' k p pᵈ X+= X= Z=
   pₛw = ⟦⟧Tmₛ (weakenTm' k p)
   p₁w = ⟦weakenTm⟧₁' k p pᵈ X+= X= Z= p₁ ∙ IdStrNat (qq^₀ ∙ Z=) ∙ ap-irr-IdStr refl Aw= (⟦weakenTm⟧=' k a aᵈ X+= X= Z=) (⟦weakenTm⟧=' k b bᵈ X+= X= Z=)

⟦weakenTy⟧=' k (uu i) _ X+= X= Z= =
  UUStrNat (qq^₀ ∙ Z=)
⟦weakenTy⟧=' k (el i v) (vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  ElStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k v vᵈ X+= X= Z=)
⟦weakenTy⟧=' k (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  PiStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-PiStr refl
                 (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)
                 (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))
⟦weakenTy⟧=' k (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  SigStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-SigStr refl
                  (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)
                  (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))
⟦weakenTy⟧=' k empty _ X+= X= Z= = EmptyStrNat (qq^₀ ∙ Z=)
⟦weakenTy⟧=' k unit _ X+= X= Z= = UnitStrNat (qq^₀ ∙ Z=)
⟦weakenTy⟧=' k nat _ X+= X= Z= =
  NatStrNat (qq^₀ ∙ Z=)
⟦weakenTy⟧=' k (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  IdStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-IdStr refl (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=) (⟦weakenTm⟧=' k u uᵈ X+= X= Z=) (⟦weakenTm⟧=' k v vᵈ X+= X= Z=)


⟦weakenTm⟧=' {n = 0} k (var ())
⟦weakenTm⟧=' {n = suc n} last (var x) tt X+= refl refl = star-varCL'' {g₀ = pp^₀ x _} ∙ ap ss (ap-irr-comp refl qq^last ∙ ! ((pp^prev {k = x} X+=)))
⟦weakenTm⟧=' {n = suc n} (prev k) (var last) tt X+= refl Z= = star-varCL' ∙ ap ss qq^prev ∙ ap ss (! (id-left qq₀) ∙ ap-irr-comp refl (ap idC Z=) {f₁' = id₁ ∙ ! Z=}) ∙ ! ss-comp
⟦weakenTm⟧=' {n = suc n} (prev k) (var (prev x)) tt X+= refl Z= = star-varCL'' {g₀ = pp^₀ (prev x) _} ∙ ap ss (ap-irr-comp (pp^prev refl) qq^prev ∙ assoc ∙ ap-irr-comp refl (pp-qq ∙ ap-irr-comp refl (ap pp Z=)) ∙ ! (assoc {f₁ = pp₁ ∙ ap ft (! Z=) ∙ ft-star ∙ qq^₀} {g₀ = qq^₀} {h₀ = pp^₀ x _})) ∙ ! (star-varCL'' {g₀ = comp₀ ∙ qq^₀}) ∙ ap ss (ap-irr-comp (! star-varCL'' ∙ ⟦weakenTm⟧=' k (var x) tt X+= refl refl) refl) ∙ star-varCL'' ∙ ap ss (! (pp^prev {k = weakenVar' k x} (ap ft (! Z=) ∙ ft-star ∙ qq^₀)))

⟦weakenTm⟧=' k (uu i) tt X+= X= Z= =
  uuStrNat (qq^₀ ∙ Z=)

⟦weakenTm⟧=' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  piStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-piStr refl
                 (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)
                 (⟦weakenTm+⟧=' k b bᵈ X+= X= ElStr= (ElStrNat qq^₀ ∙ ap-irr-ElStr Z= (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)))
⟦weakenTm⟧=' k (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  lamStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-lamStr refl
                  (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)
                  (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))
                  (⟦weakenTm+⟧=' k u uᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))
⟦weakenTm⟧=' k (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X+= X= Z= =
  appStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-appStr refl
                  (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)
                  (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))
                  (⟦weakenTm⟧=' k f fᵈ X+= X= Z=)
                  (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)

⟦weakenTm⟧=' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  sigStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-sigStr refl
                  (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)
                  (⟦weakenTm+⟧=' k b bᵈ X+= X= ElStr= (ElStrNat qq^₀ ∙ ap-irr-ElStr Z= (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)))
⟦weakenTm⟧=' k (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  pairStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-pairStr refl
                   (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)
                   (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))
                   (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)
                   (⟦weakenTm⟧=' k b bᵈ X+= X= Z=)
⟦weakenTm⟧=' k (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  pr1StrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-pr1Str refl
                  (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)
                  (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))
                  (⟦weakenTm⟧=' k u uᵈ X+= X= Z=)
⟦weakenTm⟧=' k (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  pr2StrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-pr2Str refl
                  (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)
                  (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))
                  (⟦weakenTm⟧=' k u uᵈ X+= X= Z=)

⟦weakenTm⟧=' k (empty i) tt X+= X= Z= =
  emptyStrNat (qq^₀ ∙ Z=)
⟦weakenTm⟧=' k (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  emptyelimStrNat (qq^₀ ∙ Z=) ∙ ap-irr-emptyelimStr refl (⟦weakenTy+⟧=' k A Aᵈ X+= X= EmptyStr= (EmptyStrNat (qq^₀ ∙ Z=))) (⟦weakenTm⟧=' k u uᵈ X+= X= Z=)
⟦weakenTm⟧=' k (unit i) tt X+= X= Z= =
  unitStrNat (qq^₀ ∙ Z=)
⟦weakenTm⟧=' k tt tt X+= X= Z= =
  ttStrNat (qq^₀ ∙ Z=)
⟦weakenTm⟧=' k (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁) X+= X= Z= =
  unitelimStrNat (qq^₀ ∙ Z=) ∙ ap-irr-unitelimStr refl (⟦weakenTy+⟧=' k A Aᵈ X+= X= UnitStr= (UnitStrNat (qq^₀ ∙ Z=))) (⟦weakenTm⟧=' k dtt dttᵈ X+= X= Z=) (⟦weakenTm⟧=' k u uᵈ X+= X= Z=)

⟦weakenTm⟧=' k (nat i) tt X+= X= Z= =
  natStrNat (qq^₀ ∙ Z=)
⟦weakenTm⟧=' k zero tt X+= X= Z= =
  zeroStrNat (qq^₀ ∙ Z=)
⟦weakenTm⟧=' k (suc u) (uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  sucStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-sucStr refl (⟦weakenTm⟧=' k u uᵈ X+= X= Z=)
⟦weakenTm⟧=' k (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  natelimStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-natelimStr refl
                      (⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= (NatStrNat (qq^₀ ∙ Z=)))
                      (⟦weakenTm⟧=' k dO dOᵈ X+= X= Z=)
                      (⟦weakenTm++⟧=' k dS dSᵈ X+= X= (⟦⟧Ty-ft P) NatStr= (⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= (NatStrNat (qq^₀ ∙ Z=))))
                      (⟦weakenTm⟧=' k u uᵈ X+= X= Z=)

⟦weakenTm⟧=' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  idStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-idStr refl
                 (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)
                 (⟦weakenTm⟧=' k u uᵈ X+= X= Z=)
                 (⟦weakenTm⟧=' k v vᵈ X+= X= Z=)
⟦weakenTm⟧=' k (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  reflStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-reflStr refl
                   (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)
                   (⟦weakenTm⟧=' k u uᵈ X+= X= Z=)
⟦weakenTm⟧=' k (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) X+= X= Z= =
  jjStrNat (qq^₀ ∙ Z=) ∙ ap-irr-jjStr refl
                                      (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)
                                      (⟦weakenTy+++⟧=' k P Pᵈ X+= X= T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (qq^₀ ∙ Z=) ∙ ap-irr (T-ftP _) (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=)))
                                      (⟦weakenTm+⟧=' k d dᵈ X+= X= A= (⟦weakenTy⟧=' k A Aᵈ X+= X= Z=))
                                      (⟦weakenTm⟧=' k a aᵈ X+= X= Z=)
                                      (⟦weakenTm⟧=' k b bᵈ X+= X= Z=)
                                      (⟦weakenTm⟧=' k p pᵈ X+= X= Z=)


⟦⟧TyEq Γᵈ (TySymm dA=) = ! (⟦⟧TyEq Γᵈ dA=)
⟦⟧TyEq Γᵈ (TyTran dB dA= dB=) = ⟦⟧TyEq Γᵈ dA= {A'ᵈ = ⟦⟧Tyᵈ Γᵈ dB} ∙ ⟦⟧TyEq Γᵈ dB=

⟦⟧TyEq Γᵈ UUCong = refl
⟦⟧TyEq Γᵈ (ElCong dv=) = ap-irr-ElStr refl (⟦⟧TmEq Γᵈ dv=)
⟦⟧TyEq Γᵈ {A = sig A B} (SigCong dA dA= dB=) = ap-irr-SigStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TyEq Γᵈ {A = pi A B} (PiCong dA dA= dB=) = ap-irr-PiStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TyEq Γᵈ EmptyCong = refl
⟦⟧TyEq Γᵈ UnitCong = refl
⟦⟧TyEq Γᵈ NatCong = refl
⟦⟧TyEq Γᵈ (IdCong dA du dv) = ap-irr-IdStr refl (⟦⟧TyEq Γᵈ dA) (⟦⟧TmEq Γᵈ du) (⟦⟧TmEq Γᵈ dv)

⟦⟧TyEq Γᵈ ElUU= = eluuStr
⟦⟧TyEq Γᵈ (ElPi= da db) = elpiStr
⟦⟧TyEq Γᵈ (ElSig= da db) = elsigStr
⟦⟧TyEq Γᵈ ElEmpty= = elemptyStr
⟦⟧TyEq Γᵈ ElUnit= = elunitStr
⟦⟧TyEq Γᵈ ElNat= = elnatStr
⟦⟧TyEq Γᵈ (ElId= da du dv) = elidStr

⟦⟧TmEq Γᵈ (VarLastCong dA) = refl
⟦⟧TmEq (Γᵈ , Bᵈ , tt) (VarPrevCong {B = B} {k = k} {k' = k'} dA dx) = ap ss (pp^prev (⟦⟧Ty-ft B)) ∙ (! star-varCL'' ∙ ap-irr-starTm refl (⟦⟧TmEq Γᵈ dx) ∙ star-varCL'') ∙ ! (ap ss (pp^prev (⟦⟧Ty-ft B)))
⟦⟧TmEq Γᵈ (TmSymm du=) = ! (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ (TmTran dv du= du'=) = ⟦⟧TmEq Γᵈ du= {u'ᵈ = ⟦⟧Tmᵈ Γᵈ dv} ∙ ⟦⟧TmEq Γᵈ du'=
⟦⟧TmEq Γᵈ (ConvEq dA' du= dA=) = ⟦⟧TmEq Γᵈ du=

⟦⟧TmEq Γᵈ UUUUCong = refl

⟦⟧TmEq Γᵈ {u = pi i a b} (PiUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , _)} = ap-irr-piStr refl (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq+ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db= (ap-irr-ElStr refl (⟦⟧TmEq Γᵈ da=)))
⟦⟧TmEq Γᵈ {u = lam A B u} (LamCong dA dA= dB= du=) = ap-irr-lamStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) du= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TmEq Γᵈ {u = app A B f a} (AppCong dA dA= dB= df= da=) = ap-irr-appStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ df=) (⟦⟧TmEq Γᵈ da=)

⟦⟧TmEq Γᵈ {u = sig i a b} (SigUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , bᵈ , _)} {u'ᵈ = (a'ᵈ , _ , _ , b'ᵈ , _)} = ap-irr-sigStr refl (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq+ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db= (ap-irr-ElStr refl (⟦⟧TmEq Γᵈ da=)))
⟦⟧TmEq Γᵈ {u = pair A B a b} (PairCong dA dA= dB= da= db=) = ap-irr-pairStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq Γᵈ db=)
⟦⟧TmEq Γᵈ {u = pr1 A B u} (Pr1Cong dA dA= dB= du=) = ap-irr-pr1Str refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ {u = pr2 A B u} (Pr2Cong dA dA= dB= du=) = ap-irr-pr2Str refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ EmptyUUCong = refl
⟦⟧TmEq Γᵈ (EmptyelimCong dA= du=) = ap-irr-emptyelimStr refl (⟦⟧TyEq (Γᵈ , tt , tt) dA=) (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ UnitUUCong = refl
⟦⟧TmEq Γᵈ TTCong = refl
⟦⟧TmEq Γᵈ (UnitelimCong dA= ddtt= du=) = ap-irr-unitelimStr refl (⟦⟧TyEq (Γᵈ , tt , tt) dA=) (⟦⟧TmEq Γᵈ ddtt=) (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ NatUUCong = refl
⟦⟧TmEq Γᵈ ZeroCong = refl
⟦⟧TmEq Γᵈ (SucCong du) = ap-irr-sucStr refl (⟦⟧TmEq Γᵈ du)
⟦⟧TmEq Γᵈ {u = natelim P dO dS u} (NatelimCong dP dP= ddO= ddS= du=) =
  ap-irr-natelimStr
    refl
    (⟦⟧TyEq (Γᵈ , tt , tt) dP=)
    (⟦⟧TmEq Γᵈ ddO=)
    (⟦⟧TmEq+ ((Γᵈ , (tt , tt)) , ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP , tt) ddS= (⟦⟧TyEq (Γᵈ , tt , tt) dP=))
    (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ (IdUUCong da= du= dv=) = ap-irr-idStr refl (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq Γᵈ du=) (⟦⟧TmEq Γᵈ dv=)
⟦⟧TmEq Γᵈ (ReflCong dA= du=) = ap-irr-reflStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq {Γ = Γ}  Γᵈ {u = jj A P d a b p} {u' = jj A' P' d' a' b' p'} (JJCong dA dA= dP= dd= da= db= dp=) {uᵈ = (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt)} = ap-irr-jjStr refl
                                                                                  (⟦⟧TyEq Γᵈ dA=)
                                                                                  (ap-irr (λ z p → ⟦ P ⟧Ty z $ p) (! id=) {b' = Pᵈ'} ∙ ⟦⟧TyEq+ (((Γᵈ , (Aᵈ , tt)) , (wAᵈ , tt)) , (idᵈ , tt)) dP= (id= ∙ ap-irr-IdStr wA=wA' wwA=wwA' (ap ss (ap pp wA=wA')) (ap ss (ap idC wA=wA'))))
                                                                                  (⟦⟧TmEq+ (Γᵈ , ((⟦⟧Tyᵈ Γᵈ dA) , tt)) dd= (⟦⟧TyEq Γᵈ dA=))
                                                                                  (⟦⟧TmEq Γᵈ da=)
                                                                                  (⟦⟧TmEq Γᵈ db=)
                                                                                  (⟦⟧TmEq Γᵈ dp=)
                                                               where
                                                                 X = ⟦ Γ ⟧Ctx $ Γᵈ                                                               
                                                                 [A] = ⟦ A ⟧Ty X $ Aᵈ
                                                                 wAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
                                                                 wAᵈ = ⟦weakenTy⟧ᵈ A Aᵈ A=
                                                                 wA= = ⟦weakenTy⟧= A Aᵈ A=
                                                                 A=A' = ⟦⟧TyEq Γᵈ dA=
                                                                 wA=wA' = ap-irr-star (ap pp A=A') A=A'
                                                                 wwA=wwA' = ap-irr-star (ap pp wA=wA') wA=wA'
                                                                 [wA] = ⟦ weakenTy A ⟧Ty [A] $ wAᵈ
                                                                 [wA]-ft : ft [wA] ≡ [A]
                                                                 [wA]-ft = ⟦⟧Ty-ft (weakenTy A)
                                                                 wwAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty [wA])
                                                                 wwAᵈ = ⟦weakenTy⟧ᵈ (weakenTy A) wAᵈ [wA]-ft
                                                                 wwA= = ⟦weakenTy⟧= (weakenTy A) wAᵈ [wA]-ft
                                                                 [wwA] = ⟦ weakenTy (weakenTy A) ⟧Ty [wA] $ wwAᵈ
                                                                 [wwA]-ft : ft [wwA] ≡ [wA]
                                                                 [wwA]-ft = ⟦⟧Ty-ft (weakenTy (weakenTy A))
                                                                 idᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA])
                                                                 idᵈ = (wwAᵈ , [wwA]-ft , tt , varCₛ (prev last) [wA] , (varC+₁ last [wA]-ft (varCL₁ ∙ wA=) ∙ wwA=) , tt , varCₛ last [wA] , (varCL₁ ∙ wwA=) , tt)
                                                                 id= = ap-irr-IdStr (!  wA=) (! wwA= ∙ ap-irr-star (ap pp (! wA=)) (! wA=)) (ap ss (ap pp (! wA=))) (ap ss (ap idC (! wA=))) {v'ₛ = ssₛ} {v'₁ = ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl}
                                                                 [id] = ⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA] $ idᵈ
                                                                 Pᵈ' : isDefined (⟦ P ⟧Ty [id])
                                                                 Pᵈ' = cong⟦⟧Ty {A = P} (! id=)  Pᵈ
      

⟦⟧TmEq Γᵈ {u = app A B (lam A B u) a} (BetaPi dA dB du da) = betaPiStr ∙ ! (⟦subst⟧Tm= (⟦⟧Ty-ft A) u (⟦⟧Tmᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) du) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))
⟦⟧TmEq Γᵈ (BetaSig1 dA dB da db) = betaSig1Str
⟦⟧TmEq Γᵈ (BetaSig2 dA dB da db) = betaSig2Str
⟦⟧TmEq Γᵈ (BetaUnit dA dtt) = betaUnitStr
⟦⟧TmEq Γᵈ (BetaNatZero dP ddO ddS) = betaNatZeroStr
⟦⟧TmEq {Γ = Γ} Γᵈ {u = natelim P dO dS (suc u)} (BetaNatSuc dP ddO ddS du) =
  betaNatSucStr ∙ ! (⟦subst2⟧Tm= (⟦⟧Ty-ft P) NatStr= dS dSᵈ u uᵈ (⟦⟧Tm₁ Γᵈ du) (natelim P dO dS u) natelimᵈ natelimStr₁)
    where
      Pᵈ = ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP
      dOᵈ = ⟦⟧Tmᵈ Γᵈ ddO
      dO₁ = ⟦⟧Tm₁ Γᵈ ddO ∙ ⟦subst⟧Ty= NatStr= P Pᵈ zero tt zeroStr₁
      dSᵈ = ⟦⟧Tmᵈ ((Γᵈ , tt , tt) , Pᵈ , tt) ddS
      dS₁ : ∂₁ (⟦ dS ⟧Tm (⟦ P ⟧Ty (NatStr (⟦ Γ ⟧Ctx $ Γᵈ)) $ Pᵈ) $ dSᵈ)
            ≡ T-dS₁ (⟦ Γ ⟧Ctx $ Γᵈ) (⟦ P ⟧Ty (NatStr (⟦ Γ ⟧Ctx $ Γᵈ)) $ ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP) (⟦⟧Ty-ft P)
      dS₁ = ⟦⟧Tm₁ ((Γᵈ , tt , tt) , Pᵈ , tt) ddS
            ∙ ⟦subst⟧Ty= NatStr= (weakenTy' (prev last) (weakenTy' (prev last) P))
                                 (⟦weakenTy+⟧ᵈ (weakenTy' (prev last) P) (⟦weakenTy+⟧ᵈ P Pᵈ NatStr= NatStr= (NatStrNat pp₀)) (⟦⟧Ty-ft P) NatStr= (NatStrNat pp₀))
                                 (suc (var (prev last)))
                                 (tt , ssₛ , (varC+₁ last (⟦⟧Ty-ft P) varCL₁ ∙ ! (star-comp {g₀ = pp₀}) ∙ NatStrNat (comp₀ ∙ pp₀)) , tt)
                                 sucStr₁
            ∙ ap-irr-star refl (! (ap-irr-star (ap-irr-qq refl (NatStrNat pp₀))
                                               (⟦weakenTy+⟧= P Pᵈ NatStr= NatStr= (NatStrNat pp₀))
                                  ∙ ⟦weakenTy+⟧= (weakenTy' (prev last) P) (⟦weakenTy+⟧ᵈ P Pᵈ NatStr= NatStr= (NatStrNat pp₀)) (⟦⟧Ty-ft P) NatStr= (NatStrNat pp₀)))
      uᵈ = ⟦⟧Tmᵈ Γᵈ du
      natelimᵈ = (Pᵈ , ⟦⟧Ty-ft P , dOᵈ , ⟦⟧Tmₛ dO , dO₁ , dSᵈ , ⟦⟧Tmₛ dS , dS₁ , uᵈ , ⟦⟧Tmₛ u , ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧TmEq {Γ = Γ} Γᵈ {u = jj A P d a a (refl A a)} (BetaIdRefl dA dP dd da) =
  betaIdStr ∙ ! (⟦subst⟧Tm= (⟦⟧Ty-ft A) d (⟦⟧Tmᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dd) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))
    


⟦⟧TmEq Γᵈ {u = f} {u' = lam A B _} (EtaPi dA dB df) =
  etaPiStr {fₛ = ⟦⟧Tmₛ f} {f₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = ⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Ty-ft A , ⟦⟧Tyᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB , ⟦⟧Ty-ft B , tt} df}
  ∙ ap-irr-lamStr refl refl refl
     (ap-irr-appStr refl (⟦weakenTy⟧= A (⟦⟧Tyᵈ Γᵈ dA) (⟦⟧Ty-ft A))
                         (⟦weakenTy+⟧= B (⟦⟧Tyᵈ (Γᵈ , (⟦⟧Tyᵈ Γᵈ dA) , tt) dB) (⟦⟧Ty-ft A) (⟦⟧Ty-ft A) (⟦weakenTy⟧= A (⟦⟧Tyᵈ Γᵈ dA) (⟦⟧Ty-ft A)))
                         (⟦weakenTm⟧= f (⟦⟧Tmᵈ Γᵈ df) (⟦⟧Ty-ft A))
                         refl)
⟦⟧TmEq Γᵈ (EtaSig dA dB du) =
  etaSigStr

⟦tsubst⟧Tyᵈ (uu i) tt δ δᵈ = tt
⟦tsubst⟧Tyᵈ (el i v) (vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ v₁ δ δᵈ ∙ UUStrNat (⟦⟧Mor₀ δ)) , tt)

⟦tsubst⟧Tyᵈ (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) , tt)

⟦tsubst⟧Tyᵈ (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) , tt)

⟦tsubst⟧Tyᵈ empty tt δ δᵈ = tt

⟦tsubst⟧Tyᵈ unit tt δ δᵈ = tt

⟦tsubst⟧Tyᵈ nat tt δ δᵈ = tt

⟦tsubst⟧Tyᵈ (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ v₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)
 
⟦tsubst⟧Tmᵈ (var ()) uᵈ ◇ δᵈ
⟦tsubst⟧Tmᵈ (var last) _ (δ , u) (_ , uᵈ , _) = uᵈ
⟦tsubst⟧Tmᵈ (var (prev x)) tt (δ , u) (δᵈ , _) = ⟦tsubst⟧Tmᵈ (var x) tt δ δᵈ

⟦tsubst⟧Tmᵈ (uu i) tt δ δᵈ = tt

⟦tsubst⟧Tmᵈ (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ UUStrNat (⟦⟧Mor₀ δ)) ,
  ⟦tsubst⟧Tm+ᵈ b bᵈ δ δᵈ ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) ,
  ⟦⟧Tmₛ (b [ weakenMor+ δ ]Tm) ,
  (⟦tsubst⟧Tm+₁ b bᵈ b₁ δ δᵈ UUStr= ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) ∙ UUStrNat (qq₀ ∙ ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ))) , tt)
  
⟦tsubst⟧Tmᵈ (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Tmₛ (u [ weakenMor+ δ ]Tm) ,
   (⟦tsubst⟧Tm+₁ u uᵈ u₁ δ δᵈ B= A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ∙ ⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) , tt)
     
⟦tsubst⟧Tmᵈ (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ f fᵈ δ δᵈ ,
   ⟦⟧Tmₛ (f [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ f fᵈ f₁ δ δᵈ ∙ PiStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-PiStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) ,
   ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)

⟦tsubst⟧Tmᵈ (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ) ,
  ⟦tsubst⟧Tm+ᵈ b bᵈ δ δᵈ ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) ,
  ⟦⟧Tmₛ (b [ weakenMor+ δ ]Tm) ,
  (⟦tsubst⟧Tm+₁ b bᵈ b₁ δ δᵈ UUStr= ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) ∙ UUStrNat (qq₀ ∙ ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ))) , tt)

⟦tsubst⟧Tmᵈ (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ ,
  ⟦⟧Tmₛ (b [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ b bᵈ b₁ δ δᵈ ∙ starstar A= aₛ ∙ ap-irr-star (⟦tsubst⟧Tm= a aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt ) 

⟦tsubst⟧Tmᵈ (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
  ⟦⟧Tmₛ (u [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ SigStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-SigStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt)

⟦tsubst⟧Tmᵈ (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
  ⟦⟧Tmₛ (u [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ SigStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-SigStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt)

⟦tsubst⟧Tmᵈ (empty i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ EmptyStr= (EmptyStrNat (⟦⟧Mor₀ δ)) ,
   ⟦⟧Ty-ft (A [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ EmptyStrNat (⟦⟧Mor₀ δ)) , tt)

⟦tsubst⟧Tmᵈ (unit i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ tt tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ UnitStr= (UnitStrNat (⟦⟧Mor₀ δ)) ,
   ⟦⟧Ty-ft (A [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ dtt dttᵈ δ δᵈ ,
   ⟦⟧Tmₛ (dtt [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ dtt dttᵈ dtt₁ δ δᵈ ∙ starstar UnitStr= ttStrₛ ∙ ap-irr-star (ttStrNat (⟦⟧Mor₀ δ)) (⟦tsubst⟧Ty+= A Aᵈ δ δᵈ UnitStr= (UnitStrNat (⟦⟧Mor₀ δ)))) , 
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ UnitStrNat (⟦⟧Mor₀ δ)) , tt)

⟦tsubst⟧Tmᵈ (nat i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ zero tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (suc u) (uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ NatStrNat (⟦⟧Mor₀ δ)) , tt)
⟦tsubst⟧Tmᵈ {X = X} (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (Pᵈs , P=s , dOᵈs , dOₛs , dO₁s , dSᵈs , dSₛs , dS₁s , uᵈs , uₛs , u₁s , tt)
    where
      naturalityNat = NatStrNat (⟦⟧Mor₀ δ)      
      sP= = ⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= naturalityNat
      Pᵈs = ⟦tsubst⟧Ty+ᵈ P Pᵈ δ δᵈ NatStr= naturalityNat
      P=s = ⟦⟧Ty-ft (P [ weakenMor+ δ ]Ty)
      dOᵈs = ⟦tsubst⟧Tmᵈ dO dOᵈ δ δᵈ
      dOₛs = ⟦⟧Tmₛ (dO [ δ ]Tm)
      dO₁s = ⟦tsubst⟧Tm₁ dO dOᵈ dO₁ δ δᵈ ∙ starstar NatStr= zeroStrₛ ∙ ap-irr-star (zeroStrNat (⟦⟧Mor₀ δ)) sP= 
      dSᵈs = ⟦tsubst⟧Tm++ᵈ dS dSᵈ δ δᵈ P= NatStr= sP=
      dSₛs = ⟦⟧Tmₛ (dS [ weakenMor+ (weakenMor+ δ) ]Tm)
      dS₁s = ⟦tsubst⟧Tm++₁ dS dSᵈ dS₁ δ δᵈ T-dS₁= P= NatStr= sP=
             ∙ T-dS₁Nat (⟦⟧Mor₀ δ) ∙ ap-irr-T-dS₁ refl sP=
      uᵈs = ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ
      uₛs = ⟦⟧Tmₛ (u [ δ ]Tm)
      u₁s = ⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ naturalityNat

⟦tsubst⟧Tmᵈ (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ UUStrNat (⟦⟧Mor₀ δ)) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) ,
   ⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ v₁ δ δᵈ ∙ ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) , tt)
⟦tsubst⟧Tmᵈ (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) δ δᵈ =
  (Aᵈs , A=s , Pᵈs , P=s , dᵈs , dₛs , d₁s , aᵈs , aₛs , a₁s , bᵈs , bₛs , b₁s , pᵈs , pₛs , p₁s , tt)
    where
      Aᵈs = ⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ
      A=s = ⟦⟧Ty-ft (A [ δ ]Ty)
      sA= = ⟦tsubst⟧Ty= A Aᵈ δ δᵈ
      Pᵈs = ⟦tsubst⟧Ty+++ᵈ P Pᵈ δ δᵈ T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (⟦⟧Mor₀ δ) ∙ ap-irr (T-ftP _) sA=)
      P=s = ⟦⟧Ty-ft (P [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty)
      sP= = ⟦tsubst⟧Ty+++= P Pᵈ δ δᵈ T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (⟦⟧Mor₀ δ) ∙ ap-irr (T-ftP _) sA=)
      dᵈs = ⟦tsubst⟧Tm+ᵈ d dᵈ δ δᵈ A= sA=
      dₛs = ⟦⟧Tmₛ (d [ weakenMor+ δ ]Tm)
      d₁s = ⟦tsubst⟧Tm+₁ d dᵈ d₁ δ δᵈ T-d₁= A= sA= ∙ T-d₁Nat (⟦⟧Mor₀ δ) ∙ ap-irr-T-d₁ refl sA= sP= 
      aᵈs = ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ
      aₛs = ⟦⟧Tmₛ (a [ δ ]Tm)
      a₁s = ⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ sA=
      bᵈs = ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ
      bₛs = ⟦⟧Tmₛ (b [ δ ]Tm)
      b₁s = ⟦tsubst⟧Tm₁ b bᵈ b₁ δ δᵈ ∙ sA=
      pᵈs = ⟦tsubst⟧Tmᵈ p pᵈ δ δᵈ
      pₛs = ⟦⟧Tmₛ (p [ δ ]Tm)
      p₁s = ⟦tsubst⟧Tm₁ p pᵈ p₁ δ δᵈ ∙ IdStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-IdStr refl sA= (⟦tsubst⟧Tm= a aᵈ δ δᵈ) (⟦tsubst⟧Tm= b bᵈ δ δᵈ)
  

⟦tsubst⟧Ty= (uu i) Aᵈ δ δᵈ =
  UUStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= (el i v) (vᵈ , _) δ δᵈ =
  ElStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-ElStr refl
                 (⟦tsubst⟧Tm= v vᵈ δ δᵈ)
⟦tsubst⟧Ty= (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  PiStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-PiStr refl
                 (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                 (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Ty= (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  SigStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-SigStr refl
                  (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Ty= empty Aᵈ δ δᵈ =
  EmptyStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= unit Aᵈ δ δᵈ =
  UnitStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= nat Aᵈ δ δᵈ =
  NatStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  IdStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-IdStr refl
                 (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= v vᵈ δ δᵈ)

⟦tsubst⟧Tm= (var ()) _ ◇
⟦tsubst⟧Tm= (var last) _ (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) =
  star-varCL'' {g₀ = id₀} ∙ ap ss (id-right (comp₁ ∙ qq₁)) ∙ ! ss-comp ∙ ss-of-section (⟦ u ⟧Tm _ $ _) (⟦⟧Tmₛ u)
⟦tsubst⟧Tm= (var (prev k)) _ (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) =
  (star-varCL'' {g₀ = pp^₀ (prev k) _} ∙ ap ss (ap-irr-comp (pp^prev refl) refl ∙ ! assoc ∙ ap-irr-comp (assoc ∙ ap-irr-comp refl pp-qq ∙ ! assoc) refl ∙ assoc ∙ ap-irr-comp refl (refl ∙ is-section= (ft-star ∙ ⟦⟧Mor₀ δ) (⟦⟧Tmₛ u) u₁) ∙ id-left (comp₀ ∙ ⟦⟧Mor₀ δ)) ∙ ! (star-varCL'' {g₀ = pp^₀ k _})) ∙ ⟦tsubst⟧Tm= (var k) tt δ δᵈ

⟦tsubst⟧Tm= (uu i) tt δ δᵈ =
  uuStrNat (⟦⟧Mor₀ δ)

⟦tsubst⟧Tm= (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  piStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-piStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                      (⟦tsubst⟧Tm+= b bᵈ δ δᵈ ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)))
                      
⟦tsubst⟧Tm= (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  lamStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-lamStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                       (⟦tsubst⟧Tm+= u uᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Tm= (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  appStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-appStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                       (⟦tsubst⟧Tm= f fᵈ δ δᵈ)
                       (⟦tsubst⟧Tm= a aᵈ δ δᵈ)

⟦tsubst⟧Tm= (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  sigStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-sigStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                       (⟦tsubst⟧Tm+= b bᵈ δ δᵈ ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)))

⟦tsubst⟧Tm= (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  pairStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pairStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                        (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                        (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                        (⟦tsubst⟧Tm= b bᵈ δ δᵈ)

⟦tsubst⟧Tm= (pr1 A B u) (Aᵈ , A= , Bᵈ  , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  pr1StrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pr1Str refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                       (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  pr2StrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pr2Str refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                       (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (empty i) tt δ δᵈ =
  emptyStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  emptyelimStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-emptyelimStr refl (⟦tsubst⟧Ty+= A Aᵈ δ δᵈ EmptyStr= (EmptyStrNat (⟦⟧Mor₀ δ))) (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (unit i) tt δ δᵈ =
  unitStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= tt tt δ δᵈ =
  ttStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  unitelimStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-unitelimStr refl (⟦tsubst⟧Ty+= A Aᵈ δ δᵈ UnitStr= (UnitStrNat (⟦⟧Mor₀ δ))) (⟦tsubst⟧Tm= dtt dttᵈ δ δᵈ) (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
  
⟦tsubst⟧Tm= (nat i) tt δ δᵈ =
  natStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= zero tt δ δᵈ =
  zeroStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (suc u) (uᵈ , uₛ , u₁ , tt) δ δᵈ =
  sucStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-sucStr refl (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  natelimStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-natelimStr refl (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= (NatStrNat (⟦⟧Mor₀ δ)))
                           (⟦tsubst⟧Tm= dO dOᵈ δ δᵈ)
                           (⟦tsubst⟧Tm++= dS dSᵈ δ δᵈ P= NatStr= (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= (NatStrNat (⟦⟧Mor₀ δ))))
                           (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  idStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-idStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                      (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
                      (⟦tsubst⟧Tm= v vᵈ δ δᵈ)
⟦tsubst⟧Tm= (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  reflStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-reflStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                        (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) δ δᵈ =
  jjStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-jjStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ )
                      (⟦tsubst⟧Ty+++= P Pᵈ δ δᵈ T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (⟦⟧Mor₀ δ) ∙ ap-irr (T-ftP _) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)))
                      (⟦tsubst⟧Tm+= d dᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                      (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                      (⟦tsubst⟧Tm= b bᵈ δ δᵈ)
                      (⟦tsubst⟧Tm= p pᵈ δ δᵈ)



{- To conclude, we prove a few more additional properties, needed for initiality -}

{- Totality of the interpretation function on derivable contexts -}

⟦⟧Ctxᵈ : {Γ : Ctx n} (dΓ : ⊢ Γ) → isDefined (⟦ Γ ⟧Ctx)
⟦⟧Ctxᵈ {Γ = ◇} tt = tt
⟦⟧Ctxᵈ {Γ = Γ , A} (dΓ , dA) = let Γᵈ = ⟦⟧Ctxᵈ dΓ in (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt)

{- Interpretation of context equalities -}

⟦⟧CtxEq : {Γ Γ' : Ctx n} (dΓ= : ⊢ Γ == Γ') {Γᵈ : isDefined (⟦ Γ ⟧Ctx)} {Γ'ᵈ : isDefined (⟦ Γ' ⟧Ctx)}
        → ⟦ Γ ⟧Ctx $ Γᵈ ≡ ⟦ Γ' ⟧Ctx $ Γ'ᵈ
⟦⟧CtxEq {Γ = ◇} {◇} _ = refl
⟦⟧CtxEq {Γ = Γ , A} {Γ' , A'} (dΓ= , _ , _ , dA= , _) {Γᵈ = Γᵈ , Aᵈ , tt}
  = ⟦⟧TyEq+ Γᵈ dA= (⟦⟧CtxEq dΓ=)

{- Interpretation of morphism equalities -}

⟦⟧MorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {Y : Ob m} (dδ= : Γ ⊢ δ == δ' ∷> Δ) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} {δ'ᵈ : isDefined (⟦ δ' ⟧Mor X Y)}
        → ⟦ δ ⟧Mor X Y $ δᵈ ≡ ⟦ δ' ⟧Mor X Y $ δ'ᵈ
⟦⟧MorEq {Δ = ◇} {δ = ◇} {◇} Γᵈ tt = refl
⟦⟧MorEq {Γ' = Γ'} {Δ = Δ , B} {δ = δ , u} {δ' , u'} Γᵈ (dδ= , du=) = ap-irr-comp (ap-irr-qq (⟦⟧MorEq {Γ' = Γ'} {Δ' = Δ} Γᵈ dδ=) refl) (⟦⟧TmEq Γᵈ du=)

{- Interpretation of morphism substitution -}

⟦tsubst⟧Morᵈ : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z)) → isDefined (⟦ θ [ δ ]Mor ⟧Mor X Z)
⟦tsubst⟧Mor= : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z))
             → ⟦ θ [ δ ]Mor ⟧Mor X Z $ (⟦tsubst⟧Morᵈ Y= δ δᵈ θ θᵈ) ≡ comp (⟦ θ ⟧Mor Y' Z $ θᵈ) (⟦ δ ⟧Mor X Y $ δᵈ) (⟦⟧Mor₀ θ) (⟦⟧Mor₁ δ ∙ Y=)

⟦tsubst⟧Morᵈ refl δ δᵈ ◇ tt = tt
⟦tsubst⟧Morᵈ refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) = (⟦tsubst⟧Morᵈ refl δ δᵈ θ θᵈ , ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ , ⟦⟧Mor₁ (θ [ δ ]Mor) , (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ! (ap-irr-star (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl ∙ star-comp)) , tt)

⟦tsubst⟧Mor= refl δ δᵈ ◇ θᵈ = ! (ptmor-unique _ _ (comp₀ ∙ ⟦⟧Mor₀ δ) (comp₁ ∙ ptmor₁))
⟦tsubst⟧Mor= refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) =
 let thing = ! assoc ∙ ap-irr-comp (is-section= (ap ft (comp₁ {f = idC _} {g₀ = ⟦⟧Tm₀ u} {f₁ = id₁} ∙ u₁) ∙ ft-star ∙ ⟦⟧Mor₀ θ) (⟦⟧Tmₛ u) (! comp₁)) refl ∙ id-right (⟦⟧Mor₁ δ) in
  ap-irr-comp (ap-irr-qq (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl ∙ qq-comp) (! (⟦tsubst⟧Tm= u uᵈ δ δᵈ))
  ∙ assoc {f₁ = starTm₁ _ (ft-star ∙ ⟦⟧Mor₀ θ) _ (⟦⟧Tmₛ u) u₁ _} {g₀ = qq₀}
  ∙ ! (assoc ∙ ap-irr-comp refl (ss-qq ∙ ap-irr-comp (ap-irr-qq thing (comp₁ ∙ u₁)) refl))
