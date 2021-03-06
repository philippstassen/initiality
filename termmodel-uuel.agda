{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat
open import quotients
open import termmodel-common
open import termmodel-synccat

open CCat hiding (Mor) renaming (id to idC)


{- UU -}

UUStrS-// : (i : ℕ) → DCtx n → DCtx (suc n)
UUStrS-// i Γ = ((ctx Γ , uu i) , (der Γ , UU))

UUStrS-eq : {i : ℕ} {Γ Γ' : DCtx n} → Γ ≃ Γ' → proj {R = ObEquiv} (UUStrS-// i Γ) ≡ proj (UUStrS-// i Γ')
UUStrS-eq dΓ= = eq (box (unOb≃ dΓ= ,, UUCong))

UUStrS : (i : ℕ) → ObS n → ObS (suc n)
UUStrS i = //-elim-Ctx (λ Γ → proj (UUStrS-// i Γ)) (λ rΓ → proj= (UUStrS-eq rΓ))

UUStr=S : (i : ℕ) (Γ : ObS n) → ftS (UUStrS i Γ) ≡ Γ
UUStr=S i = //-elimP-Ctx (λ Γ → refl)

UUStrSynCCat : CCatwithUU synCCat
CCatwithUU.UUStr UUStrSynCCat = UUStrS
CCatwithUU.UUStr= UUStrSynCCat = UUStr=S _ _
CCatwithUU.UUStrNat' UUStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ g₁ → refl)))


{- El -}

ElStrS-// : (i : ℕ) (Γ : DCtx n) (v : DMor n (suc n)) (vₛ : S.is-section (proj v)) (v₁ : ∂₁S (proj v) ≡ UUStrS i (proj Γ)) → DCtx (suc n)
ElStrS-// i Γ v vₛ v₁ = ((ctx Γ , el i (getTm v)) , (der Γ , El (dTm refl v vₛ v₁)))

ElStrS-eq : {i : ℕ} {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {v v' : DMor n (suc n)} (rv : v ≃ v') (vₛ : _) (v'ₛ : _) (v₁ : _) (v'₁ : _) → proj {R = ObEquiv} (ElStrS-// i Γ v vₛ v₁) ≡ proj {R = ObEquiv} (ElStrS-// i Γ' v' v'ₛ v'₁)
ElStrS-eq rΓ rv vₛ v'ₛ v₁ v'₁ =
  eq (box (unOb≃ rΓ ,, ElCong (dTm= (box (unOb≃ rΓ ,, TyRefl UU)) refl rv vₛ v'ₛ v₁ v'₁)))

ElStrS : (i : ℕ) (Γ : ObS n) (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ UUStrS i Γ) → ObS (suc n)
ElStrS i = //-elim-Ctx (λ Γ → //-elim-Tm (λ v vₛ v₁ → proj (ElStrS-// i Γ v vₛ v₁))
                                         (λ rv vₛ v'ₛ v₁ v'₁ → proj= (ElStrS-eq (ref Γ) rv vₛ v'ₛ v₁ v'₁)))
                       (λ rΓ → //-elimP-Tm (λ v vₛ v₁ v₁' → proj= (ElStrS-eq rΓ (ref v) vₛ vₛ v₁ v₁')))

ElStr=S : (i : ℕ) (Γ : ObS n) (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ UUStrS i Γ) → ftS (ElStrS i Γ v vₛ v₁) ≡ Γ
ElStr=S i = //-elimP-Ctx (λ Γ → //-elimP (λ v vₛ v₁ → refl))

ElStrSynCCat : CCatwithEl synCCat UUStrSynCCat
CCatwithEl.ElStr ElStrSynCCat i Γ v vₛ v₁ = ElStrS i Γ v vₛ v₁
CCatwithEl.ElStr= ElStrSynCCat = ElStr=S _ _ _ _ _
CCatwithEl.ElStrNat' ElStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ v vₛ v₁ g₁ → refl))))


{- uu -}

uuStrS-// : (i : ℕ) (Γ : DCtx n) → DMor n (suc n)
uuStrS-// i Γ = dmorTm Γ (uu (suc i)) UU (uu i) UUUU

uuStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → proj {R = MorEquiv} (uuStrS-// i Γ) ≡ proj (uuStrS-// i Γ')
uuStrS-eq i rΓ = dmorTm= rΓ UU UU UUCong UUUU UUUU UUUUCong

uuStrS : (i : ℕ) (Γ : ObS n) → MorS n (suc n)
uuStrS i = //-elim-Ctx (λ Γ → proj (uuStrS-// i Γ)) (λ rΓ → proj= (uuStrS-eq i rΓ))

uuStrₛS : (i : ℕ) (Γ : ObS n) → S.is-section (uuStrS i Γ)
uuStrₛS i = //-elimP (λ Γ → dmorTmₛ UU UUUU)

uuStr₁S : (i : ℕ) (Γ : ObS n) → ∂₁S (uuStrS i Γ) ≡ UUStrS (suc i) Γ
uuStr₁S i = //-elimP (λ Γ → refl)

uuStrSynCCat : CCatwithuu synCCat UUStrSynCCat
CCatwithuu.uuStr uuStrSynCCat = uuStrS
CCatwithuu.uuStrₛ uuStrSynCCat {Γ = Γ} = uuStrₛS _ Γ
CCatwithuu.uuStr₁ uuStrSynCCat {Γ = Γ} = uuStr₁S _ Γ
CCatwithuu.uuStrNat' uuStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ g₁ → refl)))


{- ElUU= -}

eluuStrS : (i : ℕ) (Γ : ObS n) → ElStrS (suc i) Γ (uuStrS i Γ) (uuStrₛS i Γ) (uuStr₁S i Γ) ≡ UUStrS i Γ
eluuStrS i = //-elimP (λ Γ → eq (box (CtxRefl (der Γ) ,, ElUU=)))
