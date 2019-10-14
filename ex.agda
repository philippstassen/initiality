{-# OPTIONS --rewriting --prop --without-K #-}

module ex where
open import common renaming (Unit to metaUnit)
open import typetheoryexplicit public
open import reflectionexplicit public
open import syntxexplicit public
open import rulesexplicit public renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)
