{-# OPTIONS --rewriting --prop --without-K #-}

module ex where
import common renaming (Unit to metaUnit)
open import typetheoryexplicit public
open import reflectionexplicit public
open import syntxexplicit public
open import rulesexplicit public 

module shared where
open common 
