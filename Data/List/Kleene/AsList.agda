{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Re-exports of the Data.List.Kleene module, renamed to duplicate the
-- Data.List API.


module Data.List.Kleene.AsList where

import Data.List.Kleene.Base as Kleene
open import Data.List.Kleene.Base
  using
    ( []
    )
  renaming
    ( _⋆ to List
    ; foldr⋆ to foldr
    ; foldl⋆ to foldl
    ; _⋆++⋆_ to _++_
    ; map⋆ to map
    ; pure⋆ to pure
    ; _⋆<*>⋆_ to _<*>_
    ; _⋆>>=⋆_ to _>>=_
    ; mapAccumL⋆ to mapAccumL
    ; _[_]⋆ to _[_]
    ; applyUpTo⋆ to applyUpTo
    ; upTo⋆ to upTo
    ; intersperse⋆ to intersperse
    ; _⋆<|>⋆_ to _<|>_
    ; ⋆zipWith⋆ to zipWith
    ; unzipWith⋆ to unzipWith
    ; partitionSumsWith⋆ to partitionSumsWith
    ; ⋆transpose⋆ to transpose
    ; reverse⋆ to reverse
    )
  public

infixr 5 _∷_
pattern _∷_ x xs = Kleene.∹ x Kleene.& xs

scanr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → List B
scanr f b xs = Kleene.∹ Kleene.scanr⋆ f b xs

scanl : ∀ {a b} {A : Set a} {B : Set b} → (B → A → B) → B → List A → List B
scanl f b xs = Kleene.∹ Kleene.scanl⋆ f b xs

tails : ∀ {a} {A : Set a} → List A → List (List A)
tails xs = foldr (λ x xs → (Kleene.∹ x) ∷ xs) ([] ∷ []) (Kleene.tails⋆ xs)

import Data.List.Kleene.Syntax

module Syntax = Data.List.Kleene.Syntax using (_]; _,_) renaming (⋆[_ to [_)
