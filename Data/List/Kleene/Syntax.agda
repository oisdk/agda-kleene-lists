{-# OPTIONS --without-K --safe #-}

module Data.List.Kleene.Syntax where

open import Data.List hiding ([_])
open import Data.List.Kleene.Base
open import Data.Product

infixr 4 _,_
infixr 5 _]
data ListSyntax {a} (A : Set a) : Set a where
  _]  : A → ListSyntax A
  _,_ : A → ListSyntax A → ListSyntax A

infixr 4 ⋆[_ ⁺[_ [_
⋆[_ : ∀ {a} {A : Set a} → ListSyntax A → A ⋆
⋆[ x ] = ∹ x & []
⋆[ x , xs = ∹ x & (⋆[ xs)

⁺[_ : ∀ {a} {A : Set a} → ListSyntax A → A ⁺
⁺[ x ] = x & []
⁺[ x , xs = x & ∹ (⁺[ xs)

[_ : ∀ {a} {A : Set a} → ListSyntax A → List A
[ x ] = x ∷ []
[ x , xs = x ∷ ([ xs)

private
  open import Data.Nat

  _ : ℕ ⋆
  _ = ⋆[ 1 , 2 , 3 ]

  _ : ℕ ⁺
  _ = ⁺[ 1 , 2 , 3 ]

  _ : List ℕ
  _ = [ 1 , 2 , 3 ]
