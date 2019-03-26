{-# OPTIONS --without-K --safe #-}

module Data.List.Kleene.Properties where

open import Data.List.Kleene.Base

open import Relation.Binary
open import Relation.Unary

open import Function

module _ {a r} {A : Set a} {R : Rel A r} where
  infix 4 _≈_
  _≈_ = R

  open import Algebra.FunctionProperties _≈_

  foldr-universal : Transitive _≈_
                  → ∀ {b} {B : Set b} (h : B ⋆ → A) f e
                  → ∀[ f ⊢ Congruent₁ ]
                  → (h [] ≈ e)
                  → (∀ x xs → h (∹ x & xs) ≈ f x (h xs))
                  → ∀ xs → h xs ≈ foldr⋆ f e xs
  foldr-universal trans h f e cong-f base cons [] = base
  foldr-universal trans h f e cong-f base cons (∹ x & xs) =
    (cons x xs) ⟨ trans ⟩ cong-f (foldr-universal trans h f e cong-f base cons xs)

  foldr-fusion : Transitive _≈_
               → Reflexive _≈_
               → ∀ {b c} {B : Set b} {C : Set c} (f : C → A) {_⊕_ : B → C → C} {_⊗_ : B → A → A} e
               → ∀[ _⊗_ ⊢ Congruent₁ ]
               → (∀ x y → f (x ⊕ y) ≈ x ⊗ f y)
               → ∀ xs → f (foldr⋆ _⊕_ e xs) ≈ foldr⋆ _⊗_ (f e) xs
  foldr-fusion trans refl h {f} {g} e cong-g fuse =
    foldr-universal trans (h ∘ foldr⋆ f e) g (h e) cong-g refl (λ x xs → fuse x (foldr⋆ f e xs))
