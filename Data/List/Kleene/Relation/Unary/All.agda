
module Data.List.Kleene.Relation.Unary.All where

open import Data.List.Kleene.Base
open import Relation.Unary
open import Relation.Nullary
open import Level using (_⊔_)
open import Function

mutual
  record All⁺ {a p} {A : Set a} (P : Pred A p) (xs : A ⁺) : Set (a ⊔ p) where
    constructor P⟨_&_⟩
    inductive
    field
      P⟨head⟩ : P (head xs)
      P⟨tail⟩ : All⋆ P (tail xs)

  data All⋆ {a p} {A : Set a} (P : Pred A p) : Pred (A ⋆) (a ⊔ p) where
    P⟨[]⟩ : All⋆ P []
    P⟨∹_⟩ : ∀ {xs} → All⁺ P xs → All⋆ P (∹ xs)
open All⁺ public

module _ {a p} {A : Set a} {P : Pred A p} where
  mutual
    all⋆ : Decidable P → Decidable (All⋆ P)
    all⋆ p? [] = yes P⟨[]⟩
    all⋆ p? (∹ xs) with all⁺ p? xs
    all⋆ p? (∹ xs) | yes p = yes P⟨∹ p ⟩
    all⋆ p? (∹ xs) | no ¬p = no λ { P⟨∹ x ⟩ → ¬p x }

    all⁺ : Decidable P → Decidable (All⁺ P)
    all⁺ p? xs with p? (head xs) | all⋆ p? (tail xs)
    all⁺ p? xs | no ¬p | ys = no (¬p ∘ P⟨head⟩)
    all⁺ p? xs | yes p | yes ps = yes P⟨ p & ps ⟩
    all⁺ p? xs | yes p | no ¬p = no (¬p ∘ P⟨tail⟩)

