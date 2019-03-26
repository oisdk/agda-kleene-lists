{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Lists, based on the Kleene star and plus.
--
-- These lists are exatcly equivalent to normal lists, except the "cons"
-- case is split into its own data type. This lets us write all the same
-- functions as before, but it has 2 advantages:
--
-- * Some functions are easier to express on the non-empty type. For
--   instance, head can be clearly expressed without the need for
--   maybes.
-- * It can make some proofs easier. By using the non-empty type where
--   possible, we can avoid an extra pattern match, which can really
--   simplify certain proofs.

module Data.List.Kleene.Base where

open import Data.Product as Product using (_×_; _,_; map₂; map₁)
open import Data.Nat     as ℕ       using (ℕ; suc; zero)
open import Data.Maybe   as Maybe   using (Maybe; just; nothing)

open import Function

------------------------------------------------------------------------
-- Definitions

infixr 5 _&_ ∹_
mutual
  -- Non-Empty Lists
  record _⁺ {a} (A : Set a) : Set a where
    inductive
    constructor _&_
    field
      head : A
      tail : A ⋆

  -- Possibly Empty Lists
  data _⋆ {a} (A : Set a) : Set a where
    [] : A ⋆
    ∹_ : A ⁺ → A ⋆
open _⁺ public

------------------------------------------------------------------------
-- Folds

module _ {a b} {A : Set a} {B : Set b} (f : A → B → B) (b : B) where
  foldr⁺ : A ⁺ → B
  foldr⋆ : A ⋆ → B

  foldr⁺ (x & xs) = f x (foldr⋆ xs)

  foldr⋆ [] = b
  foldr⋆ (∹ xs) = foldr⁺ xs

module _ {a b} {A : Set a} {B : Set b} (f : B → A → B) where
  foldl⁺ : B → A ⁺ → B
  foldl⋆ : B → A ⋆ → B

  foldl⁺ b (x & xs) = foldl⋆ (f b x) xs

  foldl⋆ b [] = b
  foldl⋆ b (∹ xs) = foldl⁺ b xs

------------------------------------------------------------------------
-- Concatenation

module _ {a} {A : Set a} where
  _⁺++⁺_ : A ⁺ → A ⁺ → A ⁺
  _⁺++⋆_ : A ⁺ → A ⋆ → A ⁺
  _⋆++⁺_ : A ⋆ → A ⁺ → A ⁺
  _⋆++⋆_ : A ⋆ → A ⋆ → A ⋆

  head (xs ⁺++⋆ ys) = head xs
  tail (xs ⁺++⋆ ys) = tail xs ⋆++⋆ ys

  []     ⋆++⋆ ys = ys
  (∹ xs) ⋆++⋆ ys = ∹ xs ⁺++⋆ ys

  head (xs ⁺++⁺ ys) = head xs
  tail (xs ⁺++⁺ ys) = ∹ tail xs ⋆++⁺ ys

  []     ⋆++⁺ ys = ys
  (∹ xs) ⋆++⁺ ys = xs ⁺++⁺ ys

------------------------------------------------------------------------
-- Mapping

module _ {a b} {A : Set a} {B : Set b} (f : A → B) where
  map⁺ : A ⁺ → B ⁺
  map⋆ : A ⋆ → B ⋆

  head (map⁺ xs) = f (head xs)
  tail (map⁺ xs) = map⋆ (tail xs)

  map⋆ [] = []
  map⋆ (∹ xs) = ∹ map⁺ xs

------------------------------------------------------------------------
-- Applicative Operations

module _ {a} {A : Set a} where
  pure⁺ : A → A ⁺
  pure⋆ : A → A ⋆

  head (pure⁺ x) = x
  tail (pure⁺ x) = []

  pure⋆ x = ∹ pure⁺ x

module _ {a b} {A : Set a} {B : Set b} where
  _⋆<*>⋆_ : (A → B) ⋆ → A ⋆ → B ⋆
  _⁺<*>⋆_ : (A → B) ⁺ → A ⋆ → B ⋆
  _⋆<*>⁺_ : (A → B) ⋆ → A ⁺ → B ⋆
  _⁺<*>⁺_ : (A → B) ⁺ → A ⁺ → B ⁺

  []     ⋆<*>⋆ xs = []
  (∹ fs) ⋆<*>⋆ xs = fs ⁺<*>⋆ xs

  fs ⁺<*>⋆ xs = map⋆ (head fs) xs ⋆++⋆ (tail fs ⋆<*>⋆ xs)

  []     ⋆<*>⁺ xs = []
  (∹ fs) ⋆<*>⁺ xs = ∹ fs ⁺<*>⁺ xs

  fs ⁺<*>⁺ xs = map⁺ (head fs) xs ⁺++⋆ (tail fs ⋆<*>⁺ xs)

------------------------------------------------------------------------
-- Monadic Operations

module _ {a b} {A : Set a} {B : Set b} where
  _⁺>>=⁺_ : A ⁺ → (A → B ⁺) → B ⁺
  _⁺>>=⋆_ : A ⁺ → (A → B ⋆) → B ⋆
  _⋆>>=⁺_ : A ⋆ → (A → B ⁺) → B ⋆
  _⋆>>=⋆_ : A ⋆ → (A → B ⋆) → B ⋆

  (x & xs) ⁺>>=⁺ k = k x ⁺++⋆ (xs ⋆>>=⁺ k)

  (x & xs) ⁺>>=⋆ k = k x ⋆++⋆ (xs ⋆>>=⋆ k)

  []     ⋆>>=⋆ k = []
  (∹ xs) ⋆>>=⋆ k = xs ⁺>>=⋆ k

  []     ⋆>>=⁺ k = []
  (∹ xs) ⋆>>=⁺ k = ∹ xs ⁺>>=⁺ k

------------------------------------------------------------------------
-- Scans

module _ {a b} {A : Set a} {B : Set b} (f : A → B → B) (b : B) where
  scanr⁺ : A ⁺ → B ⁺
  scanr⋆ : A ⋆ → B ⁺

  scanr⋆ []     = b & []
  scanr⋆ (∹ xs) = scanr⁺ xs

  scanr⁺ xs = go (scanr⋆ (tail xs))
    where
    go : B ⁺ → B ⁺
    head (go ys) = f (head xs) (head ys)
    tail (go ys) = (∹ ys)

module _ {a b} {A : Set a} {B : Set b} (f : B → A → B) where
  scanl⁺ : B → A ⁺ → B ⁺
  scanl⋆ : B → A ⋆ → B ⁺

  head (scanl⁺ b xs) = b
  tail (scanl⁺ b xs) = ∹ scanl⋆ (f b (head xs)) (tail xs)

  head (scanl⋆ b xs) = b
  tail (scanl⋆ b []) = []
  tail (scanl⋆ b (∹ xs)) = ∹ scanl⋆ (f b (head xs)) (tail xs)

  scanl₁ : B → A ⁺ → B ⁺
  scanl₁ b xs = scanl⋆ (f b (head xs)) (tail xs)

------------------------------------------------------------------------
-- Accumulating maps

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : B → A → (B × C)) where
  mapAccumL⋆ : B → A ⋆ → (B × C ⋆)
  mapAccumL⁺ : B → A ⁺ → (B × C ⁺)

  mapAccumL⋆ b [] = b , []
  mapAccumL⋆ b (∹ xs) = map₂ ∹_ (mapAccumL⁺ b xs)

  mapAccumL⁺ b (x & xs) =
    let y , ys = f b x
        z , zs = mapAccumL⋆ y xs
    in z , (ys & zs)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → (C × B)) (b : B) where
  mapAccumR⋆ : A ⋆ → (C ⋆ × B)
  mapAccumR⁺ : A ⁺ → (C ⁺ × B)

  mapAccumR⋆ [] = [] , b
  mapAccumR⋆ (∹ xs) = map₁ ∹_ (mapAccumR⁺ xs)

  mapAccumR⁺ (x & xs) =
    let ys , y = mapAccumR⋆ xs
        zs , z = f x y
    in (zs & ys) , z

------------------------------------------------------------------------
-- Non-Empty Folds

module _ {a} {A : Set a} where
  last : A ⁺ → A
  last (x & []) = x
  last (_ & (∹ xs)) = last xs

module _ {a} {A : Set a} (f : A → A → A) where
  foldr1 : A ⁺ → A
  foldr1 (x & []) = x
  foldr1 (x & (∹ xs)) = f x (foldr1 xs)

  foldl1 : A ⁺ → A
  foldl1 (x & xs) = foldl⋆ f x xs

------------------------------------------------------------------------
-- Indexing

module _ {a} {A : Set a} where
  _[_]⋆ : A ⋆ → ℕ → Maybe A
  _[_]⁺ : A ⁺ → ℕ → Maybe A

  []     [ _ ]⋆ = nothing
  (∹ xs) [ i ]⋆ = xs [ i ]⁺

  xs [ zero  ]⁺ = just (head xs)
  xs [ suc i ]⁺ = tail xs [ i ]⋆

  applyUpTo⋆ : (ℕ → A) → ℕ → A ⋆
  applyUpTo⁺ : (ℕ → A) → ℕ → A ⁺

  applyUpTo⋆ f zero    = []
  applyUpTo⋆ f (suc n) = ∹ applyUpTo⁺ f n

  head (applyUpTo⁺ f n) = f zero
  tail (applyUpTo⁺ f n) = applyUpTo⋆ (f ∘ suc) n

------------------------------------------------------------------------
-- Manipulation

module _ {a} {A : Set a} (x : A) where
  intersperse⁺ : A ⁺ → A ⁺
  intersperse⋆ : A ⋆ → A ⋆

  head (intersperse⁺ xs) = head xs
  tail (intersperse⁺ xs) = prepend (tail xs)
    where
    prepend : A ⋆ → A ⋆
    prepend [] = []
    prepend (∹ xs) = ∹ x & ∹ intersperse⁺ xs

  intersperse⋆ [] = []
  intersperse⋆ (∹ xs) = ∹ intersperse⁺ xs

module _ {a} {A : Set a} where
  _⁺<|>⁺_ : A ⁺ → A ⁺ → A ⁺
  _⁺<|>⋆_ : A ⁺ → A ⋆ → A ⁺
  _⋆<|>⁺_ : A ⋆ → A ⁺ → A ⁺
  _⋆<|>⋆_ : A ⋆ → A ⋆ → A ⋆

  head (xs ⁺<|>⁺ ys) = head xs
  tail (xs ⁺<|>⁺ ys) = ∹ (ys ⁺<|>⋆ tail xs)

  head (xs ⁺<|>⋆ ys) = head xs
  tail (xs ⁺<|>⋆ ys) = ys ⋆<|>⋆ tail xs

  []     ⋆<|>⁺ ys = ys
  (∹ xs) ⋆<|>⁺ ys = xs ⁺<|>⁺ ys

  []     ⋆<|>⋆ ys = ys
  (∹ xs) ⋆<|>⋆ ys = ∹ (xs ⁺<|>⋆ ys)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) where
  ⁺zipWith⁺ : A ⁺ → B ⁺ → C ⁺
  ⋆zipWith⁺ : A ⋆ → B ⁺ → C ⋆
  ⁺zipWith⋆ : A ⁺ → B ⋆ → C ⋆
  ⋆zipWith⋆ : A ⋆ → B ⋆ → C ⋆

  head (⁺zipWith⁺ xs ys) = f (head xs) (head ys)
  tail (⁺zipWith⁺ xs ys) = ⋆zipWith⋆ (tail xs) (tail ys)

  ⋆zipWith⁺ [] ys = []
  ⋆zipWith⁺ (∹ xs) ys = ∹ ⁺zipWith⁺ xs ys

  ⁺zipWith⋆ xs [] = []
  ⁺zipWith⋆ xs (∹ ys) = ∹ ⁺zipWith⁺ xs ys

  ⋆zipWith⋆ [] ys = []
  ⋆zipWith⋆ (∹ xs) ys = ⁺zipWith⋆ xs ys

module _ {a} {A : Set a} where
  ⋆transpose⋆ : (A ⋆) ⋆ → (A ⋆) ⋆
  ⋆transpose⁺ : (A ⋆) ⁺ → (A ⁺) ⋆
  ⁺transpose⋆ : (A ⁺) ⋆ → (A ⋆) ⁺
  ⁺transpose⁺ : (A ⁺) ⁺ → (A ⁺) ⁺

  ⋆transpose⋆ [] = []
  ⋆transpose⋆ (∹ xs) = map⋆ ∹_ (⋆transpose⁺ xs)

  ⋆transpose⁺ (x & []) = map⋆ pure⁺ x
  ⋆transpose⁺ (x & (∹ xs)) = ⋆zipWith⋆ (λ y z → y & ∹ z) x (⋆transpose⁺ xs)

  ⁺transpose⋆ [] = [] & []
  ⁺transpose⋆ (∹ xs) = map⁺ ∹_ (⁺transpose⁺ xs)

  ⁺transpose⁺ (x & []) = map⁺ pure⁺ x
  ⁺transpose⁺ (x & (∹ xs)) = ⁺zipWith⁺ (λ y z → y & ∹ z) x (⁺transpose⁺ xs)

module _ {a} {A : Set a} where
  tails⋆ : A ⋆ → (A ⁺) ⋆
  tails⁺ : A ⁺ → (A ⁺) ⁺

  head (tails⁺ xs) = xs
  tail (tails⁺ xs) = tails⋆ (tail xs)

  tails⋆ [] = []
  tails⋆ (∹ xs) = ∹ tails⁺ xs

module _ {a} {A : Set a} where
  reverse⋆ : A ⋆ → A ⋆
  reverse⋆ = foldl⋆ (λ xs x → ∹ x & xs) []

  reverse⁺ : A ⁺ → A ⁺
  reverse⁺ (x & xs) = foldl⋆ (λ ys y → y & (∹ ys)) (x & []) xs
