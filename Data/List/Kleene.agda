{-# OPTIONS --without-K --safe #-}

module Data.List.Kleene where

infixr 5 _&_
mutual
  record _⁺ {a} (A : Set a) : Set a where
    inductive
    constructor _&_
    field
      head : A
      tail : A ⋆

  data _⋆ {a} (A : Set a) : Set a where
    [] : A ⋆
    [_] : A ⁺ → A ⋆
open _⁺ public

infixr 5 _∷_
pattern _∷_ x xs = [ x & xs ]

module _ {a b} {A : Set a} {B : Set b} (f : A → B → B) (b : B) where
  foldr⁺ : A ⁺ → B
  foldr⋆ : A ⋆ → B

  foldr⁺ (x & xs) = f x (foldr⋆ xs)

  foldr⋆ [] = b
  foldr⋆ [ xs ] = foldr⁺ xs

module _ {a b} {A : Set a} {B : Set b} (f : B → A → B) where
  foldl⁺ : B → A ⁺ → B
  foldl⋆ : B → A ⋆ → B

  foldl⁺ b (x & xs) = foldl⋆ (f b x) xs

  foldl⋆ b [] = b
  foldl⋆ b [ xs ] = foldl⁺ b xs

module _ {a b} {A : Set a} {B : Set b} (f : A → B) where
  map⁺ : A ⁺ → B ⁺
  map⋆ : A ⋆ → B ⋆

  head (map⁺ xs) = f (head xs)
  tail (map⁺ xs) = map⋆ (tail xs)

  map⋆ [] = []
  map⋆ [ xs ] = [ map⁺ xs ]

module _ {a} {A : Set a} where
  pure⁺ : A → A ⁺
  pure⋆ : A → A ⋆

  head (pure⁺ x) = x
  tail (pure⁺ x) = []

  pure⋆ x = [ pure⁺ x ]

  _⁺++⁺_ : A ⁺ → A ⁺ → A ⁺
  _⁺++⋆_ : A ⁺ → A ⋆ → A ⁺
  _⋆++⁺_ : A ⋆ → A ⁺ → A ⁺
  _⋆++⋆_ : A ⋆ → A ⋆ → A ⋆

  head (xs ⁺++⋆ ys) = head xs
  tail (xs ⁺++⋆ ys) = tail xs ⋆++⋆ ys

  []     ⋆++⋆ ys = ys
  [ xs ] ⋆++⋆ ys = [ xs ⁺++⋆ ys ]

  head (xs ⁺++⁺ ys) = head xs
  tail (xs ⁺++⁺ ys) = [ tail xs ⋆++⁺ ys ]

  []     ⋆++⁺ ys = ys
  [ xs ] ⋆++⁺ ys = xs ⁺++⁺ ys

  [_]→head : (A → A) → A ⁺ → A ⁺
  head ([ f ]→head xs) = f (head xs)
  tail ([ f ]→head xs) = tail xs

module _ {a b} {A : Set a} {B : Set b} where
  _⁺>>=⁺_ : A ⁺ → (A → B ⁺) → B ⁺
  _⁺>>=⋆_ : A ⁺ → (A → B ⋆) → B ⋆
  _⋆>>=⁺_ : A ⋆ → (A → B ⁺) → B ⋆
  _⋆>>=⋆_ : A ⋆ → (A → B ⋆) → B ⋆

  (x & xs) ⁺>>=⁺ k = k x ⁺++⋆ (xs ⋆>>=⁺ k)

  (x & xs) ⁺>>=⋆ k = k x ⋆++⋆ (xs ⋆>>=⋆ k)

  []     ⋆>>=⋆ k = []
  [ xs ] ⋆>>=⋆ k = xs ⁺>>=⋆ k

  []     ⋆>>=⁺ k = []
  [ xs ] ⋆>>=⁺ k = [ xs ⁺>>=⁺ k ]

module _ {a b} {A : Set a} {B : Set b} (f : A → B → B) (b : B) where
  scanr⁺ : A ⁺ → B ⁺
  scanr⋆ : A ⋆ → B ⁺

  scanr⋆ []     = b & []
  scanr⋆ [ xs ] = scanr⁺ xs

  scanr⁺ xs = go (scanr⋆ (tail xs))
    where
    go : B ⁺ → B ⁺
    head (go ys) = f (head xs) (head ys)
    tail (go ys) = [ ys ]

module _ {a b} {A : Set a} {B : Set b} (f : B → A → B) where
  scanl⁺ : B → A ⁺ → B ⁺
  scanl⋆ : B → A ⋆ → B ⁺

  head (scanl⁺ b xs) = b
  tail (scanl⁺ b xs) = [ scanl⋆ (f b (head xs)) (tail xs) ]

  head (scanl⋆ b xs) = b
  tail (scanl⋆ b []) = []
  tail (scanl⋆ b [ xs ]) = [ scanl⋆ (f b (head xs)) (tail xs) ]

  scanl₁ : B → A ⁺ → B ⁺
  scanl₁ b xs = scanl⋆ (f b (head xs)) (tail xs)

open import Data.Product

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : B → A → (B × C)) where
  mapAccumL⋆ : B → A ⋆ → (B × C ⋆)
  mapAccumL⁺ : B → A ⁺ → (B × C ⁺)

  mapAccumL⋆ b [] = b , []
  mapAccumL⋆ b [ xs ] = map₂ [_] (mapAccumL⁺ b xs)

  mapAccumL⁺ b xs = map₂ (proj₂ ys &_) (mapAccumL⋆ (proj₁ ys) (tail xs))
    where
    ys : B × C
    ys = f b (head xs)

  mapAccumR⋆ : B → A ⋆ → (B × C ⋆)
  mapAccumR⁺ : B → A ⁺ → (B × C ⁺)

  mapAccumR⋆ b [] = b , []
  mapAccumR⋆ b [ xs ] = map₂ [_] (mapAccumR⁺ b xs)

  mapAccumR⁺ b (x & xs) =
    let y , ys = mapAccumR⋆ b xs
        z , zs = f y x
    in z , (zs & ys)

module _ {a} {A : Set a} where
  last⁺ : A ⁺ → A
  last⋆ : A → A ⋆ → A

  last⁺ (x & xs) = last⋆ x xs

  last⋆ x [] = x
  last⋆ x [ xs ] = last⁺ xs

module _ {a} {A : Set a} (f : A → A → A) where
  foldr1 : A ⁺ → A
  foldr1 (x & []) = x
  foldr1 (x & [ xs ]) = f x (foldr1 xs)

  foldl1 : A ⁺ → A
  foldl1 (x & xs) = foldl⋆ f x xs

module _ {a} {A : Set a} (x : A) where
  intersperse⁺ : A ⁺ → A ⁺
  intersperse⋆ : A ⋆ → A ⋆

  head (intersperse⁺ xs) = head xs
  tail (intersperse⁺ xs) = prepend (tail xs)
    where
    prepend : A ⋆ → A ⋆
    prepend [] = []
    prepend [ xs ] = [ x & [ intersperse⁺ xs ] ]

  intersperse⋆ [] = []
  intersperse⋆ [ xs ] = [ intersperse⁺ xs ]

open import Data.Nat
open import Data.Maybe

module _ {a} {A : Set a} where
  _[_]⋆ : A ⋆ → ℕ → Maybe A
  _[_]⁺ : A ⁺ → ℕ → Maybe A

  []     [ _ ]⋆ = nothing
  [ xs ] [ i ]⋆ = xs [ i ]⁺

  xs [ zero  ]⁺ = just (head xs)
  xs [ suc i ]⁺ = tail xs [ i ]⋆

module _ {a} {A : Set a} where
  _⁺<|>⁺_ : A ⁺ → A ⁺ → A ⁺
  _⁺<|>⋆_ : A ⁺ → A ⋆ → A ⁺
  _⋆<|>⁺_ : A ⋆ → A ⁺ → A ⁺
  _⋆<|>⋆_ : A ⋆ → A ⋆ → A ⋆

  head (xs ⁺<|>⁺ ys) = head xs
  tail (xs ⁺<|>⁺ ys) = [ ys ⁺<|>⋆ tail xs ]

  head (xs ⁺<|>⋆ ys) = head xs
  tail (xs ⁺<|>⋆ ys) = ys ⋆<|>⋆ tail xs

  []     ⋆<|>⁺ ys = ys
  [ xs ] ⋆<|>⁺ ys = xs ⁺<|>⁺ ys

  []     ⋆<|>⋆ ys = ys
  [ xs ] ⋆<|>⋆ ys = [ xs ⁺<|>⋆ ys ]

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) where
  ⁺zipWith⁺ : A ⁺ → B ⁺ → C ⁺
  ⋆zipWith⁺ : A ⋆ → B ⁺ → C ⋆
  ⁺zipWith⋆ : A ⁺ → B ⋆ → C ⋆
  ⋆zipWith⋆ : A ⋆ → B ⋆ → C ⋆

  head (⁺zipWith⁺ xs ys) = f (head xs) (head ys)
  tail (⁺zipWith⁺ xs ys) = ⋆zipWith⋆ (tail xs) (tail ys)

  ⋆zipWith⁺ [] ys = []
  ⋆zipWith⁺ [ xs ] ys = [ ⁺zipWith⁺ xs ys ]

  ⁺zipWith⋆ xs [] = []
  ⁺zipWith⋆ xs [ ys ] = [ ⁺zipWith⁺ xs ys ]

  ⋆zipWith⋆ [] ys = []
  ⋆zipWith⋆ [ xs ] ys = ⁺zipWith⋆ xs ys

module _ {a} {A : Set a} where
  ⋆transpose⋆ : (A ⋆) ⋆ → (A ⋆) ⋆
  ⋆transpose⁺ : (A ⋆) ⁺ → (A ⁺) ⋆
  ⁺transpose⋆ : (A ⁺) ⋆ → (A ⋆) ⁺
  ⁺transpose⁺ : (A ⁺) ⁺ → (A ⁺) ⁺

  ⋆transpose⋆ [] = []
  ⋆transpose⋆ [ xs ] = map⋆ [_] (⋆transpose⁺ xs)

  ⋆transpose⁺ (x & []) = map⋆ pure⁺ x
  ⋆transpose⁺ (x & [ xs ]) = ⋆zipWith⋆ (λ y z → y & [ z ]) x (⋆transpose⁺ xs)

  ⁺transpose⋆ [] = [] & []
  ⁺transpose⋆ [ xs ] = map⁺ [_] (⁺transpose⁺ xs)

  ⁺transpose⁺ (x & []) = map⁺ pure⁺ x
  ⁺transpose⁺ (x & [ xs ]) = ⁺zipWith⁺ (λ y z → y & [ z ]) x (⁺transpose⁺ xs)
