{-# OPTIONS --cubical --guarded #-}
module Guarded.Stream where

-- An example with guarded streams.

open import Guarded.Later
open import Cubical.Foundations.Prelude

private
  variable
    l : Level
    A B : Set l

data gStream (A : Set) : Set where
  cons : (x : A) (xs : ▹ gStream A) → gStream A

head : ∀ {A : Set} → gStream A → A
head (cons x xs) = x

tail : ∀ {A : Set} → gStream A → ▹ gStream A
tail (cons x xs) = xs

repeat : ∀ {A : Set} → A → gStream A
repeat a = fix \ repeat▹ → cons a repeat▹

repeat-eq : ∀ {A : Set} (a : A) → repeat a ≡ cons a (\ α → repeat a)
repeat-eq a = cong (cons a) (pdfix (cons a))

map : ∀ {A B : Set} → (A → B) → gStream A → gStream B
map f = fix \ map▹ as → cons (f (head as)) \ α → map▹ α (tail as α)

map-eq : ∀ {A B : Set} → (f : A → B) → ∀ a as → map f (cons a as) ≡ cons (f a) (\ α → map f (as α))
map-eq f a b = cong (cons _) (later-ext \ α → pfix _ α $> b α)

map-repeat : ∀ {A B : Set} → (a : A) → (f : A → B) → map f (repeat a) ≡ repeat (f a)
map-repeat a f = fix \ prf▹ →
  map f (repeat a)
       ≡⟨ cong (map f) (repeat-eq a) ⟩
  map f (cons a (λ x → repeat a))
       ≡⟨ map-eq f a _ ⟩
  cons (f a) (λ v → map f (repeat a))
       ≡⟨ cong (cons (f a)) (later-ext prf▹) ⟩
  cons (f a) (λ α → repeat (f a))
       ≡⟨ cong (cons (f a)) (later-ext \ α → sym (pfix (cons (f a)) α)) ⟩
  cons (f a) (λ x → dfix (cons (f a)) x)
       ≡⟨ refl ⟩
  repeat (f a)
       ∎
