{-# OPTIONS --cubical --guarded #-}
module Guarded.Later where

open import Cubical.Foundations.Prelude
open import Guarded.Primitives public

private
  variable
    l : Level
    A B : Set l

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) -> A

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

later-ext : ∀ {A : Set} → {f g : ▹ A} → (▸ \ α → f α ≡ g α) → f ≡ g
later-ext eq = \ i α → eq α i

-- These will compute only on diamond ticks.
postulate
  dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
  pdfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ (\ _ → f (dfix f))

pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → ▸ \ α → dfix f α ≡ f (dfix f)
pfix f α i = pdfix f i α

fix : ∀ {l} {A : Set l} → (▹ A → A) → A
fix f = f (dfix f)

-- helper function quite useful for pfix
_$>_ : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ x → f x ≡ g x
eq $> x = \ i → eq i x


private
  module Test where
    transpLater : ∀ (A : I → ▹ Set) → ▸ (A i0) → ▸ (A i1)
    transpLater A u0 a = transp (\ i → A i a) i0 (u0 a)

    transpLater-prim : (A : I → ▹ Set) → (x : ▸ (A i0)) → ▸ (A i1)
    transpLater-prim A x = transp (\ i → ▸ (A i)) i0 x

    transpLater-test : ∀ (A : I → ▹ Set) → (x : ▸ (A i0)) → transpLater-prim A x ≡ transpLater A x
    transpLater-test A x = \ _ → transpLater-prim A x


    hcompLater-prim : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
    hcompLater-prim A φ u u0 a = hcomp (\ { i (φ = i1) → u i 1=1 a }) (outS u0 a)


    hcompLater : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
    hcompLater A φ u u0 = hcomp (\ { i (φ = i1) → u i 1=1 }) (outS u0)

    hcompLater-test : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → hcompLater A φ u u0 ≡ hcompLater-prim A φ u u0
    hcompLater-test A φ u x = \ _ → hcompLater-prim A φ u x
