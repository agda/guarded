{-# OPTIONS --cubical --guarded #-}
module Clocked.Primitives where

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)

-- some equality primitives
λ= : ∀ {l l'} {A : Set l} {B : A → Set l'} {f g : ∀ x → B x} → (∀ x → f x ≡ g x) → f ≡ g
λ= eq i x = eq x i

_$>_ : ∀ {l l'} {A : Set l} {B : A -> Set l'} {f g : ∀ (a : A) → B a} → PathP {ℓ = _} (\ _ → (a : A) → B a) f g → ∀ x → f x ≡ g x
eq $> x = \ i → eq i x

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

postulate
  Cl : Set
  k0 : Cl
  Tick : Cl → LockU

▹ : ∀ {l} → Cl → Set l → Set l
▹ k A = (@tick x : Tick k) -> A

▸ : ∀ {l} k → ▹ k (Set l) → Set l
▸ k A = (@tick x : Tick k) → A x

postulate
  tick-irr : ∀ {A : Set}{k : Cl} (x : ▹ k A) → ▸ k \ α → ▸ k \ β → x α ≡ x β

postulate
  dfix : ∀ {k} {l} {A : Set l} → (▹ k A → A) → ▹ k A
  pfix : ∀ {k} {l} {A : Set l} (f : ▹ k A → A) → dfix f ≡ (\ _ → f (dfix f))

  force : ∀ {l} {A : Cl → Set l} → (∀ k → ▹ k (A k)) → ∀ k → A k
  force-delay : ∀ {l} {A : Cl → Set l} → (f : ∀ k → ▹ k (A k)) → ∀ k → ▸ k \ α → force f k ≡ f k α
  delay-force : ∀ {l} {A : Cl → Set l} → (f : ∀ k → A k)       → ∀ k → force (\ k α → f k) k ≡ f k
  force^ : ∀ {l} {A : ∀ k → ▹ k (Set l)} → (∀ k → ▸ k (A k)) → ∀ k → force A k
-- No more postulates after this line.

private
  variable
    l : Level
    A B : Set l
    k : Cl

next : A → ▹ k A
next x _ = x

_⊛_ : ▹ k (A → B) → ▹ k A → ▹ k B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ k A → ▹ k B
map▹ f x α = f (x α)

later-ext : ∀ {l} {A : Set l} → {f g : ▹ k A} → (▸ k \ α → f α ≡ g α) → f ≡ g
later-ext eq = \ i α → eq α i

pfix' : ∀ {l} {A : Set l} (f : ▹ k A → A) → ▸ k \ α → dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : ∀ {l} {A : Set l} → (▹ k A → A) → A
fix f = f (dfix f)

fix-eq : ∀ {l} {A : Set l} → (f : ▹ k A → A) → fix f ≡ f (\ _ → fix f)
fix-eq f = \ i →  f (pfix f i)

delay : ∀ {A : Cl → Set} → (∀ k → A k) → ∀ k → ▹ k (A k)
delay a k _ = a k

Later-Alg[_]_ : ∀ {l} → Cl → Set l → Set l
Later-Alg[ k ] A = ▹ k A → A
