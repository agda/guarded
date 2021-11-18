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

private
  module Prims where
    primitive
      primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

postulate
  Cl : Set
  k0 : Cl
  STick : Cl → LockU

postulate
  Tick : Cl → LockU
-- data  Tick (k  : Cl) : LockU where
--   con : (@tick α : STick k) → Tick k

postulate
  FTick : Cl → LockU
  ◇ : ∀ {k} → FTick k
  emb : ∀ {k} → Tick k → FTick k

{-# BUILTIN CLOCK Cl #-}
-- {-# BUILTIN STRONGTICK STick #-}
{-# BUILTIN TICK Tick #-}
-- {-# BUILTIN TICKCON con #-}
{-# BUILTIN FORCINGTICK FTick #-}
{-# BUILTIN EMBTICK emb #-}
{-# BUILTIN DIAMONDTICK ◇ #-}

▹ : ∀ {l} → Cl → Set l → Set l
▹ k A = (@tick x : Tick k) -> A

▸ : ∀ {l} k → ▹ k (Set l) → Set l
▸ k A = (@tick x : Tick k) → A x

private
 module Prims2 where
  primitive
    primForcingTickIrr : ∀ {k} → FTick k → FTick k → I → FTick k
    primTickIrr : ∀ {k} → Tick k → Tick k → I → Tick k

    primForcingApp : ∀ {l} {A : ∀ k → Set l} →
      (∀ k → ▹ k (A k)) → ∀ k → (@tick x : FTick k) → A k
    primForcingAppDep : ∀ {l} {A : ∀ k → ▹ k (Set l)} →
      (f : ∀ k → ▸ k (A k)) → ∀ k → (@ftick x : FTick k) →
                   primForcingApp A k x
    primPathFix : ∀ {k : Cl} {a} {A : Set a} → ((▹ k A) → A) → I → ▹ k A

open Prims2 public renaming (primForcingTickIrr to ftirr; primTickIrr to tirr;
                            primForcingApp to wF_⟨_,_⟩;
                            primForcingAppDep to _⟨_,_⟩;
                            primPathFix to lineFix)

tick-irr : ∀ {A : Set}{k : Cl} (x : ▹ k A) → ▸ k \ α → ▸ k \ β → x α ≡ x β
tick-irr x α β i = x (tirr α β i)

dfix : ∀ {k} {l} {A : Set l} → (▹ k A → A) → ▹ k A
dfix f = lineFix f i0

pfix : ∀ {k} {l} {A : Set l} (f : ▹ k A → A) → dfix f ≡ (\ _ → f (dfix f))
pfix f i = lineFix f i

force : ∀ {l} {A : Cl → Set l} → (∀ k → ▹ k (A k)) → ∀ k → A k
force f k = f ⟨ k , ◇ ⟩

force-delay : ∀ {l} {A : Cl → Set l} → (f : ∀ k → ▹ k (A k)) → ∀ k → ▸ k \ α → force f k ≡ f k α
force-delay f k α i = f ⟨ k , ftirr ◇ (emb α) i ⟩

delay-force : ∀ {l} {A : Cl → Set l} → (f : ∀ k → A k)       → ∀ k → force (\ k α → f k) k ≡ f k
delay-force f k = \ _ → f k

force^ : ∀ {l} {A : ∀ k → ▹ k (Set l)} → (∀ k → ▸ k (A k)) → ∀ k → force A k
force^ {A = A} f k = f ⟨ k , ◇ ⟩

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
