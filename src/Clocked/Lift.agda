{-# OPTIONS --cubical --guarded #-}
module Clocked.Lift where

open import Agda.Primitive
open import Clocked.Primitives
open import Cubical.Foundations.Prelude hiding (Lift)
open import Cubical.Foundations.Isomorphism

private
  variable
    l : Level
    A B : Set l
    k : Cl

data Lift {l} (k : Cl) (A : Set l) : Set l where
  now : A → Lift k A
  step : ▹ k (Lift k A) → Lift k A

_>>=_ : Lift k A → (A → Lift k B) → Lift k B
now x >>= f = f x
step x >>= f = step (\ α → x α >>= f)


bind-bind : ∀ {C : Set l} (m : Lift k A) {f : A → Lift k B} {g : B → Lift k C} → (m >>= f) >>= g ≡ (m >>= \ v → f v >>= g)
bind-bind (now x) {f} {g} = refl
bind-bind (step x) {f} {g} = cong step (later-ext (\ α → bind-bind (x α)))

data Lift^' (k : Cl) {l'} {A : Set l'} (P : A → Set l) : Lift k A → Set (l ⊔ l') where
  now : ∀ {a} → P a → Lift^' k P (now a)
  step : ∀ {m} → (▸ k \ α → Lift^' k P (m α)) → Lift^' k P (step m)

Lift^ : (k : Cl) → Lift k A → (A → Set l) → Set _
Lift^ k m P = Lift^' k P m

mapL^ : ∀ {l'} {P : A → Set l}{Q : A → Set l'}{m} → (∀ a → P a → Q a) → Lift^ k m P → Lift^ k m Q
mapL^ f (now x) = now (f _ x)
mapL^ f (step x) = step (\ α → mapL^ f (x α))

-- TODO make ticks go through fibrancy check.
Lift-step' : ∀ {m : ▹ k (Lift k A)} {Q} {l'} {Z : Set l'} → Lift^ {l = l} k (step m) Q → ((▸ k \ α → Lift^' k Q (m α)) → Z) → Z
Lift-step' (step x) k = k x

Lift-step : ∀ {m : ▹ k (Lift k A)} {Q} → Lift^ {l = l} k (step m) Q →
                 (▸ k \ α → Lift^' k Q (m α))
Lift-step q = Lift-step' q (\ z → z)

Lift-now : ∀ {m : A} {Q} → Lift^ {l = l} k (now m) Q → Q m
Lift-now (now p) = p

Lstep≡ : ∀ {m : ▹ k (Lift k A)} {Q} → Lift^ {l = l} k (step m) Q ≡ (▸ k \ α → Lift^' k Q (m α))
Lstep≡ {k = k} {m = m} = isoToPath (iso Lift-step step (\ _ → refl) \ { (step q) → refl })

Lbind≡ : ∀ {l'} {A B : Set l'}{m : Lift k A} {f : A → Lift k B} {Q} → Lift^ {l = l} k (m >>= f) Q ≡ Lift^ k m (\ x → Lift^ k (f x) Q)
Lbind≡ {m = now x} = isoToPath (iso now (\ { (now x) → x }) (\ { (now x) → refl }) \ _ → refl)
Lbind≡ {m = step x} {f} = Lstep≡ {m = (\ α → x α >>= f)} ∙ cong (▸ _) (later-ext (\ α → Lbind≡ {m = x α})) ∙ sym (Lstep≡ {m = x})

Lift-bind : ∀ {m : Lift k A} {f : A → Lift k B} {Q} → Lift^ {l = l} k (m >>= f) Q → Lift^ k m (\ x → Lift^ k (f x) Q)
Lift-bind {m = now x} q = now q
Lift-bind {m = step x} (step q) = step (\ α → Lift-bind (q α))

bind-Lift : ∀ {m : Lift k A} {f : A → Lift k B} {Q} → Lift^ k m (\ x → Lift^ k (f x) Q) → Lift^ {l = l} k (m >>= f) Q
bind-Lift {m = now x} (now q) = q
bind-Lift {m = step x} (step q) = step (\ α → bind-Lift (q α))

Lbind-in : ∀ {m : Lift k A} {f : A → Lift k B} {P  Q} → Lift^ {l = l} k m P → (∀ d → P d → Lift^ k (f d) Q) →  Lift^ {l = l} k (m >>= f) Q
Lbind-in {m = m} {f} {P} {Q} p q = bind-Lift (mapL^ (\ a p → q a p) p)

mutual

  data ∀Lift {l} (A : Set l) : Set l where
    now : A → ∀Lift A
    step : ∀Lift' A → ∀Lift A

  record ∀Lift' {l} (A : Set l) : Set l where
    coinductive
    constructor con
    field
      uncon : ∀Lift A

open ∀Lift'
data FLift (A : Set) : Set where
  now : A → FLift A
  step : FLift A → FLift A

{-# TERMINATING #-}
out∀ : ∀ {l} {A : Set l} → ∀Lift A → ∀ k → Lift k A
out∀ (now a) k = now a
out∀ (step x) k = step (\ α → out∀ (x .uncon) k)

-- Assuming clock irrelevant A.
postulate
  in∀ : ∀ {l} {A : Set l} → (∀ k → Lift k A) → ∀Lift A
  out-in-∀ : ∀ {l} {A : Set l} (m : (∀ k → Lift k A)) → out∀ (in∀ m) ≡ m

inc : ∀ {A : Set} → FLift A → ∀Lift A
inc (now a) = now a
inc (step x) = step (con (inc x))

data _⇓∀_ {l} {A : Set l} : (m : ∀Lift A) → A → Set l where
  step : ∀ {m a} → m .uncon ⇓∀ a → step m ⇓∀ a
  now : ∀ {a} →  now a ⇓∀ a

module LemmaLift {l'} {A : Set l'} where
 fwd : ∀ {Q : Cl → A → Set l} {m : ∀Lift A} → (∀ k → Lift^ k (out∀ m k) (Q k)) → (∀ a → m ⇓∀ a → ∀ k → Q k a)
 fwd p a (step d) k = fwd (\ k → force (\ k → Lift-step (p k)) k) a d k
 fwd p a now k with p k
 ... | now x = x

 bwd : ∀ {Q : Cl → A → Set l} {m : ∀Lift A} → (∀ a → m ⇓∀ a → ∀ k → Q k a) → ∀ k → Lift^ k (out∀ m k) (Q k)
 bwd {Q = Q} {m} p k = aux k m p
   where
     aux : ∀ k → (m : ∀Lift A) → (∀ a → m ⇓∀ a → ∀ k → Q k a) → Lift^ k (out∀ m k) (Q k)
     aux k = fix {k = k} \ where
               r (now x) p → now (p x now k)
               r (step x) p  → step \ α → bwd {m = x .uncon} (\ a d k → p a (step d) k) k
