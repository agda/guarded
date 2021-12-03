{-# OPTIONS --cubical --guarded --rewriting #-}
module Clocked.ListedFiniteSet where

import Agda.Builtin.Equality as R
import Agda.Builtin.Equality.Rewrite as R

open import Agda.Primitive
open import Clocked.Primitives
open import Cubical.Foundations.Prelude hiding (Lift)
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.ListedFiniteSet
open import Cubical.Foundations.HLevels

private
  variable
    l : Level

module ∀Elim {ℓ}
  {A : Cl → Set l}
  {B : (∀ k → LFSet (A k)) → Type ℓ}
  ([]* : B (\ k → []))
  (_∷*_ : (x : ∀ k → A k) {xs : ∀ k → LFSet (A k)} → B xs → B (\ k → x k ∷ xs k))
  (comm* : (x y : ∀ k → A k) {xs : ∀ k → LFSet (A k)} (b : B xs)
    → PathP (λ i → B (\ k → comm (x k) (y k) (xs k) i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
  (dup* : (x : ∀ k → A k) {xs : ∀ k → LFSet (A k)} (b : B xs)
    → PathP (λ i → B (\ k → dup (x k) (xs k) i)) (x ∷* (x ∷* b)) (x ∷* b))
  (trunc* : (xs : ∀ k → LFSet (A k)) → isSet (B xs))
  where

  postulate
    elim : ∀ xs → B xs

    elim-[] : elim (\ k → []) R.≡ []*
    elim-∷ : (x : ∀ k → A k) {xs : ∀ k → LFSet (A k)} → elim (\ k → x k ∷ xs k) R.≡ x ∷* elim xs

  {-# REWRITE elim-[] elim-∷ #-}

  -- we have to add the rewrites above for the following rewrite rules to typecheck.
  postulate
    elim-comm : (x y : ∀ k → A k) {xs : ∀ k → LFSet (A k)} (i : I) →
                elim (\ k → comm (x k) (y k) (xs k) i) R.≡ comm* x y (elim xs) i
    elim-dup : (x : ∀ k → A k) {xs : ∀ k → LFSet (A k)} (i : I) →
                elim (\ k → dup (x k) (xs k) i) R.≡ dup* x (elim xs) i

    elim-trunc : {x y : ∀ k → LFSet (A k)} (p q : ∀ k → x k ≡ y k) (i j : I) →
                 elim (\ k → trunc (x k) (y k) (p k) (q k) i j) R.≡
                 isOfHLevel→isOfHLevelDep 2 trunc* (elim x) (elim y)
                                            (\ j → elim (\ k → p k j))
                                            (\ j → elim (\ k → q k j))
                                            (λ i j k → trunc (x k) (y k) (p k) (q k) i j)
                                            i j

  {-# REWRITE elim-comm elim-dup elim-trunc #-}


  -- testing the rewrite rules
  private
    _ : elim (\ k → []) R.≡ []*
    _ = R.refl

    _ : {x : ∀ k → A k} {xs : ∀ k → LFSet (A k)} → elim (\ k → x k ∷ xs k) R.≡ x ∷* elim xs
    _ = R.refl

    _ : {x y : ∀ k → A k} {xs : ∀ k → LFSet (A k)} {i : I} →
                elim (\ k → comm (x k) (y k) (xs k) i) R.≡ comm* x y (elim xs) i
    _ = R.refl

    _ : {x : ∀ k → A k} {xs : ∀ k → LFSet (A k)} {i : I} →
                 elim (\ k → dup (x k) (xs k) i) R.≡ dup* x (elim xs) i
    _ = R.refl

    _ : {x y : ∀ k → LFSet (A k)} {p q : ∀ k → x k ≡ y k} {i j : I} →
                 elim (\ k → trunc (x k) (y k) (p k) (q k) i j) R.≡
                 isOfHLevel→isOfHLevelDep 2 trunc* (elim x) (elim y)
                                            (\ j → elim (\ k → p k j))
                                            (\ j → elim (\ k → q k j))
                                            (λ i j k → trunc (x k) (y k) (p k) (q k) i j)
                                            i j
    _ = R.refl
