{-# OPTIONS --cubical --guarded #-}
module Guarded.Primitives where

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public
