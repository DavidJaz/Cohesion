{-# OPTIONS --without-K #-}

open import Basics
open import lib.Basics
open import Flat

module Axiom.C1 {i j :{♭} ULevel} (I :{♭} Type i) (R :{♭} I → Type j) where
    open import Axiom.C0 I R

    postulate C1 : (index : I) → R index
