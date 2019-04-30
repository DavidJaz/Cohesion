{-# OPTIONS --without-K #-}

module Classifying where
  open import Basics

  open import Flat
  open import lib.types.Sigma
  open import lib.Equivalence2
  open import lib.types.Truncation

  BAut : ∀ {i} {X : Type i} (x : X) → Type i
  BAut {X = X} x = Σ X $ (\y → ∥ x == y ∥) 

  ♭-commutes-with-BAut : {i :{♭} ULevel } (X :{♭} Type i) (x :{♭} X)
                         → (♭ (BAut x)) ≃ BAut (x ^♭)
  ♭-commutes-with-BAut X x =  ♭ (BAut x)
                           ≃⟨ ♭-commutes-with-Σ ⟩
                              Σ (♭ X) (\u → let♭ y ^♭:= u in♭ (♭ ∥ x == y ∥))
                           ≃⟨ Σ-emap-r lemma₂ ⟩
                               Σ (♭ X) (\u → let♭ y ^♭:= u in♭ ∥ ♭ (x == y) ∥)
                           ≃⟨ Σ-emap-r lemma₁ ⟩
                              BAut (x ^♭)
                           ≃∎
     where
       lemma₁ : (z : ♭ X) → (let♭ y ^♭:= z in♭ ∥ ♭ (x == y) ∥) ≃ ∥ (x ^♭) == z ∥
       lemma₁ (z ^♭) = Trunc-emap (♭-identity-eq x z)
  
       lemma₂ : (z : ♭ X) → (let♭ y ^♭:= z in♭ (♭ ∥ x == y ∥)) ≃ (let♭ y ^♭:= z in♭ ∥ ♭ (x == y) ∥)
       lemma₂ (z ^♭) = (♭-Trunc-eq (x == z)) ⁻¹

  _is-locally-crisply-discrete : {i :{♭} ULevel} (X :{♭} Type i) → Type i
  _is-locally-crisply-discrete X = (x y :{♭} X) → (x == y) is-discrete

  
