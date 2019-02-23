{-# OPTIONS --without-K --rewriting #-}

module TEST where
  open import Agda.Primitive using (lzero; Level; lsuc; _⊔_)

  infix 30 _↦_
  postulate
    _↦_ : ∀ i {A : Set i} → A → A → Set i
    
  {-# BUILTIN REWRITE _↦_ #-}

  postulate
    foo : {i : Level} → Set i → Set i

    bar : {i : Level} (A : Set i) → A → foo A

    unbar : {i :{♭} Level} (A :{♭} Set i) (a :{♭} foo A) → A

    bar-unbar : {i :{♭} Level} (A :{♭} Set i) (a :{♭} foo A) → (bar A (unbar A a)) ↦ a
