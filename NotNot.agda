{-# OPTIONS --without-K #-}

module NotNot where
  open import Basics

  -- Since double negation is always proposition valued, we just define it that way
  -- for convenience.
  ¬¬ : ∀ {i} (A : Type i) → Prop i
  ¬¬ A = ¬ (¬ A), ¬¬-is-a-prop
    where
      ¬¬-is-a-prop : ∀ {i} {A : Type i} → (¬ (¬ A)) is-a-prop
      ¬¬-is-a-prop = mapping-into-prop-is-a-prop (λ _ → False holds-is-a-prop)

  continue : ∀ {i j} {A : Type i} {B : A → Type j}
             (a : A) → ((a : A) → B a) → B a
  continue a f = f a

  -- When trying to prove a negation from a double negation,
  -- You may remove the double negation.
  ¬¬-elim : ∀ {i j} {A : Type i} (B : (¬¬ A) holds → Type j)
            (f : (a : A) → ¬ (B (continue a)))
            → (nna : (¬¬ A) holds) → ¬ (B nna)
  ¬¬-elim {A = A} B f nna b =
    nna (λ a → (f a) b')
    where
      b' : {a : A} → B (continue a)
      b' {a} = transport B (prop-path (snd (¬¬ A)) nna (continue a)) b
  ¬¬-elim' : ∀ {i j} {A : Type i} {B : (¬¬ A) holds → Type j}
            (f : (a : A) → ¬ (B (continue a)))
            → (nna : (¬¬ A) holds) → ¬ (B nna)
  ¬¬-elim' {B = B} f nna = ¬¬-elim B f nna

  syntax ¬¬-elim B (λ a → t) nna = un¬¬ nna -as- a -in t in-family B
  syntax ¬¬-elim'  (λ a → t) nna = un¬¬ nna -as- a -in t

  -- The "neighbor relation"
  -- a is the neighbor of b (a ≈ b) if a is not distinct from b (¬¬ (a == b))
  infix 30 _≈_
  _≈_ : ∀ {i} {A : Type i} (a b : A) → Prop i
  a ≈ b = ¬¬ (a == b)

  refl≈ : ∀ {i} {A : Type i} {a : A} → a ≈ a holds
  refl≈ = λ nnp → nnp refl

  trans≈ : ∀ {i} {A : Type i} {a b c : A}
           → a ≈ b holds
           → b ≈ c holds
           → a ≈ c holds
  trans≈ nnp nnq =
    un¬¬ nnp -as- p -in
      un¬¬ nnq -as- q -in
        (λ npq → npq (p ∙ q))

  -- The "neighborhood" of a point of a type is the subtype of all its neighbors.
  nbhd : ∀ {i} {A : Type i} (a : A)
         → Type i
  nbhd  {i} {A} a = Subtype nbhd-prop
    where
      nbhd-prop : SubtypeProp A i
      nbhd-prop = (λ b → a ≈ b holds) , (λ b → a ≈ b holds-is-a-prop)

  -- The neighborhood bundle is the sum of all neighborhoods.
  nbhd-space : ∀ {i} (A : Type i) → Type i
  nbhd-space A = Σ A \(a : A) → nbhd a

  
