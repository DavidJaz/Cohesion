{-# OPTIONS --without-K #-}

module NotNot where
  open import Basics

  open import lib.NType2

  {-
    The definitions here follow Penon's paper "Infinitesimaux et Intuitionisme".
  -}

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
  nbhd-prop : ∀ {i} {A} (a : A) → SubtypeProp A i
  nbhd-prop a = (λ b → a ≈ b holds) , (λ b → a ≈ b holds-is-a-prop)

  nbhd : ∀ {i} {A : Type i} (a : A)
         → Type i
  nbhd  {i} {A} a = Subtype (nbhd-prop a)
      

  -- The total space neighborhood bundle is the sum of all neighborhoods.
  nbhd-space : ∀ {i} (A : Type i) → Type i
  nbhd-space A = Σ A \(a : A) → nbhd a

  private -- We give the neighborhood space a nickname
    N = nbhd-space

  germ : ∀ {i j} {A : Type i} {B : Type j} -- The germ of
         → (f : A → B) -- a function f
         → (a : A) -- at a point a
         → nbhd a → nbhd (f a) -- is a function of this type
  germ f a (d , nnp) =
    f d ,
      (un¬¬ nnp -as- p -in
        (λ ne → ne (ap f p))
      in-family (λ _ → ¬ (f a == f d)))

  chain-rule : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
                       {f : A → B} {g : B → C} (a : A)
                       → germ (g ∘ f) a == (germ g (f a)) ∘ (germ f a)
  chain-rule {f = f} {g = g} a =
    λ= $ λ {(d , p) →
      Subtype=-out (nbhd-prop (g (f a))) -- It suffices to prove the first terms are equal,
        refl -- which they are judgementally.
    }
  
  -- A map is etale if all its germs are equivalences.
  _is-etale : ∀ {i j} {A : Type i} {B : Type j}
          (f : A → B) → Type (lmax i j)
  f is-etale = ∀ a → (germ f a) is-an-equiv

  {- Some universe level error
  ∘-is-etale : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
               {f : A → B} {g : B → C}
               (p : f is-etale) (q : g is-etale)
               → (g ∘ f) is-etale
  ∘-is-etale {i}{j}{k}{A}{B}{C} {f = f} {g = g} p q =
    λ a →     transport (λ (φ : nbhd a → nbhd (g (f (a)))) → φ is-an-equiv)
      {x = (germ g (f a)) ∘ (germ f a)} {y = germ (g ∘ f) a}
      (chain-rule a) (((q (f a)) ∘ise (p a)) ) 
  -}
