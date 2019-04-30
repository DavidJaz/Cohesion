{-$ OPTIONS --without-K #-}

module Algebra.Monoid where
  open import Basics

  open import lib.types.Paths

  record ∞-monoid i : Type (lsucc i) where
    field -- data
      el : Type i
      μ  : el → End el

    μ' : el → End el
    μ' b a = μ a b

    field -- properties
      unit-l : hfiber μ  (idf el) is-contractible
      unit-r : hfiber μ' (idf el) is-contractible
      mult   : ∀ a b → hfiber μ ((μ a) ∘ (μ b)) is-contractible
      
    1l : el
    1l = fst $ contr-center unit-l

    1l-def : μ 1l == idf el
    1l-def = snd $ contr-center unit-l

    1r : el
    1r = fst $ contr-center unit-r

    1r-def : μ' 1r == idf el
    1r-def = snd $ contr-center unit-r

    infix 50 _·_
    _·_ : el → el → el
    a · b = fst $ contr-center (mult a b)

    ·-def : ∀ a b → μ (a · b) == (μ a) ∘ (μ b)
    ·-def a b =  snd $ contr-center (mult a b) 
    -- --------------------------------------------

    1l=1r : 1l == 1r
    1l=1r = 1l
          =⟨ ! (1r-def at 1l) ⟩
             μ 1l 1r
          =⟨ 1l-def at 1r ⟩
             1r
          =∎

    μ=· : ∀ a b → (μ a b) == (a · b)
    μ=· a b = μ a b
            =⟨ ! $ ap (μ a) (1r-def at b) ⟩
              μ a (μ b 1r)
            =⟨ ! $ (·-def a b) at 1r ⟩
              μ (a · b) 1r
            =⟨ 1r-def at (a · b) ⟩
              a · b
            =∎

    m-assoc : ∀ a b c → (a · b) · c == a · (b · c)
    m-assoc a b c = ap fst (! (contr-path (mult a (b · c)) in-fib))
      where
        lem : μ((a · b) · c) == (μ a) ∘ μ(b · c)
        lem = μ((a · b) · c)
            =⟨ ·-def (a · b) c ⟩
              μ(a · b) ∘ (μ c)
            =⟨ ap (λ f → f ∘ (μ c)) (·-def a b) ⟩
              (μ a) ∘ (μ b) ∘ (μ c)
            =⟨ ! $ ap (λ f → (μ a) ∘ f) (·-def b c) ⟩
              (μ a) ∘ μ(b · c)
            =∎

        in-fib : hfiber μ ((μ a) ∘ μ(b · c))
        in-fib = ((a · b) · c) , lem 

    penta : ∀ a b c d →
            (m-assoc (a · b) c d) ∙ (m-assoc a b (c · d))
              ==
            (ap (λ x → x · d) (m-assoc a b c)) ∙ (m-assoc a (b · c) d) ∙ (ap (λ x → a · x) (m-assoc b c d))
    penta a b c d = {!!}
  

  End-l : ∀ {i} (X : Type i) → ∞-monoid i
  End-l X = record { el = End X
                   ; μ = λ f → λ g → f ∘ g
                   ; unit-l = has-level-in $ (idf X , refl) , proof-unit-l
                   ; unit-r = has-level-in $ (idf X , refl) , proof-unit-r
                   ; mult = λ a b → has-level-in $ (a ∘ b , refl) , proof-mult a b}
    where
      proof-unit-l : ∀ y → (idf X , refl) == y
      proof-unit-l (f , p) = pair= (! p at idf X) $ ↓-app=cst-in $
                   idp
                   =⟨ ! (!-inv-l p) ⟩
                    (! p) ∙ p
                   =⟨ ap (λ α → α ∙ p) helper ⟩
                    (ap (λ z g → z ∘ g) (! p at idf X)) ∙ p
                   =∎
        where
          lemma : (k : End X → End X) (q : (idf (End X)) == k) (f : End X)
                  (η : (k f) ∘_ == k ∘ (f ∘_))
                → (ap (λ u g → (u f) ∘ g) q) ∙' η == (ap (λ u g → u (f ∘ g)) q)
          lemma _ idp _ idp = idp         
  
          helper : ! p == (ap (λ z g → z ∘ g) (! p at idf X))
          helper = ! p
                 =⟨ other-lemma (! p) ⟩
                   ap (λ u g → u g) (! p)
                 =⟨ ! $ lemma (f ∘_) (! p) (idf X) refl  ⟩
                   ap (λ u g → (u (idf X)) ∘ g) (! p)
                 =⟨ ap-∘ (λ z x x₁ → z (x x₁)) (λ z → z (λ x → x)) (! p) ⟩
                  (ap (λ z g → z ∘ g) (! p at idf X))
                 =∎
            where
              other-lemma : ∀ {i j} {X : Type i} {Y : Type j} {f g : X → Y}
                            (p : f == g) → p == (ap (λ u g → u g) p)
              other-lemma refl = refl

          

      proof-unit-r : ∀ y → (idf X , refl) == y
      proof-unit-r (f , p) = pair= (! p at idf X) $ ↓-app=cst-in $
                   idp
                   =⟨ ! (!-inv-l p) ⟩
                    (! p) ∙ p
                   =⟨ ap (λ α → α ∙ p) helper ⟩
                    (ap (λ z g → g ∘ z) (! p at idf X)) ∙ p
                   =∎
        where
          lemma : (k : End X → End X) (q : (idf (End X)) == k) (f : End X)
                  (η : _∘ (k f) == k ∘ (_∘ f))
                → (ap (λ u g → g ∘ (u f)) q) ∙' η == (ap (λ u g → u (g ∘ f)) q)
          lemma _ refl _ refl = refl

          helper : ! p  == (ap (λ z g → g ∘ z) (! p at idf X))
          helper = ! p
                 =⟨ other-lemma (! p) ⟩
                   ap (λ u g → u g) (! p)
                 =⟨ ! $ lemma (_∘ f) (! p) (idf X) refl ⟩
                   ap (λ u g → g ∘ (u (idf X))) (! p)
                 =⟨ ap-∘ (λ z x x₁ → x (z x₁)) (λ z → z (λ x → x)) (! p) ⟩
                   ap (λ z g → g ∘ z) (! p at idf X)
                 =∎
           where
              other-lemma : ∀ {i j} {X : Type i} {Y : Type j} {f g : X → Y}
                            (p : f == g) → p == (ap (λ u g → u g) p)
              other-lemma refl = refl
        
      proof-mult : ∀ a b y → (a ∘ b , refl) == y
      proof-mult a b (f , p) = pair= (! p at idf X) $ ↓-app=cst-in $
                 refl
                 =⟨ ! (!-inv-l p) ⟩
                  ! p ∙ p
                 =⟨ ap (λ α → α ∙ p) helper ⟩
                  (ap (λ z g → z ∘ g) (! p at idf X)) ∙ p
                 =∎
        where
          lemma : (k : End X → End X) (q : (a ∘ b) ∘_ == k) (f : End X)
                  (η : (k f) ∘_ == k ∘ (f ∘_))
                → (ap (λ u g → (u f) ∘ g) q) ∙' η == (ap (λ u g → u (f ∘ g)) q)
          lemma _ idp _ idp = idp         
  
          helper : ! p == (ap (λ z g → z ∘ g) (! p at idf X))
          helper = ! p
                 =⟨ other-lemma (! p) ⟩
                   ap (λ u g → u g) (! p)
                 =⟨ ! $ lemma (f ∘_) (! p) (idf X) refl  ⟩
                   ap (λ u g → (u (idf X)) ∘ g) (! p)
                 =⟨ ap-∘ (λ z x x₁ → z (x x₁)) (λ z → z (λ x → x)) (! p) ⟩
                  (ap (λ z g → z ∘ g) (! p at idf X))
                 =∎
            where
              other-lemma : ∀ {i j} {X : Type i} {Y : Type j} {f g : X → Y}
                            (p : f == g) → p == (ap (λ u g → u g) p)
              other-lemma refl = refl

  Aut-l : ∀ {i} {X : Type i} (x : X) → ∞-monoid i
  Aut-l {X = X} x = record { el = x == x
                           ; μ = λ p → λ q → p ∙ q
                           ; unit-l = has-level-in $ (refl , refl) , unit-l-proof
                           ; unit-r = has-level-in $ (refl , (λ= ∙-unit-r)) , unit-r-proof
                           ; mult = λ a b → has-level-in $ (a ∙ b , λ= (∙-assoc a b)) , mult-proof a b }
    where
      unit-l-proof : ∀ y → (refl , refl) == y
      unit-l-proof (p , α) = pair= (! (α at refl) ∙ (∙-unit-r p)) $ ↓-app=cst-in $
                    idp
                   =⟨ ! (!-inv-l α) ⟩
                    ! α ∙ α
                   =⟨ {!!} ⟩
                    ap (λ z q → z ∙ q) (! (α at refl) ∙ (∙-unit-r p)) ∙ α
                   =∎

      unit-r-proof : ∀ y → (refl , (λ= ∙-unit-r)) == y
      unit-r-proof (p , α) = {!!}

      mult-proof : ∀ a b y → (a ∙ b , λ= (∙-assoc a b)) == y
      mult-proof a b y = {!!}
