{-# OPTIONS --without-K --rewriting #-}

module old.Sharp where

  open import Basics
  open import Flat

  open import lib.Equivalence2

  {- I want sthing like this
  record ♯ {l : ULevel} (A : Type l) :{♭} Type l where
    constructor _^♯
    field
      _/♯ :{♭} A
  open ♯ publ
-}

  -- Following Licata


  postulate
    -- Given a type A, ♯ A is a type
    ♯ : {i : ULevel} → Type i → Type i

    -- Given an element a : A, we have an element ♯i a : ♯ A
    ♯i : {i : ULevel} {A : Type i} → A → ♯ A

    -- To map out of ♯ A into some type ♯ (B a) depending on it, you may just map out of A.
    ♯-elim : {i j : ULevel} {A : Type i} (B : ♯ A → Type j)
            → ((a : A) → ♯ (B (♯i a)))
            → ((a : ♯ A) → ♯ (B a))

    -- The resulting map out of ♯ A ``computes'' to the original map out of A on ♯i
    ♯-elim-β : {i j : ULevel} {A : Type i} {B : ♯ A → Type j}
               (f : (a : A) → ♯ (B (♯i a))) (a : A)
               → (♯-elim B f (♯i a)) ↦ (f a)
    {-# REWRITE ♯-elim-β #-}

    -- The type of equalities in a codiscrete type are codiscrete
    ♯path : {i : ULevel} {A : Type i} {x y : ♯ A}
            → (♯i {A = x == y}) is-an-equiv

    -- Given a crisp map into ♯ B, we get a cohesive map into it
    -- This encodes the adjunction between ♭ and ♯ on the level of types.
    uncrisp : {i :{♭} ULevel} {j : ULevel} {A :{♭} Type i} (B : A → Type j)
              → ((a :{♭} A) → ♯ (B a))
              → (a : A) → ♯ (B a)

    -- If we uncrispen a function and then apply it to a crisp variable, we get the original result judgementally
    uncrisp-β : {i :{♭} ULevel} {j : ULevel} {A :{♭} Type i} (B : A → Type j)
                → (f : (a :{♭} A) → ♯ (B a))
                → (a :{♭} A) → (uncrisp B f a) ↦ (f a)
    {-# REWRITE uncrisp-β #-}

    -- We can pull crisp elements out of ♯ A
    ♭♯e : {i :{♭} ULevel} {A :{♭} Type i} → ♯ A ::→ A

    -- If we take a crisp element of A, put it into ♯ A, and pull it out again, we get where we were judgementally
    ♭♯β : {i :{♭} ULevel} {A :{♭} Type i} (a :{♭} A)
          → (♭♯e (♯i a)) ↦ a
    {-# REWRITE ♭♯β #-}

    -- If we pull out a crisp element of ♯ A and then put it back in, we get back where we were
    -- Not sure why this isn't judgemental.
    ♭♯η : {i :{♭} ULevel} {A :{♭} Type i} (a :{♭} ♯ A) → a == ♯i (♭♯e a)

    -- We also posulate the half-adjoint needed for this to be a coherent adjunction.
    ♭♯η-▵ : {i :{♭} ULevel} {A :{♭} Type i} (a :{♭} A) → ♭♯η (♯i a) == refl

  ♯path-eq : {i : ULevel} {A : Type i} {x y : ♯ A}
             → (x == y) ≃ (♯ (x == y))
  ♯path-eq = ♯i , ♯path

  ♯-rec : {i j : ULevel} {A : Type i} {B : Type j} →
          (A → ♯ B) → (♯ A → ♯ B)
  ♯-rec {B = B} = ♯-elim (λ _ → B)

{-
  Given a family B : (a :{♭} A) → Type j crisply varying over A,
  we can form the family B' ≡ (λ (a :{♭} A) → ♯ (B a)).

  According to Shulman, we should be able to then get a cohesive variation
  B'' : (a : A) → Type j
  with the property that if (a :{♭} A) , B'' a ≡ B' a

  Or, shorter, from B : (a :{♭} A) → Type j, we should get C : (a : A) → Type j
  with the property that for (a :{♭} A), C a ≡ ♯ (B a)

  The signature of the operation B ↦ C must be ((a :{♭} A) → Type j) → (a : A) → Type j.
  Unfortunately, this doesn't tell us anything about where its landing
-}
  postulate
    ♯' : {i :{♭} ULevel} {Γ :{♭} Type i} {j : ULevel}
         (A : Γ ::→ Type j)
         → Γ → Type j
    ♯'-law : {i :{♭} ULevel} {Γ :{♭} Type i} {j : ULevel}
             (A : Γ ::→ Type j) (x :{♭} Γ)
             → (♯' A) x ↦ ♯ (A x)
    {-# REWRITE ♯'-law #-}

  {-
    Here, we define let notations for ♯ to approximate the upper and lower ♯s 
    that Shulman uses in his paper.

    We also define versions of the eliminator and uncrisper that take an implicit family argument, so
    we can use the let notation without explicitly noting the family.
  -}
  syntax ♯-elim B (λ u → t) a = let♯ a :=♯i u in♯ t in-family B
  syntax uncrisp B (λ u → t) a = let♯ a ↓♯:= u in♯ t in-family B

  ♯-elim' : {i j : ULevel} {A : Type i} {B : ♯ A → Type j}
            → ((a : A) → ♯ (B (♯i a)))
            → (a : ♯ A) → ♯ (B a)
  ♯-elim' {B = B} f = ♯-elim B f
  syntax ♯-elim' (λ u → t) a = let♯ a :=♯i u in♯ t

  uncrisp' : {i :{♭} ULevel} {j : ULevel} {A :{♭} Type i} {B : A → Type j}
         → (f : (a :{♭} A) → ♯ (B a))
         → (a : A) → ♯ (B a)
  uncrisp' {B = B} f = uncrisp B f
  syntax uncrisp' (λ u → t) a = let♯ u := a ↓♯in♯ t

  -- A type A is codiscrete if the counit ♯i : A → ♯ A is an equivalence.
  _is-codiscrete : {i : ULevel} (A : Type i) → Type i
  _is-codiscrete {i} A = (♯i {A = A}) is-an-equiv

  -- To prove a type is an equivalence, it suffices to give a retract of ♯i
  _is-codiscrete-because_is-retract-by_ : {i : ULevel} (A : Type i)
                                          (r : ♯ A → A) (p : (a : A) → r (♯i a)  == a)
                                          → A is-codiscrete
  A is-codiscrete-because r is-retract-by p =
    (♯i {A = A}) is-an-equivalence-because r is-inverse-by
        (λ a → -- Given an a : ♯ A,
             (let♯ a :=♯i b in♯ -- We suppose a is ♯i b
                   (♯i (ap ♯i (p b))) -- apply p to b to get r (♯i b) == b,
                                      -- then apply ♯i to get ♯i r ♯i b == ♯i b
                                      -- then hit it with ♯i to get ♯ (♯i r ♯i b == ♯i b)
              in-family (λ (b : ♯ A) → ♯i (r b) == b) -- which is ♯ (♯i r a == a) by our hypothesis,
             )
          |> (<– ♯path-eq) -- and we can strip the ♯ becacuse equality types are codiscrete.
        )
      and p

  -- (λ a → (<– ♯path-eq) ((♯-elim  (λ (b : ♯ A) → ♯i (r b) == b)
  --     (λ b → ♯i (ap ♯i (p b)))) a))

  ♯→ : {i j : ULevel} {A : Type i} {B : Type j}
       (f : A → B) → (♯ A) → (♯ B)
  ♯→ {A = A} {B = B} f = ♯-rec (♯i ∘ f)

  -- Of course, ♯ A is codiscrete for any type A
  ♯-is-codiscrete : {i : ULevel} (A : Type i) → (♯ A) is-codiscrete
  ♯-is-codiscrete A =
    (♯ A) is-codiscrete-because
      (λ (a : ♯ (♯ A)) → let♯ a :=♯i x in♯ x) is-retract-by
        (λ a → refl)

  -- This is the actual equivalence A ≃ ♯ A, given that A is codiscrete
  codisc-eq : {i : ULevel} {A : Type i} (p : A is-codiscrete)
              → A ≃ (♯ A)
  codisc-eq = ♯i ,_

  -- Theorem 3.7 of Shulman
  module _ {i :{♭} ULevel} {A :{♭} Type i} where
    code : (a b : ♯ A) → Type i
    code a = ♯' {Γ = ♯ A} {!!}
         {-
                 (let♯ u := a ↓♯in♯
                     (let♯ v := b ↓♯in♯
                       (♯i (♯ (u == v)))
                     )
                  ) 
-}
  
    ♯-identity-eq : (a b : A) → ((♯i a) == (♯i b)) ≃ ♯ (a == b)
    ♯-identity-eq a b = equiv {!!} fro {!!} {!!}
      where
        to : (♯i a) == (♯i b) → ♯ (a == b)
        to p = {!!}
      
        fro : ♯ (a == b) → ♯i a == ♯i b
        fro p = (let♯ p :=♯i q in♯
                      ♯i (ap ♯i q)
                )
                |> (<– ♯path-eq)


  -- Theorem 6.22 of Shulman
  -- ♭ and ♯ reflect into eachothers categories.
  ♭♯-eq : {i :{♭} ULevel} {A :{♭} Type i} → ♭ (♯ A) ≃ ♭ A
  ♭♯-eq {A = A} = equiv to fro to-fro fro-to
    where
      to : ♭ (♯ A) → ♭ A
      to (a ^♭) = (♭♯e a) ^♭

      fro : ♭ A → ♭ (♯ A)
      fro (a ^♭) = (♯i a) ^♭

      to-fro : (a : ♭ A) → to (fro a) == a
      to-fro (a ^♭) = refl

      fro-to : (a : ♭ (♯ A)) → fro (to a) == a
      fro-to (a ^♭) = ♭-ap _^♭ (! (♭♯η a))
      
  ♯♭-eq : {i :{♭} ULevel} {A :{♭} Type i} → ♯ (♭ A) ≃ ♯ A
  ♯♭-eq {A = A} = equiv to fro to-fro fro-to
    where
      to : ♯ (♭ A) → ♯ A
      to = ♯-rec (λ { (a ^♭) → (♯i a)})

      fro : ♯ A → ♯ (♭ A)
      fro = ♯-rec (uncrisp _ (λ (a : A) → ♯i (a ^♭)))

      to-fro : (a : ♯ A) → to (fro a) == a
      to-fro = (<– ♯path-eq) ∘
               (♯-elim (λ a → to (fro a) == a) (λ a → ♯i refl))

      fro-to : (a : ♯ (♭ A)) → fro (to a) == a
      fro-to = (<– ♯path-eq) ∘
               (♯-elim (λ a → fro (to a) == a) (λ { (a ^♭) → ♯i refl }))
       

  -- Theorem 6.27 of Shulman
  ♭♯-adjoint : {i j :{♭} ULevel} {A :{♭} Type i} {B :{♭} A → Type j}
               → ♭ ((a : ♭ A) → B (♭i a)) ≃ ♭ ((a : A) → ♯ (B a))
  ♭♯-adjoint {i} {j} {A} {B}  = equiv to fro to-fro fro-to
    where
      to : ♭ ((a : ♭ A) → B (♭i a)) → ♭ ((a : A) → ♯ (B a))
      to (f ^♭) = (uncrisp B (λ (a :{♭} A) → ♯i (f (a ^♭)))) ^♭

      fro : ♭ ((a : A) → ♯ (B a)) → ♭ ((a : ♭ A) → B (♭i a))
      fro (f ^♭) = (λ { (a ^♭) → ♭♯e (f a) }) ^♭

      to-fro : (f : ♭ ((a : A) → ♯ (B a))) → to (fro f) == f
      to-fro (f ^♭)= ♭-ap _^♭ {!!} 

      fro-to : (f : ♭ ((a : ♭ A) → B (♭i a))) → fro (to f) == f
      fro-to (f ^♭) = ♭-ap _^♭ (λ= (λ a → {!(λ { (a₁ ^♭) → ♭♯e (uncrisp B (λ (a₂ :{♭} _) → ♯i (f (a₂ ^♭))) a₁) })!}))


   
  has-level-is-codiscrete : {i : ULevel} {A : Type i} {n : ℕ₋₂}
                            → (has-level n A) is-codiscrete
  has-level-is-codiscrete = {!!}

  ♯-preserves-level : {i : ULevel} {A : Type i}
                      {n : ℕ₋₂} (p : has-level n A)
                      → has-level n (♯ A)
  ♯-preserves-level {i} {A} {⟨-2⟩} p =
    has-level-in (♯i (contr-center p) ,
      (<– ♯path-eq) ∘ (♯-elim (λ a → ♯i (contr-center p) == a)
        (λ a → ♯i (ap ♯i (contr-path p a)))))
  ♯-preserves-level {i} {A} {S n} p =
    has-level-in (λ x y → (<– (codisc-eq has-level-is-codiscrete))
                           ((♯-elim (λ y → has-level n (x == y)) {!!}) y)
                           )








  {-
  
  to-crisp : {i :{♭} ULevel} {j : ULevel} {A : ♭ (Type i)} {B : Type j}
        → (♭i A → B) → (A ♭:→ B)
  to-crisp {A = (A ^♭)} f = (<– ♭-recursion-eq) (f ∘ ♭i) 

  
  _is-codiscrete : {j :{♭} ULevel} (B : Type j) → Type (lsucc j)
  _is-codiscrete {j} B = (A : ♭ (Type j)) → to-crisp {A = A} {B = B} is-an-equiv

  codisc-eq : {j :{♭} ULevel} {B : Type j} (p : B is-codiscrete)
              {A : ♭ (Type j)} → (♭i A → B) ≃ (A ♭:→ B)
  codisc-eq {j} {B} p {A} = (to-crisp {A = A} {B = B}) , (p A)

  codisc-promote : {j :{♭} ULevel} {B : Type j} (p : B is-codiscrete)
                   {A : ♭ (Type j)} → (A ♭:→ B) → (♭i A → B)
  codisc-promote p = <– (codisc-eq p) 

  _is-codiscrete-is-a-prop : {j :{♭} ULevel} (B : Type j) → (B is-codiscrete) is-a-prop
  _is-codiscrete-is-a-prop {j} B =
    mapping-into-prop-is-a-prop (λ { (A ^♭) → is-equiv-is-prop })

  _is-codiscrete₀ : {j :{♭} ULevel} (B : Type j) → Type₀
  _is-codiscrete₀ {j} B = (resize₀ ((B is-codiscrete) , (B is-codiscrete-is-a-prop))) holds

  ⊤-is-codiscrete : ⊤ is-codiscrete
  ⊤-is-codiscrete =
    λ { (A ^♭) → to-crisp is-an-equivalence-because
      (λ _ _ → unit) is-inverse-by
        (λ f → refl) and (λ f → refl) }
  
 {-
  Π-codisc : {i :{♭} ULevel} {A : Type i} {B : A → Type i}
             → ((a : A) → (B a) is-codiscrete)
             → ((a : A) → B a) is-codiscrete
  Π-codisc {i} {A} {B} f =
     λ { (T ^♭) → to-crisp is-an-equivalence-because
      (λ g → λ t a → {!codisc-promote (f a)!}) is-inverse-by
        {!!} and {!!}}
  -}
  

  {-
  question : {i :{♭} ULevel} (B : Type i)
             (r : (A : ♭ (Type i)) → (to-crisp {A = A} {B = B}) is-split-inj)
             → B is-codiscrete
  question {i = i} B r =
    λ { (A ^♭) → to-crisp is-an-equivalence-because
      fst (r (A ^♭)) is-inverse-by
        (λ f → {!!})
        and snd (r (A ^♭)) } -}
  
  

  
  {-  The idea from this proof is to map out of the suspension

  =-is-codiscrete : {i :{♭} ULevel} {B : Type i} (p : B is-codiscrete)
                    (x y : B) → (x == y) is-codiscrete
  =-is-codiscrete {i} {B} p x y =
    λ { (A ^♭) → to-crisp is-an-equivalence-because
      {!!} is-inverse-by {!!} and {!!} } 
  
  -}


  
  -}
