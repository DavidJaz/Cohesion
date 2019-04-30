{-# OPTIONS --without-K #-}

module Flat where
  open import lib.Basics
  open import Basics
  open import Bool

  open import lib.types.Bool
  open import lib.NType2
  open import lib.Equivalence2
  open import lib.types.Suspension
  open import lib.types.IteratedSuspension
  open import lib.types.Pushout as Pushout
  open import lib.types.Truncation

  


  -- The type of points of A, ♭ A, is inductively generated by the crisp elements of A
  data ♭ {l :{♭} ULevel} (A :{♭} Type l) : Type l where
    _^♭ : A ::→ ♭ A

  -- The deduced mapping principle of ♭ A: it represents crisp functions.
  ♭-elim : {c : ULevel} {l :{♭} ULevel}{A :{♭} Type l}
         → (C : ♭ A → Type c)
         → ((u :{♭} A) → C (u ^♭))
         → (x : ♭ A) → C x
  ♭-elim C f (x ^♭) = f x
  syntax ♭-elim C (λ u → t) a = let♭ u ^♭:= a in♭ t in-family C

   {- Mike's "let" notation (following Felix) -}
   -- An implicit version of ♭-elim
  let♭ : {i j :{♭} ULevel} {A :{♭} Type i} {B : ♭ A → Type j}
         (a : ♭ A) (f : (u :{♭} A) → B (u ^♭))
         → B a
  let♭ (u ^♭) f = f u
  syntax let♭ a (λ u → t) = let♭ u ^♭:= a in♭ t


  ♭-rec : {i :{♭} ULevel} {j : ULevel} {A :{♭} Type i} {B : Type j}
                → (A ::→ B) → (♭ A) → B
  ♭-rec f (a ^♭) = f a

  ♭-rec-eq : {i :{♭} ULevel} {j : ULevel} {A :{♭} Type i} {B : Type j}
                → (A ::→ B) ≃ (♭ A → B)
  ♭-rec-eq {A = A} {B = B} =
    equiv ♭-rec
      (λ f → λ (a :{♭} A) → f (a ^♭))  -- fro
      (λ f → λ= (λ { (a ^♭) → refl })) -- to-fro
      (λ f → refl)                     -- fro-to

  -- Crisp function types, but from A : ♭ Type
  _♭:→_ : {i :{♭} ULevel} {j : ULevel} (A : ♭ (Type i)) (B : Type j) → Type (lmax i j)
  (A ^♭) ♭:→ B = A ::→ B 

  -- The inclusion of the points of A into A
  _↓♭ : {i :{♭} ULevel} {A :{♭} Type i} → (♭ A → A)
  _↓♭ (x ^♭) = x
  

  -- The (judgemental) computation rule for mapping out of points
  ♭-β : {i :{♭} ULevel} {A :{♭} Type i} (a :{♭} ♭  A)
        → ((a ↓♭) ^♭) == a
  ♭-β (a ^♭) = refl

  -- Application of crisp functions to crisp equalities
  -- Used mostly to apply _^♭.
  ♭-ap : {i j :{♭} ULevel} {A :{♭} Type i} {B : Type j}
         (f : (a :{♭} A) → B) {x y :{♭} A} (p :{♭} x == y)
         → (f x) == (f y)
  ♭-ap f refl = refl

  -- ♭ is a functor
  ♭→ : {i j :{♭} ULevel} {A :{♭} Type i} {B :{♭} Type j}
       → (f :{♭} A → B) → (♭ A → ♭ B)
  ♭→ f (x ^♭) = (f x) ^♭

  -- The naturality square of the inclusion of points (judgemental!)
  ♭→-nat : {i j :{♭} ULevel} {A :{♭} Type i} {B :{♭} Type j} (f :{♭} A → B)
           → (a : ♭ A) → (f ∘ _↓♭) a  == (_↓♭ ∘ (♭→ f)) a
  ♭→-nat f (a ^♭) = refl

  -- Proof of functoriality
  ♭→∘ : {i j k :{♭} ULevel} {A :{♭} Type i} {B :{♭} Type j} {C :{♭} Type k}
        {f :{♭} A → B} {g :{♭} B → C}
        → ♭→ (g ∘ f) == (♭→ g) ∘ (♭→ f)
  ♭→∘ {f = f} {g = g} =
    λ= (λ a → -- We test on elements, but
          let♭ u ^♭:= a in♭ -- might as well assume those elements are crisp
            refl -- where it follows by definition.
          in-family (λ a → (♭→ (g ∘ f)) a == ((♭→ g) ∘ (♭→ f)) a)  )
        

  -- ♭→ preserves crisp equivalences
  ♭→e : {i j :{♭} ULevel} {A :{♭} Type i} {B :{♭} Type j}
        → (e :{♭} A ≃ B) → (♭ A) ≃ (♭ B)
  ♭→e e =
    equiv (♭→ (–> e))
          (♭→ (<– e))
          (λ { (a ^♭) → ♭-ap _^♭ (<–-inv-r e a) })
          (λ { (a ^♭) → ♭-ap _^♭ (<–-inv-l e a) })
  

  -- A type is discrete if the inclusion of its point is an equivalence.
  _is-discrete : {l :{♭} ULevel} → (A :{♭} Type l) → Type l
  _is-discrete {l} A = is-equiv {l} {l} {♭ A} {A} _↓♭

  -- The equivalence between the points of a discrete type and itself
  discrete-eq : {l :{♭} ULevel} {A :{♭} Type l} → A is-discrete → (♭ A) ≃ A
  discrete-eq = _↓♭ ,_

  _is-discrete-is-a-prop : {l :{♭} ULevel} (A :{♭} Type l) → (A is-discrete) is-a-prop
  A is-discrete-is-a-prop = is-equiv-is-prop

  is-discrete-prop : {l :{♭} ULevel} → SubtypeProp (♭ (Type l)) l
  is-discrete-prop = (λ { (A ^♭) → A is-discrete }) , (λ { (A ^♭) → A is-discrete-is-a-prop }) 

  -- The subtype of discrete types
  Discrete : (l :{♭} ULevel) → Type (lsucc l)
  Discrete l = Subtype is-discrete-prop

  Discrete-_-Type_ : (n :{♭} ℕ₋₂) (i :{♭} ULevel) → Type (lsucc i)
  Discrete- n -Type i = Subtype prop
    where prop : SubtypeProp (♭ (n -Type i)) i
          prop = (λ { (A ^♭) → (fst A) is-discrete }) , (λ { (A ^♭) → (fst A) is-discrete-is-a-prop })

  DiscSet : (i :{♭} ULevel) → Type (lsucc i)
  DiscSet i = Discrete- ⟨ S (S O) ⟩₋₂ -Type i

  DiscSet₀ = DiscSet lzero

  ∈Disc : {i :{♭} ULevel} (A : DiscSet i) → Type i
  ∈Disc A = ((♭→ ∈) (fst A)) ↓♭

  DiscSet-to-Set : {i :{♭} ULevel} → DiscSet i → hSet i
  DiscSet-to-Set A = (fst A) ↓♭

  -- DiscSet_is-discrete : {i :{♭} ULevel} → (A :{♭} DiscSet i) → (∈Disc A) is-discrete
  -- DiscSet A is-discrete = {!(snd A)!}

  
  -- Just in case, we apply univalence to the discrete-eq
  discrete-id : {l :{♭} ULevel} {A :{♭} Type l} → A is-discrete → (♭ A) == A
  discrete-id p = ua (discrete-eq p)

  -- Obviously, the points of a type are discrete
  ♭-is-discrete : {l :{♭} ULevel} {A :{♭} Type l} → (♭ A) is-discrete
  ♭-is-discrete {_} {A} =
                        _↓♭ is-an-equivalence-because
                           fro is-inverse-by
                             to-fro
                             and
                             fro-to
                        where
                          fro : ♭ A → ♭ (♭ A)
                          fro (a ^♭) = (a ^♭) ^♭

                          to-fro : (a : ♭ A) → ((fro a) ↓♭) == a
                          to-fro (a ^♭) = refl
  
                          fro-to  : (a : ♭ (♭ A)) → fro (a ↓♭) == a
                          fro-to ((a ^♭) ^♭) = refl


  -- To prove the ♭i is an equivalence, it suffices to give a section of it.
  _is-discrete-because_is-section-by_ : {l :{♭} ULevel} (A :{♭} Type l)
                        (s :{♭} A → ♭ A) (p :{♭} (a : A) → ((s a) ↓♭)== a)
                        → A is-discrete
  A is-discrete-because s is-section-by p =
      _↓♭ is-an-equivalence-because s is-inverse-by p and
        (λ { (a ^♭) → ! (♭-β (s a)) ∙ (♭-ap _^♭ (p a))})


  

  -- ♭ commutes with identity types in the following sense
  module _ {i :{♭} ULevel} {A :{♭} Type i} where
    ♭-identity-eq : (x y :{♭} A) → ♭ (x == y) ≃ ((x ^♭) == (y ^♭))
    ♭-identity-eq _ _ = equiv to fro to-fro fro-to
      where
        to : {x y :{♭} A} → ♭ (x == y) → ((x ^♭) == (y ^♭))
        to (refl ^♭) = refl

        fro : {x y :{♭} A} → ((x ^♭) == (y ^♭)) → ♭ (x == y)
        fro refl = refl ^♭

        to-fro : {x y :{♭} A} → (p : (x ^♭) == (y ^♭)) → (to (fro p) == p)
        to-fro refl = refl

        fro-to : {x y :{♭} A} → (p : ♭ (x == y)) → fro (to p) == p
        fro-to (refl ^♭) = refl

        {- From Tslil:
                There once was a Bear in a Zoo
                Who didn't know quite what to do
                    It bored him so
                    To walk to and fro
                So he flipped it and walked fro and to
        -}

  -- ♭ preserves crisp level.
  ♭-preserves-level : {i :{♭} ULevel} {A :{♭} Type i}
                      {n :{♭} ℕ₋₂} (p :{♭} has-level n A)
                      → has-level n (♭ A)
  ♭-preserves-level {_}{A}{⟨-2⟩} p =
    has-level-in ((a ^♭) ,
      (λ {(y ^♭) → (–> (♭-identity-eq a y)) ((contr-path p y )^♭)}))
    where -- If A contracts onto a, then ♭ A contracts onto a ^♭
      a = contr-center p
  ♭-preserves-level {_}{A}{S n}  p =
    has-level-in (λ {(x ^♭) (y ^♭) →
      equiv-preserves-level
        (♭-identity-eq x y)
        {{♭-preserves-level {_}{(x == y)}{n} (has-level-apply p x y)}}})
       {-
         Because the equality types of ♭ A are themselves ♭ (x == y) for x y : A,
         and because we know that x == y has level n if A has level (S n), we can recurse
         to show that ♭ (x == y) has level n and therefore ♭ A has level (S n).
       -}

  -- A version of ♭ that acts on n-types.
  ♭ₙ : {i :{♭} ULevel} {n :{♭} ℕ₋₂}
       → (A :{♭} n -Type i) → (n -Type i)
  ♭ₙ A = (♭ (fst A)) , ♭-preserves-level (snd A)

  
  ♭-Trunc-map : {i :{♭} ULevel} {n :{♭} ℕ₋₂} (X :{♭} Type i)
             → (Trunc n (♭ X)) → ♭ (Trunc n X)
  ♭-Trunc-map X =
    Trunc-elim {{p = λ _ → ♭-preserves-level Trunc-level}}
      (λ { (a ^♭) → [ a ] ^♭ })

  -- Until ♯ works we have to postulate this.
  ♭-Trunc-eq : {i :{♭} ULevel} {n :{♭} ℕ₋₂} (X :{♭} Type i)
             → (Trunc n (♭ X)) ≃ ♭ (Trunc n X)
  ♭-Trunc-eq X = (♭-Trunc-map X) , unproven
    where
      postulate unproven : (♭-Trunc-map X) is-an-equiv

  ⊤-is-discrete : ⊤ is-discrete
  ⊤-is-discrete = _↓♭ is-an-equivalence-because
                         (λ {unit → unit ^♭}) is-inverse-by
                           (λ {unit → refl})
                           and
                           (λ {(unit ^♭) → refl})

  -- ♭ commutes with coproducts.
  ♭-commutes-with-⊔ : {i j :{♭} ULevel} {A :{♭} Type i} {B :{♭} Type j}
                      → ♭ (A ⊔ B) ≃ (♭ A) ⊔ (♭ B)
  ♭-commutes-with-⊔ = to ,
    (to is-an-equivalence-because
      fro is-inverse-by
        (λ { (inl (a ^♭)) → refl ;
             (inr (b ^♭)) → refl })
        and
        (λ { ((inl a) ^♭) → refl ;
             ((inr b) ^♭) → refl }))
    where
      to : {i j :{♭} ULevel} {A :{♭} Type i} {B :{♭} Type j}
           → ♭ (A ⊔ B) → (♭ A) ⊔ (♭ B)
      to ((inl a) ^♭) = inl (a ^♭)
      to ((inr b) ^♭) = inr (b ^♭)

      fro : {i j :{♭} ULevel} {A :{♭} Type i} {B :{♭} Type j}
           → (♭ A) ⊔ (♭ B) → ♭ (A ⊔ B)
      fro (inl (a ^♭)) = (inl a) ^♭
      fro (inr (b ^♭)) = (inr b) ^♭

  
  -- ♭ commutes with Σ types for crisp families.
  module _ {i j :{♭} ULevel} {A :{♭} Type i} {B :{♭} A → Type j} where
    ♭-commutes-with-Σ : ♭ (Σ A B) ≃ Σ (♭ A) (λ a → let♭ u ^♭:= a in♭ ♭ (B u))
    ♭-commutes-with-Σ = equiv to fro ((λ { ((a ^♭) , (b ^♭)) → refl })) ((λ { ((a , b) ^♭) → refl }))
      where
        to : ♭ (Σ A B) → Σ (♭ A) (λ a → let♭ u ^♭:= a in♭ ♭ (B u))
        to ((a , b) ^♭) = ((a ^♭) , (b ^♭))

        fro : Σ (♭ A) (λ a → let♭ u ^♭:= a in♭ ♭ (B u)) → ♭ (Σ A B)
        fro ((a ^♭) , (b ^♭)) = (a , b) ^♭
  

  ℕ-is-discrete : ℕ is-discrete
  ℕ-is-discrete =
    ℕ is-discrete-because fro is-section-by to-fro
    where
      fro : ℕ → ♭ ℕ
      fro O = O ^♭
      fro (S n) = (♭→ S) (fro n)
      
      to-fro : (n : ℕ) → ((fro n) ↓♭) == n
      to-fro O = refl
      to-fro (S n) = (fro (S n)) ↓♭
                   =⟨ ! ((♭→-nat S) (fro n)) ⟩
                     (S ∘ _↓♭) (fro n)
                   =⟨ ap S (to-fro n) ⟩
                     S n
                   =∎
        {-
          When proving this equality by induction on n, the case of 0 presents no problem,
          but when we work with (S n), we have to deal with the fact that n is not crisp.
          However, as a constructor (and therefore defined in the empty context), S is crisp.
          Therefore, we can use the naturality sqaure of ♭ to commute it past fro, and then recurse.
        -}

  -- We copy the proof for ULevel (or would but we can't pattern match on lsucc?)
  {-
  ULevel-is-discrete : ULevel is-discrete
  ULevel-is-discrete =
    ULevel is-discrete-because fro is-section-by to-fro
    where
      fro : ULevel → ♭ ULevel
      fro lzero = lzero ^♭
      fro (lsucc n) = (♭→ lsucc) (fro n)
      
      to-fro : (n : ULevel) → ♭i (fro n) == n
      to-fro lzero = refl
      to-fro (lsucc n) = ♭i (fro (lsucc n))
                       =⟨ ! ((♭→-nat lsucc) (fro n)) ⟩
                         (lsucc ∘ ♭i) (fro n)
                       =⟨ ap lsucc (to-fro n) ⟩
                         lsucc n
                       =∎ -}

  Bool-is-discrete : Bool is-discrete
  Bool-is-discrete = Bool is-discrete-because fro is-section-by to-fro
    where
      fro : Bool → ♭ Bool
      fro true = true ^♭
      fro false = false ^♭

      to-fro : (b : Bool) → ((fro b) ↓♭)== b
      to-fro true = refl
      to-fro false = refl

  Bool-to-♭Prop₀ : Bool → ♭ Prop₀
  Bool-to-♭Prop₀ true = True ^♭
  Bool-to-♭Prop₀ false = False ^♭

  Bool-to-♭Prop₀∘↓♭=♭→Bool-to-Prop₀ : Bool-to-♭Prop₀ ∘ _↓♭ == (♭→ Bool-to-Prop₀)
  Bool-to-♭Prop₀∘↓♭=♭→Bool-to-Prop₀ = λ= (λ { (true ^♭) → refl ; (false ^♭) → refl })

{-
  _-Sphere-is-discrete : (n :{♭} ℕ) → (Sphere n) is-discrete
  n -Sphere-is-discrete = (Sphere n) is-discrete-because
    (fro n) is-section-by {!!}
    where
      ♭-north : {n :{♭} ℕ} → ♭ (Sphere n)
      ♭-north {O} = true ^♭
      ♭-north {S n} = {!north!}
  
      ♭-south : {n :{♭} ℕ} → ♭ (Sphere n)
      ♭-south = {!!}

      fro : (n :{♭} ℕ) → (Sphere n) → ♭ (Sphere n)
      fro O = λ { true → true ^♭ ; false →  false ^♭ } 
      fro (S n) = {!Susp-rec {A = Sphere n} {C = ♭ (Sphere (S n))} ♭-north ♭-south!}

      
-}
