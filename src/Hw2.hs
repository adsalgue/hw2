{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Hw2 where 

import ProofCombinators

--------------------------------------------------------------------------------
-- | Recall the `Peano` datatype from class
--------------------------------------------------------------------------------
data Peano = Z | S Peano 
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- | Problem 1: Fill in the implementation of `thm_add_assoc` to prove `add` is 
--              associative. 
--------------------------------------------------------------------------------

{-@ reflect add @-}
add         :: Peano -> Peano -> Peano 
add Z     m = m 
add (S n) m = S (add n m)

{-@ thm_add_assoc :: x:_ -> y:_ -> z:_ -> { add x (add y z) == (add (add x y) z) } @-}
thm_add_assoc :: Peano -> Peano -> Peano -> Proof 
thm_add_assoc = impossible "TBD"

--------------------------------------------------------------------------------
-- | Problem 2: Fill in the implementation of `thm_double` to prove that `double` 
--              is equivalent to adding a number to itself.
--------------------------------------------------------------------------------

{-@ reflect double @-}
double :: Peano -> Peano 
double Z     = Z 
double (S n) = S (S (double n))

{-@ thm_double :: n:Peano -> { double n = add n n } @-}
thm_double :: Peano -> Proof 
thm_double = impossible "TBD" 

--------------------------------------------------------------------------------
-- | Problem 3: `itadd` is a "tail-recursive" implementation of `add`: prove 
--              that `itadd` is equivalent to `add`. 
--------------------------------------------------------------------------------

{-@ reflect itadd @-}
itadd :: Peano -> Peano -> Peano 
itadd Z     m = m 
itadd (S n) m = itadd n (S m)

{-@ thm_itadd :: n:_ -> m:_ -> {itadd n m = add n m} @-}
thm_itadd :: Peano -> Peano -> Proof 
thm_itadd = impossible "TBD"

--------------------------------------------------------------------------------
data List a = Nil | Cons a (List a)
  deriving (Eq, Show)

{-@ reflect app @-}
app :: List a -> List a -> List a 
app Nil ys         = ys 
app (Cons x xs) ys = Cons x (app xs ys)

{-@ reflect rev @-}
rev :: List a -> List a 
rev Nil         = Nil 
rev (Cons x xs) = app (rev xs) (Cons x Nil)

--------------------------------------------------------------------------------
-- | Problem 4: `itrev` is a "tail-recursive" implementation of `rev`: prove 
--              that `itrev` is equivalent to `rev`. 
--   HINT: you may need to define and prove some helper lemmas for `thm_itrev`.
--------------------------------------------------------------------------------

{-@ reflect itrev @-}
itrev :: List a -> List a -> List a 
itrev acc Nil         = acc 
itrev acc (Cons x xs) = itrev (Cons x acc) xs

{-@ thm_itrev :: xs:_ -> { rev xs == itrev Nil xs } @-}
thm_itrev :: List a -> Proof 
thm_itrev = impossible "TBD" 

--------------------------------------------------------------------------------
-- | Consider the following `Tree` datatype and associated operations.
--------------------------------------------------------------------------------
data Tree a = Tip | Node (Tree a) a (Tree a)
  deriving (Show)

{-@ reflect mirror @-}
mirror :: Tree a -> Tree a 
mirror Tip          = Tip 
mirror (Node l a r) = Node (mirror r) a (mirror l)

--------------------------------------------------------------------------------
-- | Problem 5: Prove the following property that `mirror`-ing a `Tree` twice
--              returns the same `Tree`.
--------------------------------------------------------------------------------
{-@ thm_mirror :: t:_ -> { mirror (mirror t) = t } @-}
thm_mirror :: Tree a -> Proof 
thm_mirror = impossible "TBD"

--------------------------------------------------------------------------------
-- | Problem 6: Fix the implementation of `contents` so that `q6` typechecks 
--------------------------------------------------------------------------------

{-@ reflect contents @-}
contents :: Tree a -> List a 
contents t = Nil 

{-@ q6 :: _ -> { v:_ | v = Cons 1 (Cons 2 (Cons 3 Nil)) } @-} 
q6 :: () -> List Int 
q6 _   = contents t2  
  where 
    t2 = Node t1  2 t3 
    t1 = Node Tip 1 Tip   
    t3 = Node Tip 3 Tip   

--------------------------------------------------------------------------------
-- | Problem 7 (**) Prove that the contents of a mirrored tree are the reverse of 
--                  the contents of the original tree.
--------------------------------------------------------------------------------

{-@ thm_mirror_contents :: t:_ -> { contents (mirror t) = rev (contents t) } @-}
thm_mirror_contents :: Tree a -> Proof
thm_mirror_contents = impossible "TBD"