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


{-@ thm_Z_add :: p:Peano -> { add p Z == p } @-}
thm_Z_add :: Peano -> Proof

thm_Z_add Z
   = add Z Z
   === Z
   *** QED

thm_Z_add (S p) 
   = add (S p) Z
   === S (add p Z) ? thm_Z_add p
   === S p
   *** QED

{-@ lemma :: apple:_ -> banana:_ -> { add apple (S banana) == S (add apple banana) } @-}
lemma :: Peano -> Peano -> Proof
lemma Z b
   = add Z (S b)
   === S b
   === S (add Z b)
   *** QED

lemma (S a') b
   = add (S a') (S b)
   === S (add a' (S b))
      ? lemma a' b
   === S (S (add a' b))
   === S (add (S a') b)
   *** QED


{-@ thm_add_com :: x:_ -> y:_ -> {add x y == add y x} @-}
thm_add_com :: Peano -> Peano -> Proof
thm_add_com Z y
   = add Z y
   === y
     ? thm_Z_add y
   === add y Z
   *** QED

thm_add_com (S x') y
   = add (S x') y
   === S (add x' y)
      ? thm_add_com x' y
   === S (add y x')
      ? lemma y x'
   === add y (S x')
   *** QED


{-@ thm_add_assoc :: x:_ -> y:_ -> z:_ -> { add x (add y z) == (add (add x y) z) } @-}
thm_add_assoc :: Peano -> Peano -> Peano -> Proof 

thm_add_assoc Z y' z'
   = add Z (add y' z')
   === add y' z'
   === add (add Z y') z'
   *** QED
   

{-
-- Case 1: all inputs are 0
thm_add_assoc Z Z Z
   = add Z (add Z Z)
   === add Z Z
   === (add (add Z Z) Z)
   *** QED

--- Case 2: all inputs are nonzero
thm_add_assoc (S x') (S y') (S z')
   = add (S x') (add (S y') (S z'))
   === S (add x' (add (S y') (S z')))
       ? thm_add_assoc x' (S y') (S z')
   === S (add (add x' (S y')) (S z'))
   === add (S (add x' (S y'))) (S z')
   === add (add (S x') (S y')) (S z')
   *** QED
-}

thm_add_assoc (S x') y' z'
   = add (S x') (add y' z')
   === S (add x' (add y' z'))
      ? thm_add_assoc x' y' z'
   === S (add (add x' y') z')
   === add (S (add x' y')) z'
   === add (add (S x') y') z'
   *** QED
{-

-- Case 3: x' Zero Zero
thm_add_assoc x' Z Z
    = add x' (add Z Z)
    === add x' Z
        ? thm_Z_add x'
    === add (add x' Z) Z
    *** QED

-- Case 4: Zero y' Zero
thm_add_assoc Z y' Z
    = add Z (add y' Z)
       ? thm_Z_add y'
    === add Z y'
       ? thm_Z_add (add y' Z)
    === add (add Z y') Z
    *** QED

-- Case 5: Zero Zero z'
thm_add_assoc Z Z z'
    = add Z (add Z z')
       ? thm_add_com Z z'
    === add Z (add z' Z)
       ? thm_Z_add z'
    === add Z z'
       ? thm_Z_add (add z' Z)
    === add (add Z Z) z'
    *** QED

-- Case 6: x' y' Zero
thm_add_assoc x' y' Z
    = add x' (add y' Z)
        ? thm_Z_add y'
    === add x' y'
        ? thm_Z_add (add x' y')
    === add (add x' y') Z
    *** QED

-- Case 7: x' Zero y'
thm_add_assoc x' Z y'
    = add x' (add Z y')
       ? thm_add_com Z y'
    === add x' (add y' Z)
       ? thm_Z_add x'
    === add (add x' Z) (add y' Z)
       ? thm_Z_add y'
    === add (add x' Z) y'
    *** QED

-- Case 8: Zero y' z'
thm_add_assoc Z x' y'
    = add Z (add x' y')
      ? thm_Z_add (add x' y')
    === add x' y'
      ? thm_Z_add x'
    === add (add x' Z) y'
      ? thm_add_com x' Z
    === add (add Z x') y'
    *** QED

-}

--------------------------------------------------------------------------------
-- | Problem 2: Fill in the implementation of `thm_double` to prove that `double` 
--              is equivalent to adding a number to itself.
--------------------------------------------------------------------------------

{-@ reflect double @-}
double :: Peano -> Peano 
double Z     = Z 
double (S n) = S (S (double n))

{-@ thm_double :: n:Peano -> { double n == add n n } @-}
thm_double :: Peano -> Proof 
thm_double Z
   = double Z 
   === Z
   === add Z Z
   *** QED

thm_double (S p)
   = double (S p)
   === S (S (double p))
      ? thm_double p
   === S (S (add p p))
   === S (add (S p) p)
      ? thm_add_com (S p) p
   === S (add p (S p))
   === add (S p) (S p)
   *** QED


--------------------------------------------------------------------------------
-- | Problem 3: `itadd` is a "tail-recursive" implementation of `add`: prove 
--              that `itadd` is equivalent to `add`. 
--------------------------------------------------------------------------------

{-@ reflect itadd @-}
itadd :: Peano -> Peano -> Peano 
itadd Z     m = m 
itadd (S n) m = itadd n (S m)

{-@ thm_itadd :: n:_ -> m:_ -> {itadd n m == add n m} @-}
thm_itadd :: Peano -> Peano -> Proof 

thm_itadd Z y'
   = itadd Z y'
   === y'
   === add Z y'
   *** QED

thm_itadd (S x') y'
   = itadd (S x') y'
   === itadd x' (S y')
     ? thm_itadd x' (S y')
   === add x' (S y')
     ? thm_add_com x' (S y')
   === add (S y') x'
   === S (add y' x')
     ? thm_add_com x' y'
   === S (add x' y')
   === add (S x') y'
   *** QED


{-
-- Case 1: All Zeros
thm_itadd Z Z
   = itadd Z Z
   === Z
     ? thm_Z_add Z
   === add Z Z
   *** QED

-- Case 2: All nonzeroes
thm_itadd (S x') (S y')
   = itadd (S x') (S y')
   === itadd x' (S (S y'))
      ? thm_itadd x' (S (S y'))
   === add x' (S (S y'))
      ? thm_add_com x' (S (S y'))
   === add (S (S y')) x'
   === S (add (S y') x')
      ? thm_add_com (S y') x'
   === S (add x' (S y'))
   === add (S x') (S y')
   *** QED

-- Case 3: x' Zero
thm_itadd (S x') Z
   = itadd (S x') Z
   === itadd x' (S Z)
      ? thm_itadd x' (S Z)
   === add x' (S Z)
      ? thm_add_com x' (S Z)
   === add (S Z) x'
   === S (add Z x')
      ? thm_add_com Z x'
   === S (add x' Z)
   === add (S x') Z
   *** QED

-- Case 4: Zero y'
thm_itadd Z (S y')
   = itadd Z (S y')
   === (S y')
     ? thm_Z_add (S y')
   === add (S y') Z
     ? thm_add_com (S y') Z
   === add Z (S y')
   *** QED

-}




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

-- First Helper Lemma
-- Proves that appending Nil to a List x will always return x
{-@ thm_app_Nil :: x:_ -> {app x Nil == x} @-}
thm_app_Nil :: List a -> Proof

thm_app_Nil Nil 
    = app Nil Nil
    === Nil
    === Nil
    *** QED

thm_app_Nil (Cons x xs) 
    = app (Cons x xs) Nil
    === Cons x (app xs Nil)
       ? thm_app_Nil xs
    === (Cons x xs)
    *** QED


-- Helper Lemma
-- Proves the association on app
{-@ thm_app_assoc :: x:_ -> y:_ -> z:_ -> {app x (app y z) == app (app x y) z} @-}
thm_app_assoc :: List a -> List a -> List a -> Proof

thm_app_assoc Nil Nil Nil
   = app Nil (app Nil Nil)
   === app Nil Nil
   === app (app Nil Nil) Nil
   *** QED

thm_app_assoc (Cons x xs) ys zs
   = app (Cons x xs) (app ys zs)
   === Cons x (app xs (app ys zs))
      ? thm_app_assoc xs ys zs
   === Cons x (app (app xs ys) zs)
   === app (Cons x (app xs ys)) zs
   === app (app (Cons x xs) ys) zs
   *** QED

thm_app_assoc Nil ys zs
   = app Nil (app ys zs)
   === app ys zs
   === app (app Nil ys) zs
   *** QED

thm_app_assoc xs Nil zs
   = app xs (app Nil zs)
   === app xs zs
     ? thm_app_Nil xs
   === app (app xs Nil) zs
   === app (app xs Nil) zs
   *** QED

thm_app_assoc xs ys Nil
   = app xs (app ys Nil)
     ? thm_app_Nil ys
   === app xs ys
     ? thm_app_Nil (app xs ys)
   === app (app xs ys) Nil
   *** QED

-- Second Helper Lemma
-- Tries to prove that itrev x y is the same as app y x
{-@ lazy thm_itrev_to_app @-}
{-@ thm_itrev_to_app :: x:_ -> y:_ -> {itrev x y == app (rev y) x} @-}
thm_itrev_to_app :: List a -> List a -> Proof

-- x = xs, y = Nil
thm_itrev_to_app xs Nil
   = itrev xs Nil
   === xs
   === app Nil xs
   === app (rev Nil) xs
   *** QED

-- x = xs, y = (Cons y ys)
thm_itrev_to_app xs (Cons y ys)
   = itrev xs (Cons y ys)
   === itrev (Cons y xs) ys
      ? thm_itrev_to_app (Cons y xs) ys
   === app (rev ys) (Cons y xs)
   === app (rev ys) (Cons y (app Nil xs))
   === app (rev ys) (app (Cons y Nil) xs)
      ? thm_app_assoc (rev ys) (Cons y Nil) xs
   === app (app (rev ys) (Cons y Nil)) xs
   === app (rev (Cons y ys)) xs
   *** QED


{-@ thm_itrev :: xs:_ -> { rev xs == itrev Nil xs } @-} 
thm_itrev :: List a -> Proof 

thm_itrev Nil 
    = rev Nil
    === Nil
    === itrev Nil Nil
    *** QED

thm_itrev (Cons x xs)
    = rev (Cons x xs)
    === app (rev xs) (Cons x Nil)
       ? thm_itrev_to_app (Cons x Nil) xs
    === itrev (Cons x Nil) xs
    === itrev Nil (Cons x xs)
    *** QED


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
{-@ thm_mirror :: t:_ -> { mirror (mirror t) == t } @-}
thm_mirror :: Tree a -> Proof 

thm_mirror Tip 
   = mirror (mirror (Tip))
   === mirror (Tip)
   === Tip
   *** QED
{-
thm_mirror (Node Tip a Tip)
   = mirror (mirror (Node Tip a Tip))
   === mirror (Node (mirror Tip) a (mirror Tip))
   === mirror (Node Tip a Tip)
   === Node (mirror Tip) a (mirror Tip)
   === Node Tip a Tip
   *** QED

thm_mirror (Node l a Tip)
   = mirror (mirror (Node l a Tip))
   === mirror (Node (mirror Tip) a (mirror l))
   === (Node (mirror(mirror l)) a (mirror(mirror Tip)))
       ? thm_mirror l
   === (Node l a (mirror(mirror Tip)))
   === (Node l a (mirror Tip))
   === (Node l a Tip)
   *** QED

thm_mirror (Node Tip a r)
   = mirror (mirror (Node Tip a r))
   === mirror (Node (mirror r) a (mirror Tip))
   === (Node (mirror(mirror Tip)) a (mirror(mirror r)))
       ? thm_mirror r
   === (Node (mirror(mirror Tip)) a r)
   === (Node (mirror Tip) a r)
   === (Node Tip a r)
   *** QED
-}

thm_mirror (Node l a r)
   = mirror (mirror (Node l a r))
   === mirror (Node (mirror r) a (mirror l))
   === (Node (mirror(mirror l)) a (mirror(mirror r)))
       ? thm_mirror l
   === (Node l a (mirror(mirror r)))
       ? thm_mirror r
   === (Node l a r)
   *** QED
--------------------------------------------------------------------------------
-- | Problem 6: Fix the implementation of `contents` so that `q6` typechecks 
--------------------------------------------------------------------------------

{-@ reflect contents @-}
contents :: Tree a -> List a
contents Tip                            = Nil
-- contents (Node (Node l b q) a r)        = app (app (contents (Node l b q)) (Cons a Nil)) (contents r)
-- contents (Node Tip a r)                 = app (app (contents Tip) (Cons a Nil)) (contents r)
contents (Node l a r)                   = app (app (contents l) (Cons a Nil)) (contents r)


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

thm_mirror_contents Tip 
   = contents (mirror Tip)
   === Nil
   === rev (Nil)
   === rev (contents Tip)
   *** QED

thm_mirror_contents (Node l a r)
   = contents (mirror (Node l a r))
   === contents (Node (mirror r) a (mirror l))
    === app (app (contents (mirror r)) (Cons a Nil)) (contents (mirror l))
      ? thm_mirror_contents r
      ? thm_mirror_contents l
   === app (app (rev (contents r)) (Cons a Nil)) (rev (contents l))
   === app (rev (Cons a (contents r)))(rev(contents l))

   === undefined

   -- === 
   -- === rev (app (contents l)(Cons a (contents r))
   -- === rev (app (contents l)(Cons a (app Nil (contents r)))
   -- === rev (app (contents l)(app (Cons a Nil)(contents r))
   -- === rev (app (app (contents l) (Cons a Nil)) (contents r))
   -- === rev (contents (Node l a r))
   *** QED
