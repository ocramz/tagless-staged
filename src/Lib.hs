{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# language MultiParamTypeClasses#-}
{-# language TemplateHaskell #-}
{-# options_ghc -Wno-unused-imports #-}
{-|
paper : https://okmij.org/ftp/tagless-final/TaglessStaged/beyond.pdf

code : https://okmij.org/ftp/tagless-final/TaglessStaged/TSCore.hs
-}
module Lib where

import Data.Functor.Compose (Compose(..)) -- called J in the paper

import Language.Haskell.TH (Q, runQ, runIO, TExp(..), unType)
import Language.Haskell.TH.Ppr (pprint)
import Language.Haskell.TH.Syntax (Quasi(..), Lift(..))

{-
-- A Haskell value of the type Sym repr => repr a
-- represents an expression in the object language of the type a
-}
class Sym repr where
    intS :: Int -> repr Int
    addS :: repr (Int -> Int -> Int)
    mulS :: repr (Int -> Int -> Int)
    appS :: repr (a -> b) -> repr a -> repr b
    lamS :: (repr a -> repr b) -> repr (a -> b)

-- | Pure evaluator
newtype R a = R { runR :: a }

instance Sym R where
    intS = R
    addS = R (+)
    mulS = R (*)
    R f `appS` R x = R $ f x
    lamS f = R $ runR . f . R

-- | Code generating evaluator
newtype Code a = Code { getCode :: Q (TExp a) }

instance Sym Code where
  intS = Code . liftTyped
  addS = Code [|| (+) ||]
  mulS = Code [|| (*) ||]
  appS (Code f) (Code x) = Code [|| $$(f) $$(x) ||]
  lamS f = Code [|| \x -> $$( (getCode . f . Code) [||  x ||] ) ||]

-- | pretty-print the source code
--
-- > pprCode exS1
-- (GHC.Num.+) 1 2
pprCode :: Code a -> IO ()
pprCode c = do
  q <- unType <$> runQ (getCode c)
  putStrLn $ pprint q


-- an example expression
exS1 :: Sym repr => repr Int
exS1 = (addS `appS` intS 1) `appS` intS 2





-- -- combinators from the paper, using Compose instead of defining J

infixl 2 $$
($$) :: (Sym repr, Applicative m) => 
        m (repr (a -> b)) -> m (repr a) -> m (repr b)
f $$ x = appS <$> f <*> x

infixl 7 *:
infixl 6 +:

(+:) :: (Sym repr, Applicative m) => 
        m (repr Int) -> m (repr Int) -> m (repr Int)
x +: y = pure addS $$ x $$ y

(*:) :: (Sym repr, Applicative m) => 
        m (repr Int) -> m (repr Int) -> m (repr Int)
x *: y = pure mulS $$ x $$ y

type (.:) = Compose

liftJ :: (Functor f, Applicative g) => f a -> (f .: g) a
liftJ = Compose . fmap pure

mapJ2 :: Functor f =>
         (g1 a1 -> g2 a2) -> Compose f g1 a1 -> Compose f g2 a2
mapJ2 f = Compose . fmap f . getCompose

liftJ2 :: (Functor f, Functor g, Applicative h) => (f .: g) a -> (f .: (g .: h)) a
liftJ2 = mapJ2 liftJ


-- `Injecting' a monad into an Applicative stack
-- The following class witnesses that the applicative n is `above'
-- monad m.
-- The operation bindA looks quite like monadic bind, with quite an
-- important difference

class (Monad m, Applicative m, Applicative n) => Above m n where
    bindA :: m a -> (a -> n b) -> n b


instance (Monad m, Applicative m) => Above m m where
    bindA = (>>=)

instance (Applicative i, Monad m, Applicative m, Above m n) => Above m (Compose n i) where
    m `bindA` f = Compose $ m `bindA` (getCompose . f)


-- -- lam :: (Applicative m, AppLiftable i, SSym repr, LamPure repr) =>
-- --        (forall j. AppLiftable j => 
-- --         (i :. j) (repr a) -> (m :. (i :. j)) (repr b))
-- --        -> (m :. i) (repr (a->b))
-- lam f = fmap lamS (Compose . fmap getCompose . getCompose $ f  (Compose . pure $ v))
--  where
--  -- instantiate applicative j to be a Reader: repr a -> w
--  v = \repra -> repra                    -- bound variable

-- Make a variable an expression
-- var :: Applicative m => i (repr a) -> (m :. i) (repr a)
var :: (Applicative f) => g a -> (f .: g) a
var = Compose . pure 

-- Just a specialization of liftJ2
-- weaken :: (Applicative m, Applicative i, Applicative j) => 
--           (m :. i) (repr a) -> (m :. (i :. j)) (repr a)
weaken :: (Functor f1, Functor g0, Applicative h0) => (.:) f1 g0 a -> (.:) f1 (g0 .: h0) a
weaken = liftJ2
