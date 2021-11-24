{-# LANGUAGE FlexibleContexts #-}
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

-- | A Haskell value of the type Sym repr => repr a
-- represents an expression in the object language of the type a
class Sym repr where
    -- intS :: Int -> repr Int
    constS :: Lift a => a -> repr a
    addS :: repr (Int -> Int -> Int)
    subS :: repr (Int -> Int -> Int)
    mulS :: repr (Int -> Int -> Int)
    -- | Function application
    appS :: repr (a -> b) -> repr a -> repr b
    -- | Function abstraction
    lamS :: (repr a -> repr b) -> repr (a -> b)


-- | Pure evaluator
--
-- λ> runR exS1
-- 3
newtype R a = R { runR :: a }

instance Sym R where
    -- intS = R
    constS = R
    addS = R (+)
    subS = R (-)
    mulS = R (*)
    R f `appS` R x = R $ f x
    lamS f = R $ runR . f . R

-- | Code generating evaluator
newtype Code a = Code { getCode :: Q (TExp a) }

instance Sym Code where
  constS = Code . liftTyped
  addS = Code [|| (+) ||]
  subS = Code [|| (-) ||]
  mulS = Code [|| (*) ||]
  appS (Code f) (Code x) = Code [|| $$(f) $$(x) ||]
  lamS f = Code [|| \x -> $$( (getCode . f . Code) [||  x ||] ) ||]

-- | Code generating evaluator : pretty-print the generated source code
--
-- > pprCode exS1
-- (GHC.Num.+) 1 2
pprCode :: Code a -> IO ()
pprCode c = do
  q <- unType <$> runQ (getCode c)
  putStrLn $ pprint q


-- an example expression
exS1 :: Sym repr => repr Int
exS1 = (addS `appS` constS 1) `appS` constS 2


-- * Optimization of tagless DSLs 

-- | Reflection-reification pair
--
-- instances of this, at various specialized types 't', will let us perform specific optimizations on our DSL terms, i.e. without requiring "tagged" pattern matching.
--
-- see tutorial : https://okmij.org/ftp/tagless-final/course/optimizations.html#circuit-tut
--
-- some code bits taken from :
-- 
-- https://okmij.org/ftp/tagless-final/course/RR.hs
-- https://okmij.org/ftp/tagless-final/course/B2Neg.hs
class RR t repr where
  -- | forward
  fwd :: repr a -> t repr a
  -- | backwards
  bwd :: t repr a -> repr a
  -- | map unary
  map1 :: (repr a -> repr b) -> t repr a -> t repr b
  map1 f = fwd . f . bwd
  -- | map binary
  map2 :: (repr a -> repr b -> repr c) -> t repr a -> t repr b -> t repr c
  map2 f x y = fwd $ f (bwd x) (bwd y)

-- A context for boolean values
data Ctx = Pos | Neg

-- An interpretation for a specific simplification : pushing negation to terms
data PushNeg repr a = PN (Ctx -> repr a)

-- * Tagless transformer
-- We transform one interpreter into another :

-- instance Symantics repr => Symantics (PushNeg repr) where
--     lit x = PN $ \ctx -> case ctx of
--                    Pos -> lit x
--                    Neg -> lit (not x)
--     neg (PN e) = PN $ \case
--       Pos -> e Neg
--       Neg -> e Pos
    -- and (PN e1) (PN e2) = PN $ \case
    --   Pos -> and (e1 Pos) (e2 Pos) -- homomorhism
    --   Neg -> or  (e1 Neg) (e2 Neg) -- de Morgan law
    -- or  (PN e1) (PN e2) = PN $ \case
    --   Pos -> or  (e1 Pos) (e2 Pos) -- homomorhism
    --   Neg -> and (e1 Neg) (e2 Neg) -- de Morgan law



-- | ======================================

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
