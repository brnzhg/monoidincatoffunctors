#!/usr/bin/env stack
-- stack --resolver lts-14.12 script

-- {-# LANGUAGE DataKinds                      #-}
{-# LANGUAGE GADTs                          #-}
-- {-# LANGUAGE KindSignatures                 #-}
{-# LANGUAGE LambdaCase                     #-}
-- {-# LANGUAGE MultiParamTypeClasses          #-}
{-# LANGUAGE RankNTypes                     #-}
{-# LANGUAGE ScopedTypeVariables            #-}
-- {-# LANGUAGE StandaloneDeriving             #-}
{-# LANGUAGE TypeFamilies                   #-}
{-# LANGUAGE TypeInType                     #-}
{-# LANGUAGE TypeOperators                  #-}
{-# LANGUAGE FlexibleContexts               #-}
{-# LANGUAGE FlexibleInstances              #-}
{-# LANGUAGE ExistentialQuantification      #-}
{-# LANGUAGE UndecidableInstances           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving     #-}

import Control.Applicative
import Control.Monad
import Data.Functor.Identity
--import Data.Functor.Compose
import Data.Proxy

type (~>) (f :: k -> *) (g :: k -> *) = forall (x :: k). f x -> g x

data Day f g a where
  Day :: ((a, b) -> c) -> f a -> g b -> Day f g c

{-
instance (Functor f, Functor g) => Functor (Day f g) where
  fmap y (Day z f g) = Day (y . z) f g
-}

--bifunctor (C, C) -> C, where C is the Endofunctor category
class FCBiFunctor b where
  --b is a functor when f and g are, so must have fmap
  functorMulMap :: (Functor f, Functor g) => (a -> a') -> (b f g a -> b f g a')
  functorMulNat :: (Functor f, Functor f', Functor g, Functor g') 
    => (f ~> f') -> (g ~> g') -> (b f g ~> b f' g')

instance (Functor f, Functor g, FCBiFunctor b) => Functor (b f g) where
  fmap = functorMulMap

class (FCBiFunctor b, Functor (FCId b)) => FCMonoidalProd b where
  --identity functor
  type FCId b :: * -> *
  --left identity
  fcLamb :: Functor f => b (FCId b) f ~> f
  --right identity
  fcRho :: Functor f => b f (FCId b) ~> f
  --associativity
  fcAlpha :: (Functor f, Functor g, Functor h) => b f (b g h) ~> b (b f g) h


class (Functor m, FCMonoidalProd (FCProd m)) => FCMonoid m where
  type FCProd m :: (* -> *) -> (* -> *) -> * -> *
  --return / id-like op
  fcUnit :: FCId (FCProd m) ~> m
  --join / mappend-like op
  fcMu :: FCProd m m m ~> m

--laws 
unitorDiagramLeft :: forall m a. FCMonoid m => FCProd m (FCId (FCProd m)) m a 
  -> (m a -> m a -> Bool)
  -> Bool
unitorDiagramLeft p eq = eq lambPath etamuPath
  where
    lambPath :: m a
    lambPath = fcLamb p
    etamuPath :: m a
    etamuPath = fcMu $ functorMulNat fcUnit id p

pentagonDiagram :: forall m a. (FCMonoid m) => FCProd m m (FCProd m m m) a
  -> (m a -> m a -> Bool)
  -> Bool
pentagonDiagram p eq = eq clockwisePath counterPath
  where
    clockwisePath :: m a
    clockwisePath = fcMu . functorMulNat fcMu id $ fcAlpha p
    counterPath :: m a
    counterPath = fcMu $ functorMulNat id fcMu p


-- Monads
newtype MonadW m a = MonadW { getM :: m a }
  deriving (Functor, Applicative, Monad)

newtype Compose f g a = Compose { getCompose :: f (g a) }

instance FCBiFunctor Compose where
  functorMulMap f (Compose { getCompose = c}) = 
    Compose { getCompose = fmap (fmap f) c }
  functorMulNat fnat gnat (Compose { getCompose = c }) =
    Compose { getCompose = fnat . fmap gnat $ c }

instance FCMonoidalProd Compose where
  type FCId Compose = Identity
  fcLamb = runIdentity . getCompose
  fcRho = fmap runIdentity . getCompose
  fcAlpha x = Compose { getCompose = Compose { getCompose = m3 } }
    where
      m3 = fmap getCompose . getCompose $ x

instance Monad m => FCMonoid (MonadW m) where
  type FCProd (MonadW m) = Compose
  fcUnit = return . runIdentity
  fcMu = join . getCompose


--Applicatives
newtype ApW m a = ApW { getAp :: m a }
  deriving (Functor, Applicative)

instance FCBiFunctor Day where
  functorMulMap y (Day z f g) = Day (y . z) f g
  functorMulNat fnat gnat (Day z f g) = Day z (fnat f) (gnat g)

instance FCMonoidalProd Day where
  type FCId Day = Identity
  fcLamb (Day z i m) = (curry z) (runIdentity i) <$> m
  fcRho (Day z m i) = flip (curry z) (runIdentity i) <$> m
  fcAlpha (Day z1 m1 (Day z2 m2 m3)) =
    Day z1' (Day z2' m1 m2) m3
    where
      z1' (r, x3) = r x3
      z2' (x1, x2) = curry z1 x1 . curry z2 x2

instance Applicative m => FCMonoid (ApW m) where
  type FCProd (ApW m) = Day
  fcUnit = pure . runIdentity
  fcMu (Day z m1 m2) = liftA2 (curry z) m1 m2


main :: IO ()
main = putStrLn "yo"