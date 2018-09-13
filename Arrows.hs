{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
 -- Code for Bartosz Milewski - Arrows are strong profunctors
--  https://www.youtube.com/watch?v=hrNfkP8iKAs
module Arrows where

import           Control.Monad                  ( (>=>) )
import qualified GHC.Base                       ( (.)
                                                , id
                                                )
import qualified Prelude                       as P
                                                ( IO
                                                , Int
                                                , Monad(..)
                                                , undefined
                                                )

main :: P.IO ()
main = P.undefined

class Category cat where
  id :: a `cat` a
  (.) :: cat b c -> cat a b -> cat a c

instance Category (->) where
  id = GHC.Base.id
  (.) = (GHC.Base..)

class Monoid m where
  mu :: (m, m) -> m
  eta :: () -> m

newtype IntFun =
  IF (P.Int -> P.Int)

instance Monoid IntFun where
  mu (IF f, IF g) = IF (g . f)
  eta () = IF id

class Functor (f :: * -> *) where
  fmap :: (a -> a') -> (f a -> f a')

class Bifunctor (bf :: * -> * -> *) where
  bimap :: (a -> a') -> (b -> b') -> bf a b -> bf a' b'

class Profunctor (p :: * -> * -> *) where
  dimap :: (a' -> a) -> (b -> b') -> p a b -> p a' b'

instance Profunctor (->) where
  dimap con pro f = pro . f . con

type End p = forall x. p x x

newtype NatPro f g a b =
  NatPro (f a -> g b)

instance (Functor f, Functor g) => Profunctor (NatPro f g) where
  dimap ba cd (NatPro p) = NatPro (fmap cd . p . fmap ba)

type Nat f g = End (NatPro f g)

type Nat' f g = forall x. f x -> g x

data Coend p =
  forall x. Coend (p x x)

data Compose p q a b =
  forall x. Compose (p a x)
                    (q x b)

instance (Profunctor p, Profunctor q) => Profunctor (Compose p q) where
  dimap con pro (Compose pax qxb) =
    Compose (dimap con id pax) (dimap id pro qxb)

data TensorProduct p q a b x y =
  TensorProduct (p a y)
                (q x b)

instance (Profunctor p, Profunctor q) =>
         Profunctor (TensorProduct p q a b) where
  dimap con pro (TensorProduct pay qxb) =
    TensorProduct (dimap id pro pay) (dimap con id qxb)

--data Compose p q a b = Coend (TensorProduct p q a b)
-- Yoneda Lemma
newtype PreYoneda f a x y =
  PreYoneda ((a -> x) -> f y)

instance Functor f => Profunctor (PreYoneda f a) where
  dimap con pro (PreYoneda ax_fy) =
    PreYoneda (\ax' -> fmap pro (ax_fy (con . ax')))

-- End (PreYoneda f a) ~ forall x. PreYoneda f a x x
newtype Yoneda f a =
  Yoneda (forall x. (a -> x) -> f x)

-- Yoneda f a ~ f a
toY :: Functor f => Yoneda f a -> f a
toY (Yoneda axfx) = axfx id

fromY :: Functor f => f a -> Yoneda f a
fromY fa = Yoneda (`fmap` fa) -- (\ax -> fmap ax fa)

-- type CoYoneda f a = exists x. (x -> a, f x)
data CoYoneda f a =
  forall x. CoYoneda (x -> a)
                     (f x)

toCY :: Functor f => CoYoneda f a -> f a
toCY (CoYoneda xa fx) = fmap xa fx

fromCY :: Functor f => f a -> CoYoneda f a
--fromCY fa = CoYoneda id fa
fromCY = CoYoneda id

--mu :: Compose p pa b -> p a b
(>>>) :: p a x -> p x b -> p a b
(>>>) = P.undefined

--class Profunctor p => Strong p where
--  first :: p a b -> p (a, x) (b, x)
class Category ar =>
      Arrow ar
  where
  arr :: (a -> b) -> ar a b
  first :: ar a b -> ar (a, c) (b, c)

data Kleisli m a b =
  Kl (a -> m b)

instance P.Monad m => Arrow (Kleisli m) where
  arr f = Kl (P.return . f)
  first (Kl f) =
    Kl
      (\(x, c) -> do
         y <- f x
         P.return (y, c))

instance P.Monad m => Category (Kleisli m) where
  id = arr id
  (Kl f) . (Kl g) = Kl (g >=> f)
