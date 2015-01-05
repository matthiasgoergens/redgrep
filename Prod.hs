{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}

import Red hiding (main)
import Control.Applicative

data ProductF f g (b :: * -> *) a =
      ProductF (f b a) (g b a) deriving Show

instance (Functor (f b), Functor (g b)) =>
         Functor (ProductF f g b) where
                fmap f (ProductF x y) = ProductF (fmap f x) (fmap f y)
 
instance (Applicative (f b), Applicative (g b)) =>
         Applicative (ProductF f g b) where
               pure x = ProductF (pure x) (pure x)
               (ProductF f g) <*> (ProductF x y) = ProductF (f <*> x) (g <*> y)


main = return ()
