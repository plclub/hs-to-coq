{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

-- | A minimalistic extensible product library using the 'Has' pattern.
--
-- This allows reusing a single @MonadState s m@ constraint with multiple
-- components.
module HsToCoq.Util.Has where

import Control.Monad.State
import Control.Lens

class Has s a where
  part :: Lens' s a

getPart :: (MonadState s m, Has s a) => m a
getPart = use part

putPart :: (MonadState s m, Has s a) => a -> m ()
putPart x = part .= x

modifyPart :: (MonadState s m, Has s a) => (a -> a) -> m ()
modifyPart f = part %= f

infixr 1 :*
data a :* b = a :* b

instance Has (a :* b) a where
  part f (a :* b) = (:* b) <$> f a

instance Has a a where
  part = id

instance {-# OVERLAPPABLE #-} Has b c => Has (a :* b) c where
  part f (a :* b) = (a :*) <$> part f b
