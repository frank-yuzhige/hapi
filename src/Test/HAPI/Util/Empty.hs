module Test.HAPI.Util.Empty where
import Control.Algebra (Has)
import Control.Effect.Empty (Empty, empty)

liftMaybe :: (Has Empty sig m) => Maybe a -> m a
liftMaybe = maybe empty return
