module Test.HAPI.Util.TH where

import qualified Language.Haskell.TH.Syntax
import Text.Printf (printf)

moduleOf :: Language.Haskell.TH.Syntax.Name -> String
moduleOf = reverse . tail . dropWhile (/= '.') . reverse . show

data FatalErrorKind = FATAL_ERROR | HAPI_BUG
  deriving (Eq, Ord, Show, Enum)

fatalError :: Language.Haskell.TH.Syntax.Name -> FatalErrorKind -> String -> a
fatalError name kind cause = error
   $ "[FATAL ERROR]:\n"
  <> cause <> "\n"
  <> "In: " <> show name <> "\n\n"
  <> if kind == HAPI_BUG
      then "This is a BUG in HAPI. Please contact the maintainer."
      else "HAPI terminates with a fatal error. "
