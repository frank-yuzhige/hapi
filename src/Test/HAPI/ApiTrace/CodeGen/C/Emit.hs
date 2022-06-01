{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.HAPI.ApiTrace.CodeGen.C.Emit (
  emitCCode
) where
import Language.C
import Data.Text (Text)
import qualified Data.Text as T
import Text.Printf (printf)
import Data.String (fromString)
import Text.RawString.QQ
import Test.HAPI.Constraint (CMembers)
import Test.HAPI.ApiTrace.CodeGen.C.DataType (CCodeGen)
import Test.HAPI.ApiTrace.CodeGen.C.Data (Entry2BlockC, traceMain)
import Test.HAPI.ApiTrace.Core (ApiTrace)
import Test.HAPI.ApiTrace.CodeGen.C.Util (struct, ptr, charTy)


hapiRequiredIncludes :: [Text]
hapiRequiredIncludes =
  [ "stdlib"
  , "stdio"
  , "stdbool"
  , "string"
  ]

hapiHeadComment :: Text
hapiHeadComment = [r|
/***
 *     ___  ___      ________      ________      ___
 *    |\  \|\  \    |\   __  \    |\   __  \    |\  \
 *    \ \  \\\  \   \ \  \|\  \   \ \  \|\  \   \ \  \
 *     \ \   __  \   \ \   __  \   \ \   ____\   \ \  \
 *      \ \  \ \  \   \ \  \ \  \   \ \  \___|    \ \  \
 *       \ \__\ \__\   \ \__\ \__\   \ \__\        \ \__\
 *        \|__|\|__|    \|__|\|__|    \|__|         \|__|
 *
 *  This trace file was generated by HAPI - A library/API testing framework in Haskell
 *
 */
|]

hapiTypeDefs :: Text
hapiTypeDefs = T.unlines $ map (fromString . show . pretty)
  [ cbytes
  , cubytes
  ]
  where
    cbytes  = CDeclExt $ struct "CBytes" [("bytes", [CCharType undefNode], ptr), ("size", [CIntType undefNode], id)]
    cubytes = CDeclExt $ struct "CUBytes" [("bytes", [CUnsigType undefNode, CCharType undefNode], ptr), ("size", [CIntType undefNode], id)]

decl2CCode :: [Text] -> CExtDecl -> Text
decl2CCode headers cext = T.unlines
  [ hapiHeadComment
  , sysIncludeHeaders
  , apiIncludeHeaders
  , hapiTypeDefs
  , fromString $ show $ pretty cext
  ]
  where
    sysIncludeHeaders = T.unlines [ "#include <"  <> lib <> ".h>"  | lib <- hapiRequiredIncludes]
    apiIncludeHeaders = T.unlines [ "#include \"" <> lib <> ".h\"" | lib <- headers]

emitCCode :: forall c api.
           ( CMembers CCodeGen c
           , Entry2BlockC api)
        => [String]
        -> ApiTrace api c
        -> Text
emitCCode headers trace = decl2CCode (map T.pack headers) (traceMain trace)
