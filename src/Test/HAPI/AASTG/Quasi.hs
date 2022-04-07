{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Test.HAPI.AASTG.Quasi where

import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec
import Text.Megaparsec.Char
import Data.Void (Void)
import Data.Text (Text)
import Test.HAPI.AASTG.Core (Edge)
import Test.HAPI.Api (ApiDefinition)
import Data.SOP (NP)
import Test.HAPI.Effect.QVS (Attribute)


type Parser = Parsec Void Text
-- TODO: PARSER

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

class ParseAPICall (api :: ApiDefinition) where
  parseAPI :: Parser (api p a, NP Attribute p)

-- pAPICall :: Parser (Edge sig c)
-- pAPICall = do

