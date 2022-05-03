{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE LambdaCase #-}

module Test.HAPI.AASTG.LLVM.Translate where

import Test.HAPI.AASTG.Core ( AASTG, NodeID, Edge (APICall, Redirect), IsValidCall )
import Test.HAPI.Effect.Eff ( Eff, (:+:), debug, Alg )
import Control.Effect.State (State, gets, get, put, modify, Has)
import Control.Effect.Reader (Reader, asks)
import LLVM.AST (Global(..), Named ((:=), Do), BasicBlock (BasicBlock), Instruction (..), Name (..), Type (..), Terminator (..), Operand (..))
import Test.HAPI.AASTG.Effect.Build (BuildAASTG, newEdge, newNode)
import Test.HAPI.PState ( PKey(PKey) )
import Data.Char (chr)
import Test.HAPI.Args (Attributes, Attribute (Get, Value))
import Test.HAPI.Common ( Fuzzable )
import Data.Either (fromRight)
import Test.HAPI.Util.TH (moduleOf, fatalError, FatalErrorKind (FATAL_ERROR))
import Text.Printf (printf)
import Test.HAPI.HLib.HLibPrelude (HLibPrelude)
import Test.HAPI.HLib.HLibPtr (HLibPtr)
import Test.HAPI.Api ( (:$$:), ApiMember (injApi), ApiMembers, injApis )
import Control.Lens ( makeLenses, view, over )
import Test.HAPI.DataType (BasicSpec)
import Data.Hashable (Hashable)

import qualified LLVM.AST as LLVM
import qualified LLVM.AST.Attribute as LLVM
import qualified LLVM.AST.Typed as LLVM
import qualified LLVM.AST.Global as LLVM

import qualified Data.ByteString.Short as SBS
import qualified Data.HashMap.Strict as HM
import qualified Test.HAPI.HLib.HLibPrelude as HLib
import Control.Monad (forM, forM_)
import qualified LLVM.AST.Constant as LLVMC
import Data.Int
import Data.Word (Word32)
import Control.Carrier.State.Church (runState)
import Control.Carrier.Reader (runReader)
import Control.Carrier.Lift (runM)
import Test.HAPI.AASTG.Effect.Build ( runBuildAASTG )
import Test.HAPI (NP(..))


type LLVMRequiredHLibs = HLibPrelude :$$: HLibPtr

newtype AttrParse api apis c a = AttrParse {
  runAttrParse :: forall sig m. Translator api apis c sig m => LLVM.Operand -> m (Attribute a)
}

data ApiParseCtx api apis c = forall p a. (Fuzzable a, IsValidCall c api p) => ApiParseCtx {
  getApi  :: api p a,
  getSpec :: NP (AttrParse api apis c) p
}

data TranslateConfig api apis c = TranslateConfig
  { translateCall :: LLVM.Operand -> Maybe (ApiParseCtx api apis c)
  }

data TranslateState = TranslateState {
  _block2NodeMap :: HM.HashMap LLVM.Name NodeID,
  _currNode      :: NodeID
}


type Translator api apis c sig m =
  ( Eff (Reader (TranslateConfig api apis c)
          :+: State TranslateState
          :+: BuildAASTG apis c
        ) sig m
  , ApiMembers api apis
  , ApiMembers (HLibPrelude :$$: HLibPtr) apis
  -- , BasicSpec c
  )

$(makeLenses ''TranslateState)

runLLVMTranslator :: forall api apis c sig m.
                  ( Alg sig m
                  , ApiMembers api apis
                  , ApiMembers (HLibPrelude :$$: HLibPtr) apis)
               => TranslateConfig api apis c
               -> LLVM.Global
               -> m (AASTG apis c)
runLLVMTranslator cfg llvm
  = runBuildAASTG @apis
  $ runReader cfg
  $ runState (\s a -> return a) (TranslateState HM.empty 0)
  $ fromGlobal @api @apis @c llvm

fromLLVM :: [LLVM.Definition] -> AASTG api c
fromLLVM = undefined

fromDef :: Translator api apis c sig m => LLVM.Definition -> m (AASTG api c)
fromDef = undefined

fromGlobal :: forall api apis c sig m. Translator api apis c sig m => LLVM.Global -> m ()
fromGlobal fn@Function {} = do
  ts <- get @TranslateState
  labels <- forM blocks $ \(BasicBlock b _ _) -> do
    i <- newNode @apis @c
    return (b, i)
  modify $ over block2NodeMap $ const (HM.fromList labels)
  forM_ blocks $ \block -> do
    fromBasicBlock @api @apis @c block
  put ts
  where
    blocks = LLVM.basicBlocks fn
fromGlobal _ = undefined


fromBasicBlock :: forall api apis c sig m. Translator api apis c sig m => LLVM.BasicBlock -> m ()
fromBasicBlock (BasicBlock name ins term) = do
  n <- blockNode name
  modify $ over currNode $ const n
  forM_ ins $ \instr -> fromInstruction @api @apis @c instr
  fromTerminator @api @apis @c term

fromInstruction :: forall api apis c sig m. Translator api apis c sig m
                => LLVM.Named LLVM.Instruction
                -> m ()
fromInstruction namedInstr = case namedInstr of
  x := c -> fromInstruction' c (Just x)
  Do   c -> fromInstruction' c Nothing
  where
    fromInstruction' instr mx = case instr of
      -- TODO: Handle instructions
      -- Add nuw nsw op1 op2 _ -> do
      --   j <- newNode @apis @c
      --   case LLVM.typeOf op1 of
      --     IntegerType b -> _
      --     VectorType v (IntegerType b) -> _
      --     _ -> fatalError 'fromInstruction FATAL_ERROR "Unknown type in LLVM instruction add"
      --   newEdge @apis @c (APICall @Int i j (name2Var <$> mx) (injApis (HLib.+)) undefined)
      --   return j
      Call { function, arguments } -> do
        i <- gets (view currNode)
        handler <- asks @(TranslateConfig api apis c) translateCall
        case function of
          Left  inlineAsm -> do
            debug $ printf "[WARNING] %s: HAPI does not support inline assembly call yet!" (show 'fromInstruction)
          Right callOperand ->
            case handler callOperand of
              Nothing                      -> return ()
              Just (ApiParseCtx api pargs) -> do
                args <- opsViaSpec pargs (map fst arguments)
                j <- newNode @apis @c
                newEdge @apis @c (APICall i j (name2Var <$> mx) (injApis api) args)
                modify $ over currNode $ const j
      _ -> do
        debug $ printf "[INFO] %s: Ignoring unsupported instruction"



fromTerminator :: forall api apis c sig m. Translator api apis c sig m
               => LLVM.Named LLVM.Terminator
               -> m ()
fromTerminator namedTerminator = case namedTerminator of
  x := c -> fromTerminator' c (Just x)
  Do   c -> fromTerminator' c Nothing
  where
    fromTerminator' term mx = do
      i <- gets (view currNode)
      case term of
        Br dest _ -> do
          j <- blockNode dest
          newEdge @apis @c (Redirect i j)
          modify $ over currNode $ const j
        Invoke { function', arguments' } -> do
          handler <- asks @(TranslateConfig api apis c) translateCall
          case function' of
            Left  inlineAsm -> do
              debug $ printf "[WARNING] %s: HAPI does not support inline assembly call yet!" (show 'fromInstruction)
            Right callOperand ->
              case handler callOperand of
                Nothing                      -> return ()
                Just (ApiParseCtx api pargs) -> do
                  args <- opsViaSpec pargs (map fst arguments')
                  j <- newNode @apis @c
                  newEdge @apis @c (APICall i j (name2Var <$> mx) (injApis api) args)
                  modify $ over currNode $ const j
        _ -> do
          return ()


-- Operand

opInteger :: forall api apis c sig m i.
          ( Translator api apis c sig m
          , Integral i
          , Fuzzable i)
       => Word32
       -> LLVM.Operand
       -> m (Attribute i)
opInteger bits = \case
  LocalReference ty x -> return $ Get @i (name2Var x)
  ConstantOperand con -> case con of
    LLVMC.Int b n | b == bits -> return $ Value (fromIntegral n)
    -- TODO: Support other operands
    _                         -> fatalError 'opInteger FATAL_ERROR "123"
  MetadataOperand meta -> fatalError 'opInteger FATAL_ERROR "123"


opI1 :: forall api apis c sig m. Translator api apis c sig m => AttrParse api apis c Int
opI1 = AttrParse $ opInteger @api @apis @c 1

opI8 :: forall api apis c sig m. Translator api apis c sig m => AttrParse api apis c Int
opI8 = AttrParse $ opInteger @api @apis @c 8

opI16 :: forall api apis c sig m. Translator api apis c sig m => AttrParse api apis c Int
opI16 = AttrParse $ opInteger @api @apis @c 16

opI32 :: forall api apis c sig m. Translator api apis c sig m => AttrParse api apis c Int
opI32 = AttrParse $ opInteger @api @apis @c 32

opI64 :: forall api apis c sig m. Translator api apis c sig m => AttrParse api apis c Int
opI64 = AttrParse $ opInteger @api @apis @c 64

-- Utils
name2Str :: LLVM.Name -> String
name2Str (Name   n) = map (chr . fromEnum) $ SBS.unpack n
name2Str (UnName w) = show w

name2Var :: LLVM.Name -> PKey k
name2Var = PKey . name2Str

blockNode :: Has (State TranslateState) sig m => LLVM.Name -> m NodeID
blockNode n = do
  mi <- gets (HM.lookup n . view block2NodeMap)
  case mi of
    Nothing -> fatalError 'blockNode FATAL_ERROR (printf "Unknown block name '%s'" (show n))
    Just  i -> return i

opsViaSpec :: forall api apis c sig m p. Translator api apis c sig m
           => NP (AttrParse api apis c) p
           -> [LLVM.Operand]
           -> m (Attributes p)
opsViaSpec Nil                 []       = return Nil
opsViaSpec (AttrParse p :* ps) (x : xs) = do
  a  <- p x
  as <- opsViaSpec ps xs
  return (a :* as)
opsViaSpec _ _ = fatalError 'opsViaSpec FATAL_ERROR
  "Provided operands parsing specification does not match the actual operand list in the call sequence!"

instance Hashable LLVM.Name
