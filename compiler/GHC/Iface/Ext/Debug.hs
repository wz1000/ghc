{-
Functions to validate and check .hie file ASTs generated by GHC.
-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module GHC.Iface.Ext.Debug where

import GhcPrelude

import GHC.Types.SrcLoc
import GHC.Types.Module
import FastString
import Outputable

import GHC.Iface.Ext.Types
import GHC.Iface.Ext.Binary
import GHC.Iface.Ext.Utils
import GHC.Types.Name

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Function    ( on )
import Data.List        ( sortOn )

type Diff a = a -> a -> [SDoc]

diffFile :: Diff HieFile
diffFile = diffAsts eqDiff `on` (getAsts . hie_asts)

diffAsts :: (Outputable a, Eq a, Ord a) => Diff a -> Diff (M.Map FastString (HieAST a))
diffAsts f = diffList (diffAst f) `on` M.elems

diffAst :: (Outputable a, Eq a,Ord a) => Diff a -> Diff (HieAST a)
diffAst diffType (Node info1 span1 xs1) (Node info2 span2 xs2) =
    infoDiff ++ spanDiff ++ diffList (diffAst diffType) xs1 xs2
  where
    spanDiff
      | span1 /= span2 = [hsep ["Spans", ppr span1, "and", ppr span2, "differ"]]
      | otherwise = []
    infoDiff'
      = (diffList eqDiff `on` (S.toAscList . nodeAnnotations)) info1 info2
     ++ (diffList diffType `on` nodeType) info1 info2
     ++ (diffIdents `on` nodeIdentifiers) info1 info2
    infoDiff = case infoDiff' of
      [] -> []
      xs -> xs ++ [vcat ["In Node:",ppr (nodeIdentifiers info1,span1)
                           , "and", ppr (nodeIdentifiers info2,span2)
                        , "While comparing"
                        , ppr (normalizeIdents $ nodeIdentifiers info1), "and"
                        , ppr (normalizeIdents $ nodeIdentifiers info2)
                        ]
                  ]

    diffIdents a b = (diffList diffIdent `on` normalizeIdents) a b
    diffIdent (a,b) (c,d) = diffName a c
                         ++ eqDiff b d
    diffName (Right a) (Right b) = case (a,b) of
      (ExternalName m o _, ExternalName m' o' _) -> eqDiff (m,o) (m',o')
      (LocalName o _, ExternalName _ o' _) -> eqDiff o o'
      _ -> eqDiff a b
    diffName a b = eqDiff a b

type DiffIdent = Either ModuleName HieName

normalizeIdents :: Ord a => NodeIdentifiers a -> [(DiffIdent,IdentifierDetails a)]
normalizeIdents = sortOn go . map (first toHieName) . M.toList
  where
    first f (a,b) = (fmap f a, b)
    go (a,b) = (hieNameOcc <$> a,identInfo b,identType b)

diffList :: Diff a -> Diff [a]
diffList f xs ys
  | length xs == length ys = concat $ zipWith f xs ys
  | otherwise = ["length of lists doesn't match"]

eqDiff :: (Outputable a, Eq a) => Diff a
eqDiff a b
  | a == b = []
  | otherwise = [hsep [ppr a, "and", ppr b, "do not match"]]

validAst :: HieAST a -> Either SDoc ()
validAst (Node _ span children) = do
  checkContainment children
  checkSorted children
  mapM_ validAst children
  where
    checkSorted [] = return ()
    checkSorted [_] = return ()
    checkSorted (x:y:xs)
      | nodeSpan x `leftOf` nodeSpan y = checkSorted (y:xs)
      | otherwise = Left $ hsep
          [ ppr $ nodeSpan x
          , "is not to the left of"
          , ppr $ nodeSpan y
          ]
    checkContainment [] = return ()
    checkContainment (x:xs)
      | span `containsSpan` (nodeSpan x) = checkContainment xs
      | otherwise = Left $ hsep
          [ ppr $ span
          , "does not contain"
          , ppr $ nodeSpan x
          ]

-- | Look for any identifiers which occur outside of their supposed scopes.
-- Returns a list of error messages.
validateScopes :: Module -> M.Map FastString (HieAST a) -> [SDoc]
validateScopes mod asts = validScopes
  where
    refMap = generateReferencesMap asts
    -- We use a refmap for most of the computation

    -- Check if all the names occur in their calculated scopes
    validScopes = M.foldrWithKey (\k a b -> valid k a ++ b) [] refMap
    valid (Left _) _ = []
    valid (Right n) refs = concatMap inScope refs
      where
        mapRef = foldMap getScopeFromContext . identInfo . snd
        scopes = case foldMap mapRef refs of
          Just xs -> xs
          Nothing -> []
        inScope (sp, dets)
          |  (definedInAsts asts n)
          && any isOccurrence (identInfo dets)
          -- We validate scopes for names which are defined locally, and occur
          -- in this span
            = case scopes of
              [] | (nameIsLocalOrFrom mod n
                   && not (isDerivedOccName $ nameOccName n))
                   -- If we don't get any scopes for a local name then its an error.
                   -- We can ignore derived names.
                   -> return $ hsep $
                     [ "Locally defined Name", ppr n,pprDefinedAt n , "at position", ppr sp
                     , "Doesn't have a calculated scope: ", ppr scopes]
                 | otherwise -> []
              _ -> if any (`scopeContainsSpan` sp) scopes
                   then []
                   else return $ hsep $
                     [ "Name", ppr n, pprDefinedAt n, "at position", ppr sp
                     , "doesn't occur in calculated scope", ppr scopes]
          | otherwise = []
