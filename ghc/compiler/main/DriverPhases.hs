-----------------------------------------------------------------------------
-- $Id: DriverPhases.hs,v 1.7 2001/03/13 12:50:31 simonmar Exp $
--
-- GHC Driver
--
-- (c) Simon Marlow 2000
--
-----------------------------------------------------------------------------

module DriverPhases (
   Phase(..),
   startPhase,		-- :: String -> Phase
   phaseInputExt, 	-- :: Phase -> String

   haskellish_file, haskellish_suffix,
   objish_file, objish_suffix,
   cish_file, cish_suffix
 ) where

import DriverUtil

-----------------------------------------------------------------------------
-- Phases

{-
   Phase of the           | Suffix saying | Flag saying   | (suffix of)
   compilation system     | ``start here''| ``stop after''| output file
   
   literate pre-processor | .lhs          | -             | -
   C pre-processor (opt.) | -             | -E            | -
   Haskell compiler       | .hs           | -C, -S        | .hc, .s
   C compiler (opt.)      | .hc or .c     | -S            | .s
   assembler              | .s  or .S     | -c            | .o
   linker                 | other         | -             | a.out
-}

data Phase 
	= MkDependHS	-- haskell dependency generation
	| Unlit
	| Cpp
	| Hsc -- ToDo: HscTargetLang
	| Cc
	| HCc		-- Haskellised C (as opposed to vanilla C) compilation
	| Mangle	-- assembly mangling, now done by a separate script.
	| SplitMangle	-- after mangler if splitting
	| SplitAs
	| As
	| Ln 
  deriving (Eq, Show)

-- the first compilation phase for a given file is determined
-- by its suffix.
startPhase "lhs"   = Unlit
startPhase "hs"    = Cpp
startPhase "hspp"  = Hsc
startPhase "hc"    = HCc
startPhase "c"     = Cc
startPhase "raw_s" = Mangle
startPhase "s"     = As
startPhase "S"     = As
startPhase "o"     = Ln
startPhase _       = Ln	   -- all unknown file types

-- the output suffix for a given phase is uniquely determined by
-- the input requirements of the next phase.
phaseInputExt Unlit       = "lhs"
phaseInputExt Cpp         = "lpp"	-- intermediate only
phaseInputExt Hsc         = "hspp"
phaseInputExt HCc         = "hc"
phaseInputExt Cc          = "c"
phaseInputExt Mangle      = "raw_s"
phaseInputExt SplitMangle = "split_s"	-- not really generated
phaseInputExt As          = "s"
phaseInputExt SplitAs     = "split_s"   -- not really generated
phaseInputExt Ln          = "o"
phaseInputExt MkDependHS  = "dep"

haskellish_suffix = (`elem` [ "hs", "hspp", "lhs", "hc" ])
cish_suffix       = (`elem` [ "c", "s", "S" ])  -- maybe .cc et al.??

#if mingw32_TARGET_OS || cygwin32_TARGET_OS
objish_suffix     = (`elem` [ "o", "O", "obj", "OBJ" ])
#else
objish_suffix     = (`elem` [ "o" ])
#endif

haskellish_file f = haskellish_suffix suf where (_,suf) = splitFilename f
cish_file       f = cish_suffix       suf where (_,suf) = splitFilename f
objish_file     f = objish_suffix     suf where (_,suf) = splitFilename f
