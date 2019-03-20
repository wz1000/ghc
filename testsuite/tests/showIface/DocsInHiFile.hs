{-# LANGUAGE TypeFamilies #-}
{-| `elem`, 'print',
`Unknown',
'<>', ':=:', 'Bool'
-}
module DocsInHiFile
  ( -- * First section heading

    -- | A small chunk of documentation
    DocsInHiFile.elem

    -- $namedchunk
  , D(..)
  , add
    -- * Another section heading
  , P(..)
  , Show(..)
  ) where

-- $namedchunk
-- This chunk of documentation is named "namedchunk".

-- | '()', 'elem'.
elem :: ()
elem = ()

-- | A datatype.
data D
  = D0 -- ^ A constructor for 'D'. '
  | D1 -- ^ Another constructor
  deriving ( Show -- ^ 'Show' instance
           )

add :: Int -- ^ First summand for 'add'
    -> Int -- ^ Second summand
    -> Int -- ^ Sum
add a b = a + b

-- | A class
class P f where
  -- | A class method
  p :: a -- ^ An argument
    -> f a

-- | Another datatype...
data D'
-- ^ ...with two docstrings.

-- | A type family
type family F a
-- | A type family instance
type instance F Int = Bool
