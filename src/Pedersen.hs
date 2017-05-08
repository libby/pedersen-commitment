{-|

The Pedersen commitment scheme has three operations:

- Setup
- Commit
- Open

-}
{-# LANGUAGE NoImplicitPrelude #-}

module Pedersen (
  Pedersen(..),
  CommitParams(..),
  Commitment(..),
  Reveal(..),

  -- ** Commitment Actions
  setup,
  commit,
  open,

  verifyCommitParams,
) where

import Protolude
import qualified Prelude

import Crypto.Hash
import Crypto.Number.Serialize (os2ip)
import Crypto.Random.Types (MonadRandom(..))

import Data.Bits (xor, popCount)
import qualified Data.ByteArray as BA
import qualified Data.Map as Map

import PrimeField

-------------------------------------------------------------------------------
-- Pedersen Commitment Scheme
-------------------------------------------------------------------------------

data CommitParams = CommitParams
  { pedersenSPF :: SPF     -- ^ Safe prime field for pedersen commitment
  , pedersenH   :: Integer -- ^ h = g^a mod p where a is random
  }

newtype Commitment = Commitment
  { unCommitment :: Integer }

data Reveal = Reveal
  { rVal :: Integer -- ^ Original value comitted
  , rExp :: Integer -- ^ random exponent r, g^x * h^r
  }

data Pedersen = Pedersen
  { commitment :: Commitment
  , reveal     :: Reveal
  }

-- | Generates a Safe Prime Field (p,q,g) and a random value
-- `a in Zq` such that `g^a = h`, where g and h are the bases
-- to be used in the pedersen commit function.
setup :: MonadRandom m => Int -> m (Integer, CommitParams)
setup nbits = do
  spf <- mkSPF nbits
  (a,h) <- runSPFT spf $ do
    a <- randomInZqM
    h <- gexpSafeSPFM a
    return (a,h)
  return (a, CommitParams spf h)

-- | Commit a value by generating a random number `r in Zq`
-- and computing `C(x) = g^x * h^r` where x is the value to commit
commit :: MonadRandom m => Integer -> CommitParams -> m Pedersen
commit x (CommitParams spf h) = do
  (r,c) <- runSPFT spf $ do
    r <- randomInZqM
    c <- gexpSafeSPFM x |*| expSafeSPFM h r
    return (r,c)
  return $ Pedersen (Commitment c) (Reveal x r)

-- | Open the commit by supplying the value commited, `x`, the
-- random value `r` and the pedersen bases `g` and `h`, and
-- verifying that `C(x) == g^x * h^r`
open :: CommitParams -> Pedersen -> Bool
open (CommitParams spf h) (Pedersen c (Reveal x r)) =
    resCommit == unCommitment c
  where
    resCommit = runSPFM spf $
      gexpSafeSPFM x |*| expSafeSPFM h r

-- | Check that `g^a = h` to verify integrity of a counterparty's commitment
verifyCommitParams :: Integer -> CommitParams -> Bool
verifyCommitParams a (CommitParams spf h) =
  runSPFM spf $ do
    h' <- gexpSafeSPFM a
    return $ h' == h

