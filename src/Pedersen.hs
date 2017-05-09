{-|

The Pedersen commitment scheme has three operations:

- Setup
- Commit
- Open

-}
{-# LANGUAGE NoImplicitPrelude #-}

module Pedersen (
  -- ** Datatypes
  Pedersen(..),
  CommitParams(..),
  Commitment(..),
  Reveal(..),

  -- ** Commitment Actions
  setup,
  commit,
  open,

  -- ** Homomorphic addition
  homoAdd,
  verifyHomoAdd,

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

newtype Commitment = Commitment { unCommitment :: Integer }
  deriving (Eq)

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
open :: CommitParams -> Commitment -> Reveal -> Bool
open (CommitParams spf h) (Commitment c) (Reveal x r) =
    resCommit == c
  where
    resCommit = runSPFM spf $
      gexpSafeSPFM x |*| expSafeSPFM h r

-- | This addition should be recorded as the previous commits are unable
-- to be extracted from this new commitment. The only way to open this commiment
-- is to tell the committing party the two commitments that were added so that the
-- commitment can be validated and opening parameters can be created.
homoAdd :: CommitParams -> Commitment -> Commitment -> Commitment
homoAdd cp c1 c2 = Commitment $
  modp (pedersenSPF cp) $ unCommitment c1 * unCommitment c2

-- | This function validates a homomorphic addition of two commitments using the
-- original pedersen commits and reveals to compute the new commitment without
-- homomorphic addition.
verifyHomoAdd :: CommitParams -> Pedersen -> Pedersen -> Pedersen
verifyHomoAdd (CommitParams spf h) p1 p2 =
    Pedersen newCommitment $ Reveal newVal newExp
  where
    (Reveal x r)  = reveal p1
    (Reveal y r') = reveal p2

    newVal = modp spf $ x + y
    newExp = modp spf $ r + r'

    newCommitment = Commitment $ runSPFM spf $
      gexpSafeSPFM newVal |*| expSafeSPFM h newExp

-- | Check that `g^a = h` to verify integrity of a counterparty's commitment
verifyCommitParams :: Integer -> CommitParams -> Bool
verifyCommitParams a (CommitParams spf h) =
  runSPFM spf $ do
    h' <- gexpSafeSPFM a
    return $ h' == h

