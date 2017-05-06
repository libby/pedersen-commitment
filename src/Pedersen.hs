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

  validateCommitParams,
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

setup :: MonadRandom m => Int -> m (Integer, CommitParams)
setup nbits = do
  spf <- mkSPF nbits
  (a,h) <- runSPFT spf $ do
    a <- randomInZqM
    h <- gexpSafeSPFM a
    return (a,h)
  return (a, CommitParams spf h)

commit :: MonadRandom m => Integer -> CommitParams -> m Pedersen
commit x (CommitParams spf h) = do
  (r,c) <- runSPFT spf $ do
    r <- randomInZqM
    c <- gexpSafeSPFM x |*| expSafeSPFM h r
    return (r,c)
  return $ Pedersen (Commitment c) (Reveal x r)

open :: CommitParams -> Pedersen -> Bool
open (CommitParams spf h) (Pedersen c (Reveal x r)) =
    resCommit == unCommitment c
  where
    resCommit = runSPFM spf $
      gexpSafeSPFM x |*| expSafeSPFM h r

validateCommitParams :: Integer -> CommitParams -> Bool
validateCommitParams a (CommitParams spf h) =
  runSPFM spf $ do
    h' <- gexpSafeSPFM a
    return $ h' == h

sha256 :: ByteString -> ByteString
sha256 bs = BA.convert (hash bs :: Digest SHA3_256)
