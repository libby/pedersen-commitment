
module MICP where

import Protolude
import qualified Prelude (until, unzip)

import Crypto.Hash
import Crypto.Random.Types (MonadRandom(..))

import qualified Data.ByteArray as BA
import qualified Data.Map as Map
import Data.Maybe (fromJust)

import Pedersen
import PrimeField

-------------------------------------------------------------------------------
-- Blum Micali PRNG
-------------------------------------------------------------------------------

data Bit = Zero | One
  deriving (Eq, Ord, Enum, Show)

bitsToInteger :: [Bit] -> Integer
bitsToInteger = snd . foldr (\b (n,sum) -> (n+1, bitToInt n b + sum)) (0,0)
  where
    bitToInt :: Integer -> Bit -> Integer
    bitToInt n bit
      | n < 0 = 0
      | otherwise = 2^n * toInteger (fromEnum bit)

data PRNGState = PRNGState
  { i    :: Int
  , bits :: [Bit]
  , seed :: Integer
  }

initPRNGState :: Integer -> PRNGState
initPRNGState = PRNGState 0 []

genPRNGSeed :: MonadRandom m => SPFM m Integer
genPRNGSeed = gexpSafeSPFM =<< randomInZpM

-- | Generates a hardcore bit sequence using the result from the paper:
-- "How to generate cryptographically strong sequences of pseudo random bits"
-- - M. Blum and S. Micali, 1984
--
-- resource:  https://crypto.stanford.edu/pbc/notes/crypto/blummicali.html
blumMicaliPRNG
  :: MonadRandom m
  => Int       -- ^ Number of bits to generate
  -> Integer   -- ^ Initial seed (must be in Zp)
  -> SPF       -- ^ Safe prime field to compute within
  -> m Integer -- ^ (256bit seed, Nbit result)
blumMicaliPRNG nbits seed spf = do
    let randNBits = bits $ nStepsPRNG nbits $ initPRNGState seed
    return $ bitsToInteger randNBits
  where
    nStepsPRNG :: Int -> PRNGState -> PRNGState
    nStepsPRNG n = Prelude.until (\bm -> i bm == n) blumMicaliStep

    blumMicaliStep :: PRNGState -> PRNGState
    blumMicaliStep (PRNGState i prevBits prevSeed) =
        PRNGState { i    = i + 1
                  , bits = newBit : prevBits
                  , seed = newSeed
                  }
      where
        newSeed = blumMicaliF spf prevSeed

        newBit
          | blumMicaliH (unP $ spfP spf) newSeed = One
          | otherwise = Zero

-- | Strong one way function, discrete log problem:
--     f(x) = g^x mod p in some prime field Zp
blumMicaliF :: SPF -> Integer -> Integer
blumMicaliF = gexpSafeSPF

-- | Hardcore predicate H (Blum-Micali):
--     given p from LocalParams:
--       let H(x) = if x < (p - 1)/2 then 1 else 0
--   resource: https://crypto.stanford.edu/pbc/notes/crypto/hardcore.html
blumMicaliH :: Integer -> Integer -> Bool
blumMicaliH p r = r < (p - 1) `div` 2

-------------------------------------------------------------------------------
-- Mutually Independent Commitments Protocol (MICP)
-------------------------------------------------------------------------------

data MICParams = MICParams
  { secParam    :: Int     -- ^ Security parameter, # bits of large prime
  , secretBytes :: [Word8] -- ^ Secret to commit to, as bytes
  , micpSPF     :: SPF     -- ^ Safe Prime field (shared)
  }

mkMICParams :: Int -> ByteString -> SPF -> MICParams
mkMICParams k secret spf =
  MICParams { secParam    = k
            , secretBytes = BA.unpack secret
            , micpSPF     = spf
            }

-- | Force random nums to be generated with (p,g) from shared env
-- and returns a single byte (8 random bits) as output
micpBlumMicaliPRNG :: MonadRandom m => Integer -> SPFM m Word8
micpBlumMicaliPRNG seed = fromIntegral <$> (lift . blumMicaliPRNG 8 seed =<< ask)

-- | Force random seed to be generated with (p,g) from shared env
micpBlumMicaliSeed :: MonadRandom m => SPFM m Integer
micpBlumMicaliSeed = genPRNGSeed

-------------------------------------------------------------------------------
-- Generate (k,k') pairs such that H(k) XOR H(k') == secret:
-------------------------------------------------------------------------------

type KMap = Map Int Integer
type K'Map = Map Int Integer

type GtoKMap = Map Int Integer
type GtoK'Map = Map Int Integer

-- | 2(b), 3(a):
genKMaps :: MonadRandom m => [Word8] -> SPFM m (KMap,K'Map)
genKMaps bytes = do
  (ks,k's) <- Prelude.unzip <$> mapM genKPair bytes
  let kmap = Map.fromList $ zip [0..] ks
  let k'map = Map.fromList $ zip [0..] k's
  return (kmap,k'map)

genKPair
  :: MonadRandom m
  => Word8                     -- ^ Byte to find k and k' for
  -> SPFM m (Integer,Integer) -- ^ (k,k')
genKPair byte = do
    k  <- micpBlumMicaliSeed
    hk <- micpBlumMicaliPRNG k
    k' <- findK' hk
    return (k,k')
  where
    checkHKPair :: Bits a => a -> (a,a) -> Bool
    checkHKPair byte (hk,hk') = byte == (hk `xor` hk')

    findK' :: MonadRandom m => Word8 -> SPFM m Integer
    findK' hk = do
      k'  <- micpBlumMicaliSeed
      hk' <- micpBlumMicaliPRNG k'
      if checkHKPair byte (hk,hk') then
        return k'
      else findK' hk

kpairToByte :: MonadRandom m => (Integer,Integer) -> SPFM m Word8
kpairToByte (k,k') = do
  hk <- micpBlumMicaliPRNG k
  hk' <- micpBlumMicaliPRNG k'
  return $ hk `xor` hk'

kmapToGKMap :: Monad m => Map Int Integer -> SPFM m (Map Int Integer)
kmapToGKMap kmap = do
  let (keys,vals) = Prelude.unzip $ Map.toList kmap
  newVals <- mapM gexpSafeSPFM vals
  return $ Map.fromList $ zip keys newVals

-------------------------------------------------------------------------------

-- | 2(c), 3(b): Generate random r in Zq and commit using Pedersen Commitment
genAndCommitR
  :: MonadRandom m
  => CommitParams
  -> SPFM m (Integer, Pedersen)
genAndCommitR cparams = do
  r <- randomInZqM
  gr <- gexpSafeSPFM r
  c <- lift $ commit gr cparams
  return (r,c)

-- | 3(c), 4(a): Generate random c in Zq
genC :: MonadRandom m => SPFM m Integer
genC = randomInZqM

-------------------------------------------------------------------------------

type DMap = Map Int Integer

-- | 4(c),5(c): computes di = c*ki + r
computeDMap
  :: Integer      -- ^ Counterparty's 'c'
  -> KMap         -- ^ Current party's KMap
  -> Integer      -- ^ Current party's 'r'
  -> DMap
computeDMap c kmap r = map computeD kmap
  where
    -- This function does not use modular arithmetic because the
    -- exponent laws would not hold otherwise, and this is needed for
    -- verification later in the protocol. For example:
    --   let p = 13
    --   ((x^7)^8 * (x^9) % p) /= (x^((7 * 8 + 9) % p)) % p
    computeD ki = c * ki + r

verifyDMap
  :: Monad m
  => DMap              -- ^ Counterparty's DMap
  -> GtoKMap           -- ^ Counterparty's (g^k, g^k') map
  -> Integer           -- ^ Current party's 'c'
  -> Integer           -- ^ Counterparty's 'g^r'
  -> SPFM m Bool
verifyDMap dmap gkmap c gr =
    and <$> zipWithM (verifyDi c gr) ds gks
  where
    ds = Map.elems dmap
    gks = Map.elems gkmap

-- | Verifies the ith 'd' value for the ith byte of the secret
verifyDi
  :: Monad m
  => Integer     -- ^ Current party's 'c'
  -> Integer     -- ^ Counterparty's 'g^r'
  -> Integer     -- ^ Counterparty's 'di'
  -> Integer     -- ^ Counterparty's 'g^ki'
  -> SPFM m Bool
verifyDi c gr di gki = do
  gdi <- gexpSafeSPFM di
  let gkiToC = expSafeSPFM gki c
  gdi' <- gkiToC |*| pure gr
  return $ gdi == gdi'

-------------------------------------------------------------------------------
-- Reveal Stage
-------------------------------------------------------------------------------

micpReveal :: MonadRandom m => KMap -> K'Map -> SPFM m ByteString
micpReveal kmap k'map =
    BA.pack <$> zipWithM (curry kpairToByte) ks k's
  where
    ks = Map.elems kmap
    k's = Map.elems k'map

-------------------------------------------------------------------------------
-- Testing
-------------------------------------------------------------------------------

sha256 :: ByteString -> ByteString
sha256 bs = BA.convert (hash bs :: Digest SHA3_256)

testBlumMicaliPRNG :: IO Integer
testBlumMicaliPRNG = do
  let k = 256
  (a,cparams) <- setup k
  runSPFT (pedersenSPF cparams) $ do
    seed <- genPRNGSeed
    lift . blumMicaliPRNG k seed =<< ask

-- | In this test, all values computed are in scope for both Alice & Bob,
-- so instead of "sending" those values to one another, we can just use them
-- for the respective counterparty computations.
testMICP :: Int -> IO Bool
testMICP secParam = do
  let aliceMsg = sha256 "123456789"
  let aliceMsgBytes = BA.unpack aliceMsg
  let bobMsg   = sha256 "987654321"
  let bobMsgBytes = BA.unpack bobMsg

  putText "Creating envs..."

  sharedSPF <- mkSPF secParam
  let aliceParams = mkMICParams secParam aliceMsg sharedSPF
  let bobParams = mkMICParams secParam bobMsg sharedSPF

  -- 1, 2(a): send pedersen bases to each other
  (aliceA, aCommitParams) <- setup secParam
  (bobA, bCommitParams) <- setup secParam

  -- All further computation takes places in SPF
  runSPFT sharedSPF $ do

    -- 2(b): Send bobGKMap to alice
    putText "Gen bob kmap"
    (bobKMap,bobK'Map) <- genKMaps bobMsgBytes
    bobGtoKMap <- kmapToGKMap bobKMap
    bobGtoK'Map <- kmapToGKMap bobK'Map

    -- 2(c): Send bobCommit to alice using alice params
    putText "Gen bob r"
    (bobR, bobPedersen) <- genAndCommitR aCommitParams

    -- 3(a): Send aliceGKMap to bob
    putText "Gen alice kmap"
    (aliceKMap, aliceK'Map) <- genKMaps aliceMsgBytes
    aliceGtoKMap <- kmapToGKMap aliceKMap
    aliceGtoK'Map <- kmapToGKMap aliceK'Map

    -- 3(b): Send aliceCommit to bob
    putText "Gen alice r"
    (aliceR, alicePedersen) <- genAndCommitR bCommitParams

    -- 3(c): Send aliceC to bob
    putText "Gen alice c"
    aliceC <- genC

    -- 4(a): Send bobC to alice
    putText "Gen bob c"
    bobC <- genC

    -- 4(b): Send bobReveal to alice

    -- 4(c): Send bobDMap to alice
    putText "Compute bob dmap"
    let bobDMap = computeDMap aliceC bobKMap bobR

    -- 5(a): alice checks bob's commit
    unless (decommit aCommitParams bobPedersen) $
      panic "Bob's commit is illegitimate!"
    --       alice verifies g^di = (g^ki)^c + g^r
    bobDMapVerified <- verifyDMap bobDMap bobGtoKMap aliceC $ rVal $ reveal bobPedersen
    unless bobDMapVerified $
      panic "Bob's computations are wrong!"

    -- 5(b): Send aliceReveal to bob

    -- 5(c): Send aliceDMap to bob
    putText "Compute alice dmap"
    let aliceDMap = computeDMap bobC aliceKMap aliceR

    -- 5(d): send alice's 'a' to bob

    -- 6(a): bob checks alice's commit
    unless (decommit bCommitParams alicePedersen) $
      panic "Alice's commit is illegitimate!"
    --       bob verifies g^di = (g^ki)^c + g^r
    aliceDMapVerified <- verifyDMap aliceDMap aliceGtoKMap bobC $ rVal $ reveal alicePedersen
    unless aliceDMapVerified $
      panic "Alice's computations are wrong!"

    -- 6(b): bob checks that alice's ga^a == ha
    unless (validateCommitParams aliceA aCommitParams) $
      panic "Alice's pedersen bases are not valid!"

    -- 6(c): bob sends k'map and bob's 'a' to alice

    -- 7(a): alice checks that bob's ga^a == ha
    unless (validateCommitParams bobA bCommitParams) $
      panic "Bob's pedersen bases are not valid!"

    -- 7(b): alice checks k'map from bob matches gk'map received earlier
    bobGtoK'MapCheck <- kmapToGKMap bobK'Map
    unless (bobGtoK'MapCheck == bobGtoK'Map) $
      panic "Bob's k' and gk' maps are invalid!"

    -- 7(c): alice sends k'map to bob

    -- 8(a): bob checks k'map from alice matches gk'map recieved earlier
    aliceGtoK'MapCheck <- kmapToGKMap aliceK'Map
    unless (aliceGtoK'MapCheck == aliceGtoK'Map) $
      panic "Alice's k' and gk' maps are invalid!"

    -- REVEAL STAGE:
    -- Alice & Bob reveal kMaps (map of k only, no k')

    -- Using bob/alice env respectively to show this reveal can happen within the
    -- shared env only, and doesn't care about local pedersen params
    aliceMsgRes <- micpReveal aliceKMap aliceK'Map
    let aliceResEqMsg = aliceMsgRes == aliceMsg
    bobMsgRes <- micpReveal bobKMap bobK'Map
    let bobResEqMsg = bobMsgRes == bobMsg

    return $ aliceResEqMsg && bobResEqMsg
