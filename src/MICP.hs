{-|

Mutually Independent Commitments Protocol (MICP)

- 1, 2(a): send pedersen bases to each other
- 2(b): Send bobGK1Map to alice
- 2(c): Send bobCommit to alice using alice params
- 3(a): Send aliceGK1Map to bob
- 3(b): Send aliceCommit to bob
- 3(c): Send aliceC to bob
- 4(a): Send bobC to alice
- 4(b): Send bobReveal to alice
- 4(c): Send bobDMap to alice
- 5(a): alice checks bob's commit
- 5(b): Send aliceReveal to bob
- 5(c): Send aliceDMap to bob
- 5(d): send alice's 'a' to bob
- 6(a): bob checks alice's commit
- 6(b): bob checks that alice's ga^a == ha
- 6(c): bob sends k'map and bob's 'a' to alice
- 7(a): alice checks that bob's ga^a == ha
- 7(b): alice checks k'map from bob matches gk'map received earlier
- 8(a): bob checks k'map from alice matches gk'map recieved earlier
- Reveal: Alice & Bob reveal KMaps

-}
module MICP (
  MICParams,
  K1Map,
  DMap,
  GtoK1Map,
  genKMaps,
  kmapToGKMap,
  blumMicaliPRNG,
  genPRNGSeed,
  genAndCommitR,
  computeDMap,
  mkMICParams,
  genC,
  verifyDMap,
  micpReveal,
) where

import Protolude
import GHC.Base (until)
import Data.List (unzip)

import Crypto.Hash
import Crypto.Random.Types (MonadRandom(..))

import qualified Data.ByteArray as BA
import qualified Data.Map as Map
import Data.Maybe (fromJust)

import qualified Pedersen as P
import PrimeField as PF

-------------------------------------------------------------------------------
-- Blum Micali PRNG
-------------------------------------------------------------------------------

data Bit = Zero | One
  deriving (Eq, Ord, Enum, Show)

bitsToInteger :: [Bit] -> Integer
bitsToInteger = snd . foldr accum (0,0)
  where
    accum :: Bit -> (Int,Integer) -> (Int,Integer)
    accum b (n,total) = (n+1, total + bitToInt n b)

    bitToInt :: Int -> Bit -> Integer
    bitToInt n bit
      | n < 0 = 0
      | otherwise = 2^n * toInteger (fromEnum bit)

data PRNGState = PRNGState
  { i    :: Int
  , bits :: [Bit]
  , seed :: Integer
  }

initPRNGState :: Integer -> PRNGState
initPRNGState seed =
  PRNGState { i = 0
            , bits = []
            , seed = seed
            }

genPRNGSeed :: MonadRandom m => SPF -> m Integer
genPRNGSeed spf = liftM (gexpSafeSPF spf) $ randomInZp spf

-- | Generates a hardcore bit sequence using the result from the paper:
-- "How to generate cryptographically strong sequences of pseudo random bits"
-- - M. Blum and S. Micali, 1984
--
-- Reference: https://crypto.stanford.edu/pbc/notes/crypto/blummicali.html
blumMicaliPRNG
  :: MonadRandom m
  => Int       -- ^ Number of bits to generate
  -> Integer   -- ^ Initial seed (must be in Zp)
  -> SPF       -- ^ Safe prime field to compute within
  -> m Integer -- ^ n-bit, pseudo-random result
blumMicaliPRNG nbits seed spf = do
    let randNBits = bits $ nStepsPRNG nbits $ initPRNGState seed
    return $ bitsToInteger randNBits
  where
    nStepsPRNG :: Int -> PRNGState -> PRNGState
    nStepsPRNG n = until (\bm -> i bm == n) blumMicaliStep

    blumMicaliStep :: PRNGState -> PRNGState
    blumMicaliStep (PRNGState i prevBits prevSeed) =
        PRNGState { i    = i + 1
                  , bits = newBit : prevBits
                  , seed = newSeed
                  }
      where
        newSeed = blumMicaliF spf prevSeed

        newBit
          | blumMicaliH spf newSeed = One
          | otherwise = Zero

-- | Strong one way function, discrete log problem:
--     f(x) = g^x mod p in some prime field Zp
blumMicaliF :: SPF -> Integer -> Integer
blumMicaliF = gexpSafeSPF

-- | Hardcore predicate H (Blum-Micali):
--     given p from LocalParams:
--       let H(x) = if x < (p - 1)/2 then 1 else 0
--   resource: https://crypto.stanford.edu/pbc/notes/crypto/hardcore.html
blumMicaliH :: SPF -> Integer -> Bool
blumMicaliH spf r = r < (unP (spfP spf) - 1) `div` 2

-------------------------------------------------------------------------------
-- Mutually Independent Commitments Protocol (MICP)
-------------------------------------------------------------------------------

-- | Commitment parameters
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
micpBlumMicaliSeed = lift . genPRNGSeed =<< ask

-------------------------------------------------------------------------------
-- Generate (k,k') pairs such that H(k) XOR H(k') == secret:
-------------------------------------------------------------------------------

type K1Map = Map Int Integer
type K2Map = Map Int Integer

type GtoK1Map = Map Int Integer
type GtoK2Map = Map Int Integer

-- | 2(b), 3(a): Generate two integer maps where the ith entry in
-- each map corresponds to the ith k1 and k2 values respectively such that
-- `Hn(k1_i) xor Hn(k2_i) == byte_i`. Two maps are generated map because
-- the values k and k' are to be exposed at different stages of the protocol.
genKMaps :: MonadRandom m => [Word8] -> SPFM m (K1Map,K2Map)
genKMaps bytes = do
  (k1s,k2s) <- unzip <$> mapM genKPair bytes
  let k1Map = Map.fromList $ zip [0..] k1s
  let k2Map = Map.fromList $ zip [0..] k2s
  return (k1Map,k2Map)

-- | Generate a pair of values such that `Hn(k1) xor Hn(k2) = byte`
genKPair :: MonadRandom m => Word8 -> SPFM m (Integer,Integer)
genKPair byte = do
    k1  <- micpBlumMicaliSeed
    hk1 <- micpBlumMicaliPRNG k1
    k2  <- findK2 hk1
    return (k1,k2)
  where
    checkHKPair :: Bits a => a -> (a,a) -> Bool
    checkHKPair byte (hk1,hk2) = byte == (hk1 `xor` hk2)

    findK2 :: MonadRandom m => Word8 -> SPFM m Integer
    findK2 hk1 = do
      k2  <- micpBlumMicaliSeed
      hk2 <- micpBlumMicaliPRNG k2
      if checkHKPair byte (hk1,hk2) then
        return k2
      else findK2 hk1

-- | Takes a Map k v and returns Map k (g^v mod p)
kmapToGKMap :: Monad m => Map Int Integer -> SPFM m (Map Int Integer)
kmapToGKMap kmap = liftM (flip map kmap . gexpSafeSPF) ask

-------------------------------------------------------------------------------

-- | 2(c), 3(b): Generate random r in Z_q and commit using Pedersen Commitment
genAndCommitR
  :: MonadRandom m
  => P.CommitParams
  -> SPFM m (Integer, P.Pedersen)
genAndCommitR cparams = do
  r <- randomInZqM
  gr <- gexpSafeSPFM r
  c <- lift $ P.commit gr cparams
  return (r,c)

-- | 3(c), 4(a): Generate random c in Z_q
genC :: MonadRandom m => SPFM m Integer
genC = randomInZqM

-------------------------------------------------------------------------------

type DMap = Map Int Integer

-- | 4(c),5(c): computes d_i = c*k_i + r
computeDMap
  :: Integer -- ^ Counterparty's 'c'
  -> K1Map    -- ^ Current party's K1Map
  -> Integer -- ^ Current party's 'r'
  -> DMap
computeDMap c kmap r = map computeD kmap
  where
    -- This function does not use modular arithmetic because the
    -- exponent laws would not hold otherwise, and this is needed for
    -- verification later in the protocol. For example:
    --   ((x^7)^8 * (x^9) % p) /= (x^((7 * 8 + 9) % p)) % p
    computeD ki = c * ki + r

-- | 5(a), 6(a): Verifies that the counterparty has not lied about their
-- original commitment and has not tampered with the k values they used to
-- encrypt their original message: `g^d_i == (g^k_i)^c * g^r`
verifyDMap
  :: Monad m
  => DMap   -- ^ Counterparty's DMap
  -> GtoK1Map -- ^ Counterparty's (g^k, g^k') map
  -> Integer -- ^ Current party's 'c'
  -> Integer -- ^ Counterparty's 'g^r'
  -> SPFM m Bool
verifyDMap dmap gkmap c gr =
    and <$> zipWithM (verifyDi c gr) ds gks
  where
    ds = Map.elems dmap
    gks = Map.elems gkmap

-- | Verifies the ith `d_i` value for the ith byte of the secret
verifyDi
  :: Monad m
  => Integer -- ^ Current party's 'c'
  -> Integer -- ^ Counterparty's 'g^r'
  -> Integer -- ^ Counterparty's 'di'
  -> Integer -- ^ Counterparty's 'g^ki'
  -> SPFM m Bool
verifyDi c gr di gki = do
  gdi <- gexpSafeSPFM di
  let gkiToC = expSafeSPFM gki c
  gdi' <- gkiToC |*| pure gr
  return $ gdi == gdi'

-------------------------------------------------------------------------------
-- Reveal Stage
-------------------------------------------------------------------------------

-- | Computes the original bytestring that was commited by a counterparty once
-- they have supplied the neccessary parameters k_i and k_i'.
micpReveal :: MonadRandom m => K1Map -> K2Map -> SPFM m ByteString
micpReveal k1Map k2Map =
    BA.pack <$> zipWithM (curry kpairToByte) k1s k2s
  where
    k1s = Map.elems k1Map
    k2s = Map.elems k2Map

-- | Generate the byte correspoding to `Hn(k) xor Hn(k')` where
-- Hn(k) is the blum-micali PRNG hardcore nbit output
kpairToByte :: MonadRandom m => (Integer,Integer) -> SPFM m Word8
kpairToByte (k,k') = do
  hk <- micpBlumMicaliPRNG k
  hk' <- micpBlumMicaliPRNG k'
  return $ hk `xor` hk'

-------------------------------------------------------------------------------
-- High Level Protocol functions
-------------------------------------------------------------------------------

--------------------------
-- Initiator Phase 1
--------------------------

data IPhase1Priv = IPhase1Priv
  { iprivA :: Integer -- ^ Exponent such that g^iA = h (pedersen)
  }

data IPhase1Msg = IPhase1Msg
  { iCommitParams :: P.CommitParams -- ^ Bases to send to Responder
  }

iPhase1 :: MonadRandom m => Int -> m (IPhase1Priv, IPhase1Msg)
iPhase1 = fmap (bimap IPhase1Priv IPhase1Msg) . P.setup

--------------------------
-- Initiator Phase 2
--------------------------

data IPhase2Params = IPhase2Params
  { ip2pSecretBytes   :: [Word8]
  , ip2pRCommitParams :: P.CommitParams
  }

mkIPhase2Params :: ByteString -> RPhase1Msg -> IPhase2Params
mkIPhase2Params secret rp1msg =
  IPhase2Params
    { ip2pSecretBytes   = BA.unpack secret
    , ip2pRCommitParams = rCommitParams rp1msg
    }

data IPhase2Priv = IPhase2Priv
  { iprivK1Map  :: K1Map
  , iprivK2Map  :: K2Map
  , iprivR      :: Integer
  , iprivReveal :: P.Reveal  -- ^ Info to open the g^r commitment
  }

data IPhase2Msg = IPhase2Msg
  { iGtoK1Map   :: GtoK1Map
  , iGtoK2Map   :: GtoK2Map
  , iCommitment :: P.Commitment -- ^ Commitment of private R value
  , iC          :: Integer
  }

iPhase2 :: MonadRandom m => IPhase2Params -> SPFM m (IPhase2Priv, IPhase2Msg)
iPhase2 (IPhase2Params secretBytes rcp) = do
    (k1Map,k2Map) <- genKMaps secretBytes
    gToK1map <- kmapToGKMap k1Map
    gToK2map <- kmapToGKMap k2Map
    (r,pedersen) <- genAndCommitR rcp
    c <- genC
    let ip2Priv = IPhase2Priv k1Map k2Map r (P.reveal pedersen)
    let ip2Msg  = IPhase2Msg gToK1map gToK2map (P.commitment pedersen) c
    return (ip2Priv, ip2Msg)

--------------------------
-- Initiator Phase 3
--------------------------

data IPhase3Params = IPhase3Params
  { ip3pRCommitment   :: P.Commitment
  , ip3pRReveal       :: P.Reveal
  , ip3pRDMap         :: DMap
  , ip3pRGtoK1Map     :: GtoK1Map
  , ip3pRC            :: Integer
  , ip3pICommitParams :: P.CommitParams
  , ip3pIC            :: Integer
  , ip3pK1Map         :: K1Map
  , ip3pIR            :: Integer
  , ip3pIReveal       :: P.Reveal
  , ip3pA             :: Integer
  }

mkIPhase3Params
  :: IPhase1Priv
  -> IPhase1Msg
  -> IPhase2Priv
  -> IPhase2Msg
  -> RPhase1Msg
  -> RPhase2Msg
  -> IPhase3Params
mkIPhase3Params ip1priv ip1msg ip2priv ip2msg rp1msg rp2msg =
  IPhase3Params
    { ip3pRCommitment   = rCommit rp1msg
    , ip3pRReveal       = rReveal rp2msg
    , ip3pRDMap         = rDMap rp2msg
    , ip3pRGtoK1Map     = rGtoK1Map rp1msg
    , ip3pRC            = rC rp2msg
    , ip3pICommitParams = iCommitParams ip1msg
    , ip3pIC            = iC ip2msg
    , ip3pK1Map         = iprivK1Map ip2priv
    , ip3pIR            = iprivR ip2priv
    , ip3pIReveal       = iprivReveal ip2priv
    , ip3pA             = iprivA ip1priv
    }

data IPhase3Msg
  = IPhase3Reject
  | IPhase3Msg
      { iReveal :: P.Reveal
      , iDMap   :: DMap
      , iA      :: Integer
      }

iPhase3 :: MonadRandom m => IPhase3Params -> SPFM m IPhase3Msg
iPhase3 (IPhase3Params rcom rrev rdmap rgtok1map rc icp ic ik1map ir irev ia)
  | P.open icp rcom rrev = do
      dmapIsValid <- verifyDMap rdmap rgtok1map ic $ P.revealVal rrev
      if dmapIsValid then
        return IPhase3Msg
          { iReveal = irev
          , iDMap   = computeDMap rc ik1map ir
          , iA      = ia
          }
      else return IPhase3Reject
  | otherwise = return IPhase3Reject

--------------------------
-- Initiator Phase 4
--------------------------

data IPhase4Params = IPhase4Params
  { ip4pRA            :: Integer
  , ip4pRCommitParams :: P.CommitParams
  , ip4pRK2Map        :: K2Map
  , ip4pRGK2Map       :: GtoK2Map
  , ip4pIK2Map        :: K2Map
  }

mkIPhase4Params
  :: IPhase2Priv
  -> RPhase1Msg
  -> RPhase1Priv
  -> RPhase3Msg
  -> IPhase4Params
mkIPhase4Params ip2priv rp1msg rp1priv rp3msg =
  IPhase4Params
    { ip4pRA            = rprivA rp1priv
    , ip4pRCommitParams = rCommitParams rp1msg
    , ip4pRK2Map        = rK2Map rp3msg
    , ip4pRGK2Map       = rGtoK2Map rp1msg
    , ip4pIK2Map        = iprivK2Map ip2priv
    }

data IPhase4Msg
  = IPhase4Reject
  | IPhase4Msg
      { iK2Map :: K2Map
      }

iPhase4 :: MonadRandom m => IPhase4Params -> SPFM m IPhase4Msg
iPhase4 (IPhase4Params ra rcp rk2map rgtok2map ik2map)
  | P.verifyCommitParams ra rcp = do
      gToK2Map <- kmapToGKMap rk2map
      if gToK2Map == rgtok2map then
        return IPhase4Msg
          { iK2Map = ik2map
          }
      else return IPhase4Reject
  | otherwise = return IPhase4Reject

--------------------------
-- Initiator Reveal -XXX
--------------------------

data IRevealMsg = IRevealMsg
  { iK1Map :: K1Map }

--------------------------------------------------------------------------

--------------------------
-- Responder Phase 1
--------------------------

data RPhase1Params = RPhase1Params
  { rp1pSecurityParam :: Int
  , rp1pSecretBytes   :: [Word8]
  , rp1pICommitParams :: P.CommitParams
  }

mkRPhase1Params :: Int -> ByteString -> P.CommitParams -> RPhase1Params
mkRPhase1Params secParam secret icp =
  RPhase1Params
    { rp1pSecurityParam = secParam
    , rp1pSecretBytes   = BA.unpack secret
    , rp1pICommitParams = icp
    }

data RPhase1Priv = RPhase1Priv
  { rprivA      :: Integer  -- ^ Exponent such that g^rA = h (pedersen)
  , rprivK1Map  :: K1Map
  , rprivK2Map  :: K2Map
  , rprivReveal :: P.Reveal
  , rprivR      :: Integer
  }

data RPhase1Msg = RPhase1Msg
  { rCommitParams :: P.CommitParams
  , rGtoK1Map     :: GtoK1Map
  , rGtoK2Map     :: GtoK2Map
  , rCommit       :: P.Commitment -- ^ Commitment of private R value
  }

rPhase1 :: MonadRandom m => RPhase1Params -> SPFM m (RPhase1Priv, RPhase1Msg)
rPhase1 (RPhase1Params secParam secretBytes icp) = do
  (a,commitParams) <- lift $ P.setup secParam
  (k1Map,k2Map) <- genKMaps secretBytes
  gtoK1Map <- kmapToGKMap k1Map
  gtoK2Map <- kmapToGKMap k2Map
  (r,pedersen) <- genAndCommitR icp
  let rPhase1Priv = RPhase1Priv a k1Map k2Map (P.reveal pedersen) r
  let rPhase1Msg  = RPhase1Msg commitParams gtoK1Map gtoK2Map (P.commitment pedersen)
  return (rPhase1Priv, rPhase1Msg)

--------------------------
-- Responder Phase 2
--------------------------

data RPhase2Params = RPhase2Params
  { rp2pIC      :: Integer
  , rp2pRK1Map  :: K1Map
  , rp2pRReveal :: P.Reveal
  , rp2pRR      :: Integer
  }

mkRPhase2Params :: RPhase1Priv -> IPhase2Msg -> RPhase2Params
mkRPhase2Params rp1priv ip2msg =
  RPhase2Params
    { rp2pIC      = iC ip2msg
    , rp2pRK1Map  = rprivK1Map rp1priv
    , rp2pRReveal = rprivReveal rp1priv
    , rp2pRR      = rprivR rp1priv
    }

data RPhase2Msg = RPhase2Msg
  { rC      :: Integer
  , rReveal :: P.Reveal
  , rDMap   :: DMap
  }

rPhase2 :: MonadRandom m => RPhase2Params -> SPFM m RPhase2Msg
rPhase2 (RPhase2Params ic k1Map rreveal r) = do
  r <- genC
  let dmap = computeDMap ic k1Map r
  return RPhase2Msg
    { rC = r
    , rReveal = rreveal
    , rDMap = dmap
    }

--------------------------
-- Responder Phase 3
--------------------------

data RPhase3Params = RPhase3Params
  { rp3pRCommitParams :: P.CommitParams
  , rp3pICommitment   :: P.Commitment
  , rp3pIReveal       :: P.Reveal
  , rp3pIDMap         :: DMap
  , rp3pIGtoK1Map     :: GtoK1Map
  , rp3pRC            :: Integer
  , rp3pIA            :: Integer
  , rp3pICommitParams :: P.CommitParams
  , rp3pRK2Map        :: K2Map
  , rp3pRA            :: Integer
  }

mkRPhase3Params
  :: RPhase1Priv
  -> RPhase1Msg
  -> RPhase2Msg
  -> IPhase1Msg
  -> IPhase2Msg
  -> IPhase3Msg
  -> RPhase3Params
mkRPhase3Params rp1priv rp1msg rp2msg ip1msg ip2msg ip3msg =
  RPhase3Params
    { rp3pRCommitParams = rCommitParams rp1msg
    , rp3pICommitment   = iCommitment ip2msg
    , rp3pIReveal       = iReveal ip3msg
    , rp3pIDMap         = iDMap ip3msg
    , rp3pIGtoK1Map     = iGtoK1Map ip2msg
    , rp3pRC            = rC rp2msg
    , rp3pIA            = iA ip3msg
    , rp3pICommitParams = iCommitParams ip1msg
    , rp3pRK2Map        = rprivK2Map rp1priv
    , rp3pRA            = rprivA rp1priv
    }

data RPhase3Msg
  = RPhase3Reject
  | RPhase3Msg
      { rK2Map  :: K2Map
      , rA      :: Integer
      }

rPhase3 :: MonadRandom m => RPhase3Params -> SPFM m RPhase3Msg
rPhase3 (RPhase3Params rcp icom irev idmap igtoKMap rc ia icp rK2Map ra)
  | P.open rcp icom irev = do
      dmapIsValid <- verifyDMap idmap igtoKMap rc (P.revealVal irev)
      if dmapIsValid then
        return $ RPhase3Msg rK2Map ra
      else return RPhase3Reject
  | otherwise = return RPhase3Reject


--------------------------
-- Responder Phase 4 XXX
--------------------------

data RPhase4Msg = RPhase4Msg
  { rK1Map :: K1Map
  }
