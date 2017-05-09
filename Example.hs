module Example (
  testMICP,
  testPedersen,
  testBlumMicaliPRNG,
) where

import Protolude

import MICP
import Pedersen
import PrimeField

import Crypto.Hash
import Crypto.Number.Serialize (os2ip)
import qualified Data.ByteArray as BA

sha256 :: ByteString -> ByteString
sha256 bs = BA.convert (hash bs :: Digest SHA3_256)

testBlumMicaliPRNG :: IO Integer
testBlumMicaliPRNG = do
  let k = 256
  (a,cparams) <- setup k
  runSPFT (pedersenSPF cparams) $ do
    seed <- genPRNGSeed
    lift . blumMicaliPRNG k seed =<< ask

testPedersen :: ByteString -> IO Bool
testPedersen bs = do
  let hashedBs = os2ip $ sha256 bs
  (a,commitParams) <- setup 256 -- hashStorage uses sha256
  pedersen <- commit hashedBs commitParams
  return $ open commitParams pedersen

-- | In this test, all values computed are in scope for both Alice & Bob, so
-- instead of "sending" those values to one another, we can just use them for
-- the respective counterparty computations.
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
    unless (open aCommitParams bobPedersen) $
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
    unless (open bCommitParams alicePedersen) $
      panic "Alice's commit is illegitimate!"
    --       bob verifies g^di = (g^ki)^c + g^r
    aliceDMapVerified <- verifyDMap aliceDMap aliceGtoKMap bobC $ rVal $ reveal alicePedersen
    unless aliceDMapVerified $
      panic "Alice's computations are wrong!"

    -- 6(b): bob checks that alice's ga^a == ha
    unless (verifyCommitParams aliceA aCommitParams) $
      panic "Alice's pedersen bases are not valid!"

    -- 6(c): bob sends k'map and bob's 'a' to alice

    -- 7(a): alice checks that bob's ga^a == ha
    unless (verifyCommitParams bobA bCommitParams) $
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

    -- Using bob/alice env respectively to show this reveal can happen within
    -- the shared env only, and doesn't care about local pedersen params
    aliceMsgRes <- micpReveal aliceKMap aliceK'Map
    let aliceResEqMsg = aliceMsgRes == aliceMsg
    bobMsgRes <- micpReveal bobKMap bobK'Map
    let bobResEqMsg = bobMsgRes == bobMsg

    return $ aliceResEqMsg && bobResEqMsg
