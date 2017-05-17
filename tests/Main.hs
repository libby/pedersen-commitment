{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Main (
  main,
) where

import Protolude

import qualified Crypto.PubKey.ECC.Prim as ECC

import Test.Tasty
import Test.Tasty.HUnit as HU
import Test.Tasty.QuickCheck
import Test.QuickCheck.Monadic as QM

import Example (micpWrapper, micpComponents)

import Pedersen
import PrimeField

suite :: TestTree
suite = testGroup "Test Suite" [
    testGroup "Units"
      [ pedersenTests
      , micpTests
      ]
  ]
 
pedersenTests :: TestTree
pedersenTests = testGroup "Pedersen Commitment Scheme"
  [ localOption (QuickCheckTests 50) $
      testProperty "x == Open(Commit(x),r)" $ monadicIO $ do
        (a, cp) <- liftIO $ setup 256
        x <- liftIO $ randomInZq $ pedersenSPF cp
        pc <- liftIO $ commit x cp
        QM.assert $ open cp (commitment pc) (reveal pc)

  , testCaseSteps "Additive Homomorphic Commitments" $ \step -> do
      step "Generating commit params..."
      (a,cp) <- setup 256
      let spf = pedersenSPF cp

      step "Generating two random numbers in Zp to commit..."
      x <- randomInZq spf
      y <- randomInZq spf

      step "Committing the two random numbers..."
      px@(Pedersen cx rx) <- commit x cp
      py@(Pedersen cy ry) <- commit y cp

      step "Verifying Additive Homomorphic property..."
      let cz = addCommitments cp cx cy
      let pz = verifyAddCommitments cp px py
      assertAddHomo $ cz == commitment pz

  , testProperty "x == Open(Commit(x),r) (EC) " $ 
      monadicIO $ do
        (a,cp) <- liftIO $ ecSetup Nothing -- uses SECP256k1 by default
        x <- liftIO $ ECC.scalarGenerate $ ecCurve cp
        pc <- liftIO $ ecCommit x cp
        QM.assert $ ecOpen cp (ecCommitment pc) (ecReveal pc)
  
  , testCaseSteps "Additive Homomorphic Commitments (EC) " $ \step -> do
      step "Generating commit params..."
      (a,ecp) <- ecSetup Nothing 
      let curve = ecCurve ecp

      step "Generating two random numbers in Ep (EC prime field order q)..."
      x <- ECC.scalarGenerate curve 
      y <- ECC.scalarGenerate curve

      step "Committing the two random numbers..."
      px@(ECPedersen cx rx) <- ecCommit x ecp
      py@(ECPedersen cy ry) <- ecCommit y ecp

      step "Verifying Additive Homomorphic property..."
      let cz = ecAddCommitments ecp cx cy
      let pz = ecVerifyAddCommitments ecp px py
      assertAddHomo $ cz == ecCommitment pz

  , testCaseSteps "Additive Homomorphic property (EC) | nG + C(x) == (x + n)G + rH" $ \step -> do
      step "Generating commit params..."
      (a,ecp) <- ecSetup Nothing 
      let curve = ecCurve ecp

      step "Generating a random number to commit..."
      x <- ECC.scalarGenerate curve
      step "Committing the the random number..."
      px@(ECPedersen cx rx) <- ecCommit x ecp

      step "Generating a random number to add to the commitment..."
      n <- ECC.scalarGenerate curve
    
      step "Verifying the Additive homomorphic property"
      let cy = ecAddInteger ecp cx n
      let py = ecVerifyAddInteger ecp px n 
      assertAddHomo $ cy == ecCommitment py  

  ]
  where
    assertAddHomo :: Bool -> IO () 
    assertAddHomo = assertBool "Additive homomorphic property doesn't hold."  

micpTests :: TestTree
micpTests = testGroup "Mutually Independent Commitment Protocol"
  [ testCase "Testing MICP Components" $
      assertBool "MICP Components test failed!" =<< micpComponents 256
  , testCase "Testing MICP Wrapper" $ 
      assertBool "MICP Wrapper test failed!" =<< micpWrapper 256
  ]

main :: IO ()
main = defaultMain suite
